import V185TrunkScan23Chunk0360

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2135225 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2135225 : Nat := 118140960795 + 2135225 * 2 ^ 59
def prefixEnd_2135225 : Nat := 4983230072969 + 3 ^ 40 * 2135225 * 2
def baseEnd_2135225 : Nat := 1096396730496513656067785

theorem tailTrace_2135225 : CollatzResearch.WordTrace tailWord_2135225 prefixEnd_2135225 1096396730496513656067785 := by
  unfold tailWord_2135225
  simp only [CollatzResearch.WordTrace]
  refine ⟨77878053689451967242455129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51918702459634644828303419 77878053689451967242455129)
  ·
    refine ⟨58408540267088975431841347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77878053689451967242455129 58408540267088975431841347)
    ·
      refine ⟨87612810400633463147762021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58408540267088975431841347 87612810400633463147762021)
      ·
        refine ⟨16427401950118774340205379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87612810400633463147762021 16427401950118774340205379)
        ·
          refine ⟨24641102925178161510308069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16427401950118774340205379 24641102925178161510308069)
          ·
            refine ⟨4620206798470905283182763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24641102925178161510308069 4620206798470905283182763)
            ·
              refine ⟨6930310197706357924774145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4620206798470905283182763 6930310197706357924774145)
              ·
                refine ⟨5197732648279768443580609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6930310197706357924774145 5197732648279768443580609)
                ·
                  refine ⟨3898299486209826332685457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5197732648279768443580609 3898299486209826332685457)
                  ·
                    refine ⟨2923724614657369749514093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3898299486209826332685457 2923724614657369749514093)
                    ·
                      refine ⟨1096396730496513656067785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923724614657369749514093 1096396730496513656067785)
                      ·
                        rfl

theorem cell23_2135225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2135225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135225 prefixEnd_2135225 := by exact prefixLift 2135225
  have htrace : WordTrace (prefixWord ++ tailWord_2135225) baseStart_2135225 baseEnd_2135225 := by
    simpa [prefixWord, tailWord_2135225, baseEnd_2135225] using wordTrace_append hprefix tailTrace_2135225
  have hstable : (prefixWord ++ tailWord_2135225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135225).length < 2 ^ (prefixWord ++ tailWord_2135225).sum := by decide
  have hdescent : baseEnd_2135225 < baseStart_2135225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135228 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 8]
def baseStart_2135228 : Nat := 118140960795 + 2135228 * 2 ^ 59
def prefixEnd_2135228 : Nat := 4983230072969 + 3 ^ 40 * 2135228 * 2
def baseEnd_2135228 : Nat := 121822030104275238258919

theorem tailTrace_2135228 : CollatzResearch.WordTrace tailWord_2135228 prefixEnd_2135228 121822030104275238258919 := by
  unfold tailWord_2135228
  simp only [CollatzResearch.WordTrace]
  refine ⟨38939081554220549377407169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51918775405627399169876225 38939081554220549377407169)
  ·
    refine ⟨29204311165665412033055377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38939081554220549377407169 29204311165665412033055377)
    ·
      refine ⟨21903233374249059024791533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29204311165665412033055377 21903233374249059024791533)
      ·
        refine ⟨8213712515343397134296825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21903233374249059024791533 8213712515343397134296825)
        ·
          refine ⟨6160284386507547850722619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8213712515343397134296825 6160284386507547850722619)
          ·
            refine ⟨9240426579761321776083929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6160284386507547850722619 9240426579761321776083929)
            ·
              refine ⟨6930319934820991332062947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9240426579761321776083929 6930319934820991332062947)
              ·
                refine ⟨10395479902231486998094421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6930319934820991332062947 10395479902231486998094421)
                ·
                  refine ⟨121822030104275238258919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10395479902231486998094421 121822030104275238258919)
                  ·
                    rfl

theorem cell23_2135228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_2135228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135228 prefixEnd_2135228 := by exact prefixLift 2135228
  have htrace : WordTrace (prefixWord ++ tailWord_2135228) baseStart_2135228 baseEnd_2135228 := by
    simpa [prefixWord, tailWord_2135228, baseEnd_2135228] using wordTrace_append hprefix tailTrace_2135228
  have hstable : (prefixWord ++ tailWord_2135228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135228).length < 2 ^ (prefixWord ++ tailWord_2135228).sum := by decide
  have hdescent : baseEnd_2135228 < baseStart_2135228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135231 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_2135231 : Nat := 118140960795 + 2135231 * 2 ^ 59
def prefixEnd_2135231 : Nat := 4983230072969 + 3 ^ 40 * 2135231 * 2
def baseEnd_2135231 : Nat := 1096399811380440632592757

theorem tailTrace_2135231 : CollatzResearch.WordTrace tailWord_2135231 prefixEnd_2135231 1096399811380440632592757 := by
  unfold tailWord_2135231
  simp only [CollatzResearch.WordTrace]
  refine ⟨77878272527430230267173547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51918848351620153511449031 77878272527430230267173547)
  ·
    refine ⟨116817408791145345400760321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77878272527430230267173547 116817408791145345400760321)
    ·
      refine ⟨87613056593359009050570241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116817408791145345400760321 87613056593359009050570241)
      ·
        refine ⟨65709792445019256787927681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87613056593359009050570241 65709792445019256787927681)
        ·
          refine ⟨49282344333764442590945761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65709792445019256787927681 49282344333764442590945761)
          ·
            refine ⟨36961758250323331943209321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49282344333764442590945761 36961758250323331943209321)
            ·
              refine ⟨27721318687742498957406991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36961758250323331943209321 27721318687742498957406991)
              ·
                refine ⟨41581978031613748436110487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27721318687742498957406991 41581978031613748436110487)
                ·
                  refine ⟨62372967047420622654165731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41581978031613748436110487 62372967047420622654165731)
                  ·
                    refine ⟨93559450571130933981248597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62372967047420622654165731 93559450571130933981248597)
                    ·
                      refine ⟨1096399811380440632592757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 93559450571130933981248597 1096399811380440632592757)
                      ·
                        rfl

theorem cell23_2135231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_2135231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135231 prefixEnd_2135231 := by exact prefixLift 2135231
  have htrace : WordTrace (prefixWord ++ tailWord_2135231) baseStart_2135231 baseEnd_2135231 := by
    simpa [prefixWord, tailWord_2135231, baseEnd_2135231] using wordTrace_append hprefix tailTrace_2135231
  have hstable : (prefixWord ++ tailWord_2135231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135231).length < 2 ^ (prefixWord ++ tailWord_2135231).sum := by decide
  have hdescent : baseEnd_2135231 < baseStart_2135231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135232 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 3, 4]
def baseStart_2135232 : Nat := 118140960795 + 2135232 * 2 ^ 59
def prefixEnd_2135232 : Nat := 4983230072969 + 3 ^ 40 * 2135232 * 2
def baseEnd_2135232 : Nat := 365466774953698376226751

theorem tailTrace_2135232 : CollatzResearch.WordTrace tailWord_2135232 prefixEnd_2135232 365466774953698376226751 := by
  unfold tailWord_2135232
  simp only [CollatzResearch.WordTrace]
  refine ⟨38939154500213303718979975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51918872666951071625306633 38939154500213303718979975)
  ·
    refine ⟨58408731750319955578469963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38939154500213303718979975 58408731750319955578469963)
    ·
      refine ⟨87613097625479933367704945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58408731750319955578469963 87613097625479933367704945)
      ·
        refine ⟨65709823219109950025778709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87613097625479933367704945 65709823219109950025778709)
        ·
          refine ⟨3080147963395778907458377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65709823219109950025778709 3080147963395778907458377)
          ·
            refine ⟨2310110972546834180593783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3080147963395778907458377 2310110972546834180593783)
            ·
              refine ⟨3465166458820251270890675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310110972546834180593783 3465166458820251270890675)
              ·
                refine ⟨5197749688230376906336013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3465166458820251270890675 5197749688230376906336013)
                ·
                  refine ⟨1949156133086391339876005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5197749688230376906336013 1949156133086391339876005)
                  ·
                    refine ⟨365466774953698376226751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1949156133086391339876005 365466774953698376226751)
                    ·
                      rfl

theorem cell23_2135232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_2135232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135232 prefixEnd_2135232 := by exact prefixLift 2135232
  have htrace : WordTrace (prefixWord ++ tailWord_2135232) baseStart_2135232 baseEnd_2135232 := by
    simpa [prefixWord, tailWord_2135232, baseEnd_2135232] using wordTrace_append hprefix tailTrace_2135232
  have hstable : (prefixWord ++ tailWord_2135232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135232).length < 2 ^ (prefixWord ++ tailWord_2135232).sum := by decide
  have hdescent : baseEnd_2135232 < baseStart_2135232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135251 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_2135251 : Nat := 118140960795 + 2135251 * 2 ^ 59
def prefixEnd_2135251 : Nat := 4983230072969 + 3 ^ 40 * 2135251 * 2
def baseEnd_2135251 : Nat := 1096410080993530554342665

theorem tailTrace_2135251 : CollatzResearch.WordTrace tailWord_2135251 prefixEnd_2135251 1096410080993530554342665 := by
  unfold tailWord_2135251
  simp only [CollatzResearch.WordTrace]
  refine ⟨77879001987357773682901607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51919334658238515788601071 77879001987357773682901607)
  ·
    refine ⟨116818502981036660524352411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77879001987357773682901607 116818502981036660524352411)
    ·
      refine ⟨175227754471554990786528617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116818502981036660524352411 175227754471554990786528617)
      ·
        refine ⟨131420815853666243089896463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175227754471554990786528617 131420815853666243089896463)
        ·
          refine ⟨197131223780499364634844695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131420815853666243089896463 197131223780499364634844695)
          ·
            refine ⟨295696835670749046952267043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197131223780499364634844695 295696835670749046952267043)
            ·
              refine ⟨443545253506123570428400565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295696835670749046952267043 443545253506123570428400565)
              ·
                refine ⟨41582367516199084727662553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 443545253506123570428400565 41582367516199084727662553)
                ·
                  refine ⟨31186775637149313545746915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41582367516199084727662553 31186775637149313545746915)
                  ·
                    refine ⟨46780163455723970318620373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31186775637149313545746915 46780163455723970318620373)
                    ·
                      refine ⟨1096410080993530554342665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46780163455723970318620373 1096410080993530554342665)
                      ·
                        rfl

theorem cell23_2135251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_2135251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135251 prefixEnd_2135251 := by exact prefixLift 2135251
  have htrace : WordTrace (prefixWord ++ tailWord_2135251) baseStart_2135251 baseEnd_2135251 := by
    simpa [prefixWord, tailWord_2135251, baseEnd_2135251] using wordTrace_append hprefix tailTrace_2135251
  have hstable : (prefixWord ++ tailWord_2135251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135251).length < 2 ^ (prefixWord ++ tailWord_2135251).sum := by decide
  have hdescent : baseEnd_2135251 < baseStart_2135251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135255 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_2135255 : Nat := 118140960795 + 2135255 * 2 ^ 59
def prefixEnd_2135255 : Nat := 4983230072969 + 3 ^ 40 * 2135255 * 2
def baseEnd_2135255 : Nat := 1096412134916148538692647

theorem tailTrace_2135255 : CollatzResearch.WordTrace tailWord_2135255 prefixEnd_2135255 1096412134916148538692647 := by
  unfold tailWord_2135255
  simp only [CollatzResearch.WordTrace]
  refine ⟨77879147879343282366047219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51919431919562188244031479 77879147879343282366047219)
  ·
    refine ⟨116818721819014923549070829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77879147879343282366047219 116818721819014923549070829)
    ·
      refine ⟨43807020682130596330901561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116818721819014923549070829 43807020682130596330901561)
      ·
        refine ⟨32855265511597947248176171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43807020682130596330901561 32855265511597947248176171)
        ·
          refine ⟨49282898267396920872264257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32855265511597947248176171 49282898267396920872264257)
          ·
            refine ⟨36962173700547690654198193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49282898267396920872264257 36962173700547690654198193)
            ·
              refine ⟨27721630275410767990648645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36962173700547690654198193 27721630275410767990648645)
              ·
                refine ⟨5197805676639518998246621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27721630275410767990648645 5197805676639518998246621)
                ·
                  refine ⟨1949177128739819624342483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5197805676639518998246621 1949177128739819624342483)
                  ·
                    refine ⟨2923765693109729436513725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1949177128739819624342483 2923765693109729436513725)
                    ·
                      refine ⟨1096412134916148538692647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923765693109729436513725 1096412134916148538692647)
                      ·
                        rfl

theorem cell23_2135255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_2135255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135255 prefixEnd_2135255 := by exact prefixLift 2135255
  have htrace : WordTrace (prefixWord ++ tailWord_2135255) baseStart_2135255 baseEnd_2135255 := by
    simpa [prefixWord, tailWord_2135255, baseEnd_2135255] using wordTrace_append hprefix tailTrace_2135255
  have hstable : (prefixWord ++ tailWord_2135255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135255).length < 2 ^ (prefixWord ++ tailWord_2135255).sum := by decide
  have hdescent : baseEnd_2135255 < baseStart_2135255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135305 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 2, 4]
def baseStart_2135305 : Nat := 118140960795 + 2135305 * 2 ^ 59
def prefixEnd_2135305 : Nat := 4983230072969 + 3 ^ 40 * 2135305 * 2
def baseEnd_2135305 : Nat := 365479269649624447689139

theorem tailTrace_2135305 : CollatzResearch.WordTrace tailWord_2135305 prefixEnd_2135305 365479269649624447689139 := by
  unfold tailWord_2135305
  simp only [CollatzResearch.WordTrace]
  refine ⟨77880971529162140905367369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51920647686108093936911579 77880971529162140905367369)
  ·
    refine ⟨58410728646871605679025527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77880971529162140905367369 58410728646871605679025527)
    ·
      refine ⟨87616092970307408518538291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58410728646871605679025527 87616092970307408518538291)
      ·
        refine ⟨131424139455461112777807437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87616092970307408518538291 131424139455461112777807437)
        ·
          refine ⟨49284052295797917291677789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131424139455461112777807437 49284052295797917291677789)
          ·
            refine ⟨18481519610924218984379171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49284052295797917291677789 18481519610924218984379171)
            ·
              refine ⟨27722279416386328476568757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18481519610924218984379171 27722279416386328476568757)
              ·
                refine ⟨2598963695286218294678321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27722279416386328476568757 2598963695286218294678321)
                ·
                  refine ⟨1949222771464663721008741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2598963695286218294678321 1949222771464663721008741)
                  ·
                    refine ⟨365479269649624447689139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1949222771464663721008741 365479269649624447689139)
                    ·
                      rfl

theorem cell23_2135305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_2135305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135305 prefixEnd_2135305 := by exact prefixLift 2135305
  have htrace : WordTrace (prefixWord ++ tailWord_2135305) baseStart_2135305 baseEnd_2135305 := by
    simpa [prefixWord, tailWord_2135305, baseEnd_2135305] using wordTrace_append hprefix tailTrace_2135305
  have hstable : (prefixWord ++ tailWord_2135305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135305).length < 2 ^ (prefixWord ++ tailWord_2135305).sum := by decide
  have hdescent : baseEnd_2135305 < baseStart_2135305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135332 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2135332 : Nat := 118140960795 + 2135332 * 2 ^ 59
def prefixEnd_2135332 : Nat := 4983230072969 + 3 ^ 40 * 2135332 * 2
def baseEnd_2135332 : Nat := 1096451672926544737429793

theorem tailTrace_2135332 : CollatzResearch.WordTrace tailWord_2135332 prefixEnd_2135332 1096451672926544737429793 := by
  unfold tailWord_2135332
  simp only [CollatzResearch.WordTrace]
  refine ⟨38940978150032162258300125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51921304200042883011066833 38940978150032162258300125)
  ·
    refine ⟨14602866806262060846862547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38940978150032162258300125 14602866806262060846862547)
    ·
      refine ⟨21904300209393091270293821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14602866806262060846862547 21904300209393091270293821)
      ·
        refine ⟨8214112578522409226360183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21904300209393091270293821 8214112578522409226360183)
        ·
          refine ⟨12321168867783613839540275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8214112578522409226360183 12321168867783613839540275)
          ·
            refine ⟨18481753301675420759310413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12321168867783613839540275 18481753301675420759310413)
            ·
              refine ⟨6930657488128282784741405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18481753301675420759310413 6930657488128282784741405)
              ·
                refine ⟨2598996558048106044278027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6930657488128282784741405 2598996558048106044278027)
                ·
                  refine ⟨3898494837072159066417041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598996558048106044278027 3898494837072159066417041)
                  ·
                    refine ⟨2923871127804119299812781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3898494837072159066417041 2923871127804119299812781)
                    ·
                      refine ⟨1096451672926544737429793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923871127804119299812781 1096451672926544737429793)
                      ·
                        rfl

theorem cell23_2135332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2135332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135332 prefixEnd_2135332 := by exact prefixLift 2135332
  have htrace : WordTrace (prefixWord ++ tailWord_2135332) baseStart_2135332 baseEnd_2135332 := by
    simpa [prefixWord, tailWord_2135332, baseEnd_2135332] using wordTrace_append hprefix tailTrace_2135332
  have hstable : (prefixWord ++ tailWord_2135332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135332).length < 2 ^ (prefixWord ++ tailWord_2135332).sum := by decide
  have hdescent : baseEnd_2135332 < baseStart_2135332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135346 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_2135346 : Nat := 118140960795 + 2135346 * 2 ^ 59
def prefixEnd_2135346 : Nat := 4983230072969 + 3 ^ 40 * 2135346 * 2
def baseEnd_2135346 : Nat := 1096458861655707682654729

theorem tailTrace_2135346 : CollatzResearch.WordTrace tailWord_2135346 prefixEnd_2135346 1096458861655707682654729 := by
  unfold tailWord_2135346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470616730503401226902473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51921644614675736605073261 19470616730503401226902473)
  ·
    refine ⟨14602962547877550920176855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19470616730503401226902473 14602962547877550920176855)
    ·
      refine ⟨21904443821816326380265283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14602962547877550920176855 21904443821816326380265283)
      ·
        refine ⟨32856665732724489570397925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21904443821816326380265283 32856665732724489570397925)
        ·
          refine ⟨6160624824885841794449611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32856665732724489570397925 6160624824885841794449611)
          ·
            refine ⟨9240937237328762691674417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6160624824885841794449611 9240937237328762691674417)
            ·
              refine ⟨6930702927996572018755813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9240937237328762691674417 6930702927996572018755813)
              ·
                refine ⟨1299506798999357253516715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6930702927996572018755813 1299506798999357253516715)
                ·
                  refine ⟨1949260198499035880275073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299506798999357253516715 1949260198499035880275073)
                  ·
                    refine ⟨1461945148874276910206305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949260198499035880275073 1461945148874276910206305)
                    ·
                      refine ⟨1096458861655707682654729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461945148874276910206305 1096458861655707682654729)
                      ·
                        rfl

theorem cell23_2135346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_2135346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135346 prefixEnd_2135346 := by exact prefixLift 2135346
  have htrace : WordTrace (prefixWord ++ tailWord_2135346) baseStart_2135346 baseEnd_2135346 := by
    simpa [prefixWord, tailWord_2135346, baseEnd_2135346] using wordTrace_append hprefix tailTrace_2135346
  have hstable : (prefixWord ++ tailWord_2135346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135346).length < 2 ^ (prefixWord ++ tailWord_2135346).sum := by decide
  have hdescent : baseEnd_2135346 < baseStart_2135346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135413 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_2135413 : Nat := 118140960795 + 2135413 * 2 ^ 59
def prefixEnd_2135413 : Nat := 4983230072969 + 3 ^ 40 * 2135413 * 2
def baseEnd_2135413 : Nat := 1096493264859558920516921

theorem tailTrace_2135413 : CollatzResearch.WordTrace tailWord_2135413 prefixEnd_2135413 1096493264859558920516921 := by
  unfold tailWord_2135413
  simp only [CollatzResearch.WordTrace]
  refine ⟨77884910612770875350298893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51923273741847250233532595 77884910612770875350298893)
  ·
    refine ⟨29206841479789078256362085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77884910612770875350298893 29206841479789078256362085)
    ·
      refine ⟨5476282777460452173067891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29206841479789078256362085 5476282777460452173067891)
      ·
        refine ⟨8214424166190678259601837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5476282777460452173067891 8214424166190678259601837)
        ·
          refine ⟨3080409062321504347350689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8214424166190678259601837 3080409062321504347350689)
          ·
            refine ⟨2310306796741128260513017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3080409062321504347350689 2310306796741128260513017)
            ·
              refine ⟨1732730097555846195384763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310306796741128260513017 1732730097555846195384763)
              ·
                refine ⟨2599095146333769293077145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732730097555846195384763 2599095146333769293077145)
                ·
                  refine ⟨1949321359750326969807859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2599095146333769293077145 1949321359750326969807859)
                  ·
                    refine ⟨2923982039625490454711789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1949321359750326969807859 2923982039625490454711789)
                    ·
                      refine ⟨1096493264859558920516921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2923982039625490454711789 1096493264859558920516921)
                      ·
                        rfl

theorem cell23_2135413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_2135413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135413 prefixEnd_2135413 := by exact prefixLift 2135413
  have htrace : WordTrace (prefixWord ++ tailWord_2135413) baseStart_2135413 baseEnd_2135413 := by
    simpa [prefixWord, tailWord_2135413, baseEnd_2135413] using wordTrace_append hprefix tailTrace_2135413
  have hstable : (prefixWord ++ tailWord_2135413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135413).length < 2 ^ (prefixWord ++ tailWord_2135413).sum := by decide
  have hdescent : baseEnd_2135413 < baseStart_2135413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135418 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_2135418 : Nat := 118140960795 + 2135418 * 2 ^ 59
def prefixEnd_2135418 : Nat := 4983230072969 + 3 ^ 40 * 2135418 * 2
def baseEnd_2135418 : Nat := 1096495832262831400954397

theorem tailTrace_2135418 : CollatzResearch.WordTrace tailWord_2135418 prefixEnd_2135418 1096495832262831400954397 := by
  unfold tailWord_2135418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19471273244438190301057727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51923395318501840802820605 19471273244438190301057727)
  ·
    refine ⟨29206909866657285451586591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19471273244438190301057727 29206909866657285451586591)
    ·
      refine ⟨43810364799985928177379887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29206909866657285451586591 43810364799985928177379887)
      ·
        refine ⟨65715547199978892266069831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43810364799985928177379887 65715547199978892266069831)
        ·
          refine ⟨98573320799968338399104747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65715547199978892266069831 98573320799968338399104747)
          ·
            refine ⟨147859981199952507598657121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98573320799968338399104747 147859981199952507598657121)
            ·
              refine ⟨110894985899964380698992841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147859981199952507598657121 110894985899964380698992841)
              ·
                refine ⟨83171239424973285524244631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110894985899964380698992841 83171239424973285524244631)
                ·
                  refine ⟨124756859137459928286366947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83171239424973285524244631 124756859137459928286366947)
                  ·
                    refine ⟨187135288706189892429550421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124756859137459928286366947 187135288706189892429550421)
                    ·
                      refine ⟨1096495832262831400954397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 187135288706189892429550421 1096495832262831400954397)
                      ·
                        rfl

theorem cell23_2135418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2135418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135418 prefixEnd_2135418 := by exact prefixLift 2135418
  have htrace : WordTrace (prefixWord ++ tailWord_2135418) baseStart_2135418 baseEnd_2135418 := by
    simpa [prefixWord, tailWord_2135418, baseEnd_2135418] using wordTrace_append hprefix tailTrace_2135418
  have hstable : (prefixWord ++ tailWord_2135418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135418).length < 2 ^ (prefixWord ++ tailWord_2135418).sum := by decide
  have hdescent : baseEnd_2135418 < baseStart_2135418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135419 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 2, 2, 2]
def baseStart_2135419 : Nat := 118140960795 + 2135419 * 2 ^ 59
def prefixEnd_2135419 : Nat := 4983230072969 + 3 ^ 40 * 2135419 * 2
def baseEnd_2135419 : Nat := 1096496345743485897041893

theorem tailTrace_2135419 : CollatzResearch.WordTrace tailWord_2135419 prefixEnd_2135419 1096496345743485897041893 := by
  unfold tailWord_2135419
  simp only [CollatzResearch.WordTrace]
  refine ⟨77885129450749138375017311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51923419633832758916678207 77885129450749138375017311)
  ·
    refine ⟨116827694176123707562525967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77885129450749138375017311 116827694176123707562525967)
    ·
      refine ⟨175241541264185561343788951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116827694176123707562525967 175241541264185561343788951)
      ·
        refine ⟨262862311896278342015683427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175241541264185561343788951 262862311896278342015683427)
        ·
          refine ⟨394293467844417513023525141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262862311896278342015683427 394293467844417513023525141)
          ·
            refine ⟨18482506305207070922977741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 394293467844417513023525141 18482506305207070922977741)
            ·
              refine ⟨6930939864452651596116653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18482506305207070922977741 6930939864452651596116653)
              ·
                refine ⟨2599102449169744348543745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6930939864452651596116653 2599102449169744348543745)
                ·
                  refine ⟨1949326836877308261407809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2599102449169744348543745 1949326836877308261407809)
                  ·
                    refine ⟨1461995127657981196055857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949326836877308261407809 1461995127657981196055857)
                    ·
                      refine ⟨1096496345743485897041893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1461995127657981196055857 1096496345743485897041893)
                      ·
                        rfl

theorem cell23_2135419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 2, 2].length) (baseStart_2135419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135419 prefixEnd_2135419 := by exact prefixLift 2135419
  have htrace : WordTrace (prefixWord ++ tailWord_2135419) baseStart_2135419 baseEnd_2135419 := by
    simpa [prefixWord, tailWord_2135419, baseEnd_2135419] using wordTrace_append hprefix tailTrace_2135419
  have hstable : (prefixWord ++ tailWord_2135419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135419).length < 2 ^ (prefixWord ++ tailWord_2135419).sum := by decide
  have hdescent : baseEnd_2135419 < baseStart_2135419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135469 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2135469 : Nat := 118140960795 + 2135469 * 2 ^ 59
def prefixEnd_2135469 : Nat := 4983230072969 + 3 ^ 40 * 2135469 * 2
def baseEnd_2135469 : Nat := 1096522019776210701416663

theorem tailTrace_2135469 : CollatzResearch.WordTrace tailWord_2135469 prefixEnd_2135469 1096522019776210701416663 := by
  unfold tailWord_2135469
  simp only [CollatzResearch.WordTrace]
  refine ⟨77886953100567996914337461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51924635400378664609558307 77886953100567996914337461)
  ·
    refine ⟨7301901853178249710719137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77886953100567996914337461 7301901853178249710719137)
    ·
      refine ⟨5476426389883687283039353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7301901853178249710719137 5476426389883687283039353)
      ·
        refine ⟨4107319792412765462279515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5476426389883687283039353 4107319792412765462279515)
        ·
          refine ⟨6160979688619148193419273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107319792412765462279515 6160979688619148193419273)
          ·
            refine ⟨4620734766464361145064455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6160979688619148193419273 4620734766464361145064455)
            ·
              refine ⟨6931102149696541717596683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4620734766464361145064455 6931102149696541717596683)
              ·
                refine ⟨10396653224544812576395025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6931102149696541717596683 10396653224544812576395025)
                ·
                  refine ⟨7797489918408609432296269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10396653224544812576395025 7797489918408609432296269)
                  ·
                    refine ⟨2924058719403228537111101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7797489918408609432296269 2924058719403228537111101)
                    ·
                      refine ⟨1096522019776210701416663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924058719403228537111101 1096522019776210701416663)
                      ·
                        rfl

theorem cell23_2135469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2135469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135469 prefixEnd_2135469 := by exact prefixLift 2135469
  have htrace : WordTrace (prefixWord ++ tailWord_2135469) baseStart_2135469 baseEnd_2135469 := by
    simpa [prefixWord, tailWord_2135469, baseEnd_2135469] using wordTrace_append hprefix tailTrace_2135469
  have hstable : (prefixWord ++ tailWord_2135469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135469).length < 2 ^ (prefixWord ++ tailWord_2135469).sum := by decide
  have hdescent : baseEnd_2135469 < baseStart_2135469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135475 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 4]
def baseStart_2135475 : Nat := 118140960795 + 2135475 * 2 ^ 59
def prefixEnd_2135475 : Nat := 4983230072969 + 3 ^ 40 * 2135475 * 2
def baseEnd_2135475 : Nat := 1096525100660137677941635

theorem tailTrace_2135475 : CollatzResearch.WordTrace tailWord_2135475 prefixEnd_2135475 1096525100660137677941635 := by
  unfold tailWord_2135475
  simp only [CollatzResearch.WordTrace]
  refine ⟨77887171938546259939055879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51924781292364173292703919 77887171938546259939055879)
  ·
    refine ⟨116830757907819389908583819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77887171938546259939055879 116830757907819389908583819)
    ·
      refine ⟨175246136861729084862875729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116830757907819389908583819 175246136861729084862875729)
      ·
        refine ⟨131434602646296813647156797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175246136861729084862875729 131434602646296813647156797)
        ·
          refine ⟨49287975992361305117683799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131434602646296813647156797 49287975992361305117683799)
          ·
            refine ⟨73931963988541957676525699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49287975992361305117683799 73931963988541957676525699)
            ·
              refine ⟨110897945982812936514788549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73931963988541957676525699 110897945982812936514788549)
              ·
                refine ⟨20793364871777425596522853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110897945982812936514788549 20793364871777425596522853)
                ·
                  refine ⟨3898755913458267299348035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20793364871777425596522853 3898755913458267299348035)
                  ·
                    refine ⟨5848133870187400949022053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3898755913458267299348035 5848133870187400949022053)
                    ·
                      refine ⟨1096525100660137677941635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5848133870187400949022053 1096525100660137677941635)
                      ·
                        rfl

theorem cell23_2135475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_2135475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135475 prefixEnd_2135475 := by exact prefixLift 2135475
  have htrace : WordTrace (prefixWord ++ tailWord_2135475) baseStart_2135475 baseEnd_2135475 := by
    simpa [prefixWord, tailWord_2135475, baseEnd_2135475] using wordTrace_append hprefix tailTrace_2135475
  have hstable : (prefixWord ++ tailWord_2135475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135475).length < 2 ^ (prefixWord ++ tailWord_2135475).sum := by decide
  have hdescent : baseEnd_2135475 < baseStart_2135475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135512 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2135512 : Nat := 118140960795 + 2135512 * 2 ^ 59
def prefixEnd_2135512 : Nat := 4983230072969 + 3 ^ 40 * 2135512 * 2
def baseEnd_2135512 : Nat := 1096544099444354033178965

theorem tailTrace_2135512 : CollatzResearch.WordTrace tailWord_2135512 prefixEnd_2135512 1096544099444354033178965 := by
  unfold tailWord_2135512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38944260719706107629076395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51925680959608143505435193 38944260719706107629076395)
  ·
    refine ⟨58416391079559161443614593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38944260719706107629076395 58416391079559161443614593)
    ·
      refine ⟨43812293309669371082710945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58416391079559161443614593 43812293309669371082710945)
      ·
        refine ⟨32859219982252028312033209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43812293309669371082710945 32859219982252028312033209)
        ·
          refine ⟨24644414986689021234024907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32859219982252028312033209 24644414986689021234024907)
          ·
            refine ⟨36966622480033531851037361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24644414986689021234024907 36966622480033531851037361)
            ·
              refine ⟨27724966860025148888278021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36966622480033531851037361 27724966860025148888278021)
              ·
                refine ⟨5198431286254715416552129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27724966860025148888278021 5198431286254715416552129)
                ·
                  refine ⟨3898823464691036562414097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198431286254715416552129 3898823464691036562414097)
                  ·
                    refine ⟨2924117598518277421810573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3898823464691036562414097 2924117598518277421810573)
                    ·
                      refine ⟨1096544099444354033178965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924117598518277421810573 1096544099444354033178965)
                      ·
                        rfl

theorem cell23_2135512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2135512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135512 prefixEnd_2135512 := by exact prefixLift 2135512
  have htrace : WordTrace (prefixWord ++ tailWord_2135512) baseStart_2135512 baseEnd_2135512 := by
    simpa [prefixWord, tailWord_2135512, baseEnd_2135512] using wordTrace_append hprefix tailTrace_2135512
  have hstable : (prefixWord ++ tailWord_2135512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135512).length < 2 ^ (prefixWord ++ tailWord_2135512).sum := by decide
  have hdescent : baseEnd_2135512 < baseStart_2135512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135519 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 1, 4]
def baseStart_2135519 : Nat := 118140960795 + 2135519 * 2 ^ 59
def prefixEnd_2135519 : Nat := 4983230072969 + 3 ^ 40 * 2135519 * 2
def baseEnd_2135519 : Nat := 365515897936311835263811

theorem tailTrace_2135519 : CollatzResearch.WordTrace tailWord_2135519 prefixEnd_2135519 365515897936311835263811 := by
  unfold tailWord_2135519
  simp only [CollatzResearch.WordTrace]
  refine ⟨77888776750386855453657611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51925851166924570302438407 77888776750386855453657611)
  ·
    refine ⟨116833165125580283180486417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77888776750386855453657611 116833165125580283180486417)
    ·
      refine ⟨87624873844185212385364813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116833165125580283180486417 87624873844185212385364813)
      ·
        refine ⟨32859327691569454644511805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87624873844185212385364813 32859327691569454644511805)
        ·
          refine ⟨12322247884338545491691927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32859327691569454644511805 12322247884338545491691927)
          ·
            refine ⟨18483371826507818237537891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12322247884338545491691927 18483371826507818237537891)
            ·
              refine ⟨27725057739761727356306837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18483371826507818237537891 27725057739761727356306837)
              ·
                refine ⟨1299612081551330969826883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27725057739761727356306837 1299612081551330969826883)
                ·
                  refine ⟨1949418122326996454740325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299612081551330969826883 1949418122326996454740325)
                  ·
                    refine ⟨365515897936311835263811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1949418122326996454740325 365515897936311835263811)
                    ·
                      rfl

theorem cell23_2135519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 4].length) (baseStart_2135519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135519 prefixEnd_2135519 := by exact prefixLift 2135519
  have htrace : WordTrace (prefixWord ++ tailWord_2135519) baseStart_2135519 baseEnd_2135519 := by
    simpa [prefixWord, tailWord_2135519, baseEnd_2135519] using wordTrace_append hprefix tailTrace_2135519
  have hstable : (prefixWord ++ tailWord_2135519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135519).length < 2 ^ (prefixWord ++ tailWord_2135519).sum := by decide
  have hdescent : baseEnd_2135519 < baseStart_2135519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135553 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2135553 : Nat := 118140960795 + 2135553 * 2 ^ 59
def prefixEnd_2135553 : Nat := 4983230072969 + 3 ^ 40 * 2135553 * 2
def baseEnd_2135553 : Nat := 365521717383729457588759

theorem tailTrace_2135553 : CollatzResearch.WordTrace tailWord_2135553 prefixEnd_2135553 365521717383729457588759 := by
  unfold tailWord_2135553
  simp only [CollatzResearch.WordTrace]
  refine ⟨77890016832263679260395313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51926677888175786173596875 77890016832263679260395313)
  ·
    refine ⟨58417512624197759445296485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77890016832263679260395313 58417512624197759445296485)
    ·
      refine ⟨10953283617037079895993091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58417512624197759445296485 10953283617037079895993091)
      ·
        refine ⟨16429925425555619843989637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10953283617037079895993091 16429925425555619843989637)
        ·
          refine ⟨3080611017291678720748057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16429925425555619843989637 3080611017291678720748057)
          ·
            refine ⟨2310458262968759040561043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3080611017291678720748057 2310458262968759040561043)
            ·
              refine ⟨3465687394453138560841565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310458262968759040561043 3465687394453138560841565)
              ·
                refine ⟨1299632772919926960315587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3465687394453138560841565 1299632772919926960315587)
                ·
                  refine ⟨1949449159379890440473381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299632772919926960315587 1949449159379890440473381)
                  ·
                    refine ⟨365521717383729457588759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1949449159379890440473381 365521717383729457588759)
                    ·
                      rfl

theorem cell23_2135553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2135553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135553 prefixEnd_2135553 := by exact prefixLift 2135553
  have htrace : WordTrace (prefixWord ++ tailWord_2135553) baseStart_2135553 baseEnd_2135553 := by
    simpa [prefixWord, tailWord_2135553, baseEnd_2135553] using wordTrace_append hprefix tailTrace_2135553
  have hstable : (prefixWord ++ tailWord_2135553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135553).length < 2 ^ (prefixWord ++ tailWord_2135553).sum := by decide
  have hdescent : baseEnd_2135553 < baseStart_2135553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135569 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 2, 3, 2]
def baseStart_2135569 : Nat := 118140960795 + 2135569 * 2 ^ 59
def prefixEnd_2135569 : Nat := 4983230072969 + 3 ^ 40 * 2135569 * 2
def baseEnd_2135569 : Nat := 1096573367841660310166203

theorem tailTrace_2135569 : CollatzResearch.WordTrace tailWord_2135569 prefixEnd_2135569 1096573367841660310166203 := by
  unfold tailWord_2135569
  simp only [CollatzResearch.WordTrace]
  refine ⟨77890600400205713992977761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51927066933470475995318507 77890600400205713992977761)
  ·
    refine ⟨58417950300154285494733321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77890600400205713992977761 58417950300154285494733321)
    ·
      refine ⟨43813462725115714121049991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58417950300154285494733321 43813462725115714121049991)
      ·
        refine ⟨65720194087673571181574987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43813462725115714121049991 65720194087673571181574987)
        ·
          refine ⟨98580291131510356772362481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65720194087673571181574987 98580291131510356772362481)
          ·
            refine ⟨73935218348632767579271861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98580291131510356772362481 73935218348632767579271861)
            ·
              refine ⟨6931426720184321960556737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73935218348632767579271861 6931426720184321960556737)
              ·
                refine ⟨5198570040138241470417553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6931426720184321960556737 5198570040138241470417553)
                ·
                  refine ⟨3898927530103681102813165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198570040138241470417553 3898927530103681102813165)
                  ·
                    refine ⟨1462097823788880413554937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3898927530103681102813165 1462097823788880413554937)
                    ·
                      refine ⟨1096573367841660310166203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462097823788880413554937 1096573367841660310166203)
                      ·
                        rfl

theorem cell23_2135569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_2135569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135569 prefixEnd_2135569 := by exact prefixLift 2135569
  have htrace : WordTrace (prefixWord ++ tailWord_2135569) baseStart_2135569 baseEnd_2135569 := by
    simpa [prefixWord, tailWord_2135569, baseEnd_2135569] using wordTrace_append hprefix tailTrace_2135569
  have hstable : (prefixWord ++ tailWord_2135569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135569).length < 2 ^ (prefixWord ++ tailWord_2135569).sum := by decide
  have hdescent : baseEnd_2135569 < baseStart_2135569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135632 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_2135632 : Nat := 118140960795 + 2135632 * 2 ^ 59
def prefixEnd_2135632 : Nat := 4983230072969 + 3 ^ 40 * 2135632 * 2
def baseEnd_2135632 : Nat := 1096605717122893563678413

theorem tailTrace_2135632 : CollatzResearch.WordTrace tailWord_2135632 prefixEnd_2135632 1096605717122893563678413 := by
  unfold tailWord_2135632
  simp only [CollatzResearch.WordTrace]
  refine ⟨38946449099488737876260575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51928598799318317168347433 38946449099488737876260575)
  ·
    refine ⟨58419673649233106814390863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38946449099488737876260575 58419673649233106814390863)
    ·
      refine ⟨87629510473849660221586295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58419673649233106814390863 87629510473849660221586295)
      ·
        refine ⟨131444265710774490332379443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87629510473849660221586295 131444265710774490332379443)
        ·
          refine ⟨197166398566161735498569165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131444265710774490332379443 197166398566161735498569165)
          ·
            refine ⟨73937399462310650811963437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197166398566161735498569165 73937399462310650811963437)
            ·
              refine ⟨27726524798366494054486289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73937399462310650811963437 27726524798366494054486289)
              ·
                refine ⟨20794893598774870540864717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27726524798366494054486289 20794893598774870540864717)
                ·
                  refine ⟨7798085099540576452824269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20794893598774870540864717 7798085099540576452824269)
                  ·
                    refine ⟨2924281912327716169809101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7798085099540576452824269 2924281912327716169809101)
                    ·
                      refine ⟨1096605717122893563678413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924281912327716169809101 1096605717122893563678413)
                      ·
                        rfl

theorem cell23_2135632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_2135632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135632 prefixEnd_2135632 := by exact prefixLift 2135632
  have htrace : WordTrace (prefixWord ++ tailWord_2135632) baseStart_2135632 baseEnd_2135632 := by
    simpa [prefixWord, tailWord_2135632, baseEnd_2135632] using wordTrace_append hprefix tailTrace_2135632
  have hstable : (prefixWord ++ tailWord_2135632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135632).length < 2 ^ (prefixWord ++ tailWord_2135632).sum := by decide
  have hdescent : baseEnd_2135632 < baseStart_2135632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135633 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 1, 2, 2]
def baseStart_2135633 : Nat := 118140960795 + 2135633 * 2 ^ 59
def prefixEnd_2135633 : Nat := 4983230072969 + 3 ^ 40 * 2135633 * 2
def baseEnd_2135633 : Nat := 1096606230603548059765909

theorem tailTrace_2135633 : CollatzResearch.WordTrace tailWord_2135633 prefixEnd_2135633 1096606230603548059765909 := by
  unfold tailWord_2135633
  simp only [CollatzResearch.WordTrace]
  refine ⟨77892934671973852923307553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51928623114649235282205035 77892934671973852923307553)
  ·
    refine ⟨58419701003980389692480665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77892934671973852923307553 58419701003980389692480665)
    ·
      refine ⟨43814775752985292269360499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58419701003980389692480665 43814775752985292269360499)
      ·
        refine ⟨65722163629477938404040749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43814775752985292269360499 65722163629477938404040749)
        ·
          refine ⟨24645811361054226901515281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65722163629477938404040749 24645811361054226901515281)
          ·
            refine ⟨18484358520790670176136461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24645811361054226901515281 18484358520790670176136461)
            ·
              refine ⟨6931634445296501316051173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18484358520790670176136461 6931634445296501316051173)
              ·
                refine ⟨1299681458493093996759595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6931634445296501316051173 1299681458493093996759595)
                ·
                  refine ⟨1949522187739640995139393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299681458493093996759595 1949522187739640995139393)
                  ·
                    refine ⟨1462141640804730746354545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949522187739640995139393 1462141640804730746354545)
                    ·
                      refine ⟨1096606230603548059765909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462141640804730746354545 1096606230603548059765909)
                      ·
                        rfl

theorem cell23_2135633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_2135633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135633 prefixEnd_2135633 := by exact prefixLift 2135633
  have htrace : WordTrace (prefixWord ++ tailWord_2135633) baseStart_2135633 baseEnd_2135633 := by
    simpa [prefixWord, tailWord_2135633, baseEnd_2135633] using wordTrace_append hprefix tailTrace_2135633
  have hstable : (prefixWord ++ tailWord_2135633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135633).length < 2 ^ (prefixWord ++ tailWord_2135633).sum := by decide
  have hdescent : baseEnd_2135633 < baseStart_2135633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135649 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_2135649 : Nat := 118140960795 + 2135649 * 2 ^ 59
def prefixEnd_2135649 : Nat := 4983230072969 + 3 ^ 40 * 2135649 * 2
def baseEnd_2135649 : Nat := 1096614446294019997165835

theorem tailTrace_2135649 : CollatzResearch.WordTrace tailWord_2135649 prefixEnd_2135649 1096614446294019997165835 := by
  unfold tailWord_2135649
  simp only [CollatzResearch.WordTrace]
  refine ⟨77893518239915887655890001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51929012159943925103926667 77893518239915887655890001)
  ·
    refine ⟨58420138679936915741917501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77893518239915887655890001 58420138679936915741917501)
    ·
      refine ⟨21907552004976343403219063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58420138679936915741917501 21907552004976343403219063)
      ·
        refine ⟨32861328007464515104828595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21907552004976343403219063 32861328007464515104828595)
        ·
          refine ⟨49291992011196772657242893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32861328007464515104828595 49291992011196772657242893)
          ·
            refine ⟨18484497004198789746466085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49291992011196772657242893 18484497004198789746466085)
            ·
              refine ⟨3465843188287273077462391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18484497004198789746466085 3465843188287273077462391)
              ·
                refine ⟨5198764782430909616193587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3465843188287273077462391 5198764782430909616193587)
                ·
                  refine ⟨7798147173646364424290381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5198764782430909616193587 7798147173646364424290381)
                  ·
                    refine ⟨2924305190117386659108893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7798147173646364424290381 2924305190117386659108893)
                    ·
                      refine ⟨1096614446294019997165835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924305190117386659108893 1096614446294019997165835)
                      ·
                        rfl

theorem cell23_2135649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_2135649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135649 prefixEnd_2135649 := by exact prefixLift 2135649
  have htrace : WordTrace (prefixWord ++ tailWord_2135649) baseStart_2135649 baseEnd_2135649 := by
    simpa [prefixWord, tailWord_2135649, baseEnd_2135649] using wordTrace_append hprefix tailTrace_2135649
  have hstable : (prefixWord ++ tailWord_2135649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135649).length < 2 ^ (prefixWord ++ tailWord_2135649).sum := by decide
  have hdescent : baseEnd_2135649 < baseStart_2135649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135670 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2135670 : Nat := 118140960795 + 2135670 * 2 ^ 59
def prefixEnd_2135670 : Nat := 4983230072969 + 3 ^ 40 * 2135670 * 2
def baseEnd_2135670 : Nat := 1096625229387764415003239

theorem tailTrace_2135670 : CollatzResearch.WordTrace tailWord_2135670 prefixEnd_2135670 1096625229387764415003239 := by
  unfold tailWord_2135670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4868392760802488015150279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51929522781893205494936309 4868392760802488015150279)
  ·
    refine ⟨7302589141203732022725419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4868392760802488015150279 7302589141203732022725419)
    ·
      refine ⟨10953883711805598034088129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7302589141203732022725419 10953883711805598034088129)
      ·
        refine ⟨8215412783854198525566097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10953883711805598034088129 8215412783854198525566097)
        ·
          refine ⟨6161559587890648894174573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8215412783854198525566097 6161559587890648894174573)
          ·
            refine ⟨2310584845458993335315465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6161559587890648894174573 2310584845458993335315465)
            ·
              refine ⟨1732938634094245001486599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310584845458993335315465 1732938634094245001486599)
              ·
                refine ⟨2599407951141367502229899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732938634094245001486599 2599407951141367502229899)
                ·
                  refine ⟨3899111926712051253344849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599407951141367502229899 3899111926712051253344849)
                  ·
                    refine ⟨2924333945034038440008637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3899111926712051253344849 2924333945034038440008637)
                    ·
                      refine ⟨1096625229387764415003239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924333945034038440008637 1096625229387764415003239)
                      ·
                        rfl

theorem cell23_2135670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2135670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135670 prefixEnd_2135670 := by exact prefixLift 2135670
  have htrace : WordTrace (prefixWord ++ tailWord_2135670) baseStart_2135670 baseEnd_2135670 := by
    simpa [prefixWord, tailWord_2135670, baseEnd_2135670] using wordTrace_append hprefix tailTrace_2135670
  have hstable : (prefixWord ++ tailWord_2135670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135670).length < 2 ^ (prefixWord ++ tailWord_2135670).sum := by decide
  have hdescent : baseEnd_2135670 < baseStart_2135670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135689 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 3, 4, 2]
def baseStart_2135689 : Nat := 118140960795 + 2135689 * 2 ^ 59
def prefixEnd_2135689 : Nat := 4983230072969 + 3 ^ 40 * 2135689 * 2
def baseEnd_2135689 : Nat := 1096634985520199840665651

theorem tailTrace_2135689 : CollatzResearch.WordTrace tailWord_2135689 prefixEnd_2135689 1096634985520199840665651 := by
  unfold tailWord_2135689
  simp only [CollatzResearch.WordTrace]
  refine ⟨77894977159770974487346121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51929984773180649658230747 77894977159770974487346121)
  ·
    refine ⟨58421232869828230865509591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77894977159770974487346121 58421232869828230865509591)
    ·
      refine ⟨87631849304742346298264387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58421232869828230865509591 87631849304742346298264387)
      ·
        refine ⟨131447773957113519447396581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87631849304742346298264387 131447773957113519447396581)
        ·
          refine ⟨24646457616958784896386859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131447773957113519447396581 24646457616958784896386859)
          ·
            refine ⟨36969686425438177344580289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24646457616958784896386859 36969686425438177344580289)
            ·
              refine ⟨27727264819078633008435217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36969686425438177344580289 27727264819078633008435217)
              ·
                refine ⟨20795448614308974756326413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27727264819078633008435217 20795448614308974756326413)
                ·
                  refine ⟨7798293230365865533622405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20795448614308974756326413 7798293230365865533622405)
                  ·
                    refine ⟨1462179980693599787554201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7798293230365865533622405 1462179980693599787554201)
                    ·
                      refine ⟨1096634985520199840665651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462179980693599787554201 1096634985520199840665651)
                      ·
                        rfl

theorem cell23_2135689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 4, 2].length) (baseStart_2135689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135689 prefixEnd_2135689 := by exact prefixLift 2135689
  have htrace : WordTrace (prefixWord ++ tailWord_2135689) baseStart_2135689 baseEnd_2135689 := by
    simpa [prefixWord, tailWord_2135689, baseEnd_2135689] using wordTrace_append hprefix tailTrace_2135689
  have hstable : (prefixWord ++ tailWord_2135689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135689).length < 2 ^ (prefixWord ++ tailWord_2135689).sum := by decide
  have hdescent : baseEnd_2135689 < baseStart_2135689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135700 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_2135700 : Nat := 118140960795 + 2135700 * 2 ^ 59
def prefixEnd_2135700 : Nat := 4983230072969 + 3 ^ 40 * 2135700 * 2
def baseEnd_2135700 : Nat := 1096640633807399297628101

theorem tailTrace_2135700 : CollatzResearch.WordTrace tailWord_2135700 prefixEnd_2135700 1096640633807399297628101 := by
  unfold tailWord_2135700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38947689181365561682998277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51930252241820748910664369 38947689181365561682998277)
  ·
    refine ⟨7302691721506042815562177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38947689181365561682998277 7302691721506042815562177)
    ·
      refine ⟨5477018791129532111671633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7302691721506042815562177 5477018791129532111671633)
      ·
        refine ⟨4107764093347149083753725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5477018791129532111671633 4107764093347149083753725)
        ·
          refine ⟨1540411535005180906407647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4107764093347149083753725 1540411535005180906407647)
          ·
            refine ⟨2310617302507771359611471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540411535005180906407647 2310617302507771359611471)
            ·
              refine ⟨3465925953761657039417207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310617302507771359611471 3465925953761657039417207)
              ·
                refine ⟨5198888930642485559125811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3465925953761657039417207 5198888930642485559125811)
                ·
                  refine ⟨7798333395963728338688717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5198888930642485559125811 7798333395963728338688717)
                  ·
                    refine ⟨2924375023486398127008269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7798333395963728338688717 2924375023486398127008269)
                    ·
                      refine ⟨1096640633807399297628101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924375023486398127008269 1096640633807399297628101)
                      ·
                        rfl

theorem cell23_2135700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_2135700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135700 prefixEnd_2135700 := by exact prefixLift 2135700
  have htrace : WordTrace (prefixWord ++ tailWord_2135700) baseStart_2135700 baseEnd_2135700 := by
    simpa [prefixWord, tailWord_2135700, baseEnd_2135700] using wordTrace_append hprefix tailTrace_2135700
  have hstable : (prefixWord ++ tailWord_2135700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135700).length < 2 ^ (prefixWord ++ tailWord_2135700).sum := by decide
  have hdescent : baseEnd_2135700 < baseStart_2135700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135710 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_2135710 : Nat := 118140960795 + 2135710 * 2 ^ 59
def prefixEnd_2135710 : Nat := 4983230072969 + 3 ^ 40 * 2135710 * 2
def baseEnd_2135710 : Nat := 1096645768613944258503055

theorem tailTrace_2135710 : CollatzResearch.WordTrace tailWord_2135710 prefixEnd_2135710 1096645768613944258503055 := by
  unfold tailWord_2135710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9736967886586861884232573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51930495395129930049240389 9736967886586861884232573)
  ·
    refine ⟨3651362957470073206587215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9736967886586861884232573 3651362957470073206587215)
    ·
      refine ⟨5477044436205109809880823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3651362957470073206587215 5477044436205109809880823)
      ·
        refine ⟨8215566654307664714821235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5477044436205109809880823 8215566654307664714821235)
        ·
          refine ⟨12323349981461497072231853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8215566654307664714821235 12323349981461497072231853)
          ·
            refine ⟨4621256243048061402086945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12323349981461497072231853 4621256243048061402086945)
            ·
              refine ⟨3465942182286046051565209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4621256243048061402086945 3465942182286046051565209)
              ·
                refine ⟨2599456636714534538673907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3465942182286046051565209 2599456636714534538673907)
                ·
                  refine ⟨3899184955071801808010861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599456636714534538673907 3899184955071801808010861)
                  ·
                    refine ⟨1462194358151925678004073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3899184955071801808010861 1462194358151925678004073)
                    ·
                      refine ⟨1096645768613944258503055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462194358151925678004073 1096645768613944258503055)
                      ·
                        rfl

theorem cell23_2135710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_2135710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135710 prefixEnd_2135710 := by exact prefixLift 2135710
  have htrace : WordTrace (prefixWord ++ tailWord_2135710) baseStart_2135710 baseEnd_2135710 := by
    simpa [prefixWord, tailWord_2135710, baseEnd_2135710] using wordTrace_append hprefix tailTrace_2135710
  have hstable : (prefixWord ++ tailWord_2135710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135710).length < 2 ^ (prefixWord ++ tailWord_2135710).sum := by decide
  have hdescent : baseEnd_2135710 < baseStart_2135710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135749 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 7, 2]
def baseStart_2135749 : Nat := 118140960795 + 2135749 * 2 ^ 59
def prefixEnd_2135749 : Nat := 4983230072969 + 3 ^ 40 * 2135749 * 2
def baseEnd_2135749 : Nat := 1096665794359469605915375

theorem tailTrace_2135749 : CollatzResearch.WordTrace tailWord_2135749 prefixEnd_2135749 1096665794359469605915375 := by
  unfold tailWord_2135749
  simp only [CollatzResearch.WordTrace]
  refine ⟨77897165539553604734530301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51931443693035736489686867 77897165539553604734530301)
  ·
    refine ⟨29211437077332601775448863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77897165539553604734530301 29211437077332601775448863)
    ·
      refine ⟨43817155615998902663173295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29211437077332601775448863 43817155615998902663173295)
      ·
        refine ⟨65725733423998353994759943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43817155615998902663173295 65725733423998353994759943)
        ·
          refine ⟨98588600135997530992139915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65725733423998353994759943 98588600135997530992139915)
          ·
            refine ⟨147882900203996296488209873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98588600135997530992139915 147882900203996296488209873)
            ·
              refine ⟨110912175152997222366157405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147882900203996296488209873 110912175152997222366157405)
              ·
                refine ⟨41592065682373958387309027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110912175152997222366157405 41592065682373958387309027)
                ·
                  refine ⟨62388098523560937580963541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41592065682373958387309027 62388098523560937580963541)
                  ·
                    refine ⟨1462221059145959474553833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 62388098523560937580963541 1462221059145959474553833)
                    ·
                      refine ⟨1096665794359469605915375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462221059145959474553833 1096665794359469605915375)
                      ·
                        rfl

theorem cell23_2135749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_2135749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135749 prefixEnd_2135749 := by exact prefixLift 2135749
  have htrace : WordTrace (prefixWord ++ tailWord_2135749) baseStart_2135749 baseEnd_2135749 := by
    simpa [prefixWord, tailWord_2135749, baseEnd_2135749] using wordTrace_append hprefix tailTrace_2135749
  have hstable : (prefixWord ++ tailWord_2135749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135749).length < 2 ^ (prefixWord ++ tailWord_2135749).sum := by decide
  have hdescent : baseEnd_2135749 < baseStart_2135749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135757 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2135757 : Nat := 118140960795 + 2135757 * 2 ^ 59
def prefixEnd_2135757 : Nat := 4983230072969 + 3 ^ 40 * 2135757 * 2
def baseEnd_2135757 : Nat := 1096669902204705574615339

theorem tailTrace_2135757 : CollatzResearch.WordTrace tailWord_2135757 prefixEnd_2135757 1096669902204705574615339 := by
  unfold tailWord_2135757
  simp only [CollatzResearch.WordTrace]
  refine ⟨77897457323524622100821525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51931638215683081400547683 77897457323524622100821525)
  ·
    refine ⟨3651443312040216660976009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77897457323524622100821525 3651443312040216660976009)
    ·
      refine ⟨2738582484030162495732007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3651443312040216660976009 2738582484030162495732007)
      ·
        refine ⟨4107873726045243743598011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738582484030162495732007 4107873726045243743598011)
        ·
          refine ⟨6161810589067865615397017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107873726045243743598011 6161810589067865615397017)
          ·
            refine ⟨4621357941800899211547763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6161810589067865615397017 4621357941800899211547763)
            ·
              refine ⟨6932036912701348817321645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621357941800899211547763 6932036912701348817321645)
              ·
                refine ⟨2599513842263005806495617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6932036912701348817321645 2599513842263005806495617)
                ·
                  refine ⟨1949635381697254354871713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2599513842263005806495617 1949635381697254354871713)
                  ·
                    refine ⟨1462226536272940766153785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949635381697254354871713 1462226536272940766153785)
                    ·
                      refine ⟨1096669902204705574615339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462226536272940766153785 1096669902204705574615339)
                      ·
                        rfl

theorem cell23_2135757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2135757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135757 prefixEnd_2135757 := by exact prefixLift 2135757
  have htrace : WordTrace (prefixWord ++ tailWord_2135757) baseStart_2135757 baseEnd_2135757 := by
    simpa [prefixWord, tailWord_2135757, baseEnd_2135757] using wordTrace_append hprefix tailTrace_2135757
  have hstable : (prefixWord ++ tailWord_2135757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135757).length < 2 ^ (prefixWord ++ tailWord_2135757).sum := by decide
  have hdescent : baseEnd_2135757 < baseStart_2135757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135819 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 6]
def baseStart_2135819 : Nat := 118140960795 + 2135819 * 2 ^ 59
def prefixEnd_2135819 : Nat := 4983230072969 + 3 ^ 40 * 2135819 * 2
def baseEnd_2135819 : Nat := 121855748667253814671117

theorem tailTrace_2135819 : CollatzResearch.WordTrace tailWord_2135819 prefixEnd_2135819 121855748667253814671117 := by
  unfold tailWord_2135819
  simp only [CollatzResearch.WordTrace]
  refine ⟨77899718649300006689578511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51933145766200004459719007 77899718649300006689578511)
  ·
    refine ⟨116849577973950010034367767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77899718649300006689578511 116849577973950010034367767)
    ·
      refine ⟨175274366960925015051551651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116849577973950010034367767 175274366960925015051551651)
      ·
        refine ⟨262911550441387522577327477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175274366960925015051551651 262911550441387522577327477)
        ·
          refine ⟨24647957853880080241624451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 262911550441387522577327477 24647957853880080241624451)
          ·
            refine ⟨36971936780820120362436677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24647957853880080241624451 36971936780820120362436677)
            ·
              refine ⟨6932238146403772567956877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36971936780820120362436677 6932238146403772567956877)
              ·
                refine ⟨2599589304901414712983829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6932238146403772567956877 2599589304901414712983829)
                ·
                  refine ⟨121855748667253814671117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2599589304901414712983829 121855748667253814671117)
                  ·
                    rfl

theorem cell23_2135819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 6].length) (baseStart_2135819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135819 prefixEnd_2135819 := by exact prefixLift 2135819
  have htrace : WordTrace (prefixWord ++ tailWord_2135819) baseStart_2135819 baseEnd_2135819 := by
    simpa [prefixWord, tailWord_2135819, baseEnd_2135819] using wordTrace_append hprefix tailTrace_2135819
  have hstable : (prefixWord ++ tailWord_2135819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135819).length < 2 ^ (prefixWord ++ tailWord_2135819).sum := by decide
  have hdescent : baseEnd_2135819 < baseStart_2135819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135914 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2135914 : Nat := 118140960795 + 2135914 * 2 ^ 59
def prefixEnd_2135914 : Nat := 4983230072969 + 3 ^ 40 * 2135914 * 2
def baseEnd_2135914 : Nat := 1096750518667461460352117

theorem tailTrace_2135914 : CollatzResearch.WordTrace tailWord_2135914 prefixEnd_2135914 1096750518667461460352117 := by
  unfold tailWord_2135914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19475795895988959478571699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51935455722637225276191197 19475795895988959478571699)
  ·
    refine ⟨29213693843983439217857549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19475795895988959478571699 29213693843983439217857549)
    ·
      refine ⟨10955135191493789706696581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29213693843983439217857549 10955135191493789706696581)
      ·
        refine ⟨2054087848405085570005609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10955135191493789706696581 2054087848405085570005609)
        ·
          refine ⟨1540565886303814177504207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054087848405085570005609 1540565886303814177504207)
          ·
            refine ⟨2310848829455721266256311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540565886303814177504207 2310848829455721266256311)
            ·
              refine ⟨3466273244183581899384467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310848829455721266256311 3466273244183581899384467)
              ·
                refine ⟨5199409866275372849076701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466273244183581899384467 5199409866275372849076701)
                ·
                  refine ⟨1949778699853264818403763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5199409866275372849076701 1949778699853264818403763)
                  ·
                    refine ⟨2924668049779897227605645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1949778699853264818403763 2924668049779897227605645)
                    ·
                      refine ⟨1096750518667461460352117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924668049779897227605645 1096750518667461460352117)
                      ·
                        rfl

theorem cell23_2135914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2135914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135914 prefixEnd_2135914 := by exact prefixLift 2135914
  have htrace : WordTrace (prefixWord ++ tailWord_2135914) baseStart_2135914 baseEnd_2135914 := by
    simpa [prefixWord, tailWord_2135914, baseEnd_2135914] using wordTrace_append hprefix tailTrace_2135914
  have hstable : (prefixWord ++ tailWord_2135914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135914).length < 2 ^ (prefixWord ++ tailWord_2135914).sum := by decide
  have hdescent : baseEnd_2135914 < baseStart_2135914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135929 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2135929 : Nat := 118140960795 + 2135929 * 2 ^ 59
def prefixEnd_2135929 : Nat := 4983230072969 + 3 ^ 40 * 2135929 * 2
def baseEnd_2135929 : Nat := 1096758220877278901664547

theorem tailTrace_2135929 : CollatzResearch.WordTrace tailWord_2135929 prefixEnd_2135929 1096758220877278901664547 := by
  unfold tailWord_2135929
  simp only [CollatzResearch.WordTrace]
  refine ⟨77903730678901495476082841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51935820452600996984055227 77903730678901495476082841)
  ·
    refine ⟨58427798009176121607062131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77903730678901495476082841 58427798009176121607062131)
    ·
      refine ⟨87641697013764182410593197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58427798009176121607062131 87641697013764182410593197)
      ·
        refine ⟨32865636380161568403972449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87641697013764182410593197 32865636380161568403972449)
        ·
          refine ⟨24649227285121176302979337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32865636380161568403972449 24649227285121176302979337)
          ·
            refine ⟨18486920463840882227234503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24649227285121176302979337 18486920463840882227234503)
            ·
              refine ⟨27730380695761323340851755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18486920463840882227234503 27730380695761323340851755)
              ·
                refine ⟨41595571043641985011277633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27730380695761323340851755 41595571043641985011277633)
                ·
                  refine ⟨31196678282731488758458225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41595571043641985011277633 31196678282731488758458225)
                  ·
                    refine ⟨23397508712048616568843669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31196678282731488758458225 23397508712048616568843669)
                    ·
                      refine ⟨1096758220877278901664547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23397508712048616568843669 1096758220877278901664547)
                      ·
                        rfl

theorem cell23_2135929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2135929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135929 prefixEnd_2135929 := by exact prefixLift 2135929
  have htrace : WordTrace (prefixWord ++ tailWord_2135929) baseStart_2135929 baseEnd_2135929 := by
    simpa [prefixWord, tailWord_2135929, baseEnd_2135929] using wordTrace_append hprefix tailTrace_2135929
  have hstable : (prefixWord ++ tailWord_2135929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135929).length < 2 ^ (prefixWord ++ tailWord_2135929).sum := by decide
  have hdescent : baseEnd_2135929 < baseStart_2135929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135936 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_2135936 : Nat := 118140960795 + 2135936 * 2 ^ 59
def prefixEnd_2135936 : Nat := 4983230072969 + 3 ^ 40 * 2135936 * 2
def baseEnd_2135936 : Nat := 1096761815241860374277015

theorem tailTrace_2135936 : CollatzResearch.WordTrace tailWord_2135936 prefixEnd_2135936 1096761815241860374277015 := by
  unfold tailWord_2135936
  simp only [CollatzResearch.WordTrace]
  refine ⟨38951992994938067835793831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51935990659917423781058441 38951992994938067835793831)
  ·
    refine ⟨58427989492407101753690747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38951992994938067835793831 58427989492407101753690747)
    ·
      refine ⟨87641984238610652630536121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58427989492407101753690747 87641984238610652630536121)
      ·
        refine ⟨65731488178957989472902091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87641984238610652630536121 65731488178957989472902091)
        ·
          refine ⟨98597232268436984209353137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65731488178957989472902091 98597232268436984209353137)
          ·
            refine ⟨73947924201327738157014853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98597232268436984209353137 73947924201327738157014853)
            ·
              refine ⟨13865235787748950904440285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73947924201327738157014853 13865235787748950904440285)
              ·
                refine ⟨5199463420405856589165107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13865235787748950904440285 5199463420405856589165107)
                ·
                  refine ⟨7799195130608784883747661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5199463420405856589165107 7799195130608784883747661)
                  ·
                    refine ⟨2924698173978294331405373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7799195130608784883747661 2924698173978294331405373)
                    ·
                      refine ⟨1096761815241860374277015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2924698173978294331405373 1096761815241860374277015)
                      ·
                        rfl

theorem cell23_2135936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_2135936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135936 prefixEnd_2135936 := by exact prefixLift 2135936
  have htrace : WordTrace (prefixWord ++ tailWord_2135936) baseStart_2135936 baseEnd_2135936 := by
    simpa [prefixWord, tailWord_2135936, baseEnd_2135936] using wordTrace_append hprefix tailTrace_2135936
  have hstable : (prefixWord ++ tailWord_2135936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135936).length < 2 ^ (prefixWord ++ tailWord_2135936).sum := by decide
  have hdescent : baseEnd_2135936 < baseStart_2135936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135937 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2135937 : Nat := 118140960795 + 2135937 * 2 ^ 59
def prefixEnd_2135937 : Nat := 4983230072969 + 3 ^ 40 * 2135937 * 2
def baseEnd_2135937 : Nat := 1096762328722514870364511

theorem tailTrace_2135937 : CollatzResearch.WordTrace tailWord_2135937 prefixEnd_2135937 1096762328722514870364511 := by
  unfold tailWord_2135937
  simp only [CollatzResearch.WordTrace]
  refine ⟨77904022462872512842374065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51936014975248341894916043 77904022462872512842374065)
  ·
    refine ⟨58428016847154384631780549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77904022462872512842374065 58428016847154384631780549)
    ·
      refine ⟨10955253158841447118458853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58428016847154384631780549 10955253158841447118458853)
      ·
        refine ⟨2054109967282771334711035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10955253158841447118458853 2054109967282771334711035)
        ·
          refine ⟨3081164950924157002066553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054109967282771334711035 3081164950924157002066553)
          ·
            refine ⟨2310873713193117751549915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081164950924157002066553 2310873713193117751549915)
            ·
              refine ⟨3466310569789676627324873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310873713193117751549915 3466310569789676627324873)
              ·
                refine ⟨2599732927342257470493655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3466310569789676627324873 2599732927342257470493655)
                ·
                  refine ⟨3899599391013386205740483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599732927342257470493655 3899599391013386205740483)
                  ·
                    refine ⟨5849399086520079308610725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3899599391013386205740483 5849399086520079308610725)
                    ·
                      refine ⟨1096762328722514870364511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5849399086520079308610725 1096762328722514870364511)
                      ·
                        rfl

theorem cell23_2135937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2135937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135937 prefixEnd_2135937 := by exact prefixLift 2135937
  have htrace : WordTrace (prefixWord ++ tailWord_2135937) baseStart_2135937 baseEnd_2135937 := by
    simpa [prefixWord, tailWord_2135937, baseEnd_2135937] using wordTrace_append hprefix tailTrace_2135937
  have hstable : (prefixWord ++ tailWord_2135937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135937).length < 2 ^ (prefixWord ++ tailWord_2135937).sum := by decide
  have hdescent : baseEnd_2135937 < baseStart_2135937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135950 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2135950 : Nat := 118140960795 + 2135950 * 2 ^ 59
def prefixEnd_2135950 : Nat := 4983230072969 + 3 ^ 40 * 2135950 * 2
def baseEnd_2135950 : Nat := 1096769003971023319501951

theorem tailTrace_2135950 : CollatzResearch.WordTrace tailWord_2135950 prefixEnd_2135950 1096769003971023319501951 := by
  unfold tailWord_2135950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9738062076478177007824663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51936331074550277375064869 9738062076478177007824663)
  ·
    refine ⟨14607093114717265511736995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9738062076478177007824663 14607093114717265511736995)
    ·
      refine ⟨21910639672075898267605493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14607093114717265511736995 21910639672075898267605493)
      ·
        refine ⟨2054122469257115462588015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21910639672075898267605493 2054122469257115462588015)
        ·
          refine ⟨3081183703885673193882023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054122469257115462588015 3081183703885673193882023)
          ·
            refine ⟨4621775555828509790823035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081183703885673193882023 4621775555828509790823035)
            ·
              refine ⟨6932663333742764686234553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621775555828509790823035 6932663333742764686234553)
              ·
                refine ⟨5199497500307073514675915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6932663333742764686234553 5199497500307073514675915)
                ·
                  refine ⟨7799246250460610272013873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5199497500307073514675915 7799246250460610272013873)
                  ·
                    refine ⟨5849434687845457704010405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7799246250460610272013873 5849434687845457704010405)
                    ·
                      refine ⟨1096769003971023319501951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5849434687845457704010405 1096769003971023319501951)
                      ·
                        rfl

theorem cell23_2135950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2135950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2135950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2135950 prefixEnd_2135950 := by exact prefixLift 2135950
  have htrace : WordTrace (prefixWord ++ tailWord_2135950) baseStart_2135950 baseEnd_2135950 := by
    simpa [prefixWord, tailWord_2135950, baseEnd_2135950] using wordTrace_append hprefix tailTrace_2135950
  have hstable : (prefixWord ++ tailWord_2135950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135950).length < 2 ^ (prefixWord ++ tailWord_2135950).sum := by decide
  have hdescent : baseEnd_2135950 < baseStart_2135950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136033 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 5]
def baseStart_2136033 : Nat := 118140960795 + 2136033 * 2 ^ 59
def prefixEnd_2136033 : Nat := 4983230072969 + 3 ^ 40 * 2136033 * 2
def baseEnd_2136033 : Nat := 121867958096149610529341

theorem tailTrace_2136033 : CollatzResearch.WordTrace tailWord_2136033 prefixEnd_2136033 121867958096149610529341 := by
  unfold tailWord_2136033
  simp only [CollatzResearch.WordTrace]
  refine ⟨77907523870524721237868753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51938349247016480825245835 77907523870524721237868753)
  ·
    refine ⟨58430642902893540928401565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77907523870524721237868753 58430642902893540928401565)
    ·
      refine ⟨21911491088585077848150587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58430642902893540928401565 21911491088585077848150587)
      ·
        refine ⟨32867236632877616772225881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21911491088585077848150587 32867236632877616772225881)
        ·
          refine ⟨24650427474658212579169411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32867236632877616772225881 24650427474658212579169411)
          ·
            refine ⟨36975641211987318868754117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24650427474658212579169411 36975641211987318868754117)
            ·
              refine ⟨6932932727247622287891397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36975641211987318868754117 6932932727247622287891397)
              ·
                refine ⟨1299924886358929178979637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6932932727247622287891397 1299924886358929178979637)
                ·
                  refine ⟨121867958096149610529341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299924886358929178979637 121867958096149610529341)
                  ·
                    rfl

theorem cell23_2136033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 5].length) (baseStart_2136033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136033 prefixEnd_2136033 := by exact prefixLift 2136033
  have htrace : WordTrace (prefixWord ++ tailWord_2136033) baseStart_2136033 baseEnd_2136033 := by
    simpa [prefixWord, tailWord_2136033, baseEnd_2136033] using wordTrace_append hprefix tailTrace_2136033
  have hstable : (prefixWord ++ tailWord_2136033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136033).length < 2 ^ (prefixWord ++ tailWord_2136033).sum := by decide
  have hdescent : baseEnd_2136033 < baseStart_2136033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136083 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 4, 4, 2]
def baseStart_2136083 : Nat := 118140960795 + 2136083 * 2 ^ 59
def prefixEnd_2136083 : Nat := 4983230072969 + 3 ^ 40 * 2136083 * 2
def baseEnd_2136083 : Nat := 1096837296898071299138839

theorem tailTrace_2136083 : CollatzResearch.WordTrace tailWord_2136083 prefixEnd_2136083 1096837296898071299138839 := by
  unfold tailWord_2136083
  simp only [CollatzResearch.WordTrace]
  refine ⟨77909347520343579777188903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51939565013562386518125935 77909347520343579777188903)
  ·
    refine ⟨116864021280515369665783355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77909347520343579777188903 116864021280515369665783355)
    ·
      refine ⟨175296031920773054498675033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116864021280515369665783355 175296031920773054498675033)
      ·
        refine ⟨131472023940579790874006275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175296031920773054498675033 131472023940579790874006275)
        ·
          refine ⟨197208035910869686311009413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131472023940579790874006275 197208035910869686311009413)
          ·
            refine ⟨36976506733288066183314265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197208035910869686311009413 36976506733288066183314265)
            ·
              refine ⟨27732380049966049637485699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36976506733288066183314265 27732380049966049637485699)
              ·
                refine ⟨41598570074949074456228549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27732380049966049637485699 41598570074949074456228549)
                ·
                  refine ⟨7799731889052951460542853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41598570074949074456228549 7799731889052951460542853)
                  ·
                    refine ⟨1462449729197428398851785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7799731889052951460542853 1462449729197428398851785)
                    ·
                      refine ⟨1096837296898071299138839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462449729197428398851785 1096837296898071299138839)
                      ·
                        rfl

theorem cell23_2136083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4, 2].length) (baseStart_2136083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136083 prefixEnd_2136083 := by exact prefixLift 2136083
  have htrace : WordTrace (prefixWord ++ tailWord_2136083) baseStart_2136083 baseEnd_2136083 := by
    simpa [prefixWord, tailWord_2136083, baseEnd_2136083] using wordTrace_append hprefix tailTrace_2136083
  have hstable : (prefixWord ++ tailWord_2136083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136083).length < 2 ^ (prefixWord ++ tailWord_2136083).sum := by decide
  have hdescent : baseEnd_2136083 < baseStart_2136083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136084 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 7]
def baseStart_2136084 : Nat := 118140960795 + 2136084 * 2 ^ 59
def prefixEnd_2136084 : Nat := 4983230072969 + 3 ^ 40 * 2136084 * 2
def baseEnd_2136084 : Nat := 121870867819858421691815

theorem tailTrace_2136084 : CollatzResearch.WordTrace tailWord_2136084 prefixEnd_2136084 121870867819858421691815 := by
  unfold tailWord_2136084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38954691996669978473987653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51939589328893304631983537 38954691996669978473987653)
  ·
    refine ⟨7304004749375620963872685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38954691996669978473987653 7304004749375620963872685)
    ·
      refine ⟨2739001781015857861452257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7304004749375620963872685 2739001781015857861452257)
      ·
        refine ⟨2054251335761893396089193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2739001781015857861452257 2054251335761893396089193)
        ·
          refine ⟨1540688501821420047066895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054251335761893396089193 1540688501821420047066895)
          ·
            refine ⟨2311032752732130070600343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540688501821420047066895 2311032752732130070600343)
            ·
              refine ⟨3466549129098195105900515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311032752732130070600343 3466549129098195105900515)
              ·
                refine ⟨5199823693647292658850773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466549129098195105900515 5199823693647292658850773)
                ·
                  refine ⟨121870867819858421691815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5199823693647292658850773 121870867819858421691815)
                  ·
                    rfl

theorem cell23_2136084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_2136084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136084 prefixEnd_2136084 := by exact prefixLift 2136084
  have htrace : WordTrace (prefixWord ++ tailWord_2136084) baseStart_2136084 baseEnd_2136084 := by
    simpa [prefixWord, tailWord_2136084, baseEnd_2136084] using wordTrace_append hprefix tailTrace_2136084
  have hstable : (prefixWord ++ tailWord_2136084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136084).length < 2 ^ (prefixWord ++ tailWord_2136084).sum := by decide
  have hdescent : baseEnd_2136084 < baseStart_2136084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136183 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 1, 6]
def baseStart_2136183 : Nat := 118140960795 + 2136183 * 2 ^ 59
def prefixEnd_2136183 : Nat := 4983230072969 + 3 ^ 40 * 2136183 * 2
def baseEnd_2136183 : Nat := 365629548321173635962793

theorem tailTrace_2136183 : CollatzResearch.WordTrace tailWord_2136183 prefixEnd_2136183 365629548321173635962793 := by
  unfold tailWord_2136183
  simp only [CollatzResearch.WordTrace]
  refine ⟨77912994819981296855829203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51941996546654197903886135 77912994819981296855829203)
  ·
    refine ⟨116869492229971945283743805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77912994819981296855829203 116869492229971945283743805)
    ·
      refine ⟨43826059586239479481403927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116869492229971945283743805 43826059586239479481403927)
      ·
        refine ⟨65739089379359219222105891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43826059586239479481403927 65739089379359219222105891)
        ·
          refine ⟨98608634069038828833158837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65739089379359219222105891 98608634069038828833158837)
          ·
            refine ⟨9244559443972390203108641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98608634069038828833158837 9244559443972390203108641)
            ·
              refine ⟨6933419582979292652331481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9244559443972390203108641 6933419582979292652331481)
              ·
                refine ⟨5200064687234469489248611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6933419582979292652331481 5200064687234469489248611)
                ·
                  refine ⟨7800097030851704233872917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200064687234469489248611 7800097030851704233872917)
                  ·
                    refine ⟨365629548321173635962793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7800097030851704233872917 365629548321173635962793)
                    ·
                      rfl

theorem cell23_2136183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_2136183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136183 prefixEnd_2136183 := by exact prefixLift 2136183
  have htrace : WordTrace (prefixWord ++ tailWord_2136183) baseStart_2136183 baseEnd_2136183 := by
    simpa [prefixWord, tailWord_2136183, baseEnd_2136183] using wordTrace_append hprefix tailTrace_2136183
  have hstable : (prefixWord ++ tailWord_2136183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136183).length < 2 ^ (prefixWord ++ tailWord_2136183).sum := by decide
  have hdescent : baseEnd_2136183 < baseStart_2136183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136210 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2136210 : Nat := 118140960795 + 2136210 * 2 ^ 59
def prefixEnd_2136210 : Nat := 4983230072969 + 3 ^ 40 * 2136210 * 2
def baseEnd_2136210 : Nat := 1096902508941192302250755

theorem tailTrace_2136210 : CollatzResearch.WordTrace tailWord_2136210 prefixEnd_2136210 1096902508941192302250755 := by
  unfold tailWord_2136210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19478494897720870116765521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51942653060588986978041389 19478494897720870116765521)
  ·
    refine ⟨14608871173290652587574141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19478494897720870116765521 14608871173290652587574141)
    ·
      refine ⟨5478326689983994720340303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14608871173290652587574141 5478326689983994720340303)
      ·
        refine ⟨8217490034975992080510455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5478326689983994720340303 8217490034975992080510455)
        ·
          refine ⟨12326235052463988120765683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8217490034975992080510455 12326235052463988120765683)
          ·
            refine ⟨18489352578695982181148525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12326235052463988120765683 18489352578695982181148525)
            ·
              refine ⟨6933507217010993317930697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18489352578695982181148525 6933507217010993317930697)
              ·
                refine ⟨5200130412758244988448023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6933507217010993317930697 5200130412758244988448023)
                ·
                  refine ⟨7800195619137367482672035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5200130412758244988448023 7800195619137367482672035)
                  ·
                    refine ⟨11700293428706051224008053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7800195619137367482672035 11700293428706051224008053)
                    ·
                      refine ⟨1096902508941192302250755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11700293428706051224008053 1096902508941192302250755)
                      ·
                        rfl

theorem cell23_2136210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2136210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136210 prefixEnd_2136210 := by exact prefixLift 2136210
  have htrace : WordTrace (prefixWord ++ tailWord_2136210) baseStart_2136210 baseEnd_2136210 := by
    simpa [prefixWord, tailWord_2136210, baseEnd_2136210] using wordTrace_append hprefix tailTrace_2136210
  have hstable : (prefixWord ++ tailWord_2136210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136210).length < 2 ^ (prefixWord ++ tailWord_2136210).sum := by decide
  have hdescent : baseEnd_2136210 < baseStart_2136210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136253 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2136253 : Nat := 118140960795 + 2136253 * 2 ^ 59
def prefixEnd_2136253 : Nat := 4983230072969 + 3 ^ 40 * 2136253 * 2
def baseEnd_2136253 : Nat := 1096924588609335634013057

theorem tailTrace_2136253 : CollatzResearch.WordTrace tailWord_2136253 prefixEnd_2136253 1096924588609335634013057 := by
  unfold tailWord_2136253
  simp only [CollatzResearch.WordTrace]
  refine ⟨77915547929727698810877413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51943698619818465873918275 77915547929727698810877413)
  ·
    refine ⟨14609165236823943527039515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77915547929727698810877413 14609165236823943527039515)
    ·
      refine ⟨21913747855235915290559273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14609165236823943527039515 21913747855235915290559273)
      ·
        refine ⟨16435310891426936467919455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21913747855235915290559273 16435310891426936467919455)
        ·
          refine ⟨24652966337140404701879183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16435310891426936467919455 24652966337140404701879183)
          ·
            refine ⟨36979449505710607052818775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24652966337140404701879183 36979449505710607052818775)
            ·
              refine ⟨55469174258565910579228163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36979449505710607052818775 55469174258565910579228163)
              ·
                refine ⟨83203761387848865868842245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55469174258565910579228163 83203761387848865868842245)
                ·
                  refine ⟨15600705260221662350407921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83203761387848865868842245 15600705260221662350407921)
                  ·
                    refine ⟨11700528945166246762805941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15600705260221662350407921 11700528945166246762805941)
                    ·
                      refine ⟨1096924588609335634013057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11700528945166246762805941 1096924588609335634013057)
                      ·
                        rfl

theorem cell23_2136253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2136253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136253 prefixEnd_2136253 := by exact prefixLift 2136253
  have htrace : WordTrace (prefixWord ++ tailWord_2136253) baseStart_2136253 baseEnd_2136253 := by
    simpa [prefixWord, tailWord_2136253, baseEnd_2136253] using wordTrace_append hprefix tailTrace_2136253
  have hstable : (prefixWord ++ tailWord_2136253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136253).length < 2 ^ (prefixWord ++ tailWord_2136253).sum := by decide
  have hdescent : baseEnd_2136253 < baseStart_2136253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136258 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_2136258 : Nat := 118140960795 + 2136258 * 2 ^ 59
def prefixEnd_2136258 : Nat := 4983230072969 + 3 ^ 40 * 2136258 * 2
def baseEnd_2136258 : Nat := 1096927156012608114450535

theorem tailTrace_2136258 : CollatzResearch.WordTrace tailWord_2136258 prefixEnd_2136258 1096927156012608114450535 := by
  unfold tailWord_2136258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19478932573677396166202357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51943820196473056443206285 19478932573677396166202357)
  ·
    refine ⟨1826149928782255890581471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19478932573677396166202357 1826149928782255890581471)
    ·
      refine ⟨2739224893173383835872207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826149928782255890581471 2739224893173383835872207)
      ·
        refine ⟨4108837339760075753808311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739224893173383835872207 4108837339760075753808311)
        ·
          refine ⟨6163256009640113630712467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4108837339760075753808311 6163256009640113630712467)
          ·
            refine ⟨9244884014460170446068701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6163256009640113630712467 9244884014460170446068701)
            ·
              refine ⟨3466831505422563917275763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9244884014460170446068701 3466831505422563917275763)
              ·
                refine ⟨5200247258133845875913645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3466831505422563917275763 5200247258133845875913645)
                ·
                  refine ⟨1950092721800192203467617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5200247258133845875913645 1950092721800192203467617)
                  ·
                    refine ⟨1462569541350144152600713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1950092721800192203467617 1462569541350144152600713)
                    ·
                      refine ⟨1096927156012608114450535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462569541350144152600713 1096927156012608114450535)
                      ·
                        rfl

theorem cell23_2136258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_2136258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136258 prefixEnd_2136258 := by exact prefixLift 2136258
  have htrace : WordTrace (prefixWord ++ tailWord_2136258) baseStart_2136258 baseEnd_2136258 := by
    simpa [prefixWord, tailWord_2136258, baseEnd_2136258] using wordTrace_append hprefix tailTrace_2136258
  have hstable : (prefixWord ++ tailWord_2136258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136258).length < 2 ^ (prefixWord ++ tailWord_2136258).sum := by decide
  have hdescent : baseEnd_2136258 < baseStart_2136258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136268 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_2136268 : Nat := 118140960795 + 2136268 * 2 ^ 59
def prefixEnd_2136268 : Nat := 4983230072969 + 3 ^ 40 * 2136268 * 2
def baseEnd_2136268 : Nat := 365644096939717691775163

theorem tailTrace_2136268 : CollatzResearch.WordTrace tailWord_2136268 prefixEnd_2136268 365644096939717691775163 := by
  unfold tailWord_2136268
  simp only [CollatzResearch.WordTrace]
  refine ⟨38958047512336678186336729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51944063349782237581782305 38958047512336678186336729)
  ·
    refine ⟨29218535634252508639752547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38958047512336678186336729 29218535634252508639752547)
    ·
      refine ⟨43827803451378762959628821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29218535634252508639752547 43827803451378762959628821)
      ·
        refine ⟨2054428286783379513732601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43827803451378762959628821 2054428286783379513732601)
        ·
          refine ⟨1540821215087534635299451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054428286783379513732601 1540821215087534635299451)
          ·
            refine ⟨2311231822631301952949177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540821215087534635299451 2311231822631301952949177)
            ·
              refine ⟨1733423866973476464711883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2311231822631301952949177 1733423866973476464711883)
              ·
                refine ⟨2600135800460214697067825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733423866973476464711883 2600135800460214697067825)
                ·
                  refine ⟨1950101850345161022800869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600135800460214697067825 1950101850345161022800869)
                  ·
                    refine ⟨365644096939717691775163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1950101850345161022800869 365644096939717691775163)
                    ·
                      rfl

theorem cell23_2136268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_2136268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136268 prefixEnd_2136268 := by exact prefixLift 2136268
  have htrace : WordTrace (prefixWord ++ tailWord_2136268) baseStart_2136268 baseEnd_2136268 := by
    simpa [prefixWord, tailWord_2136268, baseEnd_2136268] using wordTrace_append hprefix tailTrace_2136268
  have hstable : (prefixWord ++ tailWord_2136268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136268).length < 2 ^ (prefixWord ++ tailWord_2136268).sum := by decide
  have hdescent : baseEnd_2136268 < baseStart_2136268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136273 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_2136273 : Nat := 118140960795 + 2136273 * 2 ^ 59
def prefixEnd_2136273 : Nat := 4983230072969 + 3 ^ 40 * 2136273 * 2
def baseEnd_2136273 : Nat := 365644952740808518587655

theorem tailTrace_2136273 : CollatzResearch.WordTrace tailWord_2136273 prefixEnd_2136273 365644952740808518587655 := by
  unfold tailWord_2136273
  simp only [CollatzResearch.WordTrace]
  refine ⟨77916277389655242226605473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51944184926436828151070315 77916277389655242226605473)
  ·
    refine ⟨58437208042241431669954105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77916277389655242226605473 58437208042241431669954105)
    ·
      refine ⟨43827906031681073752465579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58437208042241431669954105 43827906031681073752465579)
      ·
        refine ⟨65741859047521610628698369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43827906031681073752465579 65741859047521610628698369)
        ·
          refine ⟨49306394285641207971523777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65741859047521610628698369 49306394285641207971523777)
          ·
            refine ⟨36979795714230905978642833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49306394285641207971523777 36979795714230905978642833)
            ·
              refine ⟨27734846785673179483982125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36979795714230905978642833 27734846785673179483982125)
              ·
                refine ⟨10400567544627442306493297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27734846785673179483982125 10400567544627442306493297)
                ·
                  refine ⟨7800425658470581729869973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10400567544627442306493297 7800425658470581729869973)
                  ·
                    refine ⟨365644952740808518587655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7800425658470581729869973 365644952740808518587655)
                    ·
                      rfl

theorem cell23_2136273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_2136273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136273 prefixEnd_2136273 := by exact prefixLift 2136273
  have htrace : WordTrace (prefixWord ++ tailWord_2136273) baseStart_2136273 baseEnd_2136273 := by
    simpa [prefixWord, tailWord_2136273, baseEnd_2136273] using wordTrace_append hprefix tailTrace_2136273
  have hstable : (prefixWord ++ tailWord_2136273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136273).length < 2 ^ (prefixWord ++ tailWord_2136273).sum := by decide
  have hdescent : baseEnd_2136273 < baseStart_2136273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136274 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2136274 : Nat := 118140960795 + 2136274 * 2 ^ 59
def prefixEnd_2136274 : Nat := 4983230072969 + 3 ^ 40 * 2136274 * 2
def baseEnd_2136274 : Nat := 1096935371703080051850461

theorem tailTrace_2136274 : CollatzResearch.WordTrace tailWord_2136274 prefixEnd_2136274 1096935371703080051850461 := by
  unfold tailWord_2136274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479078465662904849347969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51944209241767746264927917 19479078465662904849347969)
  ·
    refine ⟨14609308849247178637010977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19479078465662904849347969 14609308849247178637010977)
    ·
      refine ⟨10956981636935383977758233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14609308849247178637010977 10956981636935383977758233)
      ·
        refine ⟨8217736227701537983318675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10956981636935383977758233 8217736227701537983318675)
        ·
          refine ⟨12326604341552306974978013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8217736227701537983318675 12326604341552306974978013)
          ·
            refine ⟨4622476628082115115616755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12326604341552306974978013 4622476628082115115616755)
            ·
              refine ⟨6933714942123172673425133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4622476628082115115616755 6933714942123172673425133)
              ·
                refine ⟨2600143103296189752534425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6933714942123172673425133 2600143103296189752534425)
                ·
                  refine ⟨1950107327472142314400819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600143103296189752534425 1950107327472142314400819)
                  ·
                    refine ⟨2925160991208213471601229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1950107327472142314400819 2925160991208213471601229)
                    ·
                      refine ⟨1096935371703080051850461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2925160991208213471601229 1096935371703080051850461)
                      ·
                        rfl

theorem cell23_2136274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2136274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136274 prefixEnd_2136274 := by exact prefixLift 2136274
  have htrace : WordTrace (prefixWord ++ tailWord_2136274) baseStart_2136274 baseEnd_2136274 := by
    simpa [prefixWord, tailWord_2136274, baseEnd_2136274] using wordTrace_append hprefix tailTrace_2136274
  have hstable : (prefixWord ++ tailWord_2136274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136274).length < 2 ^ (prefixWord ++ tailWord_2136274).sum := by decide
  have hdescent : baseEnd_2136274 < baseStart_2136274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136283 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5]
def baseStart_2136283 : Nat := 118140960795 + 2136283 * 2 ^ 59
def prefixEnd_2136283 : Nat := 4983230072969 + 3 ^ 40 * 2136283 * 2
def baseEnd_2136283 : Nat := 1096939993028970516637919

theorem tailTrace_2136283 : CollatzResearch.WordTrace tailWord_2136283 prefixEnd_2136283 1096939993028970516637919 := by
  unfold tailWord_2136283
  simp only [CollatzResearch.WordTrace]
  refine ⟨77916642119619013934469503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51944428079746009289646335 77916642119619013934469503)
  ·
    refine ⟨116874963179428520901704255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77916642119619013934469503 116874963179428520901704255)
    ·
      refine ⟨175312444769142781352556383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116874963179428520901704255 175312444769142781352556383)
      ·
        refine ⟨262968667153714172028834575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175312444769142781352556383 262968667153714172028834575)
        ·
          refine ⟨394453000730571258043251863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262968667153714172028834575 394453000730571258043251863)
          ·
            refine ⟨591679501095856887064877795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394453000730571258043251863 591679501095856887064877795)
            ·
              refine ⟨887519251643785330597316693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591679501095856887064877795 887519251643785330597316693)
              ·
                refine ⟨10400616230200609342937305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 887519251643785330597316693 10400616230200609342937305)
                ·
                  refine ⟨7800462172650457007202979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10400616230200609342937305 7800462172650457007202979)
                  ·
                    refine ⟨11700693258975685510804469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7800462172650457007202979 11700693258975685510804469)
                    ·
                      refine ⟨1096939993028970516637919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11700693258975685510804469 1096939993028970516637919)
                      ·
                        rfl

theorem cell23_2136283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_2136283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136283 prefixEnd_2136283 := by exact prefixLift 2136283
  have htrace : WordTrace (prefixWord ++ tailWord_2136283) baseStart_2136283 baseEnd_2136283 := by
    simpa [prefixWord, tailWord_2136283, baseEnd_2136283] using wordTrace_append hprefix tailTrace_2136283
  have hstable : (prefixWord ++ tailWord_2136283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136283).length < 2 ^ (prefixWord ++ tailWord_2136283).sum := by decide
  have hdescent : baseEnd_2136283 < baseStart_2136283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136314 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2]
def baseStart_2136314 : Nat := 118140960795 + 2136314 * 2 ^ 59
def prefixEnd_2136314 : Nat := 4983230072969 + 3 ^ 40 * 2136314 * 2
def baseEnd_2136314 : Nat := 1096955910929259895350277

theorem tailTrace_2136314 : CollatzResearch.WordTrace tailWord_2136314 prefixEnd_2136314 1096955910929259895350277 := by
  unfold tailWord_2136314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479443195626676557211999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51945181855004470819231997 19479443195626676557211999)
  ·
    refine ⟨29219164793440014835817999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19479443195626676557211999 29219164793440014835817999)
    ·
      refine ⟨43828747190160022253726999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29219164793440014835817999 43828747190160022253726999)
      ·
        refine ⟨65743120785240033380590499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43828747190160022253726999 65743120785240033380590499)
        ·
          refine ⟨98614681177860050070885749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65743120785240033380590499 98614681177860050070885749)
          ·
            refine ⟨9245126360424379694145539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98614681177860050070885749 9245126360424379694145539)
            ·
              refine ⟨13867689540636569541218309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9245126360424379694145539 13867689540636569541218309)
              ·
                refine ⟨2600191788869356788978433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13867689540636569541218309 2600191788869356788978433)
                ·
                  refine ⟨1950143841652017591733825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600191788869356788978433 1950143841652017591733825)
                  ·
                    refine ⟨1462607881239013193800369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1950143841652017591733825 1462607881239013193800369)
                    ·
                      refine ⟨1096955910929259895350277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462607881239013193800369 1096955910929259895350277)
                      ·
                        rfl

theorem cell23_2136314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_2136314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136314 prefixEnd_2136314 := by exact prefixLift 2136314
  have htrace : WordTrace (prefixWord ++ tailWord_2136314) baseStart_2136314 baseEnd_2136314 := by
    simpa [prefixWord, tailWord_2136314, baseEnd_2136314] using wordTrace_append hprefix tailTrace_2136314
  have hstable : (prefixWord ++ tailWord_2136314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136314).length < 2 ^ (prefixWord ++ tailWord_2136314).sum := by decide
  have hdescent : baseEnd_2136314 < baseStart_2136314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136330 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2136330 : Nat := 118140960795 + 2136330 * 2 ^ 59
def prefixEnd_2136330 : Nat := 4983230072969 + 3 ^ 40 * 2136330 * 2
def baseEnd_2136330 : Nat := 1096964126619731832750203

theorem tailTrace_2136330 : CollatzResearch.WordTrace tailWord_2136330 prefixEnd_2136330 1096964126619731832750203 := by
  unfold tailWord_2136330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479589087612185240357611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51945570900299160640953629 19479589087612185240357611)
  ·
    refine ⟨29219383631418277860536417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19479589087612185240357611 29219383631418277860536417)
    ·
      refine ⟨21914537723563708395402313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29219383631418277860536417 21914537723563708395402313)
      ·
        refine ⟨16435903292672781296551735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21914537723563708395402313 16435903292672781296551735)
        ·
          refine ⟨24653854939009171944827603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16435903292672781296551735 24653854939009171944827603)
          ·
            refine ⟨36980782408513757917241405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24653854939009171944827603 36980782408513757917241405)
            ·
              refine ⟨13867793403192659218965527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36980782408513757917241405 13867793403192659218965527)
              ·
                refine ⟨20801690104788988828448291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13867793403192659218965527 20801690104788988828448291)
                ·
                  refine ⟨31202535157183483242672437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20801690104788988828448291 31202535157183483242672437)
                  ·
                    refine ⟨2925237670985951554000541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31202535157183483242672437 2925237670985951554000541)
                    ·
                      refine ⟨1096964126619731832750203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2925237670985951554000541 1096964126619731832750203)
                      ·
                        rfl

theorem cell23_2136330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2136330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136330 prefixEnd_2136330 := by exact prefixLift 2136330
  have htrace : WordTrace (prefixWord ++ tailWord_2136330) baseStart_2136330 baseEnd_2136330 := by
    simpa [prefixWord, tailWord_2136330, baseEnd_2136330] using wordTrace_append hprefix tailTrace_2136330
  have hstable : (prefixWord ++ tailWord_2136330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136330).length < 2 ^ (prefixWord ++ tailWord_2136330).sum := by decide
  have hdescent : baseEnd_2136330 < baseStart_2136330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136354 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_2136354 : Nat := 118140960795 + 2136354 * 2 ^ 59
def prefixEnd_2136354 : Nat := 4983230072969 + 3 ^ 40 * 2136354 * 2
def baseEnd_2136354 : Nat := 121886272239493304316677

theorem tailTrace_2136354 : CollatzResearch.WordTrace tailWord_2136354 prefixEnd_2136354 121886272239493304316677 := by
  unfold tailWord_2136354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479807925590448265076029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51946154468241195373536077 19479807925590448265076029)
  ·
    refine ⟨7304927972096418099403511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19479807925590448265076029 7304927972096418099403511)
    ·
      refine ⟨10957391958144627149105267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7304927972096418099403511 10957391958144627149105267)
      ·
        refine ⟨16436087937216940723657901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10957391958144627149105267 16436087937216940723657901)
        ·
          refine ⟨6163532976456352771371713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16436087937216940723657901 6163532976456352771371713)
          ·
            refine ⟨4622649732342264578528785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163532976456352771371713 4622649732342264578528785)
            ·
              refine ⟨3466987299256698433896589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4622649732342264578528785 3466987299256698433896589)
              ·
                refine ⟨1300120237221261912711221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3466987299256698433896589 1300120237221261912711221)
                ·
                  refine ⟨121886272239493304316677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300120237221261912711221 121886272239493304316677)
                  ·
                    rfl

theorem cell23_2136354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_2136354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136354 prefixEnd_2136354 := by exact prefixLift 2136354
  have htrace : WordTrace (prefixWord ++ tailWord_2136354) baseStart_2136354 baseEnd_2136354 := by
    simpa [prefixWord, tailWord_2136354, baseEnd_2136354] using wordTrace_append hprefix tailTrace_2136354
  have hstable : (prefixWord ++ tailWord_2136354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136354).length < 2 ^ (prefixWord ++ tailWord_2136354).sum := by decide
  have hdescent : baseEnd_2136354 < baseStart_2136354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136365 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2136365 : Nat := 118140960795 + 2136365 * 2 ^ 59
def prefixEnd_2136365 : Nat := 4983230072969 + 3 ^ 40 * 2136365 * 2
def baseEnd_2136365 : Nat := 1096982098442639195812543

theorem tailTrace_2136365 : CollatzResearch.WordTrace tailWord_2136365 prefixEnd_2136365 1096982098442639195812543 := by
  unfold tailWord_2136365
  simp only [CollatzResearch.WordTrace]
  refine ⟨77919632905321941938954549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51946421936881294625969699 77919632905321941938954549)
  ·
    refine ⟨7304965584873932056776989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77919632905321941938954549 7304965584873932056776989)
    ·
      refine ⟨2739362094327724521291371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7304965584873932056776989 2739362094327724521291371)
      ·
        refine ⟨4109043141491586781937057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739362094327724521291371 4109043141491586781937057)
        ·
          refine ⟨3081782356118690086452793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4109043141491586781937057 3081782356118690086452793)
          ·
            refine ⟨2311336767089017564839595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081782356118690086452793 2311336767089017564839595)
            ·
              refine ⟨3467005150633526347259393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311336767089017564839595 3467005150633526347259393)
              ·
                refine ⟨2600253862975144760444545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3467005150633526347259393 2600253862975144760444545)
                ·
                  refine ⟨1950190397231358570333409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600253862975144760444545 1950190397231358570333409)
                  ·
                    refine ⟨1462642797923518927750057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1950190397231358570333409 1462642797923518927750057)
                    ·
                      refine ⟨1096982098442639195812543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462642797923518927750057 1096982098442639195812543)
                      ·
                        rfl

theorem cell23_2136365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2136365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136365 prefixEnd_2136365 := by exact prefixLift 2136365
  have htrace : WordTrace (prefixWord ++ tailWord_2136365) baseStart_2136365 baseEnd_2136365 := by
    simpa [prefixWord, tailWord_2136365, baseEnd_2136365] using wordTrace_append hprefix tailTrace_2136365
  have hstable : (prefixWord ++ tailWord_2136365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136365).length < 2 ^ (prefixWord ++ tailWord_2136365).sum := by decide
  have hdescent : baseEnd_2136365 < baseStart_2136365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136387 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 2, 4, 2]
def baseStart_2136387 : Nat := 118140960795 + 2136387 * 2 ^ 59
def prefixEnd_2136387 : Nat := 4983230072969 + 3 ^ 40 * 2136387 * 2
def baseEnd_2136387 : Nat := 1096993395017038109737441

theorem tailTrace_2136387 : CollatzResearch.WordTrace tailWord_2136387 prefixEnd_2136387 1096993395017038109737441 := by
  unfold tailWord_2136387
  simp only [CollatzResearch.WordTrace]
  refine ⟨77920435311242239696255415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51946956874161493130836943 77920435311242239696255415)
  ·
    refine ⟨116880652966863359544383123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77920435311242239696255415 116880652966863359544383123)
    ·
      refine ⟨175320979450295039316574685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116880652966863359544383123 175320979450295039316574685)
      ·
        refine ⟨65745367293860639743715507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175320979450295039316574685 65745367293860639743715507)
        ·
          refine ⟨98618050940790959615573261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65745367293860639743715507 98618050940790959615573261)
          ·
            refine ⟨36981769102796609855839973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98618050940790959615573261 36981769102796609855839973)
            ·
              refine ⟨6934081706774364347969995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36981769102796609855839973 6934081706774364347969995)
              ·
                refine ⟨10401122560161546521954993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934081706774364347969995 10401122560161546521954993)
                ·
                  refine ⟨7800841920121159891466245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10401122560161546521954993 7800841920121159891466245)
                  ·
                    refine ⟨1462657860022717479649921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7800841920121159891466245 1462657860022717479649921)
                    ·
                      refine ⟨1096993395017038109737441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462657860022717479649921 1096993395017038109737441)
                      ·
                        rfl

theorem cell23_2136387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_2136387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136387 prefixEnd_2136387 := by exact prefixLift 2136387
  have htrace : WordTrace (prefixWord ++ tailWord_2136387) baseStart_2136387 baseEnd_2136387 := by
    simpa [prefixWord, tailWord_2136387, baseEnd_2136387] using wordTrace_append hprefix tailTrace_2136387
  have hstable : (prefixWord ++ tailWord_2136387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136387).length < 2 ^ (prefixWord ++ tailWord_2136387).sum := by decide
  have hdescent : baseEnd_2136387 < baseStart_2136387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136407 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_2136407 : Nat := 118140960795 + 2136407 * 2 ^ 59
def prefixEnd_2136407 : Nat := 4983230072969 + 3 ^ 40 * 2136407 * 2
def baseEnd_2136407 : Nat := 1097003664630128031487349

theorem tailTrace_2136407 : CollatzResearch.WordTrace tailWord_2136407 prefixEnd_2136407 1097003664630128031487349 := by
  unfold tailWord_2136407
  simp only [CollatzResearch.WordTrace]
  refine ⟨77921164771169783111983475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51947443180779855407988983 77921164771169783111983475)
  ·
    refine ⟨116881747156754674667975213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77921164771169783111983475 116881747156754674667975213)
    ·
      refine ⟨43830655183783003000490705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116881747156754674667975213 43830655183783003000490705)
      ·
        refine ⟨32872991387837252250368029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43830655183783003000490705 32872991387837252250368029)
        ·
          refine ⟨12327371770438969593888011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32872991387837252250368029 12327371770438969593888011)
          ·
            refine ⟨18491057655658454390832017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12327371770438969593888011 18491057655658454390832017)
            ·
              refine ⟨13868293241743840793124013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18491057655658454390832017 13868293241743840793124013)
              ·
                refine ⟨5200609965653940297421505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13868293241743840793124013 5200609965653940297421505)
                ·
                  refine ⟨3900457474240455223066129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5200609965653940297421505 3900457474240455223066129)
                  ·
                    refine ⟨2925343105680341417299597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3900457474240455223066129 2925343105680341417299597)
                    ·
                      refine ⟨1097003664630128031487349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2925343105680341417299597 1097003664630128031487349)
                      ·
                        rfl

theorem cell23_2136407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_2136407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136407 prefixEnd_2136407 := by exact prefixLift 2136407
  have htrace : WordTrace (prefixWord ++ tailWord_2136407) baseStart_2136407 baseEnd_2136407 := by
    simpa [prefixWord, tailWord_2136407, baseEnd_2136407] using wordTrace_append hprefix tailTrace_2136407
  have hstable : (prefixWord ++ tailWord_2136407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136407).length < 2 ^ (prefixWord ++ tailWord_2136407).sum := by decide
  have hdescent : baseEnd_2136407 < baseStart_2136407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136424 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2136424 : Nat := 118140960795 + 2136424 * 2 ^ 59
def prefixEnd_2136424 : Nat := 4983230072969 + 3 ^ 40 * 2136424 * 2
def baseEnd_2136424 : Nat := 1097012393801254464974771

theorem tailTrace_2136424 : CollatzResearch.WordTrace tailWord_2136424 prefixEnd_2136424 1097012393801254464974771 := by
  unfold tailWord_2136424
  simp only [CollatzResearch.WordTrace]
  refine ⟨38960892406054097507676163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51947856541405463343568217 38960892406054097507676163)
  ·
    refine ⟨58441338609081146261514245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38960892406054097507676163 58441338609081146261514245)
    ·
      refine ⟨10957750989202714924033921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58441338609081146261514245 10957750989202714924033921)
      ·
        refine ⟨8218313241902036193025441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10957750989202714924033921 8218313241902036193025441)
        ·
          refine ⟨6163734931426527144769081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8218313241902036193025441 6163734931426527144769081)
          ·
            refine ⟨4622801198569895358576811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163734931426527144769081 4622801198569895358576811)
            ·
              refine ⟨6934201797854843037865217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4622801198569895358576811 6934201797854843037865217)
              ·
                refine ⟨5200651348391132278398913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6934201797854843037865217 5200651348391132278398913)
                ·
                  refine ⟨3900488511293349208799185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5200651348391132278398913 3900488511293349208799185)
                  ·
                    refine ⟨2925366383470011906599389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3900488511293349208799185 2925366383470011906599389)
                    ·
                      refine ⟨1097012393801254464974771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2925366383470011906599389 1097012393801254464974771)
                      ·
                        rfl

theorem cell23_2136424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2136424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136424 prefixEnd_2136424 := by exact prefixLift 2136424
  have htrace : WordTrace (prefixWord ++ tailWord_2136424) baseStart_2136424 baseEnd_2136424 := by
    simpa [prefixWord, tailWord_2136424, baseEnd_2136424] using wordTrace_append hprefix tailTrace_2136424
  have hstable : (prefixWord ++ tailWord_2136424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136424).length < 2 ^ (prefixWord ++ tailWord_2136424).sum := by decide
  have hdescent : baseEnd_2136424 < baseStart_2136424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136457 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_2136457 : Nat := 118140960795 + 2136457 * 2 ^ 59
def prefixEnd_2136457 : Nat := 4983230072969 + 3 ^ 40 * 2136457 * 2
def baseEnd_2136457 : Nat := 365676446220950945287373

theorem tailTrace_2136457 : CollatzResearch.WordTrace tailWord_2136457 prefixEnd_2136457 365676446220950945287373 := by
  unfold tailWord_2136457
  simp only [CollatzResearch.WordTrace]
  refine ⟨77922988420988641651303625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51948658947325761100869083 77922988420988641651303625)
  ·
    refine ⟨58442241315741481238477719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77922988420988641651303625 58442241315741481238477719)
    ·
      refine ⟨87663361973612221857716579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58442241315741481238477719 87663361973612221857716579)
      ·
        refine ⟨131495042960418332786574869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87663361973612221857716579 131495042960418332786574869)
        ·
          refine ⟨6163830138769609349370697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131495042960418332786574869 6163830138769609349370697)
          ·
            refine ⟨4622872604077207012028023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6163830138769609349370697 4622872604077207012028023)
            ·
              refine ⟨6934308906115810518042035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4622872604077207012028023 6934308906115810518042035)
              ·
                refine ⟨10401463359173715777063053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934308906115810518042035 10401463359173715777063053)
                ·
                  refine ⟨3900548759690143416398645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10401463359173715777063053 3900548759690143416398645)
                  ·
                    refine ⟨365676446220950945287373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3900548759690143416398645 365676446220950945287373)
                    ·
                      rfl

theorem cell23_2136457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_2136457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136457 prefixEnd_2136457 := by exact prefixLift 2136457
  have htrace : WordTrace (prefixWord ++ tailWord_2136457) baseStart_2136457 baseEnd_2136457 := by
    simpa [prefixWord, tailWord_2136457, baseEnd_2136457] using wordTrace_append hprefix tailTrace_2136457
  have hstable : (prefixWord ++ tailWord_2136457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136457).length < 2 ^ (prefixWord ++ tailWord_2136457).sum := by decide
  have hdescent : baseEnd_2136457 < baseStart_2136457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136544 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 4, 1, 3]
def baseStart_2136544 : Nat := 118140960795 + 2136544 * 2 ^ 59
def prefixEnd_2136544 : Nat := 4983230072969 + 3 ^ 40 * 2136544 * 2
def baseEnd_2136544 : Nat := 1097074011479793995474219

theorem tailTrace_2136544 : CollatzResearch.WordTrace tailWord_2136544 prefixEnd_2136544 1097074011479793995474219 := by
  unfold tailWord_2136544
  simp only [CollatzResearch.WordTrace]
  refine ⟨38963080785836727754860343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51950774381115637006480457 38963080785836727754860343)
  ·
    refine ⟨58444621178755091632290515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38963080785836727754860343 58444621178755091632290515)
    ·
      refine ⟨87666931768132637448435773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58444621178755091632290515 87666931768132637448435773)
      ·
        refine ⟨32875099413049739043163415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87666931768132637448435773 32875099413049739043163415)
        ·
          refine ⟨49312649119574608564745123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32875099413049739043163415 49312649119574608564745123)
          ·
            refine ⟨73968973679361912847117685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49312649119574608564745123 73968973679361912847117685)
            ·
              refine ⟨6934591282440179329417283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73968973679361912847117685 6934591282440179329417283)
              ·
                refine ⟨10401886923660268994125925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6934591282440179329417283 10401886923660268994125925)
                ·
                  refine ⟨1950353798186300436398611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10401886923660268994125925 1950353798186300436398611)
                  ·
                    refine ⟨2925530697279450654597917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1950353798186300436398611 2925530697279450654597917)
                    ·
                      refine ⟨1097074011479793995474219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2925530697279450654597917 1097074011479793995474219)
                      ·
                        rfl

theorem cell23_2136544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_2136544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136544 prefixEnd_2136544 := by exact prefixLift 2136544
  have htrace : WordTrace (prefixWord ++ tailWord_2136544) baseStart_2136544 baseEnd_2136544 := by
    simpa [prefixWord, tailWord_2136544, baseEnd_2136544] using wordTrace_append hprefix tailTrace_2136544
  have hstable : (prefixWord ++ tailWord_2136544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136544).length < 2 ^ (prefixWord ++ tailWord_2136544).sum := by decide
  have hdescent : baseEnd_2136544 < baseStart_2136544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136584 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_2136584 : Nat := 118140960795 + 2136584 * 2 ^ 59
def prefixEnd_2136584 : Nat := 4983230072969 + 3 ^ 40 * 2136584 * 2
def baseEnd_2136584 : Nat := 1097094550705973838974035

theorem tailTrace_2136584 : CollatzResearch.WordTrace tailWord_2136584 prefixEnd_2136584 1097094550705973838974035 := by
  unfold tailWord_2136584
  simp only [CollatzResearch.WordTrace]
  refine ⟨38963810245764271170588403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51951746994352361560784537 38963810245764271170588403)
  ·
    refine ⟨58445715368646406755882605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38963810245764271170588403 58445715368646406755882605)
    ·
      refine ⟨21917143263242402533455977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58445715368646406755882605 21917143263242402533455977)
      ·
        refine ⟨16437857447431801900091983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21917143263242402533455977 16437857447431801900091983)
        ·
          refine ⟨24656786171147702850137975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16437857447431801900091983 24656786171147702850137975)
          ·
            refine ⟨36985179256721554275206963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24656786171147702850137975 36985179256721554275206963)
            ·
              refine ⟨55477768885082331412810445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36985179256721554275206963 55477768885082331412810445)
              ·
                refine ⟨20804163331905874279803917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55477768885082331412810445 20804163331905874279803917)
                ·
                  refine ⟨7801561249464702854926469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20804163331905874279803917 7801561249464702854926469)
                  ·
                    refine ⟨1462792734274631785298713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7801561249464702854926469 1462792734274631785298713)
                    ·
                      refine ⟨1097094550705973838974035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462792734274631785298713 1097094550705973838974035)
                      ·
                        rfl

theorem cell23_2136584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_2136584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136584 prefixEnd_2136584 := by exact prefixLift 2136584
  have htrace : WordTrace (prefixWord ++ tailWord_2136584) baseStart_2136584 baseEnd_2136584 := by
    simpa [prefixWord, tailWord_2136584, baseEnd_2136584] using wordTrace_append hprefix tailTrace_2136584
  have hstable : (prefixWord ++ tailWord_2136584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136584).length < 2 ^ (prefixWord ++ tailWord_2136584).sum := by decide
  have hdescent : baseEnd_2136584 < baseStart_2136584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136587 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5]
def baseStart_2136587 : Nat := 118140960795 + 2136587 * 2 ^ 59
def prefixEnd_2136587 : Nat := 4983230072969 + 3 ^ 40 * 2136587 * 2
def baseEnd_2136587 : Nat := 1097096091147937327236521

theorem tailTrace_2136587 : CollatzResearch.WordTrace tailWord_2136587 prefixEnd_2136587 1097096091147937327236521 := by
  unfold tailWord_2136587
  simp only [CollatzResearch.WordTrace]
  refine ⟨77927729910517673853536015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51951819940345115902357343 77927729910517673853536015)
  ·
    refine ⟨116891594865776510780304023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77927729910517673853536015 116891594865776510780304023)
    ·
      refine ⟨175337392298664766170456035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116891594865776510780304023 175337392298664766170456035)
      ·
        refine ⟨263006088447997149255684053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175337392298664766170456035 263006088447997149255684053)
        ·
          refine ⟨6164205197999933185680095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 263006088447997149255684053 6164205197999933185680095)
          ·
            refine ⟨9246307796999899778520143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164205197999933185680095 9246307796999899778520143)
            ·
              refine ⟨13869461695499849667780215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9246307796999899778520143 13869461695499849667780215)
              ·
                refine ⟨20804192543249774501670323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13869461695499849667780215 20804192543249774501670323)
                ·
                  refine ⟨31206288814874661752505485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20804192543249774501670323 31206288814874661752505485)
                  ·
                    refine ⟨11702358305577998157189557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31206288814874661752505485 11702358305577998157189557)
                    ·
                      refine ⟨1097096091147937327236521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11702358305577998157189557 1097096091147937327236521)
                      ·
                        rfl

theorem cell23_2136587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_2136587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136587 prefixEnd_2136587 := by exact prefixLift 2136587
  have htrace : WordTrace (prefixWord ++ tailWord_2136587) baseStart_2136587 baseEnd_2136587 := by
    simpa [prefixWord, tailWord_2136587, baseEnd_2136587] using wordTrace_append hprefix tailTrace_2136587
  have hstable : (prefixWord ++ tailWord_2136587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136587).length < 2 ^ (prefixWord ++ tailWord_2136587).sum := by decide
  have hdescent : baseEnd_2136587 < baseStart_2136587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136612 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2136612 : Nat := 118140960795 + 2136612 * 2 ^ 59
def prefixEnd_2136612 : Nat := 4983230072969 + 3 ^ 40 * 2136612 * 2
def baseEnd_2136612 : Nat := 1097108928164299729423907

theorem tailTrace_2136612 : CollatzResearch.WordTrace tailWord_2136612 prefixEnd_2136612 1097108928164299729423907 := by
  unfold tailWord_2136612
  simp only [CollatzResearch.WordTrace]
  refine ⟨38964320867713551561598045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51952427823618068748797393 38964320867713551561598045)
  ·
    refine ⟨14611620325392581835599267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38964320867713551561598045 14611620325392581835599267)
    ·
      refine ⟨21917430488088872753398901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14611620325392581835599267 21917430488088872753398901)
      ·
        refine ⟨2054759108258331820631147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21917430488088872753398901 2054759108258331820631147)
        ·
          refine ⟨3082138662387497730946721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054759108258331820631147 3082138662387497730946721)
          ·
            refine ⟨2311603996790623298210041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3082138662387497730946721 2311603996790623298210041)
            ·
              refine ⟨1733702997592967473657531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2311603996790623298210041 1733702997592967473657531)
              ·
                refine ⟨2600554496389451210486297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733702997592967473657531 2600554496389451210486297)
                ·
                  refine ⟨1950415872292088407864723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600554496389451210486297 1950415872292088407864723)
                  ·
                    refine ⟨2925623808438132611797085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1950415872292088407864723 2925623808438132611797085)
                    ·
                      refine ⟨1097108928164299729423907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2925623808438132611797085 1097108928164299729423907)
                      ·
                        rfl

theorem cell23_2136612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2136612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136612 prefixEnd_2136612 := by exact prefixLift 2136612
  have htrace : WordTrace (prefixWord ++ tailWord_2136612) baseStart_2136612 baseEnd_2136612 := by
    simpa [prefixWord, tailWord_2136612, baseEnd_2136612] using wordTrace_append hprefix tailTrace_2136612
  have hstable : (prefixWord ++ tailWord_2136612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136612).length < 2 ^ (prefixWord ++ tailWord_2136612).sum := by decide
  have hdescent : baseEnd_2136612 < baseStart_2136612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136622 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2136622 : Nat := 118140960795 + 2136622 * 2 ^ 59
def prefixEnd_2136622 : Nat := 4983230072969 + 3 ^ 40 * 2136622 * 2
def baseEnd_2136622 : Nat := 1097114062970844690298861

theorem tailTrace_2136622 : CollatzResearch.WordTrace tailWord_2136622 prefixEnd_2136622 1097114062970844690298861 := by
  unfold tailWord_2136622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741125808173859353882515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51952670976927249887373413 9741125808173859353882515)
  ·
    refine ⟨14611688712260789030823773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741125808173859353882515 14611688712260789030823773)
    ·
      refine ⟨5479383267097795886558915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14611688712260789030823773 5479383267097795886558915)
      ·
        refine ⟨8219074900646693829838373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5479383267097795886558915 8219074900646693829838373)
        ·
          refine ⟨1541076543871255093094695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8219074900646693829838373 1541076543871255093094695)
          ·
            refine ⟨2311614815806882639642043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541076543871255093094695 2311614815806882639642043)
            ·
              refine ⟨3467422223710323959463065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311614815806882639642043 3467422223710323959463065)
              ·
                refine ⟨2600566667782742969597299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3467422223710323959463065 2600566667782742969597299)
                ·
                  refine ⟨3900850001674114454395949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2600566667782742969597299 3900850001674114454395949)
                  ·
                    refine ⟨1462818750627792920398481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3900850001674114454395949 1462818750627792920398481)
                    ·
                      refine ⟨1097114062970844690298861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462818750627792920398481 1097114062970844690298861)
                      ·
                        rfl

theorem cell23_2136622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2136622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136622 prefixEnd_2136622 := by exact prefixLift 2136622
  have htrace : WordTrace (prefixWord ++ tailWord_2136622) baseStart_2136622 baseEnd_2136622 := by
    simpa [prefixWord, tailWord_2136622, baseEnd_2136622] using wordTrace_append hprefix tailTrace_2136622
  have hstable : (prefixWord ++ tailWord_2136622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136622).length < 2 ^ (prefixWord ++ tailWord_2136622).sum := by decide
  have hdescent : baseEnd_2136622 < baseStart_2136622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136654 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2136654 : Nat := 118140960795 + 2136654 * 2 ^ 59
def prefixEnd_2136654 : Nat := 4983230072969 + 3 ^ 40 * 2136654 * 2
def baseEnd_2136654 : Nat := 365710164783929521699571

theorem tailTrace_2136654 : CollatzResearch.WordTrace tailWord_2136654 prefixEnd_2136654 365710164783929521699571 := by
  unfold tailWord_2136654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741271700159368037028127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51953449067516629530816677 9741271700159368037028127)
  ·
    refine ⟨14611907550239052055542191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741271700159368037028127 14611907550239052055542191)
    ·
      refine ⟨21917861325358578083313287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14611907550239052055542191 21917861325358578083313287)
      ·
        refine ⟨32876791988037867124969931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21917861325358578083313287 32876791988037867124969931)
        ·
          refine ⟨49315187982056800687454897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32876791988037867124969931 49315187982056800687454897)
          ·
            refine ⟨36986390986542600515591173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49315187982056800687454897 36986390986542600515591173)
            ·
              refine ⟨6934948309976737596673345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36986390986542600515591173 6934948309976737596673345)
              ·
                refine ⟨5201211232482553197505009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6934948309976737596673345 5201211232482553197505009)
                ·
                  refine ⟨3900908424361914898128757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5201211232482553197505009 3900908424361914898128757)
                  ·
                    refine ⟨365710164783929521699571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3900908424361914898128757 365710164783929521699571)
                    ·
                      rfl

theorem cell23_2136654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2136654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136654 prefixEnd_2136654 := by exact prefixLift 2136654
  have htrace : WordTrace (prefixWord ++ tailWord_2136654) baseStart_2136654 baseEnd_2136654 := by
    simpa [prefixWord, tailWord_2136654, baseEnd_2136654] using wordTrace_append hprefix tailTrace_2136654
  have hstable : (prefixWord ++ tailWord_2136654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136654).length < 2 ^ (prefixWord ++ tailWord_2136654).sum := by decide
  have hdescent : baseEnd_2136654 < baseStart_2136654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136684 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_2136684 : Nat := 118140960795 + 2136684 * 2 ^ 59
def prefixEnd_2136684 : Nat := 4983230072969 + 3 ^ 40 * 2136684 * 2
def baseEnd_2136684 : Nat := 365715299590474482574525

theorem tailTrace_2136684 : CollatzResearch.WordTrace tailWord_2136684 prefixEnd_2136684 365715299590474482574525 := by
  unfold tailWord_2136684
  simp only [CollatzResearch.WordTrace]
  refine ⟨38965633895583129709908553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51954178527444172946544737 38965633895583129709908553)
  ·
    refine ⟨29224225421687347282431415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38965633895583129709908553 29224225421687347282431415)
    ·
      refine ⟨43836338132531020923647123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29224225421687347282431415 43836338132531020923647123)
      ·
        refine ⟨65754507198796531385470685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43836338132531020923647123 65754507198796531385470685)
        ·
          refine ⟨24657940199548699269551507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65754507198796531385470685 24657940199548699269551507)
          ·
            refine ⟨36986910299323048904327261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24657940199548699269551507 36986910299323048904327261)
            ·
              refine ⟨13870091362246143339122723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36986910299323048904327261 13870091362246143339122723)
              ·
                refine ⟨20805137043369215008684085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13870091362246143339122723 20805137043369215008684085)
                ·
                  refine ⟨1950481597815863907064133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20805137043369215008684085 1950481597815863907064133)
                  ·
                    refine ⟨365715299590474482574525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1950481597815863907064133 365715299590474482574525)
                    ·
                      rfl

theorem cell23_2136684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_2136684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136684 prefixEnd_2136684 := by exact prefixLift 2136684
  have htrace : WordTrace (prefixWord ++ tailWord_2136684) baseStart_2136684 baseEnd_2136684 := by
    simpa [prefixWord, tailWord_2136684, baseEnd_2136684] using wordTrace_append hprefix tailTrace_2136684
  have hstable : (prefixWord ++ tailWord_2136684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136684).length < 2 ^ (prefixWord ++ tailWord_2136684).sum := by decide
  have hdescent : baseEnd_2136684 < baseStart_2136684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136688 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 2, 5]
def baseStart_2136688 : Nat := 118140960795 + 2136688 * 2 ^ 59
def prefixEnd_2136688 : Nat := 4983230072969 + 3 ^ 40 * 2136688 * 2
def baseEnd_2136688 : Nat := 365715984231347144024519

theorem tailTrace_2136688 : CollatzResearch.WordTrace tailWord_2136688 prefixEnd_2136688 365715984231347144024519 := by
  unfold tailWord_2136688
  simp only [CollatzResearch.WordTrace]
  refine ⟨38965706841575884051481359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51954275788767845401975145 38965706841575884051481359)
  ·
    refine ⟨58448560262363826077222039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38965706841575884051481359 58448560262363826077222039)
    ·
      refine ⟨87672840393545739115833059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58448560262363826077222039 87672840393545739115833059)
      ·
        refine ⟨131509260590318608673749589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87672840393545739115833059 131509260590318608673749589)
        ·
          refine ⟨1541124147542796195395503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 131509260590318608673749589 1541124147542796195395503)
          ·
            refine ⟨2311686221314194293093255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541124147542796195395503 2311686221314194293093255)
            ·
              refine ⟨3467529331971291439639883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311686221314194293093255 3467529331971291439639883)
              ·
                refine ⟨5201293997956937159459825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467529331971291439639883 5201293997956937159459825)
                ·
                  refine ⟨3900970498467702869594869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5201293997956937159459825 3900970498467702869594869)
                  ·
                    refine ⟨365715984231347144024519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3900970498467702869594869 365715984231347144024519)
                    ·
                      rfl

theorem cell23_2136688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 5].length) (baseStart_2136688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136688 prefixEnd_2136688 := by exact prefixLift 2136688
  have htrace : WordTrace (prefixWord ++ tailWord_2136688) baseStart_2136688 baseEnd_2136688 := by
    simpa [prefixWord, tailWord_2136688, baseEnd_2136688] using wordTrace_append hprefix tailTrace_2136688
  have hstable : (prefixWord ++ tailWord_2136688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136688).length < 2 ^ (prefixWord ++ tailWord_2136688).sum := by decide
  have hdescent : baseEnd_2136688 < baseStart_2136688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136718 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_2136718 : Nat := 118140960795 + 2136718 * 2 ^ 59
def prefixEnd_2136718 : Nat := 4983230072969 + 3 ^ 40 * 2136718 * 2
def baseEnd_2136718 : Nat := 365721119037892104899473

theorem tailTrace_2136718 : CollatzResearch.WordTrace tailWord_2136718 prefixEnd_2136718 365721119037892104899473 := by
  unfold tailWord_2136718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741563484130385403319351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51955005248695388817703205 9741563484130385403319351)
  ·
    refine ⟨14612345226195578104979027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741563484130385403319351 14612345226195578104979027)
    ·
      refine ⟨21918517839293367157468541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14612345226195578104979027 21918517839293367157468541)
      ·
        refine ⟨8219444189735012684050703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21918517839293367157468541 8219444189735012684050703)
        ·
          refine ⟨12329166284602519026076055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219444189735012684050703 12329166284602519026076055)
          ·
            refine ⟨18493749426903778539114083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12329166284602519026076055 18493749426903778539114083)
            ·
              refine ⟨27740624140355667808671125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18493749426903778539114083 27740624140355667808671125)
              ·
                refine ⟨1300341756579171928531459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27740624140355667808671125 1300341756579171928531459)
                ·
                  refine ⟨1950512634868757892797189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300341756579171928531459 1950512634868757892797189)
                  ·
                    refine ⟨365721119037892104899473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1950512634868757892797189 365721119037892104899473)
                    ·
                      rfl

theorem cell23_2136718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_2136718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136718 prefixEnd_2136718 := by exact prefixLift 2136718
  have htrace : WordTrace (prefixWord ++ tailWord_2136718) baseStart_2136718 baseEnd_2136718 := by
    simpa [prefixWord, tailWord_2136718, baseEnd_2136718] using wordTrace_append hprefix tailTrace_2136718
  have hstable : (prefixWord ++ tailWord_2136718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136718).length < 2 ^ (prefixWord ++ tailWord_2136718).sum := by decide
  have hdescent : baseEnd_2136718 < baseStart_2136718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136751 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 1, 5, 2]
def baseStart_2136751 : Nat := 118140960795 + 2136751 * 2 ^ 59
def prefixEnd_2136751 : Nat := 4983230072969 + 3 ^ 40 * 2136751 * 2
def baseEnd_2136751 : Nat := 1097180301975274685585767

theorem tailTrace_2136751 : CollatzResearch.WordTrace tailWord_2136751 prefixEnd_2136751 1097180301975274685585767 := by
  unfold tailWord_2136751
  simp only [CollatzResearch.WordTrace]
  refine ⟨77933711481923529862506107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51955807654615686575004071 77933711481923529862506107)
  ·
    refine ⟨116900567222885294793759161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77933711481923529862506107 116900567222885294793759161)
    ·
      refine ⟨87675425417163971095319371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116900567222885294793759161 87675425417163971095319371)
      ·
        refine ⟨131513138125745956642979057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87675425417163971095319371 131513138125745956642979057)
        ·
          refine ⟨98634853594309467482234293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131513138125745956642979057 98634853594309467482234293)
          ·
            refine ⟨9247017524466512576459465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98634853594309467482234293 9247017524466512576459465)
            ·
              refine ⟨6935263143349884432344599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9247017524466512576459465 6935263143349884432344599)
              ·
                refine ⟨10402894715024826648516899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6935263143349884432344599 10402894715024826648516899)
                ·
                  refine ⟨15604342072537239972775349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10402894715024826648516899 15604342072537239972775349)
                  ·
                    refine ⟨1462907069300366247447689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15604342072537239972775349 1462907069300366247447689)
                    ·
                      refine ⟨1097180301975274685585767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462907069300366247447689 1097180301975274685585767)
                      ·
                        rfl

theorem cell23_2136751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5, 2].length) (baseStart_2136751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136751 prefixEnd_2136751 := by exact prefixLift 2136751
  have htrace : WordTrace (prefixWord ++ tailWord_2136751) baseStart_2136751 baseEnd_2136751 := by
    simpa [prefixWord, tailWord_2136751, baseEnd_2136751] using wordTrace_append hprefix tailTrace_2136751
  have hstable : (prefixWord ++ tailWord_2136751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136751).length < 2 ^ (prefixWord ++ tailWord_2136751).sum := by decide
  have hdescent : baseEnd_2136751 < baseStart_2136751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136768 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 2, 3, 2]
def baseStart_2136768 : Nat := 118140960795 + 2136768 * 2 ^ 59
def prefixEnd_2136768 : Nat := 4983230072969 + 3 ^ 40 * 2136768 * 2
def baseEnd_2136768 : Nat := 1097189031146401119073189

theorem tailTrace_2136768 : CollatzResearch.WordTrace tailWord_2136768 prefixEnd_2136768 1097189031146401119073189 := by
  unfold tailWord_2136768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38967165761430970882937479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51956221015241294510583305 38967165761430970882937479)
  ·
    refine ⟨58450748642146456324406219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38967165761430970882937479 58450748642146456324406219)
    ·
      refine ⟨87676122963219684486609329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58450748642146456324406219 87676122963219684486609329)
      ·
        refine ⟨65757092222414763364956997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87676122963219684486609329 65757092222414763364956997)
        ·
          refine ⟨12329454791702768130929437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65757092222414763364956997 12329454791702768130929437)
          ·
            refine ⟨4623545546888538049098539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12329454791702768130929437 4623545546888538049098539)
            ·
              refine ⟨6935318320332807073647809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623545546888538049098539 6935318320332807073647809)
              ·
                refine ⟨5201488740249605305235857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6935318320332807073647809 5201488740249605305235857)
                ·
                  refine ⟨3901116555187203978926893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5201488740249605305235857 3901116555187203978926893)
                  ·
                    refine ⟨1462918708195201492097585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3901116555187203978926893 1462918708195201492097585)
                    ·
                      refine ⟨1097189031146401119073189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462918708195201492097585 1097189031146401119073189)
                      ·
                        rfl

theorem cell23_2136768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_2136768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136768 prefixEnd_2136768 := by exact prefixLift 2136768
  have htrace : WordTrace (prefixWord ++ tailWord_2136768) baseStart_2136768 baseEnd_2136768 := by
    simpa [prefixWord, tailWord_2136768, baseEnd_2136768] using wordTrace_append hprefix tailTrace_2136768
  have hstable : (prefixWord ++ tailWord_2136768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136768).length < 2 ^ (prefixWord ++ tailWord_2136768).sum := by decide
  have hdescent : baseEnd_2136768 < baseStart_2136768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136769 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2136769 : Nat := 118140960795 + 2136769 * 2 ^ 59
def prefixEnd_2136769 : Nat := 4983230072969 + 3 ^ 40 * 2136769 * 2
def baseEnd_2136769 : Nat := 365729848209018538386895

theorem tailTrace_2136769 : CollatzResearch.WordTrace tailWord_2136769 prefixEnd_2136769 365729848209018538386895 := by
  unfold tailWord_2136769
  simp only [CollatzResearch.WordTrace]
  refine ⟨77934367995858318936661361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51956245330572212624440907 77934367995858318936661361)
  ·
    refine ⟨58450775996893739202496021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77934367995858318936661361 58450775996893739202496021)
    ·
      refine ⟨2739880124854394025117001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58450775996893739202496021 2739880124854394025117001)
      ·
        refine ⟨2054910093640795518837751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2739880124854394025117001 2054910093640795518837751)
        ·
          refine ⟨3082365140461193278256627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054910093640795518837751 3082365140461193278256627)
          ·
            refine ⟨4623547710691789917384941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082365140461193278256627 4623547710691789917384941)
            ·
              refine ⟨1733830391509421219019353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4623547710691789917384941 1733830391509421219019353)
              ·
                refine ⟨1300372793632065914264515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733830391509421219019353 1300372793632065914264515)
                ·
                  refine ⟨1950559190448098871396773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300372793632065914264515 1950559190448098871396773)
                  ·
                    refine ⟨365729848209018538386895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1950559190448098871396773 365729848209018538386895)
                    ·
                      rfl

theorem cell23_2136769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2136769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136769 prefixEnd_2136769 := by exact prefixLift 2136769
  have htrace : WordTrace (prefixWord ++ tailWord_2136769) baseStart_2136769 baseEnd_2136769 := by
    simpa [prefixWord, tailWord_2136769, baseEnd_2136769] using wordTrace_append hprefix tailTrace_2136769
  have hstable : (prefixWord ++ tailWord_2136769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136769).length < 2 ^ (prefixWord ++ tailWord_2136769).sum := by decide
  have hdescent : baseEnd_2136769 < baseStart_2136769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136794 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2136794 : Nat := 118140960795 + 2136794 * 2 ^ 59
def prefixEnd_2136794 : Nat := 4983230072969 + 3 ^ 40 * 2136794 * 2
def baseEnd_2136794 : Nat := 1097202381643418017348069

theorem tailTrace_2136794 : CollatzResearch.WordTrace tailWord_2136794 prefixEnd_2136794 1097202381643418017348069 := by
  unfold tailWord_2136794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19483819955191937051580359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51956853213845165470880957 19483819955191937051580359)
  ·
    refine ⟨29225729932787905577370539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19483819955191937051580359 29225729932787905577370539)
    ·
      refine ⟨43838594899181858366055809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29225729932787905577370539 43838594899181858366055809)
      ·
        refine ⟨32878946174386393774541857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43838594899181858366055809 32878946174386393774541857)
        ·
          refine ⟨24659209630789795330906393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32878946174386393774541857 24659209630789795330906393)
          ·
            refine ⟨18494407223092346498179795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24659209630789795330906393 18494407223092346498179795)
            ·
              refine ⟨27741610834638519747269693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18494407223092346498179795 27741610834638519747269693)
              ·
                refine ⟨10403104062989444905226135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27741610834638519747269693 10403104062989444905226135)
                ·
                  refine ⟨15604656094484167357839203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10403104062989444905226135 15604656094484167357839203)
                  ·
                    refine ⟨23406984141726251036758805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15604656094484167357839203 23406984141726251036758805)
                    ·
                      refine ⟨1097202381643418017348069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23406984141726251036758805 1097202381643418017348069)
                      ·
                        rfl

theorem cell23_2136794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2136794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136794 prefixEnd_2136794 := by exact prefixLift 2136794
  have htrace : WordTrace (prefixWord ++ tailWord_2136794) baseStart_2136794 baseEnd_2136794 := by
    simpa [prefixWord, tailWord_2136794, baseEnd_2136794] using wordTrace_append hprefix tailTrace_2136794
  have hstable : (prefixWord ++ tailWord_2136794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136794).length < 2 ^ (prefixWord ++ tailWord_2136794).sum := by decide
  have hdescent : baseEnd_2136794 < baseStart_2136794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136804 : List Nat := [2, 3, 1, 1, 1, 4, 2, 9]
def baseStart_2136804 : Nat := 118140960795 + 2136804 * 2 ^ 59
def prefixEnd_2136804 : Nat := 4983230072969 + 3 ^ 40 * 2136804 * 2
def baseEnd_2136804 : Nat := 40637315424072702897149

theorem tailTrace_2136804 : CollatzResearch.WordTrace tailWord_2136804 prefixEnd_2136804 40637315424072702897149 := by
  unfold tailWord_2136804
  simp only [CollatzResearch.WordTrace]
  refine ⟨38967822275365759957092733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51957096367154346609456977 38967822275365759957092733)
  ·
    refine ⟨14612933353262159983909775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38967822275365759957092733 14612933353262159983909775)
    ·
      refine ⟨21919400029893239975864663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14612933353262159983909775 21919400029893239975864663)
      ·
        refine ⟨32879100044839859963796995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21919400029893239975864663 32879100044839859963796995)
        ·
          refine ⟨49318650067259789945695493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32879100044839859963796995 49318650067259789945695493)
          ·
            refine ⟨9247246887611210614817905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49318650067259789945695493 9247246887611210614817905)
            ·
              refine ⟨6935435165708407961113429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9247246887611210614817905 6935435165708407961113429)
              ·
                refine ⟨40637315424072702897149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6935435165708407961113429 40637315424072702897149)
                ·
                  rfl

theorem cell23_2136804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 9].length) (baseStart_2136804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136804 prefixEnd_2136804 := by exact prefixLift 2136804
  have htrace : WordTrace (prefixWord ++ tailWord_2136804) baseStart_2136804 baseEnd_2136804 := by
    simpa [prefixWord, tailWord_2136804, baseEnd_2136804] using wordTrace_append hprefix tailTrace_2136804
  have hstable : (prefixWord ++ tailWord_2136804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136804).length < 2 ^ (prefixWord ++ tailWord_2136804).sum := by decide
  have hdescent : baseEnd_2136804 < baseStart_2136804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136818 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2136818 : Nat := 118140960795 + 2136818 * 2 ^ 59
def prefixEnd_2136818 : Nat := 4983230072969 + 3 ^ 40 * 2136818 * 2
def baseEnd_2136818 : Nat := 1097214705179125923447959

theorem tailTrace_2136818 : CollatzResearch.WordTrace tailWord_2136818 prefixEnd_2136818 1097214705179125923447959 := by
  unfold tailWord_2136818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19484038793170200076298777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51957436781787200203463405 19484038793170200076298777)
  ·
    refine ⟨14613029094877650057224083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19484038793170200076298777 14613029094877650057224083)
    ·
      refine ⟨21919543642316475085836125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14613029094877650057224083 21919543642316475085836125)
      ·
        refine ⟨8219828865868678157188547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21919543642316475085836125 8219828865868678157188547)
        ·
          refine ⟨12329743298803017235782821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219828865868678157188547 12329743298803017235782821)
          ·
            refine ⟨2311826868525565731709279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12329743298803017235782821 2311826868525565731709279)
            ·
              refine ⟨3467740302788348597563919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311826868525565731709279 3467740302788348597563919)
              ·
                refine ⟨5201610454182522896345879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467740302788348597563919 5201610454182522896345879)
                ·
                  refine ⟨7802415681273784344518819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5201610454182522896345879 7802415681273784344518819)
                  ·
                    refine ⟨11703623521910676516778229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7802415681273784344518819 11703623521910676516778229)
                    ·
                      refine ⟨1097214705179125923447959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11703623521910676516778229 1097214705179125923447959)
                      ·
                        rfl

theorem cell23_2136818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2136818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136818 prefixEnd_2136818 := by exact prefixLift 2136818
  have htrace : WordTrace (prefixWord ++ tailWord_2136818) baseStart_2136818 baseEnd_2136818 := by
    simpa [prefixWord, tailWord_2136818, baseEnd_2136818] using wordTrace_append hprefix tailTrace_2136818
  have hstable : (prefixWord ++ tailWord_2136818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136818).length < 2 ^ (prefixWord ++ tailWord_2136818).sum := by decide
  have hdescent : baseEnd_2136818 < baseStart_2136818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136844 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2136844 : Nat := 118140960795 + 2136844 * 2 ^ 59
def prefixEnd_2136844 : Nat := 4983230072969 + 3 ^ 40 * 2136844 * 2
def baseEnd_2136844 : Nat := 1097228055676142821722839

theorem tailTrace_2136844 : CollatzResearch.WordTrace tailWord_2136844 prefixEnd_2136844 1097228055676142821722839 := by
  unfold tailWord_2136844
  simp only [CollatzResearch.WordTrace]
  refine ⟨38968551735293303372820793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51958068980391071163761057 38968551735293303372820793)
  ·
    refine ⟨29226413801469977529615595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38968551735293303372820793 29226413801469977529615595)
    ·
      refine ⟨43839620702204966294423393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29226413801469977529615595 43839620702204966294423393)
      ·
        refine ⟨32879715526653724720817545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43839620702204966294423393 32879715526653724720817545)
        ·
          refine ⟨24659786644990293540613159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32879715526653724720817545 24659786644990293540613159)
          ·
            refine ⟨36989679967485440310919739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24659786644990293540613159 36989679967485440310919739)
            ·
              refine ⟨55484519951228160466379609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36989679967485440310919739 55484519951228160466379609)
              ·
                refine ⟨41613389963421120349784707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55484519951228160466379609 41613389963421120349784707)
                ·
                  refine ⟨62420084945131680524677061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41613389963421120349784707 62420084945131680524677061)
                  ·
                    refine ⟨11703765927212190098376949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62420084945131680524677061 11703765927212190098376949)
                    ·
                      refine ⟨1097228055676142821722839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11703765927212190098376949 1097228055676142821722839)
                      ·
                        rfl

theorem cell23_2136844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2136844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136844 prefixEnd_2136844 := by exact prefixLift 2136844
  have htrace : WordTrace (prefixWord ++ tailWord_2136844) baseStart_2136844 baseEnd_2136844 := by
    simpa [prefixWord, tailWord_2136844, baseEnd_2136844] using wordTrace_append hprefix tailTrace_2136844
  have hstable : (prefixWord ++ tailWord_2136844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136844).length < 2 ^ (prefixWord ++ tailWord_2136844).sum := by decide
  have hdescent : baseEnd_2136844 < baseStart_2136844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136858 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2]
def baseStart_2136858 : Nat := 118140960795 + 2136858 * 2 ^ 59
def prefixEnd_2136858 : Nat := 4983230072969 + 3 ^ 40 * 2136858 * 2
def baseEnd_2136858 : Nat := 1097235244405305766947775

theorem tailTrace_2136858 : CollatzResearch.WordTrace tailWord_2136858 prefixEnd_2136858 1097235244405305766947775 := by
  unfold tailWord_2136858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19484403523133971784162807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51958409395023924757767485 19484403523133971784162807)
  ·
    refine ⟨29226605284700957676244211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19484403523133971784162807 29226605284700957676244211)
    ·
      refine ⟨43839907927051436514366317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29226605284700957676244211 43839907927051436514366317)
      ·
        refine ⟨16439965472644288692887369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43839907927051436514366317 16439965472644288692887369)
        ·
          refine ⟨12329974104483216519665527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16439965472644288692887369 12329974104483216519665527)
          ·
            refine ⟨18494961156724824779498291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12329974104483216519665527 18494961156724824779498291)
            ·
              refine ⟨27742441735087237169247437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18494961156724824779498291 27742441735087237169247437)
              ·
                refine ⟨10403415650657713938467789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27742441735087237169247437 10403415650657713938467789)
                ·
                  refine ⟨3901280868996642726925421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10403415650657713938467789 3901280868996642726925421)
                  ·
                    refine ⟨1462980325873741022597033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3901280868996642726925421 1462980325873741022597033)
                    ·
                      refine ⟨1097235244405305766947775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1462980325873741022597033 1097235244405305766947775)
                      ·
                        rfl

theorem cell23_2136858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_2136858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136858 prefixEnd_2136858 := by exact prefixLift 2136858
  have htrace : WordTrace (prefixWord ++ tailWord_2136858) baseStart_2136858 baseEnd_2136858 := by
    simpa [prefixWord, tailWord_2136858, baseEnd_2136858] using wordTrace_append hprefix tailTrace_2136858
  have hstable : (prefixWord ++ tailWord_2136858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136858).length < 2 ^ (prefixWord ++ tailWord_2136858).sum := by decide
  have hdescent : baseEnd_2136858 < baseStart_2136858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136905 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 1, 4, 2]
def baseStart_2136905 : Nat := 118140960795 + 2136905 * 2 ^ 59
def prefixEnd_2136905 : Nat := 4983230072969 + 3 ^ 40 * 2136905 * 2
def baseEnd_2136905 : Nat := 1097259377996067083060059

theorem tailTrace_2136905 : CollatzResearch.WordTrace tailWord_2136905 prefixEnd_2136905 1097259377996067083060059 := by
  unfold tailWord_2136905
  simp only [CollatzResearch.WordTrace]
  refine ⟨77939328323365614163612169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51959552215577076109074779 77939328323365614163612169)
  ·
    refine ⟨58454496242524210622709127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77939328323365614163612169 58454496242524210622709127)
    ·
      refine ⟨87681744363786315934063691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58454496242524210622709127 87681744363786315934063691)
      ·
        refine ⟨131522616545679473901095537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87681744363786315934063691 131522616545679473901095537)
        ·
          refine ⟨98641962409259605425821653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131522616545679473901095537 98641962409259605425821653)
          ·
            refine ⟨2311920993967022002167695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 98641962409259605425821653 2311920993967022002167695)
            ·
              refine ⟨3467881490950533003251543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311920993967022002167695 3467881490950533003251543)
              ·
                refine ⟨5201822236425799504877315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467881490950533003251543 5201822236425799504877315)
                ·
                  refine ⟨7802733354638699257315973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5201822236425799504877315 7802733354638699257315973)
                  ·
                    refine ⟨1463012503994756110746745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7802733354638699257315973 1463012503994756110746745)
                    ·
                      refine ⟨1097259377996067083060059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463012503994756110746745 1097259377996067083060059)
                      ·
                        rfl

theorem cell23_2136905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 4, 2].length) (baseStart_2136905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136905 prefixEnd_2136905 := by exact prefixLift 2136905
  have htrace : WordTrace (prefixWord ++ tailWord_2136905) baseStart_2136905 baseEnd_2136905 := by
    simpa [prefixWord, tailWord_2136905, baseEnd_2136905] using wordTrace_append hprefix tailTrace_2136905
  have hstable : (prefixWord ++ tailWord_2136905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136905).length < 2 ^ (prefixWord ++ tailWord_2136905).sum := by decide
  have hdescent : baseEnd_2136905 < baseStart_2136905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136909 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2136909 : Nat := 118140960795 + 2136909 * 2 ^ 59
def prefixEnd_2136909 : Nat := 4983230072969 + 3 ^ 40 * 2136909 * 2
def baseEnd_2136909 : Nat := 1097261431918685067410041

theorem tailTrace_2136909 : CollatzResearch.WordTrace tailWord_2136909 prefixEnd_2136909 1097261431918685067410041 := by
  unfold tailWord_2136909
  simp only [CollatzResearch.WordTrace]
  refine ⟨77939474215351122846757781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51959649476900748564505187 77939474215351122846757781)
  ·
    refine ⟨3653412853844583883441771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77939474215351122846757781 3653412853844583883441771)
    ·
      refine ⟨5480119280766875825162657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653412853844583883441771 5480119280766875825162657)
      ·
        refine ⟨4110089460575156868871993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5480119280766875825162657 4110089460575156868871993)
        ·
          refine ⟨3082567095431367651653995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4110089460575156868871993 3082567095431367651653995)
          ·
            refine ⟨4623850643147051477480993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082567095431367651653995 4623850643147051477480993)
            ·
              refine ⟨3467887982360288608110745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4623850643147051477480993 3467887982360288608110745)
              ·
                refine ⟨2600915986770216456083059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3467887982360288608110745 2600915986770216456083059)
                ·
                  refine ⟨3901373980155324684124589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2600915986770216456083059 3901373980155324684124589)
                  ·
                    refine ⟨1463015242558246756546721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3901373980155324684124589 1463015242558246756546721)
                    ·
                      refine ⟨1097261431918685067410041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463015242558246756546721 1097261431918685067410041)
                      ·
                        rfl

theorem cell23_2136909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2136909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136909 prefixEnd_2136909 := by exact prefixLift 2136909
  have htrace : WordTrace (prefixWord ++ tailWord_2136909) baseStart_2136909 baseEnd_2136909 := by
    simpa [prefixWord, tailWord_2136909, baseEnd_2136909] using wordTrace_append hprefix tailTrace_2136909
  have hstable : (prefixWord ++ tailWord_2136909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136909).length < 2 ^ (prefixWord ++ tailWord_2136909).sum := by decide
  have hdescent : baseEnd_2136909 < baseStart_2136909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136945 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 5]
def baseStart_2136945 : Nat := 118140960795 + 2136945 * 2 ^ 59
def prefixEnd_2136945 : Nat := 4983230072969 + 3 ^ 40 * 2136945 * 2
def baseEnd_2136945 : Nat := 121919990802471880728875

theorem tailTrace_2136945 : CollatzResearch.WordTrace tailWord_2136945 prefixEnd_2136945 121919990802471880728875 := by
  unfold tailWord_2136945
  simp only [CollatzResearch.WordTrace]
  refine ⟨77940787243220700995068289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51960524828813800663378859 77940787243220700995068289)
  ·
    refine ⟨58455590432415525746301217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77940787243220700995068289 58455590432415525746301217)
    ·
      refine ⟨43841692824311644309725913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58455590432415525746301217 43841692824311644309725913)
      ·
        refine ⟨32881269618233733232294435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43841692824311644309725913 32881269618233733232294435)
        ·
          refine ⟨49321904427350599848441653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32881269618233733232294435 49321904427350599848441653)
          ·
            refine ⟨4623928540064118735791405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49321904427350599848441653 4623928540064118735791405)
            ·
              refine ⟨1733973202524044525921777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4623928540064118735791405 1733973202524044525921777)
              ·
                refine ⟨1300479901893033394441333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733973202524044525921777 1300479901893033394441333)
                ·
                  refine ⟨121919990802471880728875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300479901893033394441333 121919990802471880728875)
                  ·
                    rfl

theorem cell23_2136945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 5].length) (baseStart_2136945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2136945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2136945 prefixEnd_2136945 := by exact prefixLift 2136945
  have htrace : WordTrace (prefixWord ++ tailWord_2136945) baseStart_2136945 baseEnd_2136945 := by
    simpa [prefixWord, tailWord_2136945, baseEnd_2136945] using wordTrace_append hprefix tailTrace_2136945
  have hstable : (prefixWord ++ tailWord_2136945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136945).length < 2 ^ (prefixWord ++ tailWord_2136945).sum := by decide
  have hdescent : baseEnd_2136945 < baseStart_2136945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137012 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2137012 : Nat := 118140960795 + 2137012 * 2 ^ 59
def prefixEnd_2137012 : Nat := 4983230072969 + 3 ^ 40 * 2137012 * 2
def baseEnd_2137012 : Nat := 1097314320426098164422067

theorem tailTrace_2137012 : CollatzResearch.WordTrace tailWord_2137012 prefixEnd_2137012 1097314320426098164422067 := by
  unfold tailWord_2137012
  simp only [CollatzResearch.WordTrace]
  refine ⟨38971615466988985718878645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51962153955985314291838193 38971615466988985718878645)
  ·
    refine ⟨3653588950030217411144873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38971615466988985718878645 3653588950030217411144873)
    ·
      refine ⟨2740191712522663058358655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3653588950030217411144873 2740191712522663058358655)
      ·
        refine ⟨4110287568783994587537983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2740191712522663058358655 4110287568783994587537983)
        ·
          refine ⟨6165431353175991881306975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110287568783994587537983 6165431353175991881306975)
          ·
            refine ⟨9248147029763987821960463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6165431353175991881306975 9248147029763987821960463)
            ·
              refine ⟨13872220544645981732940695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9248147029763987821960463 13872220544645981732940695)
              ·
                refine ⟨20808330816968972599411043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13872220544645981732940695 20808330816968972599411043)
                ·
                  refine ⟨31212496225453458899116565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20808330816968972599411043 31212496225453458899116565)
                  ·
                    refine ⟨1463085760568130885896089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31212496225453458899116565 1463085760568130885896089)
                    ·
                      refine ⟨1097314320426098164422067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463085760568130885896089 1097314320426098164422067)
                      ·
                        rfl

theorem cell23_2137012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2137012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137012 prefixEnd_2137012 := by exact prefixLift 2137012
  have htrace : WordTrace (prefixWord ++ tailWord_2137012) baseStart_2137012 baseEnd_2137012 := by
    simpa [prefixWord, tailWord_2137012, baseEnd_2137012] using wordTrace_append hprefix tailTrace_2137012
  have hstable : (prefixWord ++ tailWord_2137012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137012).length < 2 ^ (prefixWord ++ tailWord_2137012).sum := by decide
  have hdescent : baseEnd_2137012 < baseStart_2137012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137032 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_2137032 : Nat := 118140960795 + 2137032 * 2 ^ 59
def prefixEnd_2137032 : Nat := 4983230072969 + 3 ^ 40 * 2137032 * 2
def baseEnd_2137032 : Nat := 1097324590039188086171975

theorem tailTrace_2137032 : CollatzResearch.WordTrace tailWord_2137032 prefixEnd_2137032 1097324590039188086171975 := by
  unfold tailWord_2137032
  simp only [CollatzResearch.WordTrace]
  refine ⟨38971980196952757426742675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51962640262603676568990233 38971980196952757426742675)
  ·
    refine ⟨58457970295429136140114013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38971980196952757426742675 58457970295429136140114013)
    ·
      refine ⟨21921738860785926052542755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58457970295429136140114013 21921738860785926052542755)
      ·
        refine ⟨32882608291178889078814133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21921738860785926052542755 32882608291178889078814133)
        ·
          refine ⟨3082744527298020851138825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32882608291178889078814133 3082744527298020851138825)
          ·
            refine ⟨2312058395473515638354119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3082744527298020851138825 2312058395473515638354119)
            ·
              refine ⟨3468087593210273457531179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312058395473515638354119 3468087593210273457531179)
              ·
                refine ⟨5202131389815410186296769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3468087593210273457531179 5202131389815410186296769)
                ·
                  refine ⟨3901598542361557639722577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5202131389815410186296769 3901598542361557639722577)
                  ·
                    refine ⟨2926198906771168229791933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3901598542361557639722577 2926198906771168229791933)
                    ·
                      refine ⟨1097324590039188086171975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2926198906771168229791933 1097324590039188086171975)
                      ·
                        rfl

theorem cell23_2137032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_2137032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137032 prefixEnd_2137032 := by exact prefixLift 2137032
  have htrace : WordTrace (prefixWord ++ tailWord_2137032) baseStart_2137032 baseEnd_2137032 := by
    simpa [prefixWord, tailWord_2137032, baseEnd_2137032] using wordTrace_append hprefix tailTrace_2137032
  have hstable : (prefixWord ++ tailWord_2137032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137032).length < 2 ^ (prefixWord ++ tailWord_2137032).sum := by decide
  have hdescent : baseEnd_2137032 < baseStart_2137032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137088 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_2137088 : Nat := 118140960795 + 2137088 * 2 ^ 59
def prefixEnd_2137088 : Nat := 4983230072969 + 3 ^ 40 * 2137088 * 2
def baseEnd_2137088 : Nat := 1097353344955839867071717

theorem tailTrace_2137088 : CollatzResearch.WordTrace tailWord_2137088 prefixEnd_2137088 1097353344955839867071717 := by
  unfold tailWord_2137088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38973001440851318208761959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51964001921135090945015945 38973001440851318208761959)
  ·
    refine ⟨58459502161276977313142939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38973001440851318208761959 58459502161276977313142939)
    ·
      refine ⟨87689253241915465969714409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58459502161276977313142939 87689253241915465969714409)
      ·
        refine ⟨65766939931436599477285807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87689253241915465969714409 65766939931436599477285807)
        ·
          refine ⟨98650409897154899215928711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65766939931436599477285807 98650409897154899215928711)
          ·
            refine ⟨147975614845732348823893067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98650409897154899215928711 147975614845732348823893067)
            ·
              refine ⟨221963422268598523235839601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147975614845732348823893067 221963422268598523235839601)
              ·
                refine ⟨166472566701448892426879701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221963422268598523235839601 166472566701448892426879701)
                ·
                  refine ⟨3901700782065208416254993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 166472566701448892426879701 3901700782065208416254993)
                  ·
                    refine ⟨2926275586548906312191245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3901700782065208416254993 2926275586548906312191245)
                    ·
                      refine ⟨1097353344955839867071717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2926275586548906312191245 1097353344955839867071717)
                      ·
                        rfl

theorem cell23_2137088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_2137088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137088 prefixEnd_2137088 := by exact prefixLift 2137088
  have htrace : WordTrace (prefixWord ++ tailWord_2137088) baseStart_2137088 baseEnd_2137088 := by
    simpa [prefixWord, tailWord_2137088, baseEnd_2137088] using wordTrace_append hprefix tailTrace_2137088
  have hstable : (prefixWord ++ tailWord_2137088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137088).length < 2 ^ (prefixWord ++ tailWord_2137088).sum := by decide
  have hdescent : baseEnd_2137088 < baseStart_2137088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137119 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 3, 2, 2]
def baseStart_2137119 : Nat := 118140960795 + 2137119 * 2 ^ 59
def prefixEnd_2137119 : Nat := 4983230072969 + 3 ^ 40 * 2137119 * 2
def baseEnd_2137119 : Nat := 1097369262856129245784075

theorem tailTrace_2137119 : CollatzResearch.WordTrace tailWord_2137119 prefixEnd_2137119 1097369262856129245784075 := by
  unfold tailWord_2137119
  simp only [CollatzResearch.WordTrace]
  refine ⟨77947133544590328711902411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51964755696393552474601607 77947133544590328711902411)
  ·
    refine ⟨116920700316885493067853617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77947133544590328711902411 116920700316885493067853617)
    ·
      refine ⟨87690525237664119800890213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116920700316885493067853617 87690525237664119800890213)
      ·
        refine ⟨16441973482062022462666915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87690525237664119800890213 16441973482062022462666915)
        ·
          refine ⟨24662960223093033694000373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16441973482062022462666915 24662960223093033694000373)
          ·
            refine ⟨2312152520914971908812535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24662960223093033694000373 2312152520914971908812535)
            ·
              refine ⟨3468228781372457863218803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312152520914971908812535 3468228781372457863218803)
              ·
                refine ⟨5202343172058686794828205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3468228781372457863218803 5202343172058686794828205)
                ·
                  refine ⟨1950878689522007548060577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5202343172058686794828205 1950878689522007548060577)
                  ·
                    refine ⟨1463159017141505661045433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1950878689522007548060577 1463159017141505661045433)
                    ·
                      refine ⟨1097369262856129245784075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463159017141505661045433 1097369262856129245784075)
                      ·
                        rfl

theorem cell23_2137119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_2137119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137119 prefixEnd_2137119 := by exact prefixLift 2137119
  have htrace : WordTrace (prefixWord ++ tailWord_2137119) baseStart_2137119 baseEnd_2137119 := by
    simpa [prefixWord, tailWord_2137119, baseEnd_2137119] using wordTrace_append hprefix tailTrace_2137119
  have hstable : (prefixWord ++ tailWord_2137119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137119).length < 2 ^ (prefixWord ++ tailWord_2137119).sum := by decide
  have hdescent : baseEnd_2137119 < baseStart_2137119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137162 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_2137162 : Nat := 118140960795 + 2137162 * 2 ^ 59
def prefixEnd_2137162 : Nat := 4983230072969 + 3 ^ 40 * 2137162 * 2
def baseEnd_2137162 : Nat := 1097391342524272577546377

theorem tailTrace_2137162 : CollatzResearch.WordTrace tailWord_2137162 prefixEnd_2137162 1097391342524272577546377 := by
  unfold tailWord_2137162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487175470858636763929435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51965801255623031370478493 19487175470858636763929435)
  ·
    refine ⟨29230763206287955145894153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19487175470858636763929435 29230763206287955145894153)
    ·
      refine ⟨21923072404715966359420615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29230763206287955145894153 21923072404715966359420615)
      ·
        refine ⟨32884608607073949539130923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21923072404715966359420615 32884608607073949539130923)
        ·
          refine ⟨49326912910610924308696385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32884608607073949539130923 49326912910610924308696385)
          ·
            refine ⟨36995184682958193231522289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49326912910610924308696385 36995184682958193231522289)
            ·
              refine ⟨27746388512218644923641717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36995184682958193231522289 27746388512218644923641717)
              ·
                refine ⟨2601223923020497961591411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27746388512218644923641717 2601223923020497961591411)
                ·
                  refine ⟨3901835884530746942387117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601223923020497961591411 3901835884530746942387117)
                  ·
                    refine ⟨1463188456699030103395169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3901835884530746942387117 1463188456699030103395169)
                    ·
                      refine ⟨1097391342524272577546377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463188456699030103395169 1097391342524272577546377)
                      ·
                        rfl

theorem cell23_2137162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_2137162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137162 prefixEnd_2137162 := by exact prefixLift 2137162
  have htrace : WordTrace (prefixWord ++ tailWord_2137162) baseStart_2137162 baseEnd_2137162 := by
    simpa [prefixWord, tailWord_2137162, baseEnd_2137162] using wordTrace_append hprefix tailTrace_2137162
  have hstable : (prefixWord ++ tailWord_2137162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137162).length < 2 ^ (prefixWord ++ tailWord_2137162).sum := by decide
  have hdescent : baseEnd_2137162 < baseStart_2137162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137175 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 5, 4, 2]
def baseStart_2137175 : Nat := 118140960795 + 2137175 * 2 ^ 59
def prefixEnd_2137175 : Nat := 4983230072969 + 3 ^ 40 * 2137175 * 2
def baseEnd_2137175 : Nat := 1097398017772781026683817

theorem tailTrace_2137175 : CollatzResearch.WordTrace tailWord_2137175 prefixEnd_2137175 1097398017772781026683817 := by
  unfold tailWord_2137175
  simp only [CollatzResearch.WordTrace]
  refine ⟨77949176032387450275940979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51966117354924966850627319 77949176032387450275940979)
  ·
    refine ⟨116923764048581175413911469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77949176032387450275940979 116923764048581175413911469)
    ·
      refine ⟨43846411518217940780216801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116923764048581175413911469 43846411518217940780216801)
      ·
        refine ⟨32884808638663455585162601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43846411518217940780216801 32884808638663455585162601)
        ·
          refine ⟨24663606478997591688871951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32884808638663455585162601 24663606478997591688871951)
          ·
            refine ⟨36995409718496387533307927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24663606478997591688871951 36995409718496387533307927)
            ·
              refine ⟨55493114577744581299961891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36995409718496387533307927 55493114577744581299961891)
              ·
                refine ⟨83239671866616871949942837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55493114577744581299961891 83239671866616871949942837)
                ·
                  refine ⟨7803719237495331745307141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83239671866616871949942837 7803719237495331745307141)
                  ·
                    refine ⟨1463197357030374702245089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7803719237495331745307141 1463197357030374702245089)
                    ·
                      refine ⟨1097398017772781026683817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463197357030374702245089 1097398017772781026683817)
                      ·
                        rfl

theorem cell23_2137175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_2137175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137175 prefixEnd_2137175 := by exact prefixLift 2137175
  have htrace : WordTrace (prefixWord ++ tailWord_2137175) baseStart_2137175 baseEnd_2137175 := by
    simpa [prefixWord, tailWord_2137175, baseEnd_2137175] using wordTrace_append hprefix tailTrace_2137175
  have hstable : (prefixWord ++ tailWord_2137175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137175).length < 2 ^ (prefixWord ++ tailWord_2137175).sum := by decide
  have hdescent : baseEnd_2137175 < baseStart_2137175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137178 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2137178 : Nat := 118140960795 + 2137178 * 2 ^ 59
def prefixEnd_2137178 : Nat := 4983230072969 + 3 ^ 40 * 2137178 * 2
def baseEnd_2137178 : Nat := 1097399558214744514946303

theorem tailTrace_2137178 : CollatzResearch.WordTrace tailWord_2137178 prefixEnd_2137178 1097399558214744514946303 := by
  unfold tailWord_2137178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487321362844145447075047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51966190300917721192200125 19487321362844145447075047)
  ·
    refine ⟨29230982044266218170612571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19487321362844145447075047 29230982044266218170612571)
    ·
      refine ⟨43846473066399327255918857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29230982044266218170612571 43846473066399327255918857)
      ·
        refine ⟨32884854799799495441939143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43846473066399327255918857 32884854799799495441939143)
        ·
          refine ⟨49327282199699243162908715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32884854799799495441939143 49327282199699243162908715)
          ·
            refine ⟨73990923299548864744363073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49327282199699243162908715 73990923299548864744363073)
            ·
              refine ⟨55493192474661648558272305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73990923299548864744363073 55493192474661648558272305)
              ·
                refine ⟨41619894355996236418704229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55493192474661648558272305 41619894355996236418704229)
                ·
                  refine ⟨7803730191749294328507043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41619894355996236418704229 7803730191749294328507043)
                  ·
                    refine ⟨11705595287623941492760565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7803730191749294328507043 11705595287623941492760565)
                    ·
                      refine ⟨1097399558214744514946303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11705595287623941492760565 1097399558214744514946303)
                      ·
                        rfl

theorem cell23_2137178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2137178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137178 prefixEnd_2137178 := by exact prefixLift 2137178
  have htrace : WordTrace (prefixWord ++ tailWord_2137178) baseStart_2137178 baseEnd_2137178 := by
    simpa [prefixWord, tailWord_2137178, baseEnd_2137178] using wordTrace_append hprefix tailTrace_2137178
  have hstable : (prefixWord ++ tailWord_2137178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137178).length < 2 ^ (prefixWord ++ tailWord_2137178).sum := by decide
  have hdescent : baseEnd_2137178 < baseStart_2137178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137225 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_2137225 : Nat := 118140960795 + 2137225 * 2 ^ 59
def prefixEnd_2137225 : Nat := 4983230072969 + 3 ^ 40 * 2137225 * 2
def baseEnd_2137225 : Nat := 1097423691805505831058587

theorem tailTrace_2137225 : CollatzResearch.WordTrace tailWord_2137225 prefixEnd_2137225 1097423691805505831058587 := by
  unfold tailWord_2137225
  simp only [CollatzResearch.WordTrace]
  refine ⟨77950999682206308815261129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51967333121470872543507419 77950999682206308815261129)
  ·
    refine ⟨58463249761654731611445847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77950999682206308815261129 58463249761654731611445847)
    ·
      refine ⟨87694874642482097417168771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58463249761654731611445847 87694874642482097417168771)
      ·
        refine ⟨131542311963723146125753157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87694874642482097417168771 131542311963723146125753157)
        ·
          refine ⟨24664183493198089898578717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131542311963723146125753157 24664183493198089898578717)
          ·
            refine ⟨9249068809949283711967019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24664183493198089898578717 9249068809949283711967019)
            ·
              refine ⟨13873603214923925567950529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9249068809949283711967019 13873603214923925567950529)
              ·
                refine ⟨10405202411192944175962897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13873603214923925567950529 10405202411192944175962897)
                ·
                  refine ⟨7803901808394708131972173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10405202411192944175962897 7803901808394708131972173)
                  ·
                    refine ⟨2926463178148015549489565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7803901808394708131972173 2926463178148015549489565)
                    ·
                      refine ⟨1097423691805505831058587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2926463178148015549489565 1097423691805505831058587)
                      ·
                        rfl

theorem cell23_2137225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_2137225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137225 prefixEnd_2137225 := by exact prefixLift 2137225
  have htrace : WordTrace (prefixWord ++ tailWord_2137225) baseStart_2137225 baseEnd_2137225 := by
    simpa [prefixWord, tailWord_2137225, baseEnd_2137225] using wordTrace_append hprefix tailTrace_2137225
  have hstable : (prefixWord ++ tailWord_2137225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137225).length < 2 ^ (prefixWord ++ tailWord_2137225).sum := by decide
  have hdescent : baseEnd_2137225 < baseStart_2137225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137235 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 7, 2]
def baseStart_2137235 : Nat := 118140960795 + 2137235 * 2 ^ 59
def prefixEnd_2137235 : Nat := 4983230072969 + 3 ^ 40 * 2137235 * 2
def baseEnd_2137235 : Nat := 1097428826612050791933541

theorem tailTrace_2137235 : CollatzResearch.WordTrace tailWord_2137235 prefixEnd_2137235 1097428826612050791933541 := by
  unfold tailWord_2137235
  simp only [CollatzResearch.WordTrace]
  refine ⟨77951364412170080523125159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51967576274780053682083439 77951364412170080523125159)
  ·
    refine ⟨116927046618255120784687739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77951364412170080523125159 116927046618255120784687739)
    ·
      refine ⟨175390569927382681177031609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116927046618255120784687739 175390569927382681177031609)
      ·
        refine ⟨131542927445537010882773707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175390569927382681177031609 131542927445537010882773707)
        ·
          refine ⟨197314391168305516324160561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131542927445537010882773707 197314391168305516324160561)
          ·
            refine ⟨147985793376229137243120421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197314391168305516324160561 147985793376229137243120421)
            ·
              refine ⟨27747336258042963233085079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147985793376229137243120421 27747336258042963233085079)
              ·
                refine ⟨41621004387064444849627619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27747336258042963233085079 41621004387064444849627619)
                ·
                  refine ⟨62431506580596667274441429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41621004387064444849627619 62431506580596667274441429)
                  ·
                    refine ⟨1463238435482734389244721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 62431506580596667274441429 1463238435482734389244721)
                    ·
                      refine ⟨1097428826612050791933541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463238435482734389244721 1097428826612050791933541)
                      ·
                        rfl

theorem cell23_2137235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7, 2].length) (baseStart_2137235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137235 prefixEnd_2137235 := by exact prefixLift 2137235
  have htrace : WordTrace (prefixWord ++ tailWord_2137235) baseStart_2137235 baseEnd_2137235 := by
    simpa [prefixWord, tailWord_2137235, baseEnd_2137235] using wordTrace_append hprefix tailTrace_2137235
  have hstable : (prefixWord ++ tailWord_2137235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137235).length < 2 ^ (prefixWord ++ tailWord_2137235).sum := by decide
  have hdescent : baseEnd_2137235 < baseStart_2137235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137242 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2137242 : Nat := 118140960795 + 2137242 * 2 ^ 59
def prefixEnd_2137242 : Nat := 4983230072969 + 3 ^ 40 * 2137242 * 2
def baseEnd_2137242 : Nat := 1097432420976632264546009

theorem tailTrace_2137242 : CollatzResearch.WordTrace tailWord_2137242 prefixEnd_2137242 1097432420976632264546009 := by
  unfold tailWord_2137242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487904930786180179657495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51967746482096480479086653 19487904930786180179657495)
  ·
    refine ⟨29231857396179270269486243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19487904930786180179657495 29231857396179270269486243)
    ·
      refine ⟨43847786094268905404229365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29231857396179270269486243 43847786094268905404229365)
      ·
        refine ⟨4110729946337709881646503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43847786094268905404229365 4110729946337709881646503)
        ·
          refine ⟨6166094919506564822469755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110729946337709881646503 6166094919506564822469755)
          ·
            refine ⟨9249142379259847233704633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6166094919506564822469755 9249142379259847233704633)
            ·
              refine ⟨6936856784444885425278475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9249142379259847233704633 6936856784444885425278475)
              ·
                refine ⟨10405285176667328137917713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6936856784444885425278475 10405285176667328137917713)
                ·
                  refine ⟨7803963882500496103438285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10405285176667328137917713 7803963882500496103438285)
                  ·
                    refine ⟨2926486455937686038789357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7803963882500496103438285 2926486455937686038789357)
                    ·
                      refine ⟨1097432420976632264546009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2926486455937686038789357 1097432420976632264546009)
                      ·
                        rfl

theorem cell23_2137242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2137242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137242 prefixEnd_2137242 := by exact prefixLift 2137242
  have htrace : WordTrace (prefixWord ++ tailWord_2137242) baseStart_2137242 baseEnd_2137242 := by
    simpa [prefixWord, tailWord_2137242, baseEnd_2137242] using wordTrace_append hprefix tailTrace_2137242
  have hstable : (prefixWord ++ tailWord_2137242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137242).length < 2 ^ (prefixWord ++ tailWord_2137242).sum := by decide
  have hdescent : baseEnd_2137242 < baseStart_2137242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137372 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2137372 : Nat := 118140960795 + 2137372 * 2 ^ 59
def prefixEnd_2137372 : Nat := 4983230072969 + 3 ^ 40 * 2137372 * 2
def baseEnd_2137372 : Nat := 1097499173461716755920411

theorem tailTrace_2137372 : CollatzResearch.WordTrace tailWord_2137372 prefixEnd_2137372 1097499173461716755920411 := by
  unfold tailWord_2137372
  simp only [CollatzResearch.WordTrace]
  refine ⟨38978180606336876460431185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51970907475115835280574913 38978180606336876460431185)
  ·
    refine ⟨29233635454752657345323389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38978180606336876460431185 29233635454752657345323389)
    ·
      refine ⟨10962613295532246504496271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29233635454752657345323389 10962613295532246504496271)
      ·
        refine ⟨16443919943298369756744407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10962613295532246504496271 16443919943298369756744407)
        ·
          refine ⟨24665879914947554635116611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16443919943298369756744407 24665879914947554635116611)
          ·
            refine ⟨36998819872421331952674917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24665879914947554635116611 36998819872421331952674917)
            ·
              refine ⟨6937278726078999741126547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36998819872421331952674917 6937278726078999741126547)
              ·
                refine ⟨10405918089118499611689821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6937278726078999741126547 10405918089118499611689821)
                ·
                  refine ⟨3902219283419437354383683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10405918089118499611689821 3902219283419437354383683)
                  ·
                    refine ⟨5853328925129156031575525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3902219283419437354383683 5853328925129156031575525)
                    ·
                      refine ⟨1097499173461716755920411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5853328925129156031575525 1097499173461716755920411)
                      ·
                        rfl

theorem cell23_2137372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2137372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137372 prefixEnd_2137372 := by exact prefixLift 2137372
  have htrace : WordTrace (prefixWord ++ tailWord_2137372) baseStart_2137372 baseEnd_2137372 := by
    simpa [prefixWord, tailWord_2137372, baseEnd_2137372] using wordTrace_append hprefix tailTrace_2137372
  have hstable : (prefixWord ++ tailWord_2137372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137372).length < 2 ^ (prefixWord ++ tailWord_2137372).sum := by decide
  have hdescent : baseEnd_2137372 < baseStart_2137372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137385 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_2137385 : Nat := 118140960795 + 2137385 * 2 ^ 59
def prefixEnd_2137385 : Nat := 4983230072969 + 3 ^ 40 * 2137385 * 2
def baseEnd_2137385 : Nat := 1097505848710225205057851

theorem tailTrace_2137385 : CollatzResearch.WordTrace tailWord_2137385 prefixEnd_2137385 1097505848710225205057851 := by
  unfold tailWord_2137385
  simp only [CollatzResearch.WordTrace]
  refine ⟨77956835361626656141085609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51971223574417770760723739 77956835361626656141085609)
  ·
    refine ⟨58467626521219992105814207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77956835361626656141085609 58467626521219992105814207)
    ·
      refine ⟨87701439781829988158721311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58467626521219992105814207 87701439781829988158721311)
      ·
        refine ⟨131552159672744982238081967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87701439781829988158721311 131552159672744982238081967)
        ·
          refine ⟨197328239509117473357122951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131552159672744982238081967 197328239509117473357122951)
          ·
            refine ⟨295992359263676210035684427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197328239509117473357122951 295992359263676210035684427)
            ·
              refine ⟨443988538895514315053526641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295992359263676210035684427 443988538895514315053526641)
              ·
                refine ⟨332991404171635736290144981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443988538895514315053526641 332991404171635736290144981)
                ·
                  refine ⟨7804486035272712569300273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 332991404171635736290144981 7804486035272712569300273)
                  ·
                    refine ⟨5853364526454534426975205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7804486035272712569300273 5853364526454534426975205)
                    ·
                      refine ⟨1097505848710225205057851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5853364526454534426975205 1097505848710225205057851)
                      ·
                        rfl

theorem cell23_2137385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_2137385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137385 prefixEnd_2137385 := by exact prefixLift 2137385
  have htrace : WordTrace (prefixWord ++ tailWord_2137385) baseStart_2137385 baseEnd_2137385 := by
    simpa [prefixWord, tailWord_2137385, baseEnd_2137385] using wordTrace_append hprefix tailTrace_2137385
  have hstable : (prefixWord ++ tailWord_2137385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137385).length < 2 ^ (prefixWord ++ tailWord_2137385).sum := by decide
  have hdescent : baseEnd_2137385 < baseStart_2137385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137386 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2137386 : Nat := 118140960795 + 2137386 * 2 ^ 59
def prefixEnd_2137386 : Nat := 4983230072969 + 3 ^ 40 * 2137386 * 2
def baseEnd_2137386 : Nat := 365835454063626567048449

theorem tailTrace_2137386 : CollatzResearch.WordTrace tailWord_2137386 prefixEnd_2137386 365835454063626567048449 := by
  unfold tailWord_2137386
  simp only [CollatzResearch.WordTrace]
  refine ⟨19489217958655758327968003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51971247889748688874581341 19489217958655758327968003)
  ·
    refine ⟨29233826937983637491952005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19489217958655758327968003 29233826937983637491952005)
    ·
      refine ⟨5481342550871932029741001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29233826937983637491952005 5481342550871932029741001)
      ·
        refine ⟨4111006913153949022305751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5481342550871932029741001 4111006913153949022305751)
        ·
          refine ⟨6166510369730923533458627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4111006913153949022305751 6166510369730923533458627)
          ·
            refine ⟨9249765554596385300187941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6166510369730923533458627 9249765554596385300187941)
            ·
              refine ⟨1734331041486822243785239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9249765554596385300187941 1734331041486822243785239)
              ·
                refine ⟨2601496562230233365677859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734331041486822243785239 2601496562230233365677859)
                ·
                  refine ⟨3902244843345350048516789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601496562230233365677859 3902244843345350048516789)
                  ·
                    refine ⟨365835454063626567048449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3902244843345350048516789 365835454063626567048449)
                    ·
                      rfl

theorem cell23_2137386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2137386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137386 prefixEnd_2137386 := by exact prefixLift 2137386
  have htrace : WordTrace (prefixWord ++ tailWord_2137386) baseStart_2137386 baseEnd_2137386 := by
    simpa [prefixWord, tailWord_2137386, baseEnd_2137386] using wordTrace_append hprefix tailTrace_2137386
  have hstable : (prefixWord ++ tailWord_2137386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137386).length < 2 ^ (prefixWord ++ tailWord_2137386).sum := by decide
  have hdescent : baseEnd_2137386 < baseStart_2137386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137395 : List Nat := [1, 1, 1, 2, 5, 3, 10]
def baseStart_2137395 : Nat := 118140960795 + 2137395 * 2 ^ 59
def prefixEnd_2137395 : Nat := 4983230072969 + 3 ^ 40 * 2137395 * 2
def baseEnd_2137395 : Nat := 13549518315021853900405

theorem tailTrace_2137395 : CollatzResearch.WordTrace tailWord_2137395 prefixEnd_2137395 13549518315021853900405 := by
  unfold tailWord_2137395
  simp only [CollatzResearch.WordTrace]
  refine ⟨77957200091590427848949639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51971466727726951899299759 77957200091590427848949639)
  ·
    refine ⟨116935800137385641773424459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77957200091590427848949639 116935800137385641773424459)
    ·
      refine ⟨175403700206078462660136689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116935800137385641773424459 175403700206078462660136689)
      ·
        refine ⟨131552775154558846995102517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175403700206078462660136689 131552775154558846995102517)
        ·
          refine ⟨12333072670739891905790861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131552775154558846995102517 12333072670739891905790861)
          ·
            refine ⟨4624902251527459464671573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12333072670739891905790861 4624902251527459464671573)
            ·
              refine ⟨13549518315021853900405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4624902251527459464671573 13549518315021853900405)
              ·
                rfl

theorem cell23_2137395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 10].length) (baseStart_2137395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137395 prefixEnd_2137395 := by exact prefixLift 2137395
  have htrace : WordTrace (prefixWord ++ tailWord_2137395) baseStart_2137395 baseEnd_2137395 := by
    simpa [prefixWord, tailWord_2137395, baseEnd_2137395] using wordTrace_append hprefix tailTrace_2137395
  have hstable : (prefixWord ++ tailWord_2137395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137395).length < 2 ^ (prefixWord ++ tailWord_2137395).sum := by decide
  have hdescent : baseEnd_2137395 < baseStart_2137395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137409 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2137409 : Nat := 118140960795 + 2137409 * 2 ^ 59
def prefixEnd_2137409 : Nat := 4983230072969 + 3 ^ 40 * 2137409 * 2
def baseEnd_2137409 : Nat := 1097518172245933111157741

theorem tailTrace_2137409 : CollatzResearch.WordTrace tailWord_2137409 prefixEnd_2137409 1097518172245933111157741 := by
  unfold tailWord_2137409
  simp only [CollatzResearch.WordTrace]
  refine ⟨77957710713539708239959281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51971807142359805493306187 77957710713539708239959281)
  ·
    refine ⟨58468283035154781179969461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77957710713539708239959281 58468283035154781179969461)
    ·
      refine ⟨5481401534545760735622137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58468283035154781179969461 5481401534545760735622137)
      ·
        refine ⟨4111051150909320551716603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5481401534545760735622137 4111051150909320551716603)
        ·
          refine ⟨6166576726363980827574905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4111051150909320551716603 6166576726363980827574905)
          ·
            refine ⟨4624932544772985620681179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6166576726363980827574905 4624932544772985620681179)
            ·
              refine ⟨6937398817159478431021769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4624932544772985620681179 6937398817159478431021769)
              ·
                refine ⟨5203049112869608823266327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6937398817159478431021769 5203049112869608823266327)
                ·
                  refine ⟨7804573669304413234899491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5203049112869608823266327 7804573669304413234899491)
                  ·
                    refine ⟨11706860503956619852349237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7804573669304413234899491 11706860503956619852349237)
                    ·
                      refine ⟨1097518172245933111157741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11706860503956619852349237 1097518172245933111157741)
                      ·
                        rfl

theorem cell23_2137409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2137409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137409 prefixEnd_2137409 := by exact prefixLift 2137409
  have htrace : WordTrace (prefixWord ++ tailWord_2137409) baseStart_2137409 baseEnd_2137409 := by
    simpa [prefixWord, tailWord_2137409, baseEnd_2137409] using wordTrace_append hprefix tailTrace_2137409
  have hstable : (prefixWord ++ tailWord_2137409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137409).length < 2 ^ (prefixWord ++ tailWord_2137409).sum := by decide
  have hdescent : baseEnd_2137409 < baseStart_2137409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137429 : List Nat := [1, 3, 2, 2, 3, 3, 2, 7]
def baseStart_2137429 : Nat := 118140960795 + 2137429 * 2 ^ 59
def prefixEnd_2137429 : Nat := 4983230072969 + 3 ^ 40 * 2137429 * 2
def baseEnd_2137429 : Nat := 40649201550334186403987

theorem tailTrace_2137429 : CollatzResearch.WordTrace tailWord_2137429 prefixEnd_2137429 40649201550334186403987 := by
  unfold tailWord_2137429
  simp only [CollatzResearch.WordTrace]
  refine ⟨77958440173467251655687341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51972293448978167770458227 77958440173467251655687341)
  ·
    refine ⟨29234415065050219370882753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77958440173467251655687341 29234415065050219370882753)
    ·
      refine ⟨21925811298787664528162065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29234415065050219370882753 21925811298787664528162065)
      ·
        refine ⟨16444358474090748396121549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21925811298787664528162065 16444358474090748396121549)
        ·
          refine ⟨6166634427784030648545581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16444358474090748396121549 6166634427784030648545581)
          ·
            refine ⟨2312487910419011493204593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6166634427784030648545581 2312487910419011493204593)
            ·
              refine ⟨1734365932814258619903445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312487910419011493204593 1734365932814258619903445)
              ·
                refine ⟨40649201550334186403987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1734365932814258619903445 40649201550334186403987)
                ·
                  rfl

theorem cell23_2137429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 7].length) (baseStart_2137429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137429 prefixEnd_2137429 := by exact prefixLift 2137429
  have htrace : WordTrace (prefixWord ++ tailWord_2137429) baseStart_2137429 baseEnd_2137429 := by
    simpa [prefixWord, tailWord_2137429, baseEnd_2137429] using wordTrace_append hprefix tailTrace_2137429
  have hstable : (prefixWord ++ tailWord_2137429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137429).length < 2 ^ (prefixWord ++ tailWord_2137429).sum := by decide
  have hdescent : baseEnd_2137429 < baseStart_2137429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137440 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 1, 2, 2]
def baseStart_2137440 : Nat := 118140960795 + 2137440 * 2 ^ 59
def prefixEnd_2137440 : Nat := 4983230072969 + 3 ^ 40 * 2137440 * 2
def baseEnd_2137440 : Nat := 1097534090146222489870099

theorem tailTrace_2137440 : CollatzResearch.WordTrace tailWord_2137440 prefixEnd_2137440 1097534090146222489870099 := by
  unfold tailWord_2137440
  simp only [CollatzResearch.WordTrace]
  refine ⟨38979420688213700267168887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51972560917618267022891849 38979420688213700267168887)
  ·
    refine ⟨58469131032320550400753331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38979420688213700267168887 58469131032320550400753331)
    ·
      refine ⟨87703696548480825601129997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58469131032320550400753331 87703696548480825601129997)
      ·
        refine ⟨32888886205680309600423749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87703696548480825601129997 32888886205680309600423749)
        ·
          refine ⟨6166666163565058050079453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32888886205680309600423749 6166666163565058050079453)
          ·
            refine ⟨2312499811336896768779795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6166666163565058050079453 2312499811336896768779795)
            ·
              refine ⟨3468749717005345153169693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312499811336896768779795 3468749717005345153169693)
              ·
                refine ⟨1300781143877004432438635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3468749717005345153169693 1300781143877004432438635)
                ·
                  refine ⟨1951171715815506648657953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300781143877004432438635 1951171715815506648657953)
                  ·
                    refine ⟨1463378786861629986493465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1951171715815506648657953 1463378786861629986493465)
                    ·
                      refine ⟨1097534090146222489870099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463378786861629986493465 1097534090146222489870099)
                      ·
                        rfl

theorem cell23_2137440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_2137440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137440 prefixEnd_2137440 := by exact prefixLift 2137440
  have htrace : WordTrace (prefixWord ++ tailWord_2137440) baseStart_2137440 baseEnd_2137440 := by
    simpa [prefixWord, tailWord_2137440, baseEnd_2137440] using wordTrace_append hprefix tailTrace_2137440
  have hstable : (prefixWord ++ tailWord_2137440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137440).length < 2 ^ (prefixWord ++ tailWord_2137440).sum := by decide
  have hdescent : baseEnd_2137440 < baseStart_2137440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137473 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2137473 : Nat := 118140960795 + 2137473 * 2 ^ 59
def prefixEnd_2137473 : Nat := 4983230072969 + 3 ^ 40 * 2137473 * 2
def baseEnd_2137473 : Nat := 1097551035007820860757447

theorem tailTrace_2137473 : CollatzResearch.WordTrace tailWord_2137473 prefixEnd_2137473 1097551035007820860757447 := by
  unfold tailWord_2137473
  simp only [CollatzResearch.WordTrace]
  refine ⟨77960044985307847170289073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51973363323538564780192715 77960044985307847170289073)
  ·
    refine ⟨58470033738980885377716805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77960044985307847170289073 58470033738980885377716805)
    ·
      refine ⟨10963131326058916008321901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58470033738980885377716805 10963131326058916008321901)
      ·
        refine ⟨4111174247272093503120713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10963131326058916008321901 4111174247272093503120713)
        ·
          refine ⟨3083380685454070127340535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4111174247272093503120713 3083380685454070127340535)
          ·
            refine ⟨4625071028181105191010803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3083380685454070127340535 4625071028181105191010803)
            ·
              refine ⟨6937606542271657786516205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625071028181105191010803 6937606542271657786516205)
              ·
                refine ⟨2601602453351871669943577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6937606542271657786516205 2601602453351871669943577)
                ·
                  refine ⟨1951201840013903752457683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2601602453351871669943577 1951201840013903752457683)
                  ·
                    refine ⟨2926802760020855628686525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1951201840013903752457683 2926802760020855628686525)
                    ·
                      refine ⟨1097551035007820860757447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2926802760020855628686525 1097551035007820860757447)
                      ·
                        rfl

theorem cell23_2137473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2137473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137473 prefixEnd_2137473 := by exact prefixLift 2137473
  have htrace : WordTrace (prefixWord ++ tailWord_2137473) baseStart_2137473 baseEnd_2137473 := by
    simpa [prefixWord, tailWord_2137473, baseEnd_2137473] using wordTrace_append hprefix tailTrace_2137473
  have hstable : (prefixWord ++ tailWord_2137473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137473).length < 2 ^ (prefixWord ++ tailWord_2137473).sum := by decide
  have hdescent : baseEnd_2137473 < baseStart_2137473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137552 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_2137552 : Nat := 118140960795 + 2137552 * 2 ^ 59
def prefixEnd_2137552 : Nat := 4983230072969 + 3 ^ 40 * 2137552 * 2
def baseEnd_2137552 : Nat := 1097591599979526051669583

theorem tailTrace_2137552 : CollatzResearch.WordTrace tailWord_2137552 prefixEnd_2137552 1097591599979526051669583 := by
  unfold tailWord_2137552
  simp only [CollatzResearch.WordTrace]
  refine ⟨38981463176010821831207455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51975284234681095774943273 38981463176010821831207455)
  ·
    refine ⟨58472194764016232746811183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38981463176010821831207455 58472194764016232746811183)
    ·
      refine ⟨87708292146024349120216775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58472194764016232746811183 87708292146024349120216775)
      ·
        refine ⟨131562438219036523680325163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87708292146024349120216775 131562438219036523680325163)
        ·
          refine ⟨197343657328554785520487745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131562438219036523680325163 197343657328554785520487745)
          ·
            refine ⟨148007742996416089140365809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197343657328554785520487745 148007742996416089140365809)
            ·
              refine ⟨111005807247312066855274357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148007742996416089140365809 111005807247312066855274357)
              ·
                refine ⟨10406794429435506267681971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111005807247312066855274357 10406794429435506267681971)
                ·
                  refine ⟨15610191644153259401522957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10406794429435506267681971 15610191644153259401522957)
                  ·
                    refine ⟨5853821866557472275571109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15610191644153259401522957 5853821866557472275571109)
                    ·
                      refine ⟨1097591599979526051669583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5853821866557472275571109 1097591599979526051669583)
                      ·
                        rfl

theorem cell23_2137552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_2137552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137552 prefixEnd_2137552 := by exact prefixLift 2137552
  have htrace : WordTrace (prefixWord ++ tailWord_2137552) baseStart_2137552 baseEnd_2137552 := by
    simpa [prefixWord, tailWord_2137552, baseEnd_2137552] using wordTrace_append hprefix tailTrace_2137552
  have hstable : (prefixWord ++ tailWord_2137552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137552).length < 2 ^ (prefixWord ++ tailWord_2137552).sum := by decide
  have hdescent : baseEnd_2137552 < baseStart_2137552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137572 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_2137572 : Nat := 118140960795 + 2137572 * 2 ^ 59
def prefixEnd_2137572 : Nat := 4983230072969 + 3 ^ 40 * 2137572 * 2
def baseEnd_2137572 : Nat := 1097601869592615973419491

theorem tailTrace_2137572 : CollatzResearch.WordTrace tailWord_2137572 prefixEnd_2137572 1097601869592615973419491 := by
  unfold tailWord_2137572
  simp only [CollatzResearch.WordTrace]
  refine ⟨38981827905974593539071485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51975770541299458052095313 38981827905974593539071485)
  ·
    refine ⟨14618185464740472577151807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38981827905974593539071485 14618185464740472577151807)
    ·
      refine ⟨21927278197110708865727711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14618185464740472577151807 21927278197110708865727711)
      ·
        refine ⟨32890917295666063298591567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21927278197110708865727711 32890917295666063298591567)
        ·
          refine ⟨49336375943499094947887351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32890917295666063298591567 49336375943499094947887351)
          ·
            refine ⟨74004563915248642421831027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49336375943499094947887351 74004563915248642421831027)
            ·
              refine ⟨111006845872872963632746541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74004563915248642421831027 111006845872872963632746541)
              ·
                refine ⟨41627567202327361362279953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111006845872872963632746541 41627567202327361362279953)
                ·
                  refine ⟨31220675401745521021709965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41627567202327361362279953 31220675401745521021709965)
                  ·
                    refine ⟨11707753275654570383141237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31220675401745521021709965 11707753275654570383141237)
                    ·
                      refine ⟨1097601869592615973419491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11707753275654570383141237 1097601869592615973419491)
                      ·
                        rfl

theorem cell23_2137572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_2137572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137572 prefixEnd_2137572 := by exact prefixLift 2137572
  have htrace : WordTrace (prefixWord ++ tailWord_2137572) baseStart_2137572 baseEnd_2137572 := by
    simpa [prefixWord, tailWord_2137572, baseEnd_2137572] using wordTrace_append hprefix tailTrace_2137572
  have hstable : (prefixWord ++ tailWord_2137572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137572).length < 2 ^ (prefixWord ++ tailWord_2137572).sum := by decide
  have hdescent : baseEnd_2137572 < baseStart_2137572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137656 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 1, 5]
def baseStart_2137656 : Nat := 118140960795 + 2137656 * 2 ^ 59
def prefixEnd_2137656 : Nat := 4983230072969 + 3 ^ 40 * 2137656 * 2
def baseEnd_2137656 : Nat := 365881667322531214923035

theorem tailTrace_2137656 : CollatzResearch.WordTrace tailWord_2137656 prefixEnd_2137656 365881667322531214923035 := by
  unfold tailWord_2137656
  simp only [CollatzResearch.WordTrace]
  refine ⟨38983359771822434712100411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51977813029096579616133881 38983359771822434712100411)
  ·
    refine ⟨58475039657733652068150617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38983359771822434712100411 58475039657733652068150617)
    ·
      refine ⟨43856279743300239051112963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58475039657733652068150617 43856279743300239051112963)
      ·
        refine ⟨65784419614950358576669445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43856279743300239051112963 65784419614950358576669445)
        ·
          refine ⟨12334578677803192233125521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65784419614950358576669445 12334578677803192233125521)
          ·
            refine ⟨9250934008352394174844141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12334578677803192233125521 9250934008352394174844141)
            ·
              refine ⟨3469100253132147815566553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9250934008352394174844141 3469100253132147815566553)
              ·
                refine ⟨2601825189849110861674915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3469100253132147815566553 2601825189849110861674915)
                ·
                  refine ⟨3902737784773666292512373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601825189849110861674915 3902737784773666292512373)
                  ·
                    refine ⟨365881667322531214923035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3902737784773666292512373 365881667322531214923035)
                    ·
                      rfl

theorem cell23_2137656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_2137656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137656 prefixEnd_2137656 := by exact prefixLift 2137656
  have htrace : WordTrace (prefixWord ++ tailWord_2137656) baseStart_2137656 baseEnd_2137656 := by
    simpa [prefixWord, tailWord_2137656, baseEnd_2137656] using wordTrace_append hprefix tailTrace_2137656
  have hstable : (prefixWord ++ tailWord_2137656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137656).length < 2 ^ (prefixWord ++ tailWord_2137656).sum := by decide
  have hdescent : baseEnd_2137656 < baseStart_2137656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137663 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 2, 3, 2]
def baseStart_2137663 : Nat := 118140960795 + 2137663 * 2 ^ 59
def prefixEnd_2137663 : Nat := 4983230072969 + 3 ^ 40 * 2137663 * 2
def baseEnd_2137663 : Nat := 1097648596332175117381573

theorem tailTrace_2137663 : CollatzResearch.WordTrace tailWord_2137663 prefixEnd_2137663 1097648596332175117381573 := by
  unfold tailWord_2137663
  simp only [CollatzResearch.WordTrace]
  refine ⟨77966974854619509619705643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51977983236413006413137095 77966974854619509619705643)
  ·
    refine ⟨116950462281929264429558465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77966974854619509619705643 116950462281929264429558465)
    ·
      refine ⟨87712846711446948322168849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116950462281929264429558465 87712846711446948322168849)
      ·
        refine ⟨65784635033585211241626637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87712846711446948322168849 65784635033585211241626637)
        ·
          refine ⟨24669238137594454215609989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65784635033585211241626637 24669238137594454215609989)
          ·
            refine ⟨4625482150798960165426873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24669238137594454215609989 4625482150798960165426873)
            ·
              refine ⟨3469111613099220124070155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4625482150798960165426873 3469111613099220124070155)
              ·
                refine ⟨5203667419648830186105233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469111613099220124070155 5203667419648830186105233)
                ·
                  refine ⟨3902750564736622639578925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5203667419648830186105233 3902750564736622639578925)
                  ·
                    refine ⟨1463531461776233489842097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3902750564736622639578925 1463531461776233489842097)
                    ·
                      refine ⟨1097648596332175117381573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463531461776233489842097 1097648596332175117381573)
                      ·
                        rfl

theorem cell23_2137663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_2137663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137663 prefixEnd_2137663 := by exact prefixLift 2137663
  have htrace : WordTrace (prefixWord ++ tailWord_2137663) baseStart_2137663 baseEnd_2137663 := by
    simpa [prefixWord, tailWord_2137663, baseEnd_2137663] using wordTrace_append hprefix tailTrace_2137663
  have hstable : (prefixWord ++ tailWord_2137663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137663).length < 2 ^ (prefixWord ++ tailWord_2137663).sum := by decide
  have hdescent : baseEnd_2137663 < baseStart_2137663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137669 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_2137669 : Nat := 118140960795 + 2137669 * 2 ^ 59
def prefixEnd_2137669 : Nat := 4983230072969 + 3 ^ 40 * 2137669 * 2
def baseEnd_2137669 : Nat := 365883892405367364635515

theorem tailTrace_2137669 : CollatzResearch.WordTrace tailWord_2137669 prefixEnd_2137669 365883892405367364635515 := by
  unfold tailWord_2137669
  simp only [CollatzResearch.WordTrace]
  refine ⟨77967193692597772644424061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51978129128398515096282707 77967193692597772644424061)
  ·
    refine ⟨29237697634724164741659023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77967193692597772644424061 29237697634724164741659023)
    ·
      refine ⟨43856546452086247112488535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29237697634724164741659023 43856546452086247112488535)
      ·
        refine ⟨65784819678129370668732803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43856546452086247112488535 65784819678129370668732803)
        ·
          refine ⟨98677229517194056003099205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65784819678129370668732803 98677229517194056003099205)
          ·
            refine ⟨18501980534473885500581101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98677229517194056003099205 18501980534473885500581101)
            ·
              refine ⟨6938242700427707062717913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18501980534473885500581101 6938242700427707062717913)
              ·
                refine ⟨5203682025320780297038435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6938242700427707062717913 5203682025320780297038435)
                ·
                  refine ⟨7805523037981170445557653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5203682025320780297038435 7805523037981170445557653)
                  ·
                    refine ⟨365883892405367364635515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7805523037981170445557653 365883892405367364635515)
                    ·
                      rfl

theorem cell23_2137669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_2137669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137669 prefixEnd_2137669 := by exact prefixLift 2137669
  have htrace : WordTrace (prefixWord ++ tailWord_2137669) baseStart_2137669 baseEnd_2137669 := by
    simpa [prefixWord, tailWord_2137669, baseEnd_2137669] using wordTrace_append hprefix tailTrace_2137669
  have hstable : (prefixWord ++ tailWord_2137669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137669).length < 2 ^ (prefixWord ++ tailWord_2137669).sum := by decide
  have hdescent : baseEnd_2137669 < baseStart_2137669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137687 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 1, 1, 3]
def baseStart_2137687 : Nat := 118140960795 + 2137687 * 2 ^ 59
def prefixEnd_2137687 : Nat := 4983230072969 + 3 ^ 40 * 2137687 * 2
def baseEnd_2137687 : Nat := 1097660919867883023481463

theorem tailTrace_2137687 : CollatzResearch.WordTrace tailWord_2137687 prefixEnd_2137687 1097660919867883023481463 := by
  unfold tailWord_2137687
  simp only [CollatzResearch.WordTrace]
  refine ⟨77967850206532561718579315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51978566804355041145719543 77967850206532561718579315)
  ·
    refine ⟨116951775309798842577868973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77967850206532561718579315 116951775309798842577868973)
    ·
      refine ⟨43856915741174565966700865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116951775309798842577868973 43856915741174565966700865)
      ·
        refine ⟨32892686805880924475025649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43856915741174565966700865 32892686805880924475025649)
        ·
          refine ⟨24669515104410693356269237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32892686805880924475025649 24669515104410693356269237)
          ·
            refine ⟨2312767041038502502150241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24669515104410693356269237 2312767041038502502150241)
            ·
              refine ⟨1734575280778876876612681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312767041038502502150241 1734575280778876876612681)
              ·
                refine ⟨1300931460584157657459511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1734575280778876876612681 1300931460584157657459511)
                ·
                  refine ⟨1951397190876236486189267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300931460584157657459511 1951397190876236486189267)
                  ·
                    refine ⟨2927095786314354729283901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1951397190876236486189267 2927095786314354729283901)
                    ·
                      refine ⟨1097660919867883023481463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2927095786314354729283901 1097660919867883023481463)
                      ·
                        rfl

theorem cell23_2137687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_2137687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137687 prefixEnd_2137687 := by exact prefixLift 2137687
  have htrace : WordTrace (prefixWord ++ tailWord_2137687) baseStart_2137687 baseEnd_2137687 := by
    simpa [prefixWord, tailWord_2137687, baseEnd_2137687] using wordTrace_append hprefix tailTrace_2137687
  have hstable : (prefixWord ++ tailWord_2137687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137687).length < 2 ^ (prefixWord ++ tailWord_2137687).sum := by decide
  have hdescent : baseEnd_2137687 < baseStart_2137687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137699 : List Nat := [1, 1, 1, 5, 1, 3, 3, 8]
def baseStart_2137699 : Nat := 118140960795 + 2137699 * 2 ^ 59
def prefixEnd_2137699 : Nat := 4983230072969 + 3 ^ 40 * 2137699 * 2
def baseEnd_2137699 : Nat := 40654336356879147278941

theorem tailTrace_2137699 : CollatzResearch.WordTrace tailWord_2137699 prefixEnd_2137699 40654336356879147278941 := by
  unfold tailWord_2137699
  simp only [CollatzResearch.WordTrace]
  refine ⟨77968287882489087768016151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51978858588326058512010767 77968287882489087768016151)
  ·
    refine ⟨116952431823733631652024227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77968287882489087768016151 116952431823733631652024227)
    ·
      refine ⟨175428647735600447478036341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116952431823733631652024227 175428647735600447478036341)
      ·
        refine ⟨16446435725212541951065907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175428647735600447478036341 16446435725212541951065907)
        ·
          refine ⟨24669653587818812926598861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16446435725212541951065907 24669653587818812926598861)
          ·
            refine ⟨9251120095432054847474573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24669653587818812926598861 9251120095432054847474573)
            ·
              refine ⟨3469170035787020567802965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9251120095432054847474573 3469170035787020567802965)
              ·
                refine ⟨40654336356879147278941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3469170035787020567802965 40654336356879147278941)
                ·
                  rfl

theorem cell23_2137699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 8].length) (baseStart_2137699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137699 prefixEnd_2137699 := by exact prefixLift 2137699
  have htrace : WordTrace (prefixWord ++ tailWord_2137699) baseStart_2137699 baseEnd_2137699 := by
    simpa [prefixWord, tailWord_2137699, baseEnd_2137699] using wordTrace_append hprefix tailTrace_2137699
  have hstable : (prefixWord ++ tailWord_2137699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137699).length < 2 ^ (prefixWord ++ tailWord_2137699).sum := by decide
  have hdescent : baseEnd_2137699 < baseStart_2137699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137706 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2137706 : Nat := 118140960795 + 2137706 * 2 ^ 59
def prefixEnd_2137706 : Nat := 4983230072969 + 3 ^ 40 * 2137706 * 2
def baseEnd_2137706 : Nat := 1097670676000318449143875

theorem tailTrace_2137706 : CollatzResearch.WordTrace tailWord_2137706 prefixEnd_2137706 1097670676000318449143875 := by
  unfold tailWord_2137706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19492135798365931990880243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51979028795642485309013981 19492135798365931990880243)
  ·
    refine ⟨29238203697548897986320365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19492135798365931990880243 29238203697548897986320365)
    ·
      refine ⟨10964326386580836744870137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29238203697548897986320365 10964326386580836744870137)
      ·
        refine ⟨8223244789935627558652603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10964326386580836744870137 8223244789935627558652603)
        ·
          refine ⟨12334867184903441337978905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223244789935627558652603 12334867184903441337978905)
          ·
            refine ⟨9251150388677581003484179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12334867184903441337978905 9251150388677581003484179)
            ·
              refine ⟨13876725583016371505226269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9251150388677581003484179 13876725583016371505226269)
              ·
                refine ⟨5203772093631139314459851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13876725583016371505226269 5203772093631139314459851)
                ·
                  refine ⟨7805658140446708971689777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5203772093631139314459851 7805658140446708971689777)
                  ·
                    refine ⟨5854243605335031728767333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7805658140446708971689777 5854243605335031728767333)
                    ·
                      refine ⟨1097670676000318449143875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5854243605335031728767333 1097670676000318449143875)
                      ·
                        rfl

theorem cell23_2137706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2137706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137706 prefixEnd_2137706 := by exact prefixLift 2137706
  have htrace : WordTrace (prefixWord ++ tailWord_2137706) baseStart_2137706 baseEnd_2137706 := by
    simpa [prefixWord, tailWord_2137706, baseEnd_2137706] using wordTrace_append hprefix tailTrace_2137706
  have hstable : (prefixWord ++ tailWord_2137706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137706).length < 2 ^ (prefixWord ++ tailWord_2137706).sum := by decide
  have hdescent : baseEnd_2137706 < baseStart_2137706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137749 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2137749 : Nat := 118140960795 + 2137749 * 2 ^ 59
def prefixEnd_2137749 : Nat := 4983230072969 + 3 ^ 40 * 2137749 * 2
def baseEnd_2137749 : Nat := 1097692755668461780906177

theorem tailTrace_2137749 : CollatzResearch.WordTrace tailWord_2137749 prefixEnd_2137749 1097692755668461780906177 := by
  unfold tailWord_2137749
  simp only [CollatzResearch.WordTrace]
  refine ⟨77970111532307946307336301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51980074354871964204890867 77970111532307946307336301)
  ·
    refine ⟨29238791824615479865251113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77970111532307946307336301 29238791824615479865251113)
    ·
      refine ⟨21929093868461609898938335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29238791824615479865251113 21929093868461609898938335)
      ·
        refine ⟨32893640802692414848407503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21929093868461609898938335 32893640802692414848407503)
        ·
          refine ⟨49340461204038622272611255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32893640802692414848407503 49340461204038622272611255)
          ·
            refine ⟨74010691806057933408916883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49340461204038622272611255 74010691806057933408916883)
            ·
              refine ⟨111016037709086900113375325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74010691806057933408916883 111016037709086900113375325)
              ·
                refine ⟨41631014140907587542515747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111016037709086900113375325 41631014140907587542515747)
                ·
                  refine ⟨62446521211361381313773621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41631014140907587542515747 62446521211361381313773621)
                  ·
                    refine ⟨5854361363565129498166277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62446521211361381313773621 5854361363565129498166277)
                    ·
                      refine ⟨1097692755668461780906177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5854361363565129498166277 1097692755668461780906177)
                      ·
                        rfl

theorem cell23_2137749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2137749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137749 prefixEnd_2137749 := by exact prefixLift 2137749
  have htrace : WordTrace (prefixWord ++ tailWord_2137749) baseStart_2137749 baseEnd_2137749 := by
    simpa [prefixWord, tailWord_2137749, baseEnd_2137749] using wordTrace_append hprefix tailTrace_2137749
  have hstable : (prefixWord ++ tailWord_2137749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137749).length < 2 ^ (prefixWord ++ tailWord_2137749).sum := by decide
  have hdescent : baseEnd_2137749 < baseStart_2137749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137786 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_2137786 : Nat := 118140960795 + 2137786 * 2 ^ 59
def prefixEnd_2137786 : Nat := 4983230072969 + 3 ^ 40 * 2137786 * 2
def baseEnd_2137786 : Nat := 1097711754452678136143507

theorem tailTrace_2137786 : CollatzResearch.WordTrace tailWord_2137786 prefixEnd_2137786 1097711754452678136143507 := by
  unfold tailWord_2137786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19492865258293475406608303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51980974022115934417622141 19492865258293475406608303)
  ·
    refine ⟨29239297887440213109912455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19492865258293475406608303 29239297887440213109912455)
    ·
      refine ⟨43858946831160319664868683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29239297887440213109912455 43858946831160319664868683)
      ·
        refine ⟨65788420246740479497303025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43858946831160319664868683 65788420246740479497303025)
        ·
          refine ⟨49341315185055359622977269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65788420246740479497303025 49341315185055359622977269)
          ·
            refine ⟨4625748298598939964654119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49341315185055359622977269 4625748298598939964654119)
            ·
              refine ⟨6938622447898409946981179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625748298598939964654119 6938622447898409946981179)
              ·
                refine ⟨10407933671847614920471769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6938622447898409946981179 10407933671847614920471769)
                ·
                  refine ⟨7805950253885711190353827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10407933671847614920471769 7805950253885711190353827)
                  ·
                    refine ⟨11708925380828566785530741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7805950253885711190353827 11708925380828566785530741)
                    ·
                      refine ⟨1097711754452678136143507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11708925380828566785530741 1097711754452678136143507)
                      ·
                        rfl

theorem cell23_2137786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_2137786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137786 prefixEnd_2137786 := by exact prefixLift 2137786
  have htrace : WordTrace (prefixWord ++ tailWord_2137786) baseStart_2137786 baseEnd_2137786 := by
    simpa [prefixWord, tailWord_2137786, baseEnd_2137786] using wordTrace_append hprefix tailTrace_2137786
  have hstable : (prefixWord ++ tailWord_2137786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137786).length < 2 ^ (prefixWord ++ tailWord_2137786).sum := by decide
  have hdescent : baseEnd_2137786 < baseStart_2137786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137799 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_2137799 : Nat := 118140960795 + 2137799 * 2 ^ 59
def prefixEnd_2137799 : Nat := 4983230072969 + 3 ^ 40 * 2137799 * 2
def baseEnd_2137799 : Nat := 1097718429701186585280947

theorem tailTrace_2137799 : CollatzResearch.WordTrace tailWord_2137799 prefixEnd_2137799 1097718429701186585280947 := by
  unfold tailWord_2137799
  simp only [CollatzResearch.WordTrace]
  refine ⟨77971935182126804846656451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51981290121417869897770967 77971935182126804846656451)
  ·
    refine ⟨116957902773190207269984677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77971935182126804846656451 116957902773190207269984677)
    ·
      refine ⟨21929606769973163863122127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116957902773190207269984677 21929606769973163863122127)
      ·
        refine ⟨32894410154959745794683191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21929606769973163863122127 32894410154959745794683191)
        ·
          refine ⟨49341615232439618692024787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32894410154959745794683191 49341615232439618692024787)
          ·
            refine ⟨74012422848659428038037181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49341615232439618692024787 74012422848659428038037181)
            ·
              refine ⟨27754658568247285514263943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74012422848659428038037181 27754658568247285514263943)
              ·
                refine ⟨41631987852370928271395915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27754658568247285514263943 41631987852370928271395915)
                ·
                  refine ⟨62447981778556392407093873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41631987852370928271395915 62447981778556392407093873)
                  ·
                    refine ⟨46835986333917294305320405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62447981778556392407093873 46835986333917294305320405)
                    ·
                      refine ⟨1097718429701186585280947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46835986333917294305320405 1097718429701186585280947)
                      ·
                        rfl

theorem cell23_2137799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_2137799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137799 prefixEnd_2137799 := by exact prefixLift 2137799
  have htrace : WordTrace (prefixWord ++ tailWord_2137799) baseStart_2137799 baseEnd_2137799 := by
    simpa [prefixWord, tailWord_2137799, baseEnd_2137799] using wordTrace_append hprefix tailTrace_2137799
  have hstable : (prefixWord ++ tailWord_2137799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137799).length < 2 ^ (prefixWord ++ tailWord_2137799).sum := by decide
  have hdescent : baseEnd_2137799 < baseStart_2137799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137800 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_2137800 : Nat := 118140960795 + 2137800 * 2 ^ 59
def prefixEnd_2137800 : Nat := 4983230072969 + 3 ^ 40 * 2137800 * 2
def baseEnd_2137800 : Nat := 1097718943181841081368443

theorem tailTrace_2137800 : CollatzResearch.WordTrace tailWord_2137800 prefixEnd_2137800 1097718943181841081368443 := by
  unfold tailWord_2137800
  simp only [CollatzResearch.WordTrace]
  refine ⟨38985985827561591008721427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51981314436748788011628569 38985985827561591008721427)
  ·
    refine ⟨58478978741342386513082141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38985985827561591008721427 58478978741342386513082141)
    ·
      refine ⟨21929617028003394942405803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58478978741342386513082141 21929617028003394942405803)
      ·
        refine ⟨32894425542005092413608705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21929617028003394942405803 32894425542005092413608705)
        ·
          refine ⟨24670819156503819310206529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32894425542005092413608705 24670819156503819310206529)
          ·
            refine ⟨18503114367377864482654897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24670819156503819310206529 18503114367377864482654897)
            ·
              refine ⟨13877335775533398361991173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18503114367377864482654897 13877335775533398361991173)
              ·
                refine ⟨2602000457912512192873345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13877335775533398361991173 2602000457912512192873345)
                ·
                  refine ⟨1951500343434384144655009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2602000457912512192873345 1951500343434384144655009)
                  ·
                    refine ⟨1463625257575788108491257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1951500343434384144655009 1463625257575788108491257)
                    ·
                      refine ⟨1097718943181841081368443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463625257575788108491257 1097718943181841081368443)
                      ·
                        rfl

theorem cell23_2137800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_2137800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137800 prefixEnd_2137800 := by exact prefixLift 2137800
  have htrace : WordTrace (prefixWord ++ tailWord_2137800) baseStart_2137800 baseEnd_2137800 := by
    simpa [prefixWord, tailWord_2137800, baseEnd_2137800] using wordTrace_append hprefix tailTrace_2137800
  have hstable : (prefixWord ++ tailWord_2137800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137800).length < 2 ^ (prefixWord ++ tailWord_2137800).sum := by decide
  have hdescent : baseEnd_2137800 < baseStart_2137800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137816 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2137816 : Nat := 118140960795 + 2137816 * 2 ^ 59
def prefixEnd_2137816 : Nat := 4983230072969 + 3 ^ 40 * 2137816 * 2
def baseEnd_2137816 : Nat := 1097727158872313018768369

theorem tailTrace_2137816 : CollatzResearch.WordTrace tailWord_2137816 prefixEnd_2137816 1097727158872313018768369 := by
  unfold tailWord_2137816
  simp only [CollatzResearch.WordTrace]
  refine ⟨38986277611532608375012651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51981703482043477833350201 38986277611532608375012651)
  ·
    refine ⟨58479416417298912562518977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38986277611532608375012651 58479416417298912562518977)
    ·
      refine ⟨43859562312974184421889233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58479416417298912562518977 43859562312974184421889233)
      ·
        refine ⟨32894671734730638316416925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43859562312974184421889233 32894671734730638316416925)
        ·
          refine ⟨12335501900523989368656347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32894671734730638316416925 12335501900523989368656347)
          ·
            refine ⟨18503252850785984052984521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12335501900523989368656347 18503252850785984052984521)
            ·
              refine ⟨13877439638089488039738391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18503252850785984052984521 13877439638089488039738391)
              ·
                refine ⟨20816159457134232059607587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13877439638089488039738391 20816159457134232059607587)
                ·
                  refine ⟨31224239185701348089411381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20816159457134232059607587 31224239185701348089411381)
                  ·
                    refine ⟨2927272423659501383382317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31224239185701348089411381 2927272423659501383382317)
                    ·
                      refine ⟨1097727158872313018768369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2927272423659501383382317 1097727158872313018768369)
                      ·
                        rfl

theorem cell23_2137816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2137816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137816 prefixEnd_2137816 := by exact prefixLift 2137816
  have htrace : WordTrace (prefixWord ++ tailWord_2137816) baseStart_2137816 baseEnd_2137816 := by
    simpa [prefixWord, tailWord_2137816, baseEnd_2137816] using wordTrace_append hprefix tailTrace_2137816
  have hstable : (prefixWord ++ tailWord_2137816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137816).length < 2 ^ (prefixWord ++ tailWord_2137816).sum := by decide
  have hdescent : baseEnd_2137816 < baseStart_2137816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137817 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 2, 2, 2]
def baseStart_2137817 : Nat := 118140960795 + 2137817 * 2 ^ 59
def prefixEnd_2137817 : Nat := 4983230072969 + 3 ^ 40 * 2137817 * 2
def baseEnd_2137817 : Nat := 1097727672352967514855865

theorem tailTrace_2137817 : CollatzResearch.WordTrace tailWord_2137817 prefixEnd_2137817 1097727672352967514855865 := by
  unfold tailWord_2137817
  simp only [CollatzResearch.WordTrace]
  refine ⟨77972591696061593920811705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51981727797374395947207803 77972591696061593920811705)
  ·
    refine ⟨58479443772046195440608779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77972591696061593920811705 58479443772046195440608779)
    ·
      refine ⟨87719165658069293160913169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58479443772046195440608779 87719165658069293160913169)
      ·
        refine ⟨65789374243551969870684877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87719165658069293160913169 65789374243551969870684877)
        ·
          refine ⟨24671015341331988701506829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65789374243551969870684877 24671015341331988701506829)
          ·
            refine ⟨9251630752999495763065061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24671015341331988701506829 9251630752999495763065061)
            ·
              refine ⟨1734680766187405455574699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9251630752999495763065061 1734680766187405455574699)
              ·
                refine ⟨2602021149281108183362049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734680766187405455574699 2602021149281108183362049)
                ·
                  refine ⟨1951515861960831137521537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2602021149281108183362049 1951515861960831137521537)
                  ·
                    refine ⟨1463636896470623353141153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1951515861960831137521537 1463636896470623353141153)
                    ·
                      refine ⟨1097727672352967514855865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463636896470623353141153 1097727672352967514855865)
                      ·
                        rfl

theorem cell23_2137817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_2137817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137817 prefixEnd_2137817 := by exact prefixLift 2137817
  have htrace : WordTrace (prefixWord ++ tailWord_2137817) baseStart_2137817 baseEnd_2137817 := by
    simpa [prefixWord, tailWord_2137817, baseEnd_2137817] using wordTrace_append hprefix tailTrace_2137817
  have hstable : (prefixWord ++ tailWord_2137817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137817).length < 2 ^ (prefixWord ++ tailWord_2137817).sum := by decide
  have hdescent : baseEnd_2137817 < baseStart_2137817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137821 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2137821 : Nat := 118140960795 + 2137821 * 2 ^ 59
def prefixEnd_2137821 : Nat := 4983230072969 + 3 ^ 40 * 2137821 * 2
def baseEnd_2137821 : Nat := 1097729726275585499205847

theorem tailTrace_2137821 : CollatzResearch.WordTrace tailWord_2137821 prefixEnd_2137821 1097729726275585499205847 := by
  unfold tailWord_2137821
  simp only [CollatzResearch.WordTrace]
  refine ⟨77972737588047102603957317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51981825058698068402638211 77972737588047102603957317)
  ·
    refine ⟨14619888297758831738241997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77972737588047102603957317 14619888297758831738241997)
    ·
      refine ⟨5482458111659561901840749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14619888297758831738241997 5482458111659561901840749)
      ·
        refine ⟨2055921791872335713190281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5482458111659561901840749 2055921791872335713190281)
        ·
          refine ⟨1541941343904251784892711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2055921791872335713190281 1541941343904251784892711)
          ·
            refine ⟨2312912015856377677339067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541941343904251784892711 2312912015856377677339067)
            ·
              refine ⟨3469368023784566516008601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312912015856377677339067 3469368023784566516008601)
              ·
                refine ⟨2602026017838424887006451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3469368023784566516008601 2602026017838424887006451)
                ·
                  refine ⟨3903039026757637330509677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602026017838424887006451 3903039026757637330509677)
                  ·
                    refine ⟨1463639635034113998941129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3903039026757637330509677 1463639635034113998941129)
                    ·
                      refine ⟨1097729726275585499205847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463639635034113998941129 1097729726275585499205847)
                      ·
                        rfl

theorem cell23_2137821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2137821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137821 prefixEnd_2137821 := by exact prefixLift 2137821
  have htrace : WordTrace (prefixWord ++ tailWord_2137821) baseStart_2137821 baseEnd_2137821 := by
    simpa [prefixWord, tailWord_2137821, baseEnd_2137821] using wordTrace_append hprefix tailTrace_2137821
  have hstable : (prefixWord ++ tailWord_2137821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137821).length < 2 ^ (prefixWord ++ tailWord_2137821).sum := by decide
  have hdescent : baseEnd_2137821 < baseStart_2137821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137836 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_2137836 : Nat := 118140960795 + 2137836 * 2 ^ 59
def prefixEnd_2137836 : Nat := 4983230072969 + 3 ^ 40 * 2137836 * 2
def baseEnd_2137836 : Nat := 365912476161800980172759

theorem tailTrace_2137836 : CollatzResearch.WordTrace tailWord_2137836 prefixEnd_2137836 365912476161800980172759 := by
  unfold tailWord_2137836
  simp only [CollatzResearch.WordTrace]
  refine ⟨38986642341496380082876681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51982189788661840110502241 38986642341496380082876681)
  ·
    refine ⟨29239981756122285062157511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38986642341496380082876681 29239981756122285062157511)
    ·
      refine ⟨43859972634183427593236267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29239981756122285062157511 43859972634183427593236267)
      ·
        refine ⟨65789958951275141389854401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43859972634183427593236267 65789958951275141389854401)
        ·
          refine ⟨49342469213456356042390801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65789958951275141389854401 49342469213456356042390801)
          ·
            refine ⟨37006851910092267031793101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49342469213456356042390801 37006851910092267031793101)
            ·
              refine ⟨13877569466284600136922413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37006851910092267031793101 13877569466284600136922413)
              ·
                refine ⟨5204088549856725051345905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13877569466284600136922413 5204088549856725051345905)
                ·
                  refine ⟨3903066412392543788509429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204088549856725051345905 3903066412392543788509429)
                  ·
                    refine ⟨365912476161800980172759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3903066412392543788509429 365912476161800980172759)
                    ·
                      rfl

theorem cell23_2137836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_2137836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137836 prefixEnd_2137836 := by exact prefixLift 2137836
  have htrace : WordTrace (prefixWord ++ tailWord_2137836) baseStart_2137836 baseEnd_2137836 := by
    simpa [prefixWord, tailWord_2137836, baseEnd_2137836] using wordTrace_append hprefix tailTrace_2137836
  have hstable : (prefixWord ++ tailWord_2137836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137836).length < 2 ^ (prefixWord ++ tailWord_2137836).sum := by decide
  have hdescent : baseEnd_2137836 < baseStart_2137836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137893 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_2137893 : Nat := 118140960795 + 2137893 * 2 ^ 59
def prefixEnd_2137893 : Nat := 4983230072969 + 3 ^ 40 * 2137893 * 2
def baseEnd_2137893 : Nat := 1097766696882709217505515

theorem tailTrace_2137893 : CollatzResearch.WordTrace tailWord_2137893 prefixEnd_2137893 1097766696882709217505515 := by
  unfold tailWord_2137893
  simp only [CollatzResearch.WordTrace]
  refine ⟨77975363643786258900578333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51983575762524172600385555 77975363643786258900578333)
  ·
    refine ⟨29240761366419847087716875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77975363643786258900578333 29240761366419847087716875)
    ·
      refine ⟨43861142049629770631575313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29240761366419847087716875 43861142049629770631575313)
      ·
        refine ⟨32895856537222327973681485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43861142049629770631575313 32895856537222327973681485)
        ·
          refine ⟨12335946201458372990130557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32895856537222327973681485 12335946201458372990130557)
          ·
            refine ⟨4625979825546889871298959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12335946201458372990130557 4625979825546889871298959)
            ·
              refine ⟨6938969738320334806948439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625979825546889871298959 6938969738320334806948439)
              ·
                refine ⟨10408454607480502210422659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6938969738320334806948439 10408454607480502210422659)
                ·
                  refine ⟨15612681911220753315633989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10408454607480502210422659 15612681911220753315633989)
                  ·
                    refine ⟨2927377858353891246681373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15612681911220753315633989 2927377858353891246681373)
                    ·
                      refine ⟨1097766696882709217505515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2927377858353891246681373 1097766696882709217505515)
                      ·
                        rfl

theorem cell23_2137893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_2137893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137893 prefixEnd_2137893 := by exact prefixLift 2137893
  have htrace : WordTrace (prefixWord ++ tailWord_2137893) baseStart_2137893 baseEnd_2137893 := by
    simpa [prefixWord, tailWord_2137893, baseEnd_2137893] using wordTrace_append hprefix tailTrace_2137893
  have hstable : (prefixWord ++ tailWord_2137893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137893).length < 2 ^ (prefixWord ++ tailWord_2137893).sum := by decide
  have hdescent : baseEnd_2137893 < baseStart_2137893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137900 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_2137900 : Nat := 118140960795 + 2137900 * 2 ^ 59
def prefixEnd_2137900 : Nat := 4983230072969 + 3 ^ 40 * 2137900 * 2
def baseEnd_2137900 : Nat := 365923430415763563372661

theorem tailTrace_2137900 : CollatzResearch.WordTrace tailWord_2137900 prefixEnd_2137900 365923430415763563372661 := by
  unfold tailWord_2137900
  simp only [CollatzResearch.WordTrace]
  refine ⟨38987809477380449548041577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51983745969840599397388769 38987809477380449548041577)
  ·
    refine ⟨29240857108035337161031183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38987809477380449548041577 29240857108035337161031183)
    ·
      refine ⟨43861285662053005741546775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29240857108035337161031183 43861285662053005741546775)
      ·
        refine ⟨65791928493079508612320163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43861285662053005741546775 65791928493079508612320163)
        ·
          refine ⟨98687892739619262918480245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65791928493079508612320163 98687892739619262918480245)
          ·
            refine ⟨9251989944339305898607523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98687892739619262918480245 9251989944339305898607523)
            ·
              refine ⟨13877984916508958847911285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9251989944339305898607523 13877984916508958847911285)
              ·
                refine ⟨1301061085922714891991683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13877984916508958847911285 1301061085922714891991683)
                ·
                  refine ⟨1951591628884072337987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301061085922714891991683 1951591628884072337987525)
                  ·
                    refine ⟨365923430415763563372661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1951591628884072337987525 365923430415763563372661)
                    ·
                      rfl

theorem cell23_2137900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_2137900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137900 prefixEnd_2137900 := by exact prefixLift 2137900
  have htrace : WordTrace (prefixWord ++ tailWord_2137900) baseStart_2137900 baseEnd_2137900 := by
    simpa [prefixWord, tailWord_2137900, baseEnd_2137900] using wordTrace_append hprefix tailTrace_2137900
  have hstable : (prefixWord ++ tailWord_2137900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137900).length < 2 ^ (prefixWord ++ tailWord_2137900).sum := by decide
  have hdescent : baseEnd_2137900 < baseStart_2137900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137916 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2137916 : Nat := 118140960795 + 2137916 * 2 ^ 59
def prefixEnd_2137916 : Nat := 4983230072969 + 3 ^ 40 * 2137916 * 2
def baseEnd_2137916 : Nat := 1097778506937762627517909

theorem tailTrace_2137916 : CollatzResearch.WordTrace tailWord_2137916 prefixEnd_2137916 1097778506937762627517909 := by
  unfold tailWord_2137916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38988101261351466914332801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51984135015135289219110401 38988101261351466914332801)
  ·
    refine ⟨29241075946013600185749601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38988101261351466914332801 29241075946013600185749601)
    ·
      refine ⟨21930806959510200139312201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29241075946013600185749601 21930806959510200139312201)
      ·
        refine ⟨16448105219632650104484151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21930806959510200139312201 16448105219632650104484151)
        ·
          refine ⟨24672157829448975156726227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16448105219632650104484151 24672157829448975156726227)
          ·
            refine ⟨37008236744173462735089341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24672157829448975156726227 37008236744173462735089341)
            ·
              refine ⟨13878088779065048525658503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37008236744173462735089341 13878088779065048525658503)
              ·
                refine ⟨20817133168597572788487755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13878088779065048525658503 20817133168597572788487755)
                ·
                  refine ⟨31225699752896359182731633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20817133168597572788487755 31225699752896359182731633)
                  ·
                    refine ⟨23419274814672269387048725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31225699752896359182731633 23419274814672269387048725)
                    ·
                      refine ⟨1097778506937762627517909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23419274814672269387048725 1097778506937762627517909)
                      ·
                        rfl

theorem cell23_2137916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2137916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137916 prefixEnd_2137916 := by exact prefixLift 2137916
  have htrace : WordTrace (prefixWord ++ tailWord_2137916) baseStart_2137916 baseEnd_2137916 := by
    simpa [prefixWord, tailWord_2137916, baseEnd_2137916] using wordTrace_append hprefix tailTrace_2137916
  have hstable : (prefixWord ++ tailWord_2137916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137916).length < 2 ^ (prefixWord ++ tailWord_2137916).sum := by decide
  have hdescent : baseEnd_2137916 < baseStart_2137916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137917 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_2137917 : Nat := 118140960795 + 2137917 * 2 ^ 59
def prefixEnd_2137917 : Nat := 4983230072969 + 3 ^ 40 * 2137917 * 2
def baseEnd_2137917 : Nat := 365926340139472374535135

theorem tailTrace_2137917 : CollatzResearch.WordTrace tailWord_2137917 prefixEnd_2137917 365926340139472374535135 := by
  unfold tailWord_2137917
  simp only [CollatzResearch.WordTrace]
  refine ⟨77976238995699310999452005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51984159330466207332968003 77976238995699310999452005)
  ·
    refine ⟨14620544811693620812397251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77976238995699310999452005 14620544811693620812397251)
    ·
      refine ⟨21930817217540431218595877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14620544811693620812397251 21930817217540431218595877)
      ·
        refine ⟨4112028228288830853486727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21930817217540431218595877 4112028228288830853486727)
        ·
          refine ⟨6168042342433246280230091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4112028228288830853486727 6168042342433246280230091)
          ·
            refine ⟨9252063513649869420345137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168042342433246280230091 9252063513649869420345137)
            ·
              refine ⟨6939047635237402065258853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9252063513649869420345137 6939047635237402065258853)
              ·
                refine ⟨1301071431607012887236035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6939047635237402065258853 1301071431607012887236035)
                ·
                  refine ⟨1951607147410519330854053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301071431607012887236035 1951607147410519330854053)
                  ·
                    refine ⟨365926340139472374535135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1951607147410519330854053 365926340139472374535135)
                    ·
                      rfl

theorem cell23_2137917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_2137917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137917 prefixEnd_2137917 := by exact prefixLift 2137917
  have htrace : WordTrace (prefixWord ++ tailWord_2137917) baseStart_2137917 baseEnd_2137917 := by
    simpa [prefixWord, tailWord_2137917, baseEnd_2137917] using wordTrace_append hprefix tailTrace_2137917
  have hstable : (prefixWord ++ tailWord_2137917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137917).length < 2 ^ (prefixWord ++ tailWord_2137917).sum := by decide
  have hdescent : baseEnd_2137917 < baseStart_2137917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137983 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_2137983 : Nat := 118140960795 + 2137983 * 2 ^ 59
def prefixEnd_2137983 : Nat := 4983230072969 + 3 ^ 40 * 2137983 * 2
def baseEnd_2137983 : Nat := 1097812910141613865380101

theorem tailTrace_2137983 : CollatzResearch.WordTrace tailWord_2137983 prefixEnd_2137983 1097812910141613865380101 := by
  unfold tailWord_2137983
  simp only [CollatzResearch.WordTrace]
  refine ⟨77978646213460204271354603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51985764142306802847569735 77978646213460204271354603)
  ·
    refine ⟨116967969320190306407031905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77978646213460204271354603 116967969320190306407031905)
    ·
      refine ⟨87725976990142729805273929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116967969320190306407031905 87725976990142729805273929)
      ·
        refine ⟨65794482742607047353955447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87725976990142729805273929 65794482742607047353955447)
        ·
          refine ⟨98691724113910571030933171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65794482742607047353955447 98691724113910571030933171)
          ·
            refine ⟨148037586170865856546399757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98691724113910571030933171 148037586170865856546399757)
            ·
              refine ⟨55514094814074696204899909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148037586170865856546399757 55514094814074696204899909)
              ·
                refine ⟨10408892777639005538418733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55514094814074696204899909 10408892777639005538418733)
                ·
                  refine ⟨3903334791614627076907025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10408892777639005538418733 3903334791614627076907025)
                  ·
                    refine ⟨2927501093710970307680269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903334791614627076907025 2927501093710970307680269)
                    ·
                      refine ⟨1097812910141613865380101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2927501093710970307680269 1097812910141613865380101)
                      ·
                        rfl

theorem cell23_2137983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_2137983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137983 prefixEnd_2137983 := by exact prefixLift 2137983
  have htrace : WordTrace (prefixWord ++ tailWord_2137983) baseStart_2137983 baseEnd_2137983 := by
    simpa [prefixWord, tailWord_2137983, baseEnd_2137983] using wordTrace_append hprefix tailTrace_2137983
  have hstable : (prefixWord ++ tailWord_2137983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137983).length < 2 ^ (prefixWord ++ tailWord_2137983).sum := by decide
  have hdescent : baseEnd_2137983 < baseStart_2137983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137993 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_2137993 : Nat := 118140960795 + 2137993 * 2 ^ 59
def prefixEnd_2137993 : Nat := 4983230072969 + 3 ^ 40 * 2137993 * 2
def baseEnd_2137993 : Nat := 1097818044948158826255055

theorem tailTrace_2137993 : CollatzResearch.WordTrace tailWord_2137993 prefixEnd_2137993 1097818044948158826255055 := by
  unfold tailWord_2137993
  simp only [CollatzResearch.WordTrace]
  refine ⟨77979010943423975979218633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51986007295615983986145755 77979010943423975979218633)
  ·
    refine ⟨58484258207567981984413975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77979010943423975979218633 58484258207567981984413975)
    ·
      refine ⟨87726387311351972976620963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58484258207567981984413975 87726387311351972976620963)
      ·
        refine ⟨131589580967027959464931445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87726387311351972976620963 131589580967027959464931445)
        ·
          refine ⟨12336523215658871199837323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131589580967027959464931445 12336523215658871199837323)
          ·
            refine ⟨18504784823488306799755985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12336523215658871199837323 18504784823488306799755985)
            ·
              refine ⟨13878588617616230099816989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18504784823488306799755985 13878588617616230099816989)
              ·
                refine ⟨5204470731606086287431371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13878588617616230099816989 5204470731606086287431371)
                ·
                  refine ⟨7806706097409129431147057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204470731606086287431371 7806706097409129431147057)
                  ·
                    refine ⟨5855029573056847073360293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7806706097409129431147057 5855029573056847073360293)
                    ·
                      refine ⟨1097818044948158826255055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5855029573056847073360293 1097818044948158826255055)
                      ·
                        rfl

theorem cell23_2137993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_2137993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137993 prefixEnd_2137993 := by exact prefixLift 2137993
  have htrace : WordTrace (prefixWord ++ tailWord_2137993) baseStart_2137993 baseEnd_2137993 := by
    simpa [prefixWord, tailWord_2137993, baseEnd_2137993] using wordTrace_append hprefix tailTrace_2137993
  have hstable : (prefixWord ++ tailWord_2137993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137993).length < 2 ^ (prefixWord ++ tailWord_2137993).sum := by decide
  have hdescent : baseEnd_2137993 < baseStart_2137993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137994 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_2137994 : Nat := 118140960795 + 2137994 * 2 ^ 59
def prefixEnd_2137994 : Nat := 4983230072969 + 3 ^ 40 * 2137994 * 2
def baseEnd_2137994 : Nat := 365939519476271107447517

theorem tailTrace_2137994 : CollatzResearch.WordTrace tailWord_2137994 prefixEnd_2137994 365939519476271107447517 := by
  unfold tailWord_2137994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19494761854105088287501259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51986031610946902100003357 19494761854105088287501259)
  ·
    refine ⟨29242142781157632431251889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19494761854105088287501259 29242142781157632431251889)
    ·
      refine ⟨21931607085868224323438917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29242142781157632431251889 21931607085868224323438917)
      ·
        refine ⟨4112176328600292060644797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21931607085868224323438917 4112176328600292060644797)
        ·
          refine ⟨1542066123225109522741799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4112176328600292060644797 1542066123225109522741799)
          ·
            refine ⟨2313099184837664284112699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542066123225109522741799 2313099184837664284112699)
            ·
              refine ⟨3469648777256496426169049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313099184837664284112699 3469648777256496426169049)
              ·
                refine ⟨2602236582942372319626787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3469648777256496426169049 2602236582942372319626787)
                ·
                  refine ⟨3903354874413558479440181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602236582942372319626787 3903354874413558479440181)
                  ·
                    refine ⟨365939519476271107447517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3903354874413558479440181 365939519476271107447517)
                    ·
                      rfl

theorem cell23_2137994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_2137994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2137994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2137994 prefixEnd_2137994 := by exact prefixLift 2137994
  have htrace : WordTrace (prefixWord ++ tailWord_2137994) baseStart_2137994 baseEnd_2137994 := by
    simpa [prefixWord, tailWord_2137994, baseEnd_2137994] using wordTrace_append hprefix tailTrace_2137994
  have hstable : (prefixWord ++ tailWord_2137994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137994).length < 2 ^ (prefixWord ++ tailWord_2137994).sum := by decide
  have hdescent : baseEnd_2137994 < baseStart_2137994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138010 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2138010 : Nat := 118140960795 + 2138010 * 2 ^ 59
def prefixEnd_2138010 : Nat := 4983230072969 + 3 ^ 40 * 2138010 * 2
def baseEnd_2138010 : Nat := 1097826774119285259742477

theorem tailTrace_2138010 : CollatzResearch.WordTrace tailWord_2138010 prefixEnd_2138010 1097826774119285259742477 := by
  unfold tailWord_2138010
  simp only [CollatzResearch.WordTrace]
  refine ⟨19494907746090596970646871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51986420656241591921724989 19494907746090596970646871)
  ·
    refine ⟨29242361619135895455970307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19494907746090596970646871 29242361619135895455970307)
    ·
      refine ⟨43863542428703843183955461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29242361619135895455970307 43863542428703843183955461)
      ·
        refine ⟨8224414205381970596991649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43863542428703843183955461 8224414205381970596991649)
        ·
          refine ⟨6168310654036477947743737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8224414205381970596991649 6168310654036477947743737)
          ·
            refine ⟨4626232990527358460807803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6168310654036477947743737 4626232990527358460807803)
            ·
              refine ⟨6939349485791037691211705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626232990527358460807803 6939349485791037691211705)
              ·
                refine ⟨5204512114343278268408779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6939349485791037691211705 5204512114343278268408779)
                ·
                  refine ⟨7806768171514917402613169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204512114343278268408779 7806768171514917402613169)
                  ·
                    refine ⟨5855076128636188051959877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7806768171514917402613169 5855076128636188051959877)
                    ·
                      refine ⟨1097826774119285259742477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5855076128636188051959877 1097826774119285259742477)
                      ·
                        rfl

theorem cell23_2138010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2138010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138010 prefixEnd_2138010 := by exact prefixLift 2138010
  have htrace : WordTrace (prefixWord ++ tailWord_2138010) baseStart_2138010 baseEnd_2138010 := by
    simpa [prefixWord, tailWord_2138010, baseEnd_2138010] using wordTrace_append hprefix tailTrace_2138010
  have hstable : (prefixWord ++ tailWord_2138010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138010).length < 2 ^ (prefixWord ++ tailWord_2138010).sum := by decide
  have hdescent : baseEnd_2138010 < baseStart_2138010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138017 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2138017 : Nat := 118140960795 + 2138017 * 2 ^ 59
def prefixEnd_2138017 : Nat := 4983230072969 + 3 ^ 40 * 2138017 * 2
def baseEnd_2138017 : Nat := 1097830368483866732354945

theorem tailTrace_2138017 : CollatzResearch.WordTrace tailWord_2138017 prefixEnd_2138017 1097830368483866732354945 := by
  unfold tailWord_2138017
  simp only [CollatzResearch.WordTrace]
  refine ⟨77979886295337028078092305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51986590863558018718728203 77979886295337028078092305)
  ·
    refine ⟨58484914721502771058569229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77979886295337028078092305 58484914721502771058569229)
    ·
      refine ⟨21931843020563539146963461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58484914721502771058569229 21931843020563539146963461)
      ·
        refine ⟨4112220566355663590055649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21931843020563539146963461 4112220566355663590055649)
        ·
          refine ⟨3084165424766747692541737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4112220566355663590055649 3084165424766747692541737)
          ·
            refine ⟨2313124068575060769406303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3084165424766747692541737 2313124068575060769406303)
            ·
              refine ⟨3469686102862591154109455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313124068575060769406303 3469686102862591154109455)
              ·
                refine ⟨5204529154293886731164183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469686102862591154109455 5204529154293886731164183)
                ·
                  refine ⟨7806793731440830096746275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5204529154293886731164183 7806793731440830096746275)
                  ·
                    refine ⟨11710190597161245145119413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7806793731440830096746275 11710190597161245145119413)
                    ·
                      refine ⟨1097830368483866732354945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11710190597161245145119413 1097830368483866732354945)
                      ·
                        rfl

theorem cell23_2138017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2138017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138017 prefixEnd_2138017 := by exact prefixLift 2138017
  have htrace : WordTrace (prefixWord ++ tailWord_2138017) baseStart_2138017 baseEnd_2138017 := by
    simpa [prefixWord, tailWord_2138017, baseEnd_2138017] using wordTrace_append hprefix tailTrace_2138017
  have hstable : (prefixWord ++ tailWord_2138017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138017).length < 2 ^ (prefixWord ++ tailWord_2138017).sum := by decide
  have hdescent : baseEnd_2138017 < baseStart_2138017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138033 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_2138033 : Nat := 118140960795 + 2138033 * 2 ^ 59
def prefixEnd_2138033 : Nat := 4983230072969 + 3 ^ 40 * 2138033 * 2
def baseEnd_2138033 : Nat := 365946194724779556584957

theorem tailTrace_2138033 : CollatzResearch.WordTrace tailWord_2138033 prefixEnd_2138033 365946194724779556584957 := by
  unfold tailWord_2138033
  simp only [CollatzResearch.WordTrace]
  refine ⟨77980469863279062810674753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51986979908852708540449835 77980469863279062810674753)
  ·
    refine ⟨58485352397459297108006065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77980469863279062810674753 58485352397459297108006065)
    ·
      refine ⟨43864014298094472831004549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58485352397459297108006065 43864014298094472831004549)
      ·
        refine ⟨8224502680892713655813353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43864014298094472831004549 8224502680892713655813353)
        ·
          refine ⟨6168377010669535241860015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8224502680892713655813353 6168377010669535241860015)
          ·
            refine ⟨9252565516004302862790023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168377010669535241860015 9252565516004302862790023)
            ·
              refine ⟨13878848274006454294185035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9252565516004302862790023 13878848274006454294185035)
              ·
                refine ⟨20818272411009681441277553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13878848274006454294185035 20818272411009681441277553)
                ·
                  refine ⟨15613704308257261080958165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20818272411009681441277553 15613704308257261080958165)
                  ·
                    refine ⟨365946194724779556584957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15613704308257261080958165 365946194724779556584957)
                    ·
                      rfl

theorem cell23_2138033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_2138033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138033 prefixEnd_2138033 := by exact prefixLift 2138033
  have htrace : WordTrace (prefixWord ++ tailWord_2138033) baseStart_2138033 baseEnd_2138033 := by
    simpa [prefixWord, tailWord_2138033, baseEnd_2138033] using wordTrace_append hprefix tailTrace_2138033
  have hstable : (prefixWord ++ tailWord_2138033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138033).length < 2 ^ (prefixWord ++ tailWord_2138033).sum := by decide
  have hdescent : baseEnd_2138033 < baseStart_2138033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138040 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 5, 3, 2]
def baseStart_2138040 : Nat := 118140960795 + 2138040 * 2 ^ 59
def prefixEnd_2138040 : Nat := 4983230072969 + 3 ^ 40 * 2138040 * 2
def baseEnd_2138040 : Nat := 1097842178538920142367339

theorem tailTrace_2138040 : CollatzResearch.WordTrace tailWord_2138040 prefixEnd_2138040 1097842178538920142367339 := by
  unfold tailWord_2138040
  simp only [CollatzResearch.WordTrace]
  refine ⟨38990362587126851503089787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51987150116169135337453049 38990362587126851503089787)
  ·
    refine ⟨58485543880690277254634681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38990362587126851503089787 58485543880690277254634681)
    ·
      refine ⟨43864157910517707940976011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58485543880690277254634681 43864157910517707940976011)
      ·
        refine ⟨65796236865776561911464017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43864157910517707940976011 65796236865776561911464017)
        ·
          refine ⟨49347177649332421433598013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65796236865776561911464017 49347177649332421433598013)
          ·
            refine ⟨18505191618499658037599255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49347177649332421433598013 18505191618499658037599255)
            ·
              refine ⟨27757787427749487056398883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18505191618499658037599255 27757787427749487056398883)
              ·
                refine ⟨41636681141624230584598325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27757787427749487056398883 41636681141624230584598325)
                ·
                  refine ⟨3903438857027271617306093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41636681141624230584598325 3903438857027271617306093)
                  ·
                    refine ⟨1463789571385226856489785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3903438857027271617306093 1463789571385226856489785)
                    ·
                      refine ⟨1097842178538920142367339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463789571385226856489785 1097842178538920142367339)
                      ·
                        rfl

theorem cell23_2138040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_2138040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138040 prefixEnd_2138040 := by exact prefixLift 2138040
  have htrace : WordTrace (prefixWord ++ tailWord_2138040) baseStart_2138040 baseEnd_2138040 := by
    simpa [prefixWord, tailWord_2138040, baseEnd_2138040] using wordTrace_append hprefix tailTrace_2138040
  have hstable : (prefixWord ++ tailWord_2138040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138040).length < 2 ^ (prefixWord ++ tailWord_2138040).sum := by decide
  have hdescent : baseEnd_2138040 < baseStart_2138040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138074 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2]
def baseStart_2138074 : Nat := 118140960795 + 2138074 * 2 ^ 59
def prefixEnd_2138074 : Nat := 4983230072969 + 3 ^ 40 * 2138074 * 2
def baseEnd_2138074 : Nat := 1097859636881173009342183

theorem tailTrace_2138074 : CollatzResearch.WordTrace tailWord_2138074 prefixEnd_2138074 1097859636881173009342183 := by
  unfold tailWord_2138074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19495491314032631703229319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51987976837420351208611517 19495491314032631703229319)
  ·
    refine ⟨29243236971048947554843979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19495491314032631703229319 29243236971048947554843979)
    ·
      refine ⟨43864855456573421332265969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29243236971048947554843979 43864855456573421332265969)
      ·
        refine ⟨32898641592430065999199477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43864855456573421332265969 32898641592430065999199477)
        ·
          refine ⟨3084247649290318687424951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32898641592430065999199477 3084247649290318687424951)
          ·
            refine ⟨4626371473935478031137427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3084247649290318687424951 4626371473935478031137427)
            ·
              refine ⟨6939557210903217046706141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626371473935478031137427 6939557210903217046706141)
              ·
                refine ⟨2602333954088706392514803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6939557210903217046706141 2602333954088706392514803)
                ·
                  refine ⟨3903500931133059588772205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602333954088706392514803 3903500931133059588772205)
                  ·
                    refine ⟨1463812849174897345789577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3903500931133059588772205 1463812849174897345789577)
                    ·
                      refine ⟨1097859636881173009342183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463812849174897345789577 1097859636881173009342183)
                      ·
                        rfl

theorem cell23_2138074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_2138074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138074 prefixEnd_2138074 := by exact prefixLift 2138074
  have htrace : WordTrace (prefixWord ++ tailWord_2138074) baseStart_2138074 baseEnd_2138074 := by
    simpa [prefixWord, tailWord_2138074, baseEnd_2138074] using wordTrace_append hprefix tailTrace_2138074
  have hstable : (prefixWord ++ tailWord_2138074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138074).length < 2 ^ (prefixWord ++ tailWord_2138074).sum := by decide
  have hdescent : baseEnd_2138074 < baseStart_2138074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138123 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 1, 7]
def baseStart_2138123 : Nat := 118140960795 + 2138123 * 2 ^ 59
def prefixEnd_2138123 : Nat := 4983230072969 + 3 ^ 40 * 2138123 * 2
def baseEnd_2138123 : Nat := 365961599144414439209819

theorem tailTrace_2138123 : CollatzResearch.WordTrace tailWord_2138123 prefixEnd_2138123 365961599144414439209819 := by
  unfold tailWord_2138123
  simp only [CollatzResearch.WordTrace]
  refine ⟨77983752432953008181451023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51989168288635338787634015 77983752432953008181451023)
  ·
    refine ⟨116975628649429512272176535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77983752432953008181451023 116975628649429512272176535)
    ·
      refine ⟨175463442974144268408264803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116975628649429512272176535 175463442974144268408264803)
      ·
        refine ⟨263195164461216402612397205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175463442974144268408264803 263195164461216402612397205)
        ·
          refine ⟨12337273334119518872456119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 263195164461216402612397205 12337273334119518872456119)
          ·
            refine ⟨18505910001179278308684179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12337273334119518872456119 18505910001179278308684179)
            ·
              refine ⟨27758865001768917463026269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18505910001179278308684179 27758865001768917463026269)
              ·
                refine ⟨10409574375663344048634851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27758865001768917463026269 10409574375663344048634851)
                ·
                  refine ⟨15614361563495016072952277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10409574375663344048634851 15614361563495016072952277)
                  ·
                    refine ⟨365961599144414439209819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15614361563495016072952277 365961599144414439209819)
                    ·
                      rfl

theorem cell23_2138123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_2138123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138123 prefixEnd_2138123 := by exact prefixLift 2138123
  have htrace : WordTrace (prefixWord ++ tailWord_2138123) baseStart_2138123 baseEnd_2138123 := by
    simpa [prefixWord, tailWord_2138123, baseEnd_2138123] using wordTrace_append hprefix tailTrace_2138123
  have hstable : (prefixWord ++ tailWord_2138123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138123).length < 2 ^ (prefixWord ++ tailWord_2138123).sum := by decide
  have hdescent : baseEnd_2138123 < baseStart_2138123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138140 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_2138140 : Nat := 118140960795 + 2138140 * 2 ^ 59
def prefixEnd_2138140 : Nat := 4983230072969 + 3 ^ 40 * 2138140 * 2
def baseEnd_2138140 : Nat := 365964508868123250372293

theorem tailTrace_2138140 : CollatzResearch.WordTrace tailWord_2138140 prefixEnd_2138140 365964508868123250372293 := by
  unfold tailWord_2138140
  simp only [CollatzResearch.WordTrace]
  refine ⟨38992186236945710042409937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51989581649260946723213249 38992186236945710042409937)
  ·
    refine ⟨29244139677709282531807453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38992186236945710042409937 29244139677709282531807453)
    ·
      refine ⟨10966552379140980949427795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29244139677709282531807453 10966552379140980949427795)
      ·
        refine ⟨16449828568711471424141693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10966552379140980949427795 16449828568711471424141693)
        ·
          refine ⟨6168685713266801784053135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16449828568711471424141693 6168685713266801784053135)
          ·
            refine ⟨9253028569900202676079703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168685713266801784053135 9253028569900202676079703)
            ·
              refine ⟨13879542854850304014119555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9253028569900202676079703 13879542854850304014119555)
              ·
                refine ⟨20819314282275456021179333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13879542854850304014119555 20819314282275456021179333)
                ·
                  refine ⟨3903621427926648003971125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20819314282275456021179333 3903621427926648003971125)
                  ·
                    refine ⟨365964508868123250372293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3903621427926648003971125 365964508868123250372293)
                    ·
                      rfl

theorem cell23_2138140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_2138140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138140 prefixEnd_2138140 := by exact prefixLift 2138140
  have htrace : WordTrace (prefixWord ++ tailWord_2138140) baseStart_2138140 baseEnd_2138140 := by
    simpa [prefixWord, tailWord_2138140, baseEnd_2138140] using wordTrace_append hprefix tailTrace_2138140
  have hstable : (prefixWord ++ tailWord_2138140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138140).length < 2 ^ (prefixWord ++ tailWord_2138140).sum := by decide
  have hdescent : baseEnd_2138140 < baseStart_2138140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138170 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_2138170 : Nat := 118140960795 + 2138170 * 2 ^ 59
def prefixEnd_2138170 : Nat := 4983230072969 + 3 ^ 40 * 2138170 * 2
def baseEnd_2138170 : Nat := 365969643674668211247247

theorem tailTrace_2138170 : CollatzResearch.WordTrace tailWord_2138170 prefixEnd_2138170 365969643674668211247247 := by
  unfold tailWord_2138170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496366665945683802102991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51990311109188490138941309 19496366665945683802102991)
  ·
    refine ⟨29244549998918525703154487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19496366665945683802102991 29244549998918525703154487)
    ·
      refine ⟨43866824998377788554731731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29244549998918525703154487 43866824998377788554731731)
      ·
        refine ⟨65800237497566682832097597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43866824998377788554731731 65800237497566682832097597)
        ·
          refine ⟨24675089061587506062036599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65800237497566682832097597 24675089061587506062036599)
          ·
            refine ⟨37012633592381259093054899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24675089061587506062036599 37012633592381259093054899)
            ·
              refine ⟨55518950388571888639582349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37012633592381259093054899 55518950388571888639582349)
              ·
                refine ⟨20819606395714458239843381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55518950388571888639582349 20819606395714458239843381)
                ·
                  refine ⟨1951838099598230459985317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20819606395714458239843381 1951838099598230459985317)
                  ·
                    refine ⟨365969643674668211247247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1951838099598230459985317 365969643674668211247247)
                    ·
                      rfl

theorem cell23_2138170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_2138170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138170 prefixEnd_2138170 := by exact prefixLift 2138170
  have htrace : WordTrace (prefixWord ++ tailWord_2138170) baseStart_2138170 baseEnd_2138170 := by
    simpa [prefixWord, tailWord_2138170, baseEnd_2138170] using wordTrace_append hprefix tailTrace_2138170
  have hstable : (prefixWord ++ tailWord_2138170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138170).length < 2 ^ (prefixWord ++ tailWord_2138170).sum := by decide
  have hdescent : baseEnd_2138170 < baseStart_2138170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138174 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2138174 : Nat := 118140960795 + 2138174 * 2 ^ 59
def prefixEnd_2138174 : Nat := 4983230072969 + 3 ^ 40 * 2138174 * 2
def baseEnd_2138174 : Nat := 365970328315540872697241

theorem tailTrace_2138174 : CollatzResearch.WordTrace tailWord_2138174 prefixEnd_2138174 365970328315540872697241 := by
  unfold tailWord_2138174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748201569471030486444697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51990408370512162594371717 9748201569471030486444697)
  ·
    refine ⟨7311151177103272864833523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9748201569471030486444697 7311151177103272864833523)
    ·
      refine ⟨10966726765654909297250285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7311151177103272864833523 10966726765654909297250285)
      ·
        refine ⟨4112522537120590986468857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10966726765654909297250285 4112522537120590986468857)
        ·
          refine ⟨3084391902840443239851643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4112522537120590986468857 3084391902840443239851643)
          ·
            refine ⟨4626587854260664859777465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3084391902840443239851643 4626587854260664859777465)
            ·
              refine ⟨3469940890695498644833099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4626587854260664859777465 3469940890695498644833099)
              ·
                refine ⟨5204911336043247967249649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469940890695498644833099 5204911336043247967249649)
                ·
                  refine ⟨3903683502032435975437237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204911336043247967249649 3903683502032435975437237)
                  ·
                    refine ⟨365970328315540872697241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3903683502032435975437237 365970328315540872697241)
                    ·
                      rfl

theorem cell23_2138174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2138174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138174 prefixEnd_2138174 := by exact prefixLift 2138174
  have htrace : WordTrace (prefixWord ++ tailWord_2138174) baseStart_2138174 baseEnd_2138174 := by
    simpa [prefixWord, tailWord_2138174, baseEnd_2138174] using wordTrace_append hprefix tailTrace_2138174
  have hstable : (prefixWord ++ tailWord_2138174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138174).length < 2 ^ (prefixWord ++ tailWord_2138174).sum := by decide
  have hdescent : baseEnd_2138174 < baseStart_2138174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138177 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2138177 : Nat := 118140960795 + 2138177 * 2 ^ 59
def prefixEnd_2138177 : Nat := 4983230072969 + 3 ^ 40 * 2138177 * 2
def baseEnd_2138177 : Nat := 1097912525388586106354209

theorem tailTrace_2138177 : CollatzResearch.WordTrace tailWord_2138177 prefixEnd_2138177 1097912525388586106354209 := by
  unfold tailWord_2138177
  simp only [CollatzResearch.WordTrace]
  refine ⟨77985721974757375403916785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51990481316504916935944523 77985721974757375403916785)
  ·
    refine ⟨58489291481068031552937589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77985721974757375403916785 58489291481068031552937589)
    ·
      refine ⟨5483371076350127958087899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58489291481068031552937589 5483371076350127958087899)
      ·
        refine ⟨8225056614525191937131849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5483371076350127958087899 8225056614525191937131849)
        ·
          refine ⟨6168792460893893952848887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8225056614525191937131849 6168792460893893952848887)
          ·
            refine ⟨9253188691340840929273331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168792460893893952848887 9253188691340840929273331)
            ·
              refine ⟨13879783037011261393909997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9253188691340840929273331 13879783037011261393909997)
              ·
                refine ⟨5204918638879223022716249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13879783037011261393909997 5204918638879223022716249)
                ·
                  refine ⟨3903688979159417267037187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204918638879223022716249 3903688979159417267037187)
                  ·
                    refine ⟨5855533468739125900555781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3903688979159417267037187 5855533468739125900555781)
                    ·
                      refine ⟨1097912525388586106354209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5855533468739125900555781 1097912525388586106354209)
                      ·
                        rfl

theorem cell23_2138177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2138177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138177 prefixEnd_2138177 := by exact prefixLift 2138177
  have htrace : WordTrace (prefixWord ++ tailWord_2138177) baseStart_2138177 baseEnd_2138177 := by
    simpa [prefixWord, tailWord_2138177, baseEnd_2138177] using wordTrace_append hprefix tailTrace_2138177
  have hstable : (prefixWord ++ tailWord_2138177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138177).length < 2 ^ (prefixWord ++ tailWord_2138177).sum := by decide
  have hdescent : baseEnd_2138177 < baseStart_2138177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138197 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2138197 : Nat := 118140960795 + 2138197 * 2 ^ 59
def prefixEnd_2138197 : Nat := 4983230072969 + 3 ^ 40 * 2138197 * 2
def baseEnd_2138197 : Nat := 1097922795001676028104117

theorem tailTrace_2138197 : CollatzResearch.WordTrace tailWord_2138197 prefixEnd_2138197 1097922795001676028104117 := by
  unfold tailWord_2138197
  simp only [CollatzResearch.WordTrace]
  refine ⟨77986451434684918819644845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51990967623123279213096563 77986451434684918819644845)
  ·
    refine ⟨29244919288006844557366817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77986451434684918819644845 29244919288006844557366817)
    ·
      refine ⟨21933689466005133418025113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29244919288006844557366817 21933689466005133418025113)
      ·
        refine ⟨16450267099503850063518835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21933689466005133418025113 16450267099503850063518835)
        ·
          refine ⟨24675400649255775095278253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16450267099503850063518835 24675400649255775095278253)
          ·
            refine ⟨9253275243470915660729345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24675400649255775095278253 9253275243470915660729345)
            ·
              refine ⟨6939956432603186745547009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9253275243470915660729345 6939956432603186745547009)
              ·
                refine ⟨5204967324452390059160257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6939956432603186745547009 5204967324452390059160257)
                ·
                  refine ⟨3903725493339292544370193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204967324452390059160257 3903725493339292544370193)
                  ·
                    refine ⟨2927794120004469408277645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903725493339292544370193 2927794120004469408277645)
                    ·
                      refine ⟨1097922795001676028104117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2927794120004469408277645 1097922795001676028104117)
                      ·
                        rfl

theorem cell23_2138197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2138197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138197 prefixEnd_2138197 := by exact prefixLift 2138197
  have htrace : WordTrace (prefixWord ++ tailWord_2138197) baseStart_2138197 baseEnd_2138197 := by
    simpa [prefixWord, tailWord_2138197, baseEnd_2138197] using wordTrace_append hprefix tailTrace_2138197
  have hstable : (prefixWord ++ tailWord_2138197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138197).length < 2 ^ (prefixWord ++ tailWord_2138197).sum := by decide
  have hdescent : baseEnd_2138197 < baseStart_2138197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138200 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 6]
def baseStart_2138200 : Nat := 118140960795 + 2138200 * 2 ^ 59
def prefixEnd_2138200 : Nat := 4983230072969 + 3 ^ 40 * 2138200 * 2
def baseEnd_2138200 : Nat := 121991592827071057374067

theorem tailTrace_2138200 : CollatzResearch.WordTrace tailWord_2138200 prefixEnd_2138200 121991592827071057374067 := by
  unfold tailWord_2138200
  simp only [CollatzResearch.WordTrace]
  refine ⟨38993280426837025166002027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51991040569116033554669369 38993280426837025166002027)
  ·
    refine ⟨58489920640255537749003041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38993280426837025166002027 58489920640255537749003041)
    ·
      refine ⟨43867440480191653311752281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58489920640255537749003041 43867440480191653311752281)
      ·
        refine ⟨32900580360143739983814211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43867440480191653311752281 32900580360143739983814211)
        ·
          refine ⟨49350870540215609975721317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32900580360143739983814211 49350870540215609975721317)
          ·
            refine ⟨9253288226290426870447747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49350870540215609975721317 9253288226290426870447747)
            ·
              refine ⟨13879932339435640305671621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9253288226290426870447747 13879932339435640305671621)
              ·
                refine ⟨2602487313644182557313429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13879932339435640305671621 2602487313644182557313429)
                ·
                  refine ⟨121991592827071057374067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2602487313644182557313429 121991592827071057374067)
                  ·
                    rfl

theorem cell23_2138200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 6].length) (baseStart_2138200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138200 prefixEnd_2138200 := by exact prefixLift 2138200
  have htrace : WordTrace (prefixWord ++ tailWord_2138200) baseStart_2138200 baseEnd_2138200 := by
    simpa [prefixWord, tailWord_2138200, baseEnd_2138200] using wordTrace_append hprefix tailTrace_2138200
  have hstable : (prefixWord ++ tailWord_2138200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138200).length < 2 ^ (prefixWord ++ tailWord_2138200).sum := by decide
  have hdescent : baseEnd_2138200 < baseStart_2138200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138290 : List Nat := [3, 2, 1, 1, 1, 3, 3, 9]
def baseStart_2138290 : Nat := 118140960795 + 2138290 * 2 ^ 59
def prefixEnd_2138290 : Nat := 4983230072969 + 3 ^ 40 * 2138290 * 2
def baseEnd_2138290 : Nat := 40665575877872006083007

theorem tailTrace_2138290 : CollatzResearch.WordTrace tailWord_2138290 prefixEnd_2138290 40665575877872006083007 := by
  unfold tailWord_2138290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19497460855836998925695081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51993228948898663801853549 19497460855836998925695081)
  ·
    refine ⟨14623095641877749194271311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19497460855836998925695081 14623095641877749194271311)
    ·
      refine ⟨21934643462816623791406967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14623095641877749194271311 21934643462816623791406967)
      ·
        refine ⟨32901965194224935687110451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21934643462816623791406967 32901965194224935687110451)
        ·
          refine ⟨49352947791337403530665677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32901965194224935687110451 49352947791337403530665677)
          ·
            refine ⟨18507355421751526323999629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49352947791337403530665677 18507355421751526323999629)
            ·
              refine ⟨6940258283156822371499861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18507355421751526323999629 6940258283156822371499861)
              ·
                refine ⟨40665575877872006083007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6940258283156822371499861 40665575877872006083007)
                ·
                  rfl

theorem cell23_2138290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_2138290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138290 prefixEnd_2138290 := by exact prefixLift 2138290
  have htrace : WordTrace (prefixWord ++ tailWord_2138290) baseStart_2138290 baseEnd_2138290 := by
    simpa [prefixWord, tailWord_2138290, baseEnd_2138290] using wordTrace_append hprefix tailTrace_2138290
  have hstable : (prefixWord ++ tailWord_2138290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138290).length < 2 ^ (prefixWord ++ tailWord_2138290).sum := by decide
  have hdescent : baseEnd_2138290 < baseStart_2138290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138304 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3]
def baseStart_2138304 : Nat := 118140960795 + 2138304 * 2 ^ 59
def prefixEnd_2138304 : Nat := 4983230072969 + 3 ^ 40 * 2138304 * 2
def baseEnd_2138304 : Nat := 1097977737431707109466125

theorem tailTrace_2138304 : CollatzResearch.WordTrace tailWord_2138304 prefixEnd_2138304 1097977737431707109466125 := by
  unfold tailWord_2138304
  simp only [CollatzResearch.WordTrace]
  refine ⟨38995177022648638046894983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51993569363531517395859977 38995177022648638046894983)
  ·
    refine ⟨58492765533972957070342475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38995177022648638046894983 58492765533972957070342475)
    ·
      refine ⟨87739148300959435605513713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58492765533972957070342475 87739148300959435605513713)
      ·
        refine ⟨65804361225719576704135285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87739148300959435605513713 65804361225719576704135285)
        ·
          refine ⟨6169158864911210316012683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65804361225719576704135285 6169158864911210316012683)
          ·
            refine ⟨9253738297366815474019025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6169158864911210316012683 9253738297366815474019025)
            ·
              refine ⟨6940303723025111605514269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9253738297366815474019025 6940303723025111605514269)
              ·
                refine ⟨2602613896134416852067851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6940303723025111605514269 2602613896134416852067851)
                ·
                  refine ⟨3903920844201625278101777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602613896134416852067851 3903920844201625278101777)
                  ·
                    refine ⟨2927940633151218958576333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3903920844201625278101777 2927940633151218958576333)
                    ·
                      refine ⟨1097977737431707109466125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2927940633151218958576333 1097977737431707109466125)
                      ·
                        rfl

theorem cell23_2138304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_2138304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138304 prefixEnd_2138304 := by exact prefixLift 2138304
  have htrace : WordTrace (prefixWord ++ tailWord_2138304) baseStart_2138304 baseEnd_2138304 := by
    simpa [prefixWord, tailWord_2138304, baseEnd_2138304] using wordTrace_append hprefix tailTrace_2138304
  have hstable : (prefixWord ++ tailWord_2138304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138304).length < 2 ^ (prefixWord ++ tailWord_2138304).sum := by decide
  have hdescent : baseEnd_2138304 < baseStart_2138304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138318 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_2138318 : Nat := 118140960795 + 2138318 * 2 ^ 59
def prefixEnd_2138318 : Nat := 4983230072969 + 3 ^ 40 * 2138318 * 2
def baseEnd_2138318 : Nat := 1097984926160870054691061

theorem tailTrace_2138318 : CollatzResearch.WordTrace tailWord_2138318 prefixEnd_2138318 1097984926160870054691061 := by
  unfold tailWord_2138318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748858083405819560599951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51993909778164370989866405 9748858083405819560599951)
  ·
    refine ⟨14623287125108729340899927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9748858083405819560599951 14623287125108729340899927)
    ·
      refine ⟨21934930687663094011349891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14623287125108729340899927 21934930687663094011349891)
      ·
        refine ⟨32902396031494641017024837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21934930687663094011349891 32902396031494641017024837)
        ·
          refine ⟨6169199255905245190692157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32902396031494641017024837 6169199255905245190692157)
          ·
            refine ⟨2313449720964466946509559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6169199255905245190692157 2313449720964466946509559)
            ·
              refine ⟨3470174581446700419764339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313449720964466946509559 3470174581446700419764339)
              ·
                refine ⟨5205261872170050629646509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470174581446700419764339 5205261872170050629646509)
                ·
                  refine ⟨1951973202063768986117441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5205261872170050629646509 1951973202063768986117441)
                  ·
                    refine ⟨1463979901547826739588081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1951973202063768986117441 1463979901547826739588081)
                    ·
                      refine ⟨1097984926160870054691061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463979901547826739588081 1097984926160870054691061)
                      ·
                        rfl

theorem cell23_2138318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_2138318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138318 prefixEnd_2138318 := by exact prefixLift 2138318
  have htrace : WordTrace (prefixWord ++ tailWord_2138318) baseStart_2138318 baseEnd_2138318 := by
    simpa [prefixWord, tailWord_2138318, baseEnd_2138318] using wordTrace_append hprefix tailTrace_2138318
  have hstable : (prefixWord ++ tailWord_2138318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138318).length < 2 ^ (prefixWord ++ tailWord_2138318).sum := by decide
  have hdescent : baseEnd_2138318 < baseStart_2138318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138327 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 7, 2]
def baseStart_2138327 : Nat := 118140960795 + 2138327 * 2 ^ 59
def prefixEnd_2138327 : Nat := 4983230072969 + 3 ^ 40 * 2138327 * 2
def baseEnd_2138327 : Nat := 1097989547486760519478519

theorem tailTrace_2138327 : CollatzResearch.WordTrace tailWord_2138327 prefixEnd_2138327 1097989547486760519478519 := by
  unfold tailWord_2138327
  simp only [CollatzResearch.WordTrace]
  refine ⟨77991192924213951021877235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51994128616142634014584823 77991192924213951021877235)
  ·
    refine ⟨116986789386320926532815853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77991192924213951021877235 116986789386320926532815853)
    ·
      refine ⟨43870046019870347449805945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116986789386320926532815853 43870046019870347449805945)
      ·
        refine ⟨32902534514902760587354459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43870046019870347449805945 32902534514902760587354459)
        ·
          refine ⟨49353801772354140881031689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32902534514902760587354459 49353801772354140881031689)
          ·
            refine ⟨37015351329265605660773767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49353801772354140881031689 37015351329265605660773767)
            ·
              refine ⟨55523026993898408491160651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37015351329265605660773767 55523026993898408491160651)
              ·
                refine ⟨83284540490847612736740977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55523026993898408491160651 83284540490847612736740977)
                ·
                  refine ⟨62463405368135709552555733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83284540490847612736740977 62463405368135709552555733)
                  ·
                    refine ⟨1463986063315680692638025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 62463405368135709552555733 1463986063315680692638025)
                    ·
                      refine ⟨1097989547486760519478519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1463986063315680692638025 1097989547486760519478519)
                      ·
                        rfl

theorem cell23_2138327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_2138327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138327 prefixEnd_2138327 := by exact prefixLift 2138327
  have htrace : WordTrace (prefixWord ++ tailWord_2138327) baseStart_2138327 baseEnd_2138327 := by
    simpa [prefixWord, tailWord_2138327, baseEnd_2138327] using wordTrace_append hprefix tailTrace_2138327
  have hstable : (prefixWord ++ tailWord_2138327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138327).length < 2 ^ (prefixWord ++ tailWord_2138327).sum := by decide
  have hdescent : baseEnd_2138327 < baseStart_2138327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138340 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2138340 : Nat := 118140960795 + 2138340 * 2 ^ 59
def prefixEnd_2138340 : Nat := 4983230072969 + 3 ^ 40 * 2138340 * 2
def baseEnd_2138340 : Nat := 1097996222735268968615959

theorem tailTrace_2138340 : CollatzResearch.WordTrace tailWord_2138340 prefixEnd_2138340 1097996222735268968615959 := by
  unfold tailWord_2138340
  simp only [CollatzResearch.WordTrace]
  refine ⟨38995833536583427121050237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51994444715444569494733649 38995833536583427121050237)
  ·
    refine ⟨14623437576218785170393839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38995833536583427121050237 14623437576218785170393839)
    ·
      refine ⟨21935156364328177755590759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14623437576218785170393839 21935156364328177755590759)
      ·
        refine ⟨32902734546492266633386139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21935156364328177755590759 32902734546492266633386139)
        ·
          refine ⟨49354101819738399950079209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32902734546492266633386139 49354101819738399950079209)
          ·
            refine ⟨37015576364803799962559407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49354101819738399950079209 37015576364803799962559407)
            ·
              refine ⟨55523364547205699943839111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37015576364803799962559407 55523364547205699943839111)
              ·
                refine ⟨83285046820808549915758667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55523364547205699943839111 83285046820808549915758667)
                ·
                  refine ⟨124927570231212824873638001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83285046820808549915758667 124927570231212824873638001)
                  ·
                    refine ⟨93695677673409618655228501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124927570231212824873638001 93695677673409618655228501)
                    ·
                      refine ⟨1097996222735268968615959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 93695677673409618655228501 1097996222735268968615959)
                      ·
                        rfl

theorem cell23_2138340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2138340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138340 prefixEnd_2138340 := by exact prefixLift 2138340
  have htrace : WordTrace (prefixWord ++ tailWord_2138340) baseStart_2138340 baseEnd_2138340 := by
    simpa [prefixWord, tailWord_2138340, baseEnd_2138340] using wordTrace_append hprefix tailTrace_2138340
  have hstable : (prefixWord ++ tailWord_2138340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138340).length < 2 ^ (prefixWord ++ tailWord_2138340).sum := by decide
  have hdescent : baseEnd_2138340 < baseStart_2138340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138377 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_2138377 : Nat := 118140960795 + 2138377 * 2 ^ 59
def prefixEnd_2138377 : Nat := 4983230072969 + 3 ^ 40 * 2138377 * 2
def baseEnd_2138377 : Nat := 1098015221519485323853289

theorem tailTrace_2138377 : CollatzResearch.WordTrace tailWord_2138377 prefixEnd_2138377 1098015221519485323853289 := by
  unfold tailWord_2138377
  simp only [CollatzResearch.WordTrace]
  refine ⟨77993016574032809561197385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51995344382688539707464923 77993016574032809561197385)
  ·
    refine ⟨58494762430524607170898039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77993016574032809561197385 58494762430524607170898039)
    ·
      refine ⟨87742143645786910756347059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58494762430524607170898039 87742143645786910756347059)
      ·
        refine ⟨131613215468680366134520589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87742143645786910756347059 131613215468680366134520589)
        ·
          refine ⟨49354955800755137300445221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131613215468680366134520589 49354955800755137300445221)
          ·
            refine ⟨9254054212641588243833479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49354955800755137300445221 9254054212641588243833479)
            ·
              refine ⟨13881081318962382365750219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9254054212641588243833479 13881081318962382365750219)
              ·
                refine ⟨20821621978443573548625329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13881081318962382365750219 20821621978443573548625329)
                ·
                  refine ⟨15616216483832680161468997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20821621978443573548625329 15616216483832680161468997)
                  ·
                    refine ⟨2928040590718627530275437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15616216483832680161468997 2928040590718627530275437)
                    ·
                      refine ⟨1098015221519485323853289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2928040590718627530275437 1098015221519485323853289)
                      ·
                        rfl

theorem cell23_2138377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_2138377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138377 prefixEnd_2138377 := by exact prefixLift 2138377
  have htrace : WordTrace (prefixWord ++ tailWord_2138377) baseStart_2138377 baseEnd_2138377 := by
    simpa [prefixWord, tailWord_2138377, baseEnd_2138377] using wordTrace_append hprefix tailTrace_2138377
  have hstable : (prefixWord ++ tailWord_2138377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138377).length < 2 ^ (prefixWord ++ tailWord_2138377).sum := by decide
  have hdescent : baseEnd_2138377 < baseStart_2138377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138391 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 1, 4, 2]
def baseStart_2138391 : Nat := 118140960795 + 2138391 * 2 ^ 59
def prefixEnd_2138391 : Nat := 4983230072969 + 3 ^ 40 * 2138391 * 2
def baseEnd_2138391 : Nat := 1098022410248648269078225

theorem tailTrace_2138391 : CollatzResearch.WordTrace tailWord_2138391 prefixEnd_2138391 1098022410248648269078225 := by
  unfold tailWord_2138391
  simp only [CollatzResearch.WordTrace]
  refine ⟨77993527195982089952207027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51995684797321393301471351 77993527195982089952207027)
  ·
    refine ⟨116990290793973134928310541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77993527195982089952207027 116990290793973134928310541)
    ·
      refine ⟨43871359047739925598116453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116990290793973134928310541 43871359047739925598116453)
      ·
        refine ⟨8225879821451236049646835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43871359047739925598116453 8225879821451236049646835)
        ·
          refine ⟨12338819732176854074470253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8225879821451236049646835 12338819732176854074470253)
          ·
            refine ⟨4627057399566320277926345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12338819732176854074470253 4627057399566320277926345)
            ·
              refine ⟨3470293049674740208444759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4627057399566320277926345 3470293049674740208444759)
              ·
                refine ⟨5205439574512110312667139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470293049674740208444759 5205439574512110312667139)
                ·
                  refine ⟨7808159361768165469000709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205439574512110312667139 7808159361768165469000709)
                  ·
                    refine ⟨1464029880331531025437633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7808159361768165469000709 1464029880331531025437633)
                    ·
                      refine ⟨1098022410248648269078225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464029880331531025437633 1098022410248648269078225)
                      ·
                        rfl

theorem cell23_2138391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_2138391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138391 prefixEnd_2138391 := by exact prefixLift 2138391
  have htrace : WordTrace (prefixWord ++ tailWord_2138391) baseStart_2138391 baseEnd_2138391 := by
    simpa [prefixWord, tailWord_2138391, baseEnd_2138391] using wordTrace_append hprefix tailTrace_2138391
  have hstable : (prefixWord ++ tailWord_2138391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138391).length < 2 ^ (prefixWord ++ tailWord_2138391).sum := by decide
  have hdescent : baseEnd_2138391 < baseStart_2138391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138425 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2138425 : Nat := 118140960795 + 2138425 * 2 ^ 59
def prefixEnd_2138425 : Nat := 4983230072969 + 3 ^ 40 * 2138425 * 2
def baseEnd_2138425 : Nat := 1098039868590901136053069

theorem tailTrace_2138425 : CollatzResearch.WordTrace tailWord_2138425 prefixEnd_2138425 1098039868590901136053069 := by
  unfold tailWord_2138425
  simp only [CollatzResearch.WordTrace]
  refine ⟨77994767277858913758944729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51996511518572609172629819 77994767277858913758944729)
  ·
    refine ⟨58496075458394185319208547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77994767277858913758944729 58496075458394185319208547)
    ·
      refine ⟨87744113187591277978812821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58496075458394185319208547 87744113187591277978812821)
      ·
        refine ⟨4113005305668341155256851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87744113187591277978812821 4113005305668341155256851)
        ·
          refine ⟨6169507958502511732885277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113005305668341155256851 6169507958502511732885277)
          ·
            refine ⟨2313565484438441899831979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6169507958502511732885277 2313565484438441899831979)
            ·
              refine ⟨3470348226657662849747969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313565484438441899831979 3470348226657662849747969)
              ·
                refine ⟨2602761169993247137310977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3470348226657662849747969 2602761169993247137310977)
                ·
                  refine ⟨1952070877494935352983233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2602761169993247137310977 1952070877494935352983233)
                  ·
                    refine ⟨1464053158121201514737425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1952070877494935352983233 1464053158121201514737425)
                    ·
                      refine ⟨1098039868590901136053069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464053158121201514737425 1098039868590901136053069)
                      ·
                        rfl

theorem cell23_2138425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2138425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138425 prefixEnd_2138425 := by exact prefixLift 2138425
  have htrace : WordTrace (prefixWord ++ tailWord_2138425) baseStart_2138425 baseEnd_2138425 := by
    simpa [prefixWord, tailWord_2138425, baseEnd_2138425] using wordTrace_append hprefix tailTrace_2138425
  have hstable : (prefixWord ++ tailWord_2138425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138425).length < 2 ^ (prefixWord ++ tailWord_2138425).sum := by decide
  have hdescent : baseEnd_2138425 < baseStart_2138425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138447 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_2138447 : Nat := 118140960795 + 2138447 * 2 ^ 59
def prefixEnd_2138447 : Nat := 4983230072969 + 3 ^ 40 * 2138447 * 2
def baseEnd_2138447 : Nat := 1098051165165300049977967

theorem tailTrace_2138447 : CollatzResearch.WordTrace tailWord_2138447 prefixEnd_2138447 1098051165165300049977967 := by
  unfold tailWord_2138447
  simp only [CollatzResearch.WordTrace]
  refine ⟨77995569683779211516245595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51997046455852807677497063 77995569683779211516245595)
  ·
    refine ⟨116993354525668817274368393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77995569683779211516245595 116993354525668817274368393)
    ·
      refine ⟨87745015894251612955776295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116993354525668817274368393 87745015894251612955776295)
      ·
        refine ⟨131617523841377419433664443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87745015894251612955776295 131617523841377419433664443)
        ·
          refine ⟨197426285762066129150496665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131617523841377419433664443 197426285762066129150496665)
          ·
            refine ⟨148069714321549596862872499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197426285762066129150496665 148069714321549596862872499)
            ·
              refine ⟨222104571482324395294308749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148069714321549596862872499 222104571482324395294308749)
              ·
                refine ⟨83289214305871648235365781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222104571482324395294308749 83289214305871648235365781)
                ·
                  refine ⟨3904181920587733511032771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83289214305871648235365781 3904181920587733511032771)
                  ·
                    refine ⟨5856272880881600266549157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904181920587733511032771 5856272880881600266549157)
                    ·
                      refine ⟨1098051165165300049977967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5856272880881600266549157 1098051165165300049977967)
                      ·
                        rfl

theorem cell23_2138447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_2138447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138447 prefixEnd_2138447 := by exact prefixLift 2138447
  have htrace : WordTrace (prefixWord ++ tailWord_2138447) baseStart_2138447 baseEnd_2138447 := by
    simpa [prefixWord, tailWord_2138447, baseEnd_2138447] using wordTrace_append hprefix tailTrace_2138447
  have hstable : (prefixWord ++ tailWord_2138447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138447).length < 2 ^ (prefixWord ++ tailWord_2138447).sum := by decide
  have hdescent : baseEnd_2138447 < baseStart_2138447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138491 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 3, 4]
def baseStart_2138491 : Nat := 118140960795 + 2138491 * 2 ^ 59
def prefixEnd_2138491 : Nat := 4983230072969 + 3 ^ 40 * 2138491 * 2
def baseEnd_2138491 : Nat := 366024586104699292609255

theorem tailTrace_2138491 : CollatzResearch.WordTrace tailWord_2138491 prefixEnd_2138491 366024586104699292609255 := by
  unfold tailWord_2138491
  simp only [CollatzResearch.WordTrace]
  refine ⟨77997174495619807030847327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51998116330413204687231551 77997174495619807030847327)
  ·
    refine ⟨116995761743429710546270991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77997174495619807030847327 116995761743429710546270991)
    ·
      refine ⟨175493642615144565819406487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116995761743429710546270991 175493642615144565819406487)
      ·
        refine ⟨263240463922716848729109731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175493642615144565819406487 263240463922716848729109731)
        ·
          refine ⟨394860695884075273093664597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263240463922716848729109731 394860695884075273093664597)
          ·
            refine ⟨2313636889945753553283191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 394860695884075273093664597 2313636889945753553283191)
            ·
              refine ⟨3470455334918630329924787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313636889945753553283191 3470455334918630329924787)
              ·
                refine ⟨5205683002377945494887181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470455334918630329924787 5205683002377945494887181)
                ·
                  refine ⟨1952131125891729560582693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5205683002377945494887181 1952131125891729560582693)
                  ·
                    refine ⟨366024586104699292609255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1952131125891729560582693 366024586104699292609255)
                    ·
                      rfl

theorem cell23_2138491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 4].length) (baseStart_2138491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138491 prefixEnd_2138491 := by exact prefixLift 2138491
  have htrace : WordTrace (prefixWord ++ tailWord_2138491) baseStart_2138491 baseEnd_2138491 := by
    simpa [prefixWord, tailWord_2138491, baseEnd_2138491] using wordTrace_append hprefix tailTrace_2138491
  have hstable : (prefixWord ++ tailWord_2138491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138491).length < 2 ^ (prefixWord ++ tailWord_2138491).sum := by decide
  have hdescent : baseEnd_2138491 < baseStart_2138491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138504 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 6]
def baseStart_2138504 : Nat := 118140960795 + 2138504 * 2 ^ 59
def prefixEnd_2138504 : Nat := 4983230072969 + 3 ^ 40 * 2138504 * 2
def baseEnd_2138504 : Nat := 122008937062511814107245

theorem tailTrace_2138504 : CollatzResearch.WordTrace tailWord_2138504 prefixEnd_2138504 122008937062511814107245 := by
  unfold tailWord_2138504
  simp only [CollatzResearch.WordTrace]
  refine ⟨38998824322286355125535283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51998432429715140167380377 38998824322286355125535283)
  ·
    refine ⟨58498236483429532688302925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38998824322286355125535283 58498236483429532688302925)
    ·
      refine ⟨21936838681286074758113597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58498236483429532688302925 21936838681286074758113597)
      ·
        refine ⟨8226314505482278034292599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21936838681286074758113597 8226314505482278034292599)
        ·
          refine ⟨12339471758223417051438899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8226314505482278034292599 12339471758223417051438899)
          ·
            refine ⟨18509207637335125577158349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12339471758223417051438899 18509207637335125577158349)
            ·
              refine ⟨6940952864000672091434381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18509207637335125577158349 6940952864000672091434381)
              ·
                refine ⟨2602857324000252034287893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6940952864000672091434381 2602857324000252034287893)
                ·
                  refine ⟨122008937062511814107245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2602857324000252034287893 122008937062511814107245)
                  ·
                    rfl

theorem cell23_2138504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 6].length) (baseStart_2138504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138504 prefixEnd_2138504 := by exact prefixLift 2138504
  have htrace : WordTrace (prefixWord ++ tailWord_2138504) baseStart_2138504 baseEnd_2138504 := by
    simpa [prefixWord, tailWord_2138504, baseEnd_2138504] using wordTrace_append hprefix tailTrace_2138504
  have hstable : (prefixWord ++ tailWord_2138504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138504).length < 2 ^ (prefixWord ++ tailWord_2138504).sum := by decide
  have hdescent : baseEnd_2138504 < baseStart_2138504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138577 : List Nat := [1, 2, 2, 1, 2, 1, 1, 13]
def baseStart_2138577 : Nat := 118140960795 + 2138577 * 2 ^ 59
def prefixEnd_2138577 : Nat := 4983230072969 + 3 ^ 40 * 2138577 * 2
def baseEnd_2138577 : Nat := 40671033987051279309347

theorem tailTrace_2138577 : CollatzResearch.WordTrace tailWord_2138577 prefixEnd_2138577 40671033987051279309347 := by
  unfold tailWord_2138577
  simp only [CollatzResearch.WordTrace]
  refine ⟨78000311173308243718477985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52000207448872162478985323 78000311173308243718477985)
  ·
    refine ⟨58500233379981182788858489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78000311173308243718477985 58500233379981182788858489)
    ·
      refine ⟨43875175034985887091643867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58500233379981182788858489 43875175034985887091643867)
      ·
        refine ⟨65812762552478830637465801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43875175034985887091643867 65812762552478830637465801)
        ·
          refine ⟨49359571914359122978099351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65812762552478830637465801 49359571914359122978099351)
          ·
            refine ⟨74039357871538684467149027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49359571914359122978099351 74039357871538684467149027)
            ·
              refine ⟨111059036807308026700723541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74039357871538684467149027 111059036807308026700723541)
              ·
                refine ⟨40671033987051279309347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 111059036807308026700723541 40671033987051279309347)
                ·
                  rfl

theorem cell23_2138577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 13].length) (baseStart_2138577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138577 prefixEnd_2138577 := by exact prefixLift 2138577
  have htrace : WordTrace (prefixWord ++ tailWord_2138577) baseStart_2138577 baseEnd_2138577 := by
    simpa [prefixWord, tailWord_2138577, baseEnd_2138577] using wordTrace_append hprefix tailTrace_2138577
  have hstable : (prefixWord ++ tailWord_2138577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138577).length < 2 ^ (prefixWord ++ tailWord_2138577).sum := by decide
  have hdescent : baseEnd_2138577 < baseStart_2138577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138582 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2138582 : Nat := 118140960795 + 2138582 * 2 ^ 59
def prefixEnd_2138582 : Nat := 4983230072969 + 3 ^ 40 * 2138582 * 2
def baseEnd_2138582 : Nat := 1098120485053657021789847

theorem tailTrace_2138582 : CollatzResearch.WordTrace tailWord_2138582 prefixEnd_2138582 1098120485053657021789847 := by
  unfold tailWord_2138582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875030846143133098275625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52000329025526753048273333 4875030846143133098275625)
  ·
    refine ⟨3656273134607349823706719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4875030846143133098275625 3656273134607349823706719)
    ·
      refine ⟨5484409701911024735560079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3656273134607349823706719 5484409701911024735560079)
      ·
        refine ⟨8226614552866537103340119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5484409701911024735560079 8226614552866537103340119)
        ·
          refine ⟨12339921829299805655010179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8226614552866537103340119 12339921829299805655010179)
          ·
            refine ⟨18509882743949708482515269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12339921829299805655010179 18509882743949708482515269)
            ·
              refine ⟨3470603014490570340471613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18509882743949708482515269 3470603014490570340471613)
              ·
                refine ⟨1301476130433963877676855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3470603014490570340471613 1301476130433963877676855)
                ·
                  refine ⟨1952214195650945816515283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301476130433963877676855 1952214195650945816515283)
                  ·
                    refine ⟨2928321293476418724772925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1952214195650945816515283 2928321293476418724772925)
                    ·
                      refine ⟨1098120485053657021789847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2928321293476418724772925 1098120485053657021789847)
                      ·
                        rfl

theorem cell23_2138582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2138582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138582 prefixEnd_2138582 := by exact prefixLift 2138582
  have htrace : WordTrace (prefixWord ++ tailWord_2138582) baseStart_2138582 baseEnd_2138582 := by
    simpa [prefixWord, tailWord_2138582, baseEnd_2138582] using wordTrace_append hprefix tailTrace_2138582
  have hstable : (prefixWord ++ tailWord_2138582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138582).length < 2 ^ (prefixWord ++ tailWord_2138582).sum := by decide
  have hdescent : baseEnd_2138582 < baseStart_2138582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138605 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2138605 : Nat := 118140960795 + 2138605 * 2 ^ 59
def prefixEnd_2138605 : Nat := 4983230072969 + 3 ^ 40 * 2138605 * 2
def baseEnd_2138605 : Nat := 1098132295108710431802241

theorem tailTrace_2138605 : CollatzResearch.WordTrace tailWord_2138605 prefixEnd_2138605 1098132295108710431802241 := by
  unfold tailWord_2138605
  simp only [CollatzResearch.WordTrace]
  refine ⟨78001332417206804500497269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52000888278137869666998179 78001332417206804500497269)
  ·
    refine ⟨7312624914113137921921619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78001332417206804500497269 7312624914113137921921619)
    ·
      refine ⟨10968937371169706882882429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7312624914113137921921619 10968937371169706882882429)
      ·
        refine ⟨4113351514188640081080911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10968937371169706882882429 4113351514188640081080911)
        ·
          refine ⟨6170027271282960121621367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113351514188640081080911 6170027271282960121621367)
          ·
            refine ⟨9255040906924440182432051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170027271282960121621367 9255040906924440182432051)
            ·
              refine ⟨13882561360386660273648077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9255040906924440182432051 13882561360386660273648077)
              ·
                refine ⟨5205960510144997602618029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13882561360386660273648077 5205960510144997602618029)
                ·
                  refine ⟨1952235191304374100981761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5205960510144997602618029 1952235191304374100981761)
                  ·
                    refine ⟨1464176393478280575736321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1952235191304374100981761 1464176393478280575736321)
                    ·
                      refine ⟨1098132295108710431802241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464176393478280575736321 1098132295108710431802241)
                      ·
                        rfl

theorem cell23_2138605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2138605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138605 prefixEnd_2138605 := by exact prefixLift 2138605
  have htrace : WordTrace (prefixWord ++ tailWord_2138605) baseStart_2138605 baseEnd_2138605 := by
    simpa [prefixWord, tailWord_2138605, baseEnd_2138605] using wordTrace_append hprefix tailTrace_2138605
  have hstable : (prefixWord ++ tailWord_2138605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138605).length < 2 ^ (prefixWord ++ tailWord_2138605).sum := by decide
  have hdescent : baseEnd_2138605 < baseStart_2138605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138628 : List Nat := [2, 3, 2, 3, 1, 3, 2, 7]
def baseStart_2138628 : Nat := 118140960795 + 2138628 * 2 ^ 59
def prefixEnd_2138628 : Nat := 4983230072969 + 3 ^ 40 * 2138628 * 2
def baseEnd_2138628 : Nat := 40672003894954216363505

theorem tailTrace_2138628 : CollatzResearch.WordTrace tailWord_2138628 prefixEnd_2138628 40672003894954216363505 := by
  unfold tailWord_2138628
  simp only [CollatzResearch.WordTrace]
  refine ⟨39001085648061739714292269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52001447530748986285723025 39001085648061739714292269)
  ·
    refine ⟨14625407118023152392859601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39001085648061739714292269 14625407118023152392859601)
    ·
      refine ⟨10969055338517364294644701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14625407118023152392859601 10969055338517364294644701)
      ·
        refine ⟨4113395751944011610491763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10969055338517364294644701 4113395751944011610491763)
        ·
          refine ⟨6170093627916017415737645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113395751944011610491763 6170093627916017415737645)
          ·
            refine ⟨2313785110468506530901617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6170093627916017415737645 2313785110468506530901617)
            ·
              refine ⟨1735338832851379898176213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2313785110468506530901617 1735338832851379898176213)
              ·
                refine ⟨40672003894954216363505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1735338832851379898176213 40672003894954216363505)
                ·
                  rfl

theorem cell23_2138628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 7].length) (baseStart_2138628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138628 prefixEnd_2138628 := by exact prefixLift 2138628
  have htrace : WordTrace (prefixWord ++ tailWord_2138628) baseStart_2138628 baseEnd_2138628 := by
    simpa [prefixWord, tailWord_2138628, baseEnd_2138628] using wordTrace_append hprefix tailTrace_2138628
  have hstable : (prefixWord ++ tailWord_2138628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138628).length < 2 ^ (prefixWord ++ tailWord_2138628).sum := by decide
  have hdescent : baseEnd_2138628 < baseStart_2138628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138634 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2138634 : Nat := 118140960795 + 2138634 * 2 ^ 59
def prefixEnd_2138634 : Nat := 4983230072969 + 3 ^ 40 * 2138634 * 2
def baseEnd_2138634 : Nat := 1098147186047690818339607

theorem tailTrace_2138634 : CollatzResearch.WordTrace tailWord_2138634 prefixEnd_2138634 1098147186047690818339607 := by
  unfold tailWord_2138634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19500597533525435613325739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52001593422734494968868637 19500597533525435613325739)
  ·
    refine ⟨29250896300288153419988609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19500597533525435613325739 29250896300288153419988609)
    ·
      refine ⟨21938172225216115064991457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29250896300288153419988609 21938172225216115064991457)
      ·
        refine ⟨16453629168912086298743593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21938172225216115064991457 16453629168912086298743593)
        ·
          refine ⟨12340221876684064724057695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16453629168912086298743593 12340221876684064724057695)
          ·
            refine ⟨18510332815026097086086543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12340221876684064724057695 18510332815026097086086543)
            ·
              refine ⟨27765499222539145629129815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18510332815026097086086543 27765499222539145629129815)
              ·
                refine ⟨41648248833808718443694723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27765499222539145629129815 41648248833808718443694723)
                ·
                  refine ⟨62472373250713077665542085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41648248833808718443694723 62472373250713077665542085)
                  ·
                    refine ⟨11713569984508702062289141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62472373250713077665542085 11713569984508702062289141)
                    ·
                      refine ⟨1098147186047690818339607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11713569984508702062289141 1098147186047690818339607)
                      ·
                        rfl

theorem cell23_2138634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2138634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138634 prefixEnd_2138634 := by exact prefixLift 2138634
  have htrace : WordTrace (prefixWord ++ tailWord_2138634) baseStart_2138634 baseEnd_2138634 := by
    simpa [prefixWord, tailWord_2138634, baseEnd_2138634] using wordTrace_append hprefix tailTrace_2138634
  have hstable : (prefixWord ++ tailWord_2138634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138634).length < 2 ^ (prefixWord ++ tailWord_2138634).sum := by decide
  have hdescent : baseEnd_2138634 < baseStart_2138634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138638 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2138638 : Nat := 118140960795 + 2138638 * 2 ^ 59
def prefixEnd_2138638 : Nat := 4983230072969 + 3 ^ 40 * 2138638 * 2
def baseEnd_2138638 : Nat := 1098149239970308802689589

theorem tailTrace_2138638 : CollatzResearch.WordTrace tailWord_2138638 prefixEnd_2138638 1098149239970308802689589 := by
  unfold tailWord_2138638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750317003260906392056071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52001690684058167424299045 9750317003260906392056071)
  ·
    refine ⟨14625475504891359588084107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9750317003260906392056071 14625475504891359588084107)
    ·
      refine ⟨21938213257337039382126161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14625475504891359588084107 21938213257337039382126161)
      ·
        refine ⟨16453659943002779536594621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21938213257337039382126161 16453659943002779536594621)
        ·
          refine ⟨6170122478626042326222983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16453659943002779536594621 6170122478626042326222983)
          ·
            refine ⟨9255183717939063489334475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170122478626042326222983 9255183717939063489334475)
            ·
              refine ⟨13882775576908595234001713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9255183717939063489334475 13882775576908595234001713)
              ·
                refine ⟨10412081682681446425501285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13882775576908595234001713 10412081682681446425501285)
                ·
                  refine ⟨1952265315502771204781491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10412081682681446425501285 1952265315502771204781491)
                  ·
                    refine ⟨2928397973254156807172237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1952265315502771204781491 2928397973254156807172237)
                    ·
                      refine ⟨1098149239970308802689589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2928397973254156807172237 1098149239970308802689589)
                      ·
                        rfl

theorem cell23_2138638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2138638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138638 prefixEnd_2138638 := by exact prefixLift 2138638
  have htrace : WordTrace (prefixWord ++ tailWord_2138638) baseStart_2138638 baseEnd_2138638 := by
    simpa [prefixWord, tailWord_2138638, baseEnd_2138638] using wordTrace_append hprefix tailTrace_2138638
  have hstable : (prefixWord ++ tailWord_2138638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138638).length < 2 ^ (prefixWord ++ tailWord_2138638).sum := by decide
  have hdescent : baseEnd_2138638 < baseStart_2138638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138711 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_2138711 : Nat := 118140960795 + 2138711 * 2 ^ 59
def prefixEnd_2138711 : Nat := 4983230072969 + 3 ^ 40 * 2138711 * 2
def baseEnd_2138711 : Nat := 1098186724058087017076753

theorem tailTrace_2138711 : CollatzResearch.WordTrace tailWord_2138711 prefixEnd_2138711 1098186724058087017076753 := by
  unfold tailWord_2138711
  simp only [CollatzResearch.WordTrace]
  refine ⟨78005198554822784603855987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52003465703215189735903991 78005198554822784603855987)
  ·
    refine ⟨117007797832234176905783981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78005198554822784603855987 117007797832234176905783981)
    ·
      refine ⟨43877924187087816339668993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117007797832234176905783981 43877924187087816339668993)
      ·
        refine ⟨32908443140315862254751745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43877924187087816339668993 32908443140315862254751745)
        ·
          refine ⟨24681332355236896691063809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32908443140315862254751745 24681332355236896691063809)
          ·
            refine ⟨18510999266427672518297857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24681332355236896691063809 18510999266427672518297857)
            ·
              refine ⟨13883249449820754388723393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18510999266427672518297857 13883249449820754388723393)
              ·
                refine ⟨10412437087365565791542545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13883249449820754388723393 10412437087365565791542545)
                ·
                  refine ⟨7809327815524174343656909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10412437087365565791542545 7809327815524174343656909)
                  ·
                    refine ⟨2928497930821565378871341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7809327815524174343656909 2928497930821565378871341)
                    ·
                      refine ⟨1098186724058087017076753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2928497930821565378871341 1098186724058087017076753)
                      ·
                        rfl

theorem cell23_2138711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_2138711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138711 prefixEnd_2138711 := by exact prefixLift 2138711
  have htrace : WordTrace (prefixWord ++ tailWord_2138711) baseStart_2138711 baseEnd_2138711 := by
    simpa [prefixWord, tailWord_2138711, baseEnd_2138711] using wordTrace_append hprefix tailTrace_2138711
  have hstable : (prefixWord ++ tailWord_2138711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138711).length < 2 ^ (prefixWord ++ tailWord_2138711).sum := by decide
  have hdescent : baseEnd_2138711 < baseStart_2138711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138714 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_2138714 : Nat := 118140960795 + 2138714 * 2 ^ 59
def prefixEnd_2138714 : Nat := 4983230072969 + 3 ^ 40 * 2138714 * 2
def baseEnd_2138714 : Nat := 366062754833350168446413

theorem tailTrace_2138714 : CollatzResearch.WordTrace tailWord_2138714 prefixEnd_2138714 366062754833350168446413 := by
  unfold tailWord_2138714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19501326993452979029053799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52003538649207944077476797 19501326993452979029053799)
  ·
    refine ⟨29251990490179468543580699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19501326993452979029053799 29251990490179468543580699)
    ·
      refine ⟨43877985735269202815371049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29251990490179468543580699 43877985735269202815371049)
      ·
        refine ⟨32908489301451902111528287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43877985735269202815371049 32908489301451902111528287)
        ·
          refine ⟨49362733952177853167292431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32908489301451902111528287 49362733952177853167292431)
          ·
            refine ⟨74044100928266779750938647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49362733952177853167292431 74044100928266779750938647)
            ·
              refine ⟨111066151392400169626407971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74044100928266779750938647 111066151392400169626407971)
              ·
                refine ⟨166599227088600254439611957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111066151392400169626407971 166599227088600254439611957)
                ·
                  refine ⟨15618677539556273853713621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166599227088600254439611957 15618677539556273853713621)
                  ·
                    refine ⟨366062754833350168446413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15618677539556273853713621 366062754833350168446413)
                    ·
                      rfl

theorem cell23_2138714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_2138714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138714 prefixEnd_2138714 := by exact prefixLift 2138714
  have htrace : WordTrace (prefixWord ++ tailWord_2138714) baseStart_2138714 baseEnd_2138714 := by
    simpa [prefixWord, tailWord_2138714, baseEnd_2138714] using wordTrace_append hprefix tailTrace_2138714
  have hstable : (prefixWord ++ tailWord_2138714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138714).length < 2 ^ (prefixWord ++ tailWord_2138714).sum := by decide
  have hdescent : baseEnd_2138714 < baseStart_2138714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138744 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_2138744 : Nat := 118140960795 + 2138744 * 2 ^ 59
def prefixEnd_2138744 : Nat := 4983230072969 + 3 ^ 40 * 2138744 * 2
def baseEnd_2138744 : Nat := 366067889639895129321367

theorem tailTrace_2138744 : CollatzResearch.WordTrace tailWord_2138744 prefixEnd_2138744 366067889639895129321367 := by
  unfold tailWord_2138744
  simp only [CollatzResearch.WordTrace]
  refine ⟨39003201081851615619903643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52004268109135487493204857 39003201081851615619903643)
  ·
    refine ⟨58504801622777423429855465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39003201081851615619903643 58504801622777423429855465)
    ·
      refine ⟨43878601217083067572391599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58504801622777423429855465 43878601217083067572391599)
      ·
        refine ⟨65817901825624601358587399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43878601217083067572391599 65817901825624601358587399)
        ·
          refine ⟨98726852738436902037881099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65817901825624601358587399 98726852738436902037881099)
          ·
            refine ⟨148090279107655353056821649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98726852738436902037881099 148090279107655353056821649)
            ·
              refine ⟨111067709330741514792616237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148090279107655353056821649 111067709330741514792616237)
              ·
                refine ⟨41650390999028068047231089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111067709330741514792616237 41650390999028068047231089)
                ·
                  refine ⟨31237793249271051035423317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41650390999028068047231089 31237793249271051035423317)
                  ·
                    refine ⟨366067889639895129321367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31237793249271051035423317 366067889639895129321367)
                    ·
                      rfl

theorem cell23_2138744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_2138744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138744 prefixEnd_2138744 := by exact prefixLift 2138744
  have htrace : WordTrace (prefixWord ++ tailWord_2138744) baseStart_2138744 baseEnd_2138744 := by
    simpa [prefixWord, tailWord_2138744, baseEnd_2138744] using wordTrace_append hprefix tailTrace_2138744
  have hstable : (prefixWord ++ tailWord_2138744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138744).length < 2 ^ (prefixWord ++ tailWord_2138744).sum := by decide
  have hdescent : baseEnd_2138744 < baseStart_2138744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138751 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_2138751 : Nat := 118140960795 + 2138751 * 2 ^ 59
def prefixEnd_2138751 : Nat := 4983230072969 + 3 ^ 40 * 2138751 * 2
def baseEnd_2138751 : Nat := 1098207263284266860576569

theorem tailTrace_2138751 : CollatzResearch.WordTrace tailWord_2138751 prefixEnd_2138751 1098207263284266860576569 := by
  unfold tailWord_2138751
  simp only [CollatzResearch.WordTrace]
  refine ⟨78006657474677871435312107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52004438316451914290208071 78006657474677871435312107)
  ·
    refine ⟨117009986212016807152968161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78006657474677871435312107 117009986212016807152968161)
    ·
      refine ⟨87757489659012605364726121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117009986212016807152968161 87757489659012605364726121)
      ·
        refine ⟨65818117244259454023544591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87757489659012605364726121 65818117244259454023544591)
        ·
          refine ⟨98727175866389181035316887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65818117244259454023544591 98727175866389181035316887)
          ·
            refine ⟨148090763799583771552975331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98727175866389181035316887 148090763799583771552975331)
            ·
              refine ⟨222136145699375657329462997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148090763799583771552975331 222136145699375657329462997)
              ·
                refine ⟨5206315914829116968659289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 222136145699375657329462997 5206315914829116968659289)
                ·
                  refine ⟨3904736936121837726494467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5206315914829116968659289 3904736936121837726494467)
                  ·
                    refine ⟨5857105404182756589741701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904736936121837726494467 5857105404182756589741701)
                    ·
                      refine ⟨1098207263284266860576569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5857105404182756589741701 1098207263284266860576569)
                      ·
                        rfl

theorem cell23_2138751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_2138751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138751 prefixEnd_2138751 := by exact prefixLift 2138751
  have htrace : WordTrace (prefixWord ++ tailWord_2138751) baseStart_2138751 baseEnd_2138751 := by
    simpa [prefixWord, tailWord_2138751, baseEnd_2138751] using wordTrace_append hprefix tailTrace_2138751
  have hstable : (prefixWord ++ tailWord_2138751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138751).length < 2 ^ (prefixWord ++ tailWord_2138751).sum := by decide
  have hdescent : baseEnd_2138751 < baseStart_2138751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138761 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 7, 4]
def baseStart_2138761 : Nat := 118140960795 + 2138761 * 2 ^ 59
def prefixEnd_2138761 : Nat := 4983230072969 + 3 ^ 40 * 2138761 * 2
def baseEnd_2138761 : Nat := 366070799363603940483841

theorem tailTrace_2138761 : CollatzResearch.WordTrace tailWord_2138761 prefixEnd_2138761 366070799363603940483841 := by
  unfold tailWord_2138761
  simp only [CollatzResearch.WordTrace]
  refine ⟨78007022204641643143176137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52004681469761095428784091 78007022204641643143176137)
  ·
    refine ⟨58505266653481232357382103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78007022204641643143176137 58505266653481232357382103)
    ·
      refine ⟨87757899980221848536073155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58505266653481232357382103 87757899980221848536073155)
      ·
        refine ⟨131636849970332772804109733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87757899980221848536073155 131636849970332772804109733)
        ·
          refine ⟨24681909369437394900770575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131636849970332772804109733 24681909369437394900770575)
          ·
            refine ⟨37022864054156092351155863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24681909369437394900770575 37022864054156092351155863)
            ·
              refine ⟨55534296081234138526733795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37022864054156092351155863 55534296081234138526733795)
              ·
                refine ⟨83301444121851207790100693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55534296081234138526733795 83301444121851207790100693)
                ·
                  refine ⟨1952377596605887682580485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 83301444121851207790100693 1952377596605887682580485)
                  ·
                    refine ⟨366070799363603940483841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1952377596605887682580485 366070799363603940483841)
                    ·
                      rfl

theorem cell23_2138761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_2138761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138761 prefixEnd_2138761 := by exact prefixLift 2138761
  have htrace : WordTrace (prefixWord ++ tailWord_2138761) baseStart_2138761 baseEnd_2138761 := by
    simpa [prefixWord, tailWord_2138761, baseEnd_2138761] using wordTrace_append hprefix tailTrace_2138761
  have hstable : (prefixWord ++ tailWord_2138761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138761).length < 2 ^ (prefixWord ++ tailWord_2138761).sum := by decide
  have hdescent : baseEnd_2138761 < baseStart_2138761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138829 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2138829 : Nat := 118140960795 + 2138829 * 2 ^ 59
def prefixEnd_2138829 : Nat := 4983230072969 + 3 ^ 40 * 2138829 * 2
def baseEnd_2138829 : Nat := 366082438258439185133737

theorem tailTrace_2138829 : CollatzResearch.WordTrace tailWord_2138829 prefixEnd_2138829 366082438258439185133737 := by
  unfold tailWord_2138829
  simp only [CollatzResearch.WordTrace]
  refine ⟨78009502368395290756651541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52006334912263527171101027 78009502368395290756651541)
  ·
    refine ⟨3656695423518529254218041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78009502368395290756651541 3656695423518529254218041)
    ·
      refine ⟨2742521567638896940663531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3656695423518529254218041 2742521567638896940663531)
      ·
        refine ⟨4113782351458345410995297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742521567638896940663531 4113782351458345410995297)
        ·
          refine ⟨3085336763593759058246473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4113782351458345410995297 3085336763593759058246473)
          ·
            refine ⟨2314002572695319293684855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085336763593759058246473 2314002572695319293684855)
            ·
              refine ⟨3471003859042978940527283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314002572695319293684855 3471003859042978940527283)
              ·
                refine ⟨5206505788564468410790925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471003859042978940527283 5206505788564468410790925)
                ·
                  refine ⟨1952439670711675654046597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5206505788564468410790925 1952439670711675654046597)
                  ·
                    refine ⟨366082438258439185133737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1952439670711675654046597 366082438258439185133737)
                    ·
                      rfl

theorem cell23_2138829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2138829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138829 prefixEnd_2138829 := by exact prefixLift 2138829
  have htrace : WordTrace (prefixWord ++ tailWord_2138829) baseStart_2138829 baseEnd_2138829 := by
    simpa [prefixWord, tailWord_2138829, baseEnd_2138829] using wordTrace_append hprefix tailTrace_2138829
  have hstable : (prefixWord ++ tailWord_2138829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138829).length < 2 ^ (prefixWord ++ tailWord_2138829).sum := by decide
  have hdescent : baseEnd_2138829 < baseStart_2138829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138862 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_2138862 : Nat := 118140960795 + 2138862 * 2 ^ 59
def prefixEnd_2138862 : Nat := 4983230072969 + 3 ^ 40 * 2138862 * 2
def baseEnd_2138862 : Nat := 1098264259636915926288559

theorem tailTrace_2138862 : CollatzResearch.WordTrace tailWord_2138862 prefixEnd_2138862 1098264259636915926288559 := by
  unfold tailWord_2138862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751338247159467174075355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52007137318183824928401893 9751338247159467174075355)
  ·
    refine ⟨14627007370739200761113033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9751338247159467174075355 14627007370739200761113033)
    ·
      refine ⟨10970255528054400570834775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14627007370739200761113033 10970255528054400570834775)
      ·
        refine ⟨16455383292081600856252163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10970255528054400570834775 16455383292081600856252163)
        ·
          refine ⟨24683074938122401284378245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16455383292081600856252163 24683074938122401284378245)
          ·
            refine ⟨4628076550897950240820921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24683074938122401284378245 4628076550897950240820921)
            ·
              refine ⟨3471057413173462680615691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628076550897950240820921 3471057413173462680615691)
              ·
                refine ⟨5206586119760194020923537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471057413173462680615691 5206586119760194020923537)
                ·
                  refine ⟨3904939589820145515692653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5206586119760194020923537 3904939589820145515692653)
                  ·
                    refine ⟨1464352346182554568384745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3904939589820145515692653 1464352346182554568384745)
                    ·
                      refine ⟨1098264259636915926288559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464352346182554568384745 1098264259636915926288559)
                      ·
                        rfl

theorem cell23_2138862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_2138862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138862 prefixEnd_2138862 := by exact prefixLift 2138862
  have htrace : WordTrace (prefixWord ++ tailWord_2138862) baseStart_2138862 baseEnd_2138862 := by
    simpa [prefixWord, tailWord_2138862, baseEnd_2138862] using wordTrace_append hprefix tailTrace_2138862
  have hstable : (prefixWord ++ tailWord_2138862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138862).length < 2 ^ (prefixWord ++ tailWord_2138862).sum := by decide
  have hdescent : baseEnd_2138862 < baseStart_2138862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138921 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_2138921 : Nat := 118140960795 + 2138921 * 2 ^ 59
def prefixEnd_2138921 : Nat := 4983230072969 + 3 ^ 40 * 2138921 * 2
def baseEnd_2138921 : Nat := 1098294554995531195450787

theorem tailTrace_2138921 : CollatzResearch.WordTrace tailWord_2138921 prefixEnd_2138921 1098294554995531195450787 := by
  unfold tailWord_2138921
  simp only [CollatzResearch.WordTrace]
  refine ⟨78012857884061990469000617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52008571922707993646000411 78012857884061990469000617)
  ·
    refine ⟨58509643413046492851750463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78012857884061990469000617 58509643413046492851750463)
    ·
      refine ⟨87764465119569739277625695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58509643413046492851750463 87764465119569739277625695)
      ·
        refine ⟨131646697679354608916438543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87764465119569739277625695 131646697679354608916438543)
        ·
          refine ⟨197470046519031913374657815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131646697679354608916438543 197470046519031913374657815)
          ·
            refine ⟨296205069778547870061986723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197470046519031913374657815 296205069778547870061986723)
            ·
              refine ⟨444307604667821805092980085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296205069778547870061986723 444307604667821805092980085)
              ·
                refine ⟨41653837937608294227466883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 444307604667821805092980085 41653837937608294227466883)
                ·
                  refine ⟨62480756906412441341200325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41653837937608294227466883 62480756906412441341200325)
                  ·
                    refine ⟨11715141919952332751475061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62480756906412441341200325 11715141919952332751475061)
                    ·
                      refine ⟨1098294554995531195450787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11715141919952332751475061 1098294554995531195450787)
                      ·
                        rfl

theorem cell23_2138921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_2138921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138921 prefixEnd_2138921 := by exact prefixLift 2138921
  have htrace : WordTrace (prefixWord ++ tailWord_2138921) baseStart_2138921 baseEnd_2138921 := by
    simpa [prefixWord, tailWord_2138921, baseEnd_2138921] using wordTrace_append hprefix tailTrace_2138921
  have hstable : (prefixWord ++ tailWord_2138921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138921).length < 2 ^ (prefixWord ++ tailWord_2138921).sum := by decide
  have hdescent : baseEnd_2138921 < baseStart_2138921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138926 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2138926 : Nat := 118140960795 + 2138926 * 2 ^ 59
def prefixEnd_2138926 : Nat := 4983230072969 + 3 ^ 40 * 2138926 * 2
def baseEnd_2138926 : Nat := 1098297122398803675888265

theorem tailTrace_2138926 : CollatzResearch.WordTrace tailWord_2138926 prefixEnd_2138926 1098297122398803675888265 := by
  unfold tailWord_2138926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751630031130484540366579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52008693499362584215288421 9751630031130484540366579)
  ·
    refine ⟨14627445046695726810549869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9751630031130484540366579 14627445046695726810549869)
    ·
      refine ⟨5485291892510897553956201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14627445046695726810549869 5485291892510897553956201)
      ·
        refine ⟨4113968919383173165467151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5485291892510897553956201 4113968919383173165467151)
        ·
          refine ⟨6170953379074759748200727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113968919383173165467151 6170953379074759748200727)
          ·
            refine ⟨9256430068612139622301091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170953379074759748200727 9256430068612139622301091)
            ·
              refine ⟨13884645102918209433451637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9256430068612139622301091 13884645102918209433451637)
              ·
                refine ⟨1301685478398582134386091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13884645102918209433451637 1301685478398582134386091)
                ·
                  refine ⟨1952528217597873201579137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301685478398582134386091 1952528217597873201579137)
                  ·
                    refine ⟨1464396163198404901184353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1952528217597873201579137 1464396163198404901184353)
                    ·
                      refine ⟨1098297122398803675888265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464396163198404901184353 1098297122398803675888265)
                      ·
                        rfl

theorem cell23_2138926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2138926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138926 prefixEnd_2138926 := by exact prefixLift 2138926
  have htrace : WordTrace (prefixWord ++ tailWord_2138926) baseStart_2138926 baseEnd_2138926 := by
    simpa [prefixWord, tailWord_2138926, baseEnd_2138926] using wordTrace_append hprefix tailTrace_2138926
  have hstable : (prefixWord ++ tailWord_2138926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138926).length < 2 ^ (prefixWord ++ tailWord_2138926).sum := by decide
  have hdescent : baseEnd_2138926 < baseStart_2138926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138968 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2138968 : Nat := 118140960795 + 2138968 * 2 ^ 59
def prefixEnd_2138968 : Nat := 4983230072969 + 3 ^ 40 * 2138968 * 2
def baseEnd_2138968 : Nat := 1098318688586292511563071

theorem tailTrace_2138968 : CollatzResearch.WordTrace tailWord_2138968 prefixEnd_2138968 1098318688586292511563071 := by
  unfold tailWord_2138968
  simp only [CollatzResearch.WordTrace]
  refine ⟨39007286057445858747980779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52009714743261144997307705 39007286057445858747980779)
  ·
    refine ⟨58510929086168788121971169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39007286057445858747980779 58510929086168788121971169)
    ·
      refine ⟨43883196814626591091478377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58510929086168788121971169 43883196814626591091478377)
      ·
        refine ⟨32912397610969943318608783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43883196814626591091478377 32912397610969943318608783)
        ·
          refine ⟨49368596416454914977913175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32912397610969943318608783 49368596416454914977913175)
          ·
            refine ⟨74052894624682372466869763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49368596416454914977913175 74052894624682372466869763)
            ·
              refine ⟨111079341937023558700304645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74052894624682372466869763 111079341937023558700304645)
              ·
                refine ⟨20827376613191917256307121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111079341937023558700304645 20827376613191917256307121)
                ·
                  refine ⟨15620532459893937942230341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20827376613191917256307121 15620532459893937942230341)
                  ·
                    refine ⟨2928849836230113364168189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15620532459893937942230341 2928849836230113364168189)
                    ·
                      refine ⟨1098318688586292511563071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2928849836230113364168189 1098318688586292511563071)
                      ·
                        rfl

theorem cell23_2138968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2138968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138968 prefixEnd_2138968 := by exact prefixLift 2138968
  have htrace : WordTrace (prefixWord ++ tailWord_2138968) baseStart_2138968 baseEnd_2138968 := by
    simpa [prefixWord, tailWord_2138968, baseEnd_2138968] using wordTrace_append hprefix tailTrace_2138968
  have hstable : (prefixWord ++ tailWord_2138968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138968).length < 2 ^ (prefixWord ++ tailWord_2138968).sum := by decide
  have hdescent : baseEnd_2138968 < baseStart_2138968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138971 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 15]
def baseStart_2138971 : Nat := 118140960795 + 2138971 * 2 ^ 59
def prefixEnd_2138971 : Nat := 4983230072969 + 3 ^ 40 * 2138971 * 2
def baseEnd_2138971 : Nat := 122035581003139555536173

theorem tailTrace_2138971 : CollatzResearch.WordTrace tailWord_2138971 prefixEnd_2138971 122035581003139555536173 := by
  unfold tailWord_2138971
  simp only [CollatzResearch.WordTrace]
  refine ⟨78014681533880849008320767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52009787689253899338880511 78014681533880849008320767)
  ·
    refine ⟨117022022300821273512481151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78014681533880849008320767 117022022300821273512481151)
    ·
      refine ⟨175533033451231910268721727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117022022300821273512481151 175533033451231910268721727)
      ·
        refine ⟨263299550176847865403082591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175533033451231910268721727 263299550176847865403082591)
        ·
          refine ⟨394949325265271798104623887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263299550176847865403082591 394949325265271798104623887)
          ·
            refine ⟨592423987897907697156935831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394949325265271798104623887 592423987897907697156935831)
            ·
              refine ⟨888635981846861545735403747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592423987897907697156935831 888635981846861545735403747)
              ·
                refine ⟨1332953972770292318603105621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888635981846861545735403747 1332953972770292318603105621)
                ·
                  refine ⟨122035581003139555536173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 15 1332953972770292318603105621 122035581003139555536173)
                  ·
                    rfl

theorem cell23_2138971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15].length) (baseStart_2138971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2138971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2138971 prefixEnd_2138971 := by exact prefixLift 2138971
  have htrace : WordTrace (prefixWord ++ tailWord_2138971) baseStart_2138971 baseEnd_2138971 := by
    simpa [prefixWord, tailWord_2138971, baseEnd_2138971] using wordTrace_append hprefix tailTrace_2138971
  have hstable : (prefixWord ++ tailWord_2138971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138971).length < 2 ^ (prefixWord ++ tailWord_2138971).sum := by decide
  have hdescent : baseEnd_2138971 < baseStart_2138971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139005 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 5]
def baseStart_2139005 : Nat := 118140960795 + 2139005 * 2 ^ 59
def prefixEnd_2139005 : Nat := 4983230072969 + 3 ^ 40 * 2139005 * 2
def baseEnd_2139005 : Nat := 122037520818945429644489

theorem tailTrace_2139005 : CollatzResearch.WordTrace tailWord_2139005 prefixEnd_2139005 122037520818945429644489 := by
  unfold tailWord_2139005
  simp only [CollatzResearch.WordTrace]
  refine ⟨78015921615757672815058469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52010614410505115210038979 78015921615757672815058469)
  ·
    refine ⟨14627985302954563652823463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78015921615757672815058469 14627985302954563652823463)
    ·
      refine ⟨21941977954431845479235195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14627985302954563652823463 21941977954431845479235195)
      ·
        refine ⟨32912966931647768218852793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21941977954431845479235195 32912966931647768218852793)
        ·
          refine ⟨24684725198735826164139595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32912966931647768218852793 24684725198735826164139595)
          ·
            refine ⟨37027087798103739246209393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24684725198735826164139595 37027087798103739246209393)
            ·
              refine ⟨27770315848577804434657045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37027087798103739246209393 27770315848577804434657045)
              ·
                refine ⟨1301733555402084582874549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27770315848577804434657045 1301733555402084582874549)
                ·
                  refine ⟨122037520818945429644489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1301733555402084582874549 122037520818945429644489)
                  ·
                    rfl

theorem cell23_2139005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_2139005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139005 prefixEnd_2139005 := by exact prefixLift 2139005
  have htrace : WordTrace (prefixWord ++ tailWord_2139005) baseStart_2139005 baseEnd_2139005 := by
    simpa [prefixWord, tailWord_2139005, baseEnd_2139005] using wordTrace_append hprefix tailTrace_2139005
  have hstable : (prefixWord ++ tailWord_2139005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139005).length < 2 ^ (prefixWord ++ tailWord_2139005).sum := by decide
  have hdescent : baseEnd_2139005 < baseStart_2139005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139010 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2139010 : Nat := 118140960795 + 2139010 * 2 ^ 59
def prefixEnd_2139010 : Nat := 4983230072969 + 3 ^ 40 * 2139010 * 2
def baseEnd_2139010 : Nat := 1098340254773781347237879

theorem tailTrace_2139010 : CollatzResearch.WordTrace tailWord_2139010 prefixEnd_2139010 1098340254773781347237879 := by
  unfold tailWord_2139010
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504025995184889667247621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52010735987159705779326989 19504025995184889667247621)
  ·
    refine ⟨3657004874097166812608929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19504025995184889667247621 3657004874097166812608929)
    ·
      refine ⟨2742753655572875109456697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3657004874097166812608929 2742753655572875109456697)
      ·
        refine ⟨2057065241679656332092523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2742753655572875109456697 2057065241679656332092523)
        ·
          refine ⟨3085597862519484498138785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057065241679656332092523 3085597862519484498138785)
          ·
            refine ⟨2314198396889613373604089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085597862519484498138785 2314198396889613373604089)
            ·
              refine ⟨1735648797667210030203067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2314198396889613373604089 1735648797667210030203067)
              ·
                refine ⟨2603473196500815045304601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735648797667210030203067 2603473196500815045304601)
                ·
                  refine ⟨1952604897375611283978451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603473196500815045304601 1952604897375611283978451)
                  ·
                    refine ⟨2928907346063416925967677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1952604897375611283978451 2928907346063416925967677)
                    ·
                      refine ⟨1098340254773781347237879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2928907346063416925967677 1098340254773781347237879)
                      ·
                        rfl

theorem cell23_2139010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2139010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139010 prefixEnd_2139010 := by exact prefixLift 2139010
  have htrace : WordTrace (prefixWord ++ tailWord_2139010) baseStart_2139010 baseEnd_2139010 := by
    simpa [prefixWord, tailWord_2139010, baseEnd_2139010] using wordTrace_append hprefix tailTrace_2139010
  have hstable : (prefixWord ++ tailWord_2139010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139010).length < 2 ^ (prefixWord ++ tailWord_2139010).sum := by decide
  have hdescent : baseEnd_2139010 < baseStart_2139010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139016 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_2139016 : Nat := 118140960795 + 2139016 * 2 ^ 59
def prefixEnd_2139016 : Nat := 4983230072969 + 3 ^ 40 * 2139016 * 2
def baseEnd_2139016 : Nat := 1098343335657708323762851

theorem tailTrace_2139016 : CollatzResearch.WordTrace tailWord_2139016 prefixEnd_2139016 1098343335657708323762851 := by
  unfold tailWord_2139016
  simp only [CollatzResearch.WordTrace]
  refine ⟨39008161409358910846854451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52010881879145214462472601 39008161409358910846854451)
  ·
    refine ⟨58512242114038366270281677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39008161409358910846854451 58512242114038366270281677)
    ·
      refine ⟨21942090792764387351355629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58512242114038366270281677 21942090792764387351355629)
      ·
        refine ⟨8228284047286645256758361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21942090792764387351355629 8228284047286645256758361)
        ·
          refine ⟨6171213035464983942568771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8228284047286645256758361 6171213035464983942568771)
          ·
            refine ⟨9256819553197475913853157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6171213035464983942568771 9256819553197475913853157)
            ·
              refine ⟨1735653666224526733847467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9256819553197475913853157 1735653666224526733847467)
              ·
                refine ⟨2603480499336790100771201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735653666224526733847467 2603480499336790100771201)
                ·
                  refine ⟨1952610374502592575578401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603480499336790100771201 1952610374502592575578401)
                  ·
                    refine ⟨1464457780876944431683801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1952610374502592575578401 1464457780876944431683801)
                    ·
                      refine ⟨1098343335657708323762851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464457780876944431683801 1098343335657708323762851)
                      ·
                        rfl

theorem cell23_2139016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_2139016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139016 prefixEnd_2139016 := by exact prefixLift 2139016
  have htrace : WordTrace (prefixWord ++ tailWord_2139016) baseStart_2139016 baseEnd_2139016 := by
    simpa [prefixWord, tailWord_2139016, baseEnd_2139016] using wordTrace_append hprefix tailTrace_2139016
  have hstable : (prefixWord ++ tailWord_2139016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139016).length < 2 ^ (prefixWord ++ tailWord_2139016).sum := by decide
  have hdescent : baseEnd_2139016 < baseStart_2139016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139072 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 2, 4, 2]
def baseStart_2139072 : Nat := 118140960795 + 2139072 * 2 ^ 59
def prefixEnd_2139072 : Nat := 4983230072969 + 3 ^ 40 * 2139072 * 2
def baseEnd_2139072 : Nat := 1098372090574360104662593

theorem tailTrace_2139072 : CollatzResearch.WordTrace tailWord_2139072 prefixEnd_2139072 1098372090574360104662593 := by
  unfold tailWord_2139072
  simp only [CollatzResearch.WordTrace]
  refine ⟨39009182653257471628873735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52012243537676628838498313 39009182653257471628873735)
  ·
    refine ⟨58513773979886207443310603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39009182653257471628873735 58513773979886207443310603)
    ·
      refine ⟨87770660969829311164965905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58513773979886207443310603 87770660969829311164965905)
      ·
        refine ⟨65827995727371983373724429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87770660969829311164965905 65827995727371983373724429)
        ·
          refine ⟨24685498397764493765146661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65827995727371983373724429 24685498397764493765146661)
          ·
            refine ⟨4628530949580842580964999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24685498397764493765146661 4628530949580842580964999)
            ·
              refine ⟨6942796424371263871447499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628530949580842580964999 6942796424371263871447499)
              ·
                refine ⟨10414194636556895807171249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6942796424371263871447499 10414194636556895807171249)
                ·
                  refine ⟨7810645977417671855378437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10414194636556895807171249 7810645977417671855378437)
                  ·
                    refine ⟨1464496120765813472883457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7810645977417671855378437 1464496120765813472883457)
                    ·
                      refine ⟨1098372090574360104662593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464496120765813472883457 1098372090574360104662593)
                      ·
                        rfl

theorem cell23_2139072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_2139072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139072 prefixEnd_2139072 := by exact prefixLift 2139072
  have htrace : WordTrace (prefixWord ++ tailWord_2139072) baseStart_2139072 baseEnd_2139072 := by
    simpa [prefixWord, tailWord_2139072, baseEnd_2139072] using wordTrace_append hprefix tailTrace_2139072
  have hstable : (prefixWord ++ tailWord_2139072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139072).length < 2 ^ (prefixWord ++ tailWord_2139072).sum := by decide
  have hdescent : baseEnd_2139072 < baseStart_2139072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139092 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2139092 : Nat := 118140960795 + 2139092 * 2 ^ 59
def prefixEnd_2139092 : Nat := 4983230072969 + 3 ^ 40 * 2139092 * 2
def baseEnd_2139092 : Nat := 1098382360187450026412501

theorem tailTrace_2139092 : CollatzResearch.WordTrace tailWord_2139092 prefixEnd_2139092 1098382360187450026412501 := by
  unfold tailWord_2139092
  simp only [CollatzResearch.WordTrace]
  refine ⟨39009547383221243336737765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52012729844294991115650353 39009547383221243336737765)
  ·
    refine ⟨7314290134353983125638331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39009547383221243336737765 7314290134353983125638331)
    ·
      refine ⟨10971435201530974688457497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7314290134353983125638331 10971435201530974688457497)
      ·
        refine ⟨8228576401148231016343123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10971435201530974688457497 8228576401148231016343123)
        ·
          refine ⟨12342864601722346524514685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8228576401148231016343123 12342864601722346524514685)
          ·
            refine ⟨4628574225645879946693007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12342864601722346524514685 4628574225645879946693007)
            ·
              refine ⟨6942861338468819920039511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4628574225645879946693007 6942861338468819920039511)
              ·
                refine ⟨10414292007703229880059267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6942861338468819920039511 10414292007703229880059267)
                ·
                  refine ⟨15621438011554844820088901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414292007703229880059267 15621438011554844820088901)
                  ·
                    refine ⟨2929019627166533403766669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15621438011554844820088901 2929019627166533403766669)
                    ·
                      refine ⟨1098382360187450026412501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929019627166533403766669 1098382360187450026412501)
                      ·
                        rfl

theorem cell23_2139092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2139092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139092 prefixEnd_2139092 := by exact prefixLift 2139092
  have htrace : WordTrace (prefixWord ++ tailWord_2139092) baseStart_2139092 baseEnd_2139092 := by
    simpa [prefixWord, tailWord_2139092, baseEnd_2139092] using wordTrace_append hprefix tailTrace_2139092
  have hstable : (prefixWord ++ tailWord_2139092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139092).length < 2 ^ (prefixWord ++ tailWord_2139092).sum := by decide
  have hdescent : baseEnd_2139092 < baseStart_2139092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139132 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_2139132 : Nat := 118140960795 + 2139132 * 2 ^ 59
def prefixEnd_2139132 : Nat := 4983230072969 + 3 ^ 40 * 2139132 * 2
def baseEnd_2139132 : Nat := 1098402899413629869912317

theorem tailTrace_2139132 : CollatzResearch.WordTrace tailWord_2139132 prefixEnd_2139132 1098402899413629869912317 := by
  unfold tailWord_2139132
  simp only [CollatzResearch.WordTrace]
  refine ⟨39010276843148786752465825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52013702457531715669954433 39010276843148786752465825)
  ·
    refine ⟨29257707632361590064349369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39010276843148786752465825 29257707632361590064349369)
    ·
      refine ⟨21943280724271192548262027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29257707632361590064349369 21943280724271192548262027)
      ·
        refine ⟨32914921086406788822393041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21943280724271192548262027 32914921086406788822393041)
        ·
          refine ⟨24686190814805091616794781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32914921086406788822393041 24686190814805091616794781)
          ·
            refine ⟨9257321555551909356298043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24686190814805091616794781 9257321555551909356298043)
            ·
              refine ⟨13885982333327864034447065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9257321555551909356298043 13885982333327864034447065)
              ·
                refine ⟨10414486749995898025835299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13885982333327864034447065 10414486749995898025835299)
                ·
                  refine ⟨15621730124993847038752949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414486749995898025835299 15621730124993847038752949)
                  ·
                    refine ⟨1464537199218173159883089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15621730124993847038752949 1464537199218173159883089)
                    ·
                      refine ⟨1098402899413629869912317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464537199218173159883089 1098402899413629869912317)
                      ·
                        rfl

theorem cell23_2139132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_2139132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139132 prefixEnd_2139132 := by exact prefixLift 2139132
  have htrace : WordTrace (prefixWord ++ tailWord_2139132) baseStart_2139132 baseEnd_2139132 := by
    simpa [prefixWord, tailWord_2139132, baseEnd_2139132] using wordTrace_append hprefix tailTrace_2139132
  have hstable : (prefixWord ++ tailWord_2139132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139132).length < 2 ^ (prefixWord ++ tailWord_2139132).sum := by decide
  have hdescent : baseEnd_2139132 < baseStart_2139132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139145 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_2139145 : Nat := 118140960795 + 2139145 * 2 ^ 59
def prefixEnd_2139145 : Nat := 4983230072969 + 3 ^ 40 * 2139145 * 2
def baseEnd_2139145 : Nat := 1098409574662138319049757

theorem tailTrace_2139145 : CollatzResearch.WordTrace tailWord_2139145 prefixEnd_2139145 1098409574662138319049757 := by
  unfold tailWord_2139145
  simp only [CollatzResearch.WordTrace]
  refine ⟨78021027835250476725154889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52014018556833651150103259 78021027835250476725154889)
  ·
    refine ⟨58515770876437857543866167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78021027835250476725154889 58515770876437857543866167)
    ·
      refine ⟨87773656314656786315799251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58515770876437857543866167 87773656314656786315799251)
      ·
        refine ⟨131660484471985179473698877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87773656314656786315799251 131660484471985179473698877)
        ·
          refine ⟨49372681676994442302637079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131660484471985179473698877 49372681676994442302637079)
          ·
            refine ⟨74059022515491663453955619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49372681676994442302637079 74059022515491663453955619)
            ·
              refine ⟨111088533773237495180933429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74059022515491663453955619 111088533773237495180933429)
              ·
                refine ⟨10414550041241015173212509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111088533773237495180933429 10414550041241015173212509)
                ·
                  refine ⟨3905456265465380689954691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10414550041241015173212509 3905456265465380689954691)
                  ·
                    refine ⟨5858184398198071034932037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3905456265465380689954691 5858184398198071034932037)
                    ·
                      refine ⟨1098409574662138319049757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5858184398198071034932037 1098409574662138319049757)
                      ·
                        rfl

theorem cell23_2139145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_2139145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139145 prefixEnd_2139145 := by exact prefixLift 2139145
  have htrace : WordTrace (prefixWord ++ tailWord_2139145) baseStart_2139145 baseEnd_2139145 := by
    simpa [prefixWord, tailWord_2139145, baseEnd_2139145] using wordTrace_append hprefix tailTrace_2139145
  have hstable : (prefixWord ++ tailWord_2139145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139145).length < 2 ^ (prefixWord ++ tailWord_2139145).sum := by decide
  have hdescent : baseEnd_2139145 < baseStart_2139145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139162 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_2139162 : Nat := 118140960795 + 2139162 * 2 ^ 59
def prefixEnd_2139162 : Nat := 4983230072969 + 3 ^ 40 * 2139162 * 2
def baseEnd_2139162 : Nat := 1098418303833264752537179

theorem tailTrace_2139162 : CollatzResearch.WordTrace tailWord_2139162 prefixEnd_2139162 1098418303833264752537179 := by
  unfold tailWord_2139162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19505411969047222157130935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52014431917459259085682493 19505411969047222157130935)
  ·
    refine ⟨29258117953570833235696403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19505411969047222157130935 29258117953570833235696403)
    ·
      refine ⟨43887176930356249853544605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29258117953570833235696403 43887176930356249853544605)
      ·
        refine ⟨16457691348883593695079227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43887176930356249853544605 16457691348883593695079227)
        ·
          refine ⟨24686537023325390542618841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16457691348883593695079227 24686537023325390542618841)
          ·
            refine ⟨18514902767494042906964131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24686537023325390542618841 18514902767494042906964131)
            ·
              refine ⟨27772354151241064360446197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18514902767494042906964131 27772354151241064360446197)
              ·
                refine ⟨2603658201678849783791831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27772354151241064360446197 2603658201678849783791831)
                ·
                  refine ⟨3905487302518274675687747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603658201678849783791831 3905487302518274675687747)
                  ·
                    refine ⟨5858230953777412013531621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3905487302518274675687747 5858230953777412013531621)
                    ·
                      refine ⟨1098418303833264752537179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5858230953777412013531621 1098418303833264752537179)
                      ·
                        rfl

theorem cell23_2139162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_2139162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139162 prefixEnd_2139162 := by exact prefixLift 2139162
  have htrace : WordTrace (prefixWord ++ tailWord_2139162) baseStart_2139162 baseEnd_2139162 := by
    simpa [prefixWord, tailWord_2139162, baseEnd_2139162] using wordTrace_append hprefix tailTrace_2139162
  have hstable : (prefixWord ++ tailWord_2139162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139162).length < 2 ^ (prefixWord ++ tailWord_2139162).sum := by decide
  have hdescent : baseEnd_2139162 < baseStart_2139162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139182 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2139182 : Nat := 118140960795 + 2139182 * 2 ^ 59
def prefixEnd_2139182 : Nat := 4983230072969 + 3 ^ 40 * 2139182 * 2
def baseEnd_2139182 : Nat := 1098428573446354674287087

theorem tailTrace_2139182 : CollatzResearch.WordTrace tailWord_2139182 prefixEnd_2139182 1098428573446354674287087 := by
  unfold tailWord_2139182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9752797167014554005531475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52014918224077621362834533 9752797167014554005531475)
  ·
    refine ⟨14629195750521831008297213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9752797167014554005531475 14629195750521831008297213)
    ·
      refine ⟨5485948406445686628111455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14629195750521831008297213 5485948406445686628111455)
      ·
        refine ⟨8228922609668529942167183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5485948406445686628111455 8228922609668529942167183)
        ·
          refine ⟨12343383914502794913250775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8228922609668529942167183 12343383914502794913250775)
          ·
            refine ⟨18515075871754192369876163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12343383914502794913250775 18515075871754192369876163)
            ·
              refine ⟨27772613807631288554814245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18515075871754192369876163 27772613807631288554814245)
              ·
                refine ⟨5207365088930866604027671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27772613807631288554814245 5207365088930866604027671)
                ·
                  refine ⟨7811047633396299906041507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5207365088930866604027671 7811047633396299906041507)
                  ·
                    refine ⟨11716571450094449859062261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7811047633396299906041507 11716571450094449859062261)
                    ·
                      refine ⟨1098428573446354674287087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11716571450094449859062261 1098428573446354674287087)
                      ·
                        rfl

theorem cell23_2139182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2139182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139182 prefixEnd_2139182 := by exact prefixLift 2139182
  have htrace : WordTrace (prefixWord ++ tailWord_2139182) baseStart_2139182 baseEnd_2139182 := by
    simpa [prefixWord, tailWord_2139182, baseEnd_2139182] using wordTrace_append hprefix tailTrace_2139182
  have hstable : (prefixWord ++ tailWord_2139182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139182).length < 2 ^ (prefixWord ++ tailWord_2139182).sum := by decide
  have hdescent : baseEnd_2139182 < baseStart_2139182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139185 : List Nat := [1, 2, 2, 3, 1, 2, 4, 8]
def baseStart_2139185 : Nat := 118140960795 + 2139185 * 2 ^ 59
def prefixEnd_2139185 : Nat := 4983230072969 + 3 ^ 40 * 2139185 * 2
def baseEnd_2139185 : Nat := 40682596810678450464799

theorem tailTrace_2139185 : CollatzResearch.WordTrace tailWord_2139185 prefixEnd_2139185 40682596810678450464799 := by
  unfold tailWord_2139185
  simp only [CollatzResearch.WordTrace]
  refine ⟨78022486755105563556611009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52014991170070375704407339 78022486755105563556611009)
  ·
    refine ⟨58516865066329172667458257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78022486755105563556611009 58516865066329172667458257)
    ·
      refine ⟨43887648799746879500593693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58516865066329172667458257 43887648799746879500593693)
      ·
        refine ⟨16457868299905079812722635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43887648799746879500593693 16457868299905079812722635)
        ·
          refine ⟨24686802449857619719083953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16457868299905079812722635 24686802449857619719083953)
          ·
            refine ⟨18515101837393214789312965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24686802449857619719083953 18515101837393214789312965)
            ·
              refine ⟨3471581594511227772996181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18515101837393214789312965 3471581594511227772996181)
              ·
                refine ⟨40682596810678450464799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3471581594511227772996181 40682596810678450464799)
                ·
                  rfl

theorem cell23_2139185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 8].length) (baseStart_2139185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139185 prefixEnd_2139185 := by exact prefixLift 2139185
  have htrace : WordTrace (prefixWord ++ tailWord_2139185) baseStart_2139185 baseEnd_2139185 := by
    simpa [prefixWord, tailWord_2139185, baseEnd_2139185] using wordTrace_append hprefix tailTrace_2139185
  have hstable : (prefixWord ++ tailWord_2139185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139185).length < 2 ^ (prefixWord ++ tailWord_2139185).sum := by decide
  have hdescent : baseEnd_2139185 < baseStart_2139185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139239 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_2139239 : Nat := 118140960795 + 2139239 * 2 ^ 59
def prefixEnd_2139239 : Nat := 4983230072969 + 3 ^ 40 * 2139239 * 2
def baseEnd_2139239 : Nat := 1098457841843660951274325

theorem tailTrace_2139239 : CollatzResearch.WordTrace tailWord_2139239 prefixEnd_2139239 1098457841843660951274325 := by
  unfold tailWord_2139239
  simp only [CollatzResearch.WordTrace]
  refine ⟨78024456296909930779076771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52016304197939953852717847 78024456296909930779076771)
  ·
    refine ⟨117036684445364896168615157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78024456296909930779076771 117036684445364896168615157)
    ·
      refine ⟨10972189166752959015807671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117036684445364896168615157 10972189166752959015807671)
      ·
        refine ⟨16458283750129438523711507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10972189166752959015807671 16458283750129438523711507)
        ·
          refine ⟨24687425625194157785567261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16458283750129438523711507 24687425625194157785567261)
          ·
            refine ⟨9257784609447809169587723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24687425625194157785567261 9257784609447809169587723)
            ·
              refine ⟨13886676914171713754381585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9257784609447809169587723 13886676914171713754381585)
              ·
                refine ⟨10415007685628785315786189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13886676914171713754381585 10415007685628785315786189)
                ·
                  refine ⟨3905627882110794493419821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10415007685628785315786189 3905627882110794493419821)
                  ·
                    refine ⟨1464610455791547935032433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3905627882110794493419821 1464610455791547935032433)
                    ·
                      refine ⟨1098457841843660951274325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464610455791547935032433 1098457841843660951274325)
                      ·
                        rfl

theorem cell23_2139239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_2139239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139239 prefixEnd_2139239 := by exact prefixLift 2139239
  have htrace : WordTrace (prefixWord ++ tailWord_2139239) baseStart_2139239 baseEnd_2139239 := by
    simpa [prefixWord, tailWord_2139239, baseEnd_2139239] using wordTrace_append hprefix tailTrace_2139239
  have hstable : (prefixWord ++ tailWord_2139239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139239).length < 2 ^ (prefixWord ++ tailWord_2139239).sum := by decide
  have hdescent : baseEnd_2139239 < baseStart_2139239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139246 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2139246 : Nat := 118140960795 + 2139246 * 2 ^ 59
def prefixEnd_2139246 : Nat := 4983230072969 + 3 ^ 40 * 2139246 * 2
def baseEnd_2139246 : Nat := 1098461436208242423886793

theorem tailTrace_2139246 : CollatzResearch.WordTrace tailWord_2139246 prefixEnd_2139246 1098461436208242423886793 := by
  unfold tailWord_2139246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9753088950985571371822699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52016474405256380649721061 9753088950985571371822699)
  ·
    refine ⟨14629633426478357057734049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9753088950985571371822699 14629633426478357057734049)
    ·
      refine ⟨10972225069858767793300537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14629633426478357057734049 10972225069858767793300537)
      ·
        refine ⟨8229168802394075844975403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10972225069858767793300537 8229168802394075844975403)
        ·
          refine ⟨12343753203591113767463105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8229168802394075844975403 12343753203591113767463105)
          ·
            refine ⟨9257814902693335325597329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12343753203591113767463105 9257814902693335325597329)
            ·
              refine ⟨6943361177020001494197997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9257814902693335325597329 6943361177020001494197997)
              ·
                refine ⟨2603760441382500560324249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6943361177020001494197997 2603760441382500560324249)
                ·
                  refine ⟨1952820331036875420243187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603760441382500560324249 1952820331036875420243187)
                  ·
                    refine ⟨2929230496555313130364781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1952820331036875420243187 2929230496555313130364781)
                    ·
                      refine ⟨1098461436208242423886793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929230496555313130364781 1098461436208242423886793)
                      ·
                        rfl

theorem cell23_2139246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2139246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139246 prefixEnd_2139246 := by exact prefixLift 2139246
  have htrace : WordTrace (prefixWord ++ tailWord_2139246) baseStart_2139246 baseEnd_2139246 := by
    simpa [prefixWord, tailWord_2139246, baseEnd_2139246] using wordTrace_append hprefix tailTrace_2139246
  have hstable : (prefixWord ++ tailWord_2139246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139246).length < 2 ^ (prefixWord ++ tailWord_2139246).sum := by decide
  have hdescent : baseEnd_2139246 < baseStart_2139246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139273 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 1, 3, 2]
def baseStart_2139273 : Nat := 118140960795 + 2139273 * 2 ^ 59
def prefixEnd_2139273 : Nat := 4983230072969 + 3 ^ 40 * 2139273 * 2
def baseEnd_2139273 : Nat := 1098475300185913818249169

theorem tailTrace_2139273 : CollatzResearch.WordTrace tailWord_2139273 prefixEnd_2139273 1098475300185913818249169 := by
  unfold tailWord_2139273
  simp only [CollatzResearch.WordTrace]
  refine ⟨78025696378786754585814473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52017130919191169723876315 78025696378786754585814473)
  ·
    refine ⟨58519272284090065939360855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78025696378786754585814473 58519272284090065939360855)
    ·
      refine ⟨87778908426135098909041283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58519272284090065939360855 87778908426135098909041283)
      ·
        refine ⟨131668362639202648363561925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87778908426135098909041283 131668362639202648363561925)
        ·
          refine ⟨24687817994850496568167861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131668362639202648363561925 24687817994850496568167861)
          ·
            refine ⟨2314482937017234053265737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24687817994850496568167861 2314482937017234053265737)
            ·
              refine ⟨1735862202762925539949303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2314482937017234053265737 1735862202762925539949303)
              ·
                refine ⟨2603793304144388309923955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735862202762925539949303 2603793304144388309923955)
                ·
                  refine ⟨3905689956216582464885933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603793304144388309923955 3905689956216582464885933)
                  ·
                    refine ⟨1464633733581218424332225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3905689956216582464885933 1464633733581218424332225)
                    ·
                      refine ⟨1098475300185913818249169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464633733581218424332225 1098475300185913818249169)
                      ·
                        rfl

theorem cell23_2139273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 3, 2].length) (baseStart_2139273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139273 prefixEnd_2139273 := by exact prefixLift 2139273
  have htrace : WordTrace (prefixWord ++ tailWord_2139273) baseStart_2139273 baseEnd_2139273 := by
    simpa [prefixWord, tailWord_2139273, baseEnd_2139273] using wordTrace_append hprefix tailTrace_2139273
  have hstable : (prefixWord ++ tailWord_2139273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139273).length < 2 ^ (prefixWord ++ tailWord_2139273).sum := by decide
  have hdescent : baseEnd_2139273 < baseStart_2139273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139285 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2139285 : Nat := 118140960795 + 2139285 * 2 ^ 59
def prefixEnd_2139285 : Nat := 4983230072969 + 3 ^ 40 * 2139285 * 2
def baseEnd_2139285 : Nat := 1098481461953767771299113

theorem tailTrace_2139285 : CollatzResearch.WordTrace tailWord_2139285 prefixEnd_2139285 1098481461953767771299113 := by
  unfold tailWord_2139285
  simp only [CollatzResearch.WordTrace]
  refine ⟨78026134054743280635251309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52017422703162187090167539 78026134054743280635251309)
  ·
    refine ⟨29259800270528730238219241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78026134054743280635251309 29259800270528730238219241)
    ·
      refine ⟨21944850202896547678664431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29259800270528730238219241 21944850202896547678664431)
      ·
        refine ⟨32917275304344821517996647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21944850202896547678664431 32917275304344821517996647)
        ·
          refine ⟨49375912956517232276994971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32917275304344821517996647 49375912956517232276994971)
          ·
            refine ⟨74063869434775848415492457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49375912956517232276994971 74063869434775848415492457)
            ·
              refine ⟨55547902076081886311619343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74063869434775848415492457 55547902076081886311619343)
              ·
                refine ⟨83321853114122829467429015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55547902076081886311619343 83321853114122829467429015)
                ·
                  refine ⟨124982779671184244201143523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83321853114122829467429015 124982779671184244201143523)
                  ·
                    refine ⟨187474169506776366301715285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124982779671184244201143523 187474169506776366301715285)
                    ·
                      refine ⟨1098481461953767771299113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 187474169506776366301715285 1098481461953767771299113)
                      ·
                        rfl

theorem cell23_2139285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2139285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139285 prefixEnd_2139285 := by exact prefixLift 2139285
  have htrace : WordTrace (prefixWord ++ tailWord_2139285) baseStart_2139285 baseEnd_2139285 := by
    simpa [prefixWord, tailWord_2139285, baseEnd_2139285] using wordTrace_append hprefix tailTrace_2139285
  have hstable : (prefixWord ++ tailWord_2139285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139285).length < 2 ^ (prefixWord ++ tailWord_2139285).sum := by decide
  have hdescent : baseEnd_2139285 < baseStart_2139285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139292 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 7]
def baseStart_2139292 : Nat := 118140960795 + 2139292 * 2 ^ 59
def prefixEnd_2139292 : Nat := 4983230072969 + 3 ^ 40 * 2139292 * 2
def baseEnd_2139292 : Nat := 122053895146483249323509

theorem tailTrace_2139292 : CollatzResearch.WordTrace tailWord_2139292 prefixEnd_2139292 122053895146483249323509 := by
  unfold tailWord_2139292
  simp only [CollatzResearch.WordTrace]
  refine ⟨39013194682858960415378065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52017592910478613887170753 39013194682858960415378065)
  ·
    refine ⟨29259896012144220311533549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39013194682858960415378065 29259896012144220311533549)
    ·
      refine ⟨10972461004554082616825081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29259896012144220311533549 10972461004554082616825081)
      ·
        refine ⟨8229345753415561962618811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10972461004554082616825081 8229345753415561962618811)
        ·
          refine ⟨12344018630123342943928217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8229345753415561962618811 12344018630123342943928217)
          ·
            refine ⟨9258013972592507207946163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12344018630123342943928217 9258013972592507207946163)
            ·
              refine ⟨13887020958888760811919245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9258013972592507207946163 13887020958888760811919245)
              ·
                refine ⟨5207632859583285304469717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13887020958888760811919245 5207632859583285304469717)
                ·
                  refine ⟨122053895146483249323509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5207632859583285304469717 122053895146483249323509)
                  ·
                    rfl

theorem cell23_2139292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_2139292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139292 prefixEnd_2139292 := by exact prefixLift 2139292
  have htrace : WordTrace (prefixWord ++ tailWord_2139292) baseStart_2139292 baseEnd_2139292 := by
    simpa [prefixWord, tailWord_2139292, baseEnd_2139292] using wordTrace_append hprefix tailTrace_2139292
  have hstable : (prefixWord ++ tailWord_2139292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139292).length < 2 ^ (prefixWord ++ tailWord_2139292).sum := by decide
  have hdescent : baseEnd_2139292 < baseStart_2139292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139303 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_2139303 : Nat := 118140960795 + 2139303 * 2 ^ 59
def prefixEnd_2139303 : Nat := 4983230072969 + 3 ^ 40 * 2139303 * 2
def baseEnd_2139303 : Nat := 1098490704605548700874031

theorem tailTrace_2139303 : CollatzResearch.WordTrace tailWord_2139303 prefixEnd_2139303 1098490704605548700874031 := by
  unfold tailWord_2139303
  simp only [CollatzResearch.WordTrace]
  refine ⟨78026790568678069709406563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52017860379118713139604375 78026790568678069709406563)
  ·
    refine ⟨117040185853017104564109845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78026790568678069709406563 117040185853017104564109845)
    ·
      refine ⟨5486258711860176776442649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117040185853017104564109845 5486258711860176776442649)
      ·
        refine ⟨4114694033895132582331987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5486258711860176776442649 4114694033895132582331987)
        ·
          refine ⟨6172041050842698873497981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114694033895132582331987 6172041050842698873497981)
          ·
            refine ⟨2314515394066012077561743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6172041050842698873497981 2314515394066012077561743)
            ·
              refine ⟨3471773091099018116342615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314515394066012077561743 3471773091099018116342615)
              ·
                refine ⟨5207659636648527174513923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471773091099018116342615 5207659636648527174513923)
                ·
                  refine ⟨7811489454972790761770885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5207659636648527174513923 7811489454972790761770885)
                  ·
                    refine ⟨1464654272807398267832041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7811489454972790761770885 1464654272807398267832041)
                    ·
                      refine ⟨1098490704605548700874031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464654272807398267832041 1098490704605548700874031)
                      ·
                        rfl

theorem cell23_2139303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_2139303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139303 prefixEnd_2139303 := by exact prefixLift 2139303
  have htrace : WordTrace (prefixWord ++ tailWord_2139303) baseStart_2139303 baseEnd_2139303 := by
    simpa [prefixWord, tailWord_2139303, baseEnd_2139303] using wordTrace_append hprefix tailTrace_2139303
  have hstable : (prefixWord ++ tailWord_2139303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139303).length < 2 ^ (prefixWord ++ tailWord_2139303).sum := by decide
  have hdescent : baseEnd_2139303 < baseStart_2139303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139322 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_2139322 : Nat := 118140960795 + 2139322 * 2 ^ 59
def prefixEnd_2139322 : Nat := 4983230072969 + 3 ^ 40 * 2139322 * 2
def baseEnd_2139322 : Nat := 366166820245994708845481

theorem tailTrace_2139322 : CollatzResearch.WordTrace tailWord_2139322 prefixEnd_2139322 366166820245994708845481 := by
  unfold tailWord_2139322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19506870888902308988587055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52018322370406157302898813 19506870888902308988587055)
  ·
    refine ⟨29260306333353463482880583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19506870888902308988587055 29260306333353463482880583)
    ·
      refine ⟨43890459500030195224320875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29260306333353463482880583 43890459500030195224320875)
      ·
        refine ⟨65835689250045292836481313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43890459500030195224320875 65835689250045292836481313)
        ·
          refine ⟨49376766937533969627360985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65835689250045292836481313 49376766937533969627360985)
          ·
            refine ⟨37032575203150477220520739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49376766937533969627360985 37032575203150477220520739)
            ·
              refine ⟨55548862804725715830781109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37032575203150477220520739 55548862804725715830781109)
              ·
                refine ⟨5207705887943035859135729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55548862804725715830781109 5207705887943035859135729)
                ·
                  refine ⟨3905779415957276894351797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207705887943035859135729 3905779415957276894351797)
                  ·
                    refine ⟨366166820245994708845481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3905779415957276894351797 366166820245994708845481)
                    ·
                      rfl

theorem cell23_2139322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_2139322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139322 prefixEnd_2139322 := by exact prefixLift 2139322
  have htrace : WordTrace (prefixWord ++ tailWord_2139322) baseStart_2139322 baseEnd_2139322 := by
    simpa [prefixWord, tailWord_2139322, baseEnd_2139322] using wordTrace_append hprefix tailTrace_2139322
  have hstable : (prefixWord ++ tailWord_2139322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139322).length < 2 ^ (prefixWord ++ tailWord_2139322).sum := by decide
  have hdescent : baseEnd_2139322 < baseStart_2139322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139326 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_2139326 : Nat := 118140960795 + 2139326 * 2 ^ 59
def prefixEnd_2139326 : Nat := 4983230072969 + 3 ^ 40 * 2139326 * 2
def baseEnd_2139326 : Nat := 122055834962289123431825

theorem tailTrace_2139326 : CollatzResearch.WordTrace tailWord_2139326 prefixEnd_2139326 122055834962289123431825 := by
  unfold tailWord_2139326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9753453680949343079686729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52018419631729829758329221 9753453680949343079686729)
  ·
    refine ⟨7315090260712007309765047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9753453680949343079686729 7315090260712007309765047)
    ·
      refine ⟨10972635391068010964647571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7315090260712007309765047 10972635391068010964647571)
      ·
        refine ⟨16458953086602016446971357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10972635391068010964647571 16458953086602016446971357)
        ·
          refine ⟨6172107407475756167614259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16458953086602016446971357 6172107407475756167614259)
          ·
            refine ⟨9258161111213634251421389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6172107407475756167614259 9258161111213634251421389)
            ·
              refine ⟨3471810416705112844283021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9258161111213634251421389 3471810416705112844283021)
              ·
                refine ⟨1301928906264417316606133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3471810416705112844283021 1301928906264417316606133)
                ·
                  refine ⟨122055834962289123431825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1301928906264417316606133 122055834962289123431825)
                  ·
                    rfl

theorem cell23_2139326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_2139326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139326 prefixEnd_2139326 := by exact prefixLift 2139326
  have htrace : WordTrace (prefixWord ++ tailWord_2139326) baseStart_2139326 baseEnd_2139326 := by
    simpa [prefixWord, tailWord_2139326, baseEnd_2139326] using wordTrace_append hprefix tailTrace_2139326
  have hstable : (prefixWord ++ tailWord_2139326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139326).length < 2 ^ (prefixWord ++ tailWord_2139326).sum := by decide
  have hdescent : baseEnd_2139326 < baseStart_2139326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139349 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2139349 : Nat := 118140960795 + 2139349 * 2 ^ 59
def prefixEnd_2139349 : Nat := 4983230072969 + 3 ^ 40 * 2139349 * 2
def baseEnd_2139349 : Nat := 1098514324715655520898819

theorem tailTrace_2139349 : CollatzResearch.WordTrace tailWord_2139349 prefixEnd_2139349 1098514324715655520898819 := by
  unfold tailWord_2139349
  simp only [CollatzResearch.WordTrace]
  refine ⟨78028468326511419565581101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52018978884340946377054067 78028468326511419565581101)
  ·
    refine ⟨29260675622441782337092913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78028468326511419565581101 29260675622441782337092913)
    ·
      refine ⟨21945506716831336752819685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29260675622441782337092913 21945506716831336752819685)
      ·
        refine ⟨4114782509405875641153691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21945506716831336752819685 4114782509405875641153691)
        ·
          refine ⟨6172173764108813461730537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114782509405875641153691 6172173764108813461730537)
          ·
            refine ⟨4629130323081610096297903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6172173764108813461730537 4629130323081610096297903)
            ·
              refine ⟨6943695484622415144446855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629130323081610096297903 6943695484622415144446855)
              ·
                refine ⟨10415543226933622716670283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943695484622415144446855 10415543226933622716670283)
                ·
                  refine ⟨15623314840400434075005425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10415543226933622716670283 15623314840400434075005425)
                  ·
                    refine ⟨11717486130300325556254069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15623314840400434075005425 11717486130300325556254069)
                    ·
                      refine ⟨1098514324715655520898819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11717486130300325556254069 1098514324715655520898819)
                      ·
                        rfl

theorem cell23_2139349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2139349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139349 prefixEnd_2139349 := by exact prefixLift 2139349
  have htrace : WordTrace (prefixWord ++ tailWord_2139349) baseStart_2139349 baseEnd_2139349 := by
    simpa [prefixWord, tailWord_2139349, baseEnd_2139349] using wordTrace_append hprefix tailTrace_2139349
  have hstable : (prefixWord ++ tailWord_2139349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139349).length < 2 ^ (prefixWord ++ tailWord_2139349).sum := by decide
  have hdescent : baseEnd_2139349 < baseStart_2139349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139359 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 2, 4, 2]
def baseStart_2139359 : Nat := 118140960795 + 2139359 * 2 ^ 59
def prefixEnd_2139359 : Nat := 4983230072969 + 3 ^ 40 * 2139359 * 2
def baseEnd_2139359 : Nat := 1098519459522200481773773

theorem tailTrace_2139359 : CollatzResearch.WordTrace tailWord_2139359 prefixEnd_2139359 1098519459522200481773773 := by
  unfold tailWord_2139359
  simp only [CollatzResearch.WordTrace]
  refine ⟨78028833056475191273445131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52019222037650127515630087 78028833056475191273445131)
  ·
    refine ⟨117043249584712786910167697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78028833056475191273445131 117043249584712786910167697)
    ·
      refine ⟨87782437188534590182625773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117043249584712786910167697 87782437188534590182625773)
      ·
        refine ⟨32918413945700471318484665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87782437188534590182625773 32918413945700471318484665)
        ·
          refine ⟨24688810459275353488863499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32918413945700471318484665 24688810459275353488863499)
          ·
            refine ⟨37033215688913030233295249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24688810459275353488863499 37033215688913030233295249)
            ·
              refine ⟨27774911766684772674971437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37033215688913030233295249 27774911766684772674971437)
              ·
                refine ⟨10415591912506789753114289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27774911766684772674971437 10415591912506789753114289)
                ·
                  refine ⟨7811693934380092314835717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10415591912506789753114289 7811693934380092314835717)
                  ·
                    refine ⟨1464692612696267309031697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7811693934380092314835717 1464692612696267309031697)
                    ·
                      refine ⟨1098519459522200481773773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464692612696267309031697 1098519459522200481773773)
                      ·
                        rfl

theorem cell23_2139359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_2139359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139359 prefixEnd_2139359 := by exact prefixLift 2139359
  have htrace : WordTrace (prefixWord ++ tailWord_2139359) baseStart_2139359 baseEnd_2139359 := by
    simpa [prefixWord, tailWord_2139359, baseEnd_2139359] using wordTrace_append hprefix tailTrace_2139359
  have hstable : (prefixWord ++ tailWord_2139359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139359).length < 2 ^ (prefixWord ++ tailWord_2139359).sum := by decide
  have hdescent : baseEnd_2139359 < baseStart_2139359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139379 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 3]
def baseStart_2139379 : Nat := 118140960795 + 2139379 * 2 ^ 59
def prefixEnd_2139379 : Nat := 4983230072969 + 3 ^ 40 * 2139379 * 2
def baseEnd_2139379 : Nat := 1098529729135290403523681

theorem tailTrace_2139379 : CollatzResearch.WordTrace tailWord_2139379 prefixEnd_2139379 1098529729135290403523681 := by
  unfold tailWord_2139379
  simp only [CollatzResearch.WordTrace]
  refine ⟨78029562516402734689173191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52019708344268489792782127 78029562516402734689173191)
  ·
    refine ⟨117044343774604102033759787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78029562516402734689173191 117044343774604102033759787)
    ·
      refine ⟨175566515661906153050639681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117044343774604102033759787 175566515661906153050639681)
      ·
        refine ⟨131674886746429614787979761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175566515661906153050639681 131674886746429614787979761)
        ·
          refine ⟨98756165059822211090984821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131674886746429614787979761 98756165059822211090984821)
          ·
            refine ⟨9258390474358332289779827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98756165059822211090984821 9258390474358332289779827)
            ·
              refine ⟨13887585711537498434669741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9258390474358332289779827 13887585711537498434669741)
              ·
                refine ⟨5207844641826561913001153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13887585711537498434669741 5207844641826561913001153)
                ·
                  refine ⟨3905883481369921434750865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207844641826561913001153 3905883481369921434750865)
                  ·
                    refine ⟨2929412611027441076063149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3905883481369921434750865 2929412611027441076063149)
                    ·
                      refine ⟨1098529729135290403523681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929412611027441076063149 1098529729135290403523681)
                      ·
                        rfl

theorem cell23_2139379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_2139379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139379 prefixEnd_2139379 := by exact prefixLift 2139379
  have htrace : WordTrace (prefixWord ++ tailWord_2139379) baseStart_2139379 baseEnd_2139379 := by
    simpa [prefixWord, tailWord_2139379, baseEnd_2139379] using wordTrace_append hprefix tailTrace_2139379
  have hstable : (prefixWord ++ tailWord_2139379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139379).length < 2 ^ (prefixWord ++ tailWord_2139379).sum := by decide
  have hdescent : baseEnd_2139379 < baseStart_2139379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139386 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_2139386 : Nat := 118140960795 + 2139386 * 2 ^ 59
def prefixEnd_2139386 : Nat := 4983230072969 + 3 ^ 40 * 2139386 * 2
def baseEnd_2139386 : Nat := 366177774499957292045383

theorem tailTrace_2139386 : CollatzResearch.WordTrace tailWord_2139386 prefixEnd_2139386 366177774499957292045383 := by
  unfold tailWord_2139386
  simp only [CollatzResearch.WordTrace]
  refine ⟨19507454456844343721169503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52019878551584916589785341 19507454456844343721169503)
  ·
    refine ⟨29261181685266515581754255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19507454456844343721169503 29261181685266515581754255)
    ·
      refine ⟨43891772527899773372631383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29261181685266515581754255 43891772527899773372631383)
      ·
        refine ⟨65837658791849660058947075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43891772527899773372631383 65837658791849660058947075)
        ·
          refine ⟨98756488187774490088420613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65837658791849660058947075 98756488187774490088420613)
          ·
            refine ⟨18516841535207716891578865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98756488187774490088420613 18516841535207716891578865)
            ·
              refine ⟨13887631151405787668684149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18516841535207716891578865 13887631151405787668684149)
              ·
                refine ⟨1301965420444292593939139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13887631151405787668684149 1301965420444292593939139)
                ·
                  refine ⟨1952948130666438890908709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301965420444292593939139 1952948130666438890908709)
                  ·
                    refine ⟨366177774499957292045383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1952948130666438890908709 366177774499957292045383)
                    ·
                      rfl

theorem cell23_2139386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_2139386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139386 prefixEnd_2139386 := by exact prefixLift 2139386
  have htrace : WordTrace (prefixWord ++ tailWord_2139386) baseStart_2139386 baseEnd_2139386 := by
    simpa [prefixWord, tailWord_2139386, baseEnd_2139386] using wordTrace_append hprefix tailTrace_2139386
  have hstable : (prefixWord ++ tailWord_2139386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139386).length < 2 ^ (prefixWord ++ tailWord_2139386).sum := by decide
  have hdescent : baseEnd_2139386 < baseStart_2139386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139396 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2139396 : Nat := 118140960795 + 2139396 * 2 ^ 59
def prefixEnd_2139396 : Nat := 4983230072969 + 3 ^ 40 * 2139396 * 2
def baseEnd_2139396 : Nat := 1098538458306416837011103

theorem tailTrace_2139396 : CollatzResearch.WordTrace tailWord_2139396 prefixEnd_2139396 1098538458306416837011103 := by
  unfold tailWord_2139396
  simp only [CollatzResearch.WordTrace]
  refine ⟨39015091278670573296271021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52020121704894097728361361 39015091278670573296271021)
  ·
    refine ⟨14630659229501464986101633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39015091278670573296271021 14630659229501464986101633)
    ·
      refine ⟨10972994422126098739576225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14630659229501464986101633 10972994422126098739576225)
      ·
        refine ⟨8229745816594574054682169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10972994422126098739576225 8229745816594574054682169)
        ·
          refine ⟨6172309362445930541011627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8229745816594574054682169 6172309362445930541011627)
          ·
            refine ⟨9258464043668895811517441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6172309362445930541011627 9258464043668895811517441)
            ·
              refine ⟨6943848032751671858638081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9258464043668895811517441 6943848032751671858638081)
              ·
                refine ⟨5207886024563753893978561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6943848032751671858638081 5207886024563753893978561)
                ·
                  refine ⟨3905914518422815420483921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207886024563753893978561 3905914518422815420483921)
                  ·
                    refine ⟨2929435888817111565362941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3905914518422815420483921 2929435888817111565362941)
                    ·
                      refine ⟨1098538458306416837011103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929435888817111565362941 1098538458306416837011103)
                      ·
                        rfl

theorem cell23_2139396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2139396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139396 prefixEnd_2139396 := by exact prefixLift 2139396
  have htrace : WordTrace (prefixWord ++ tailWord_2139396) baseStart_2139396 baseEnd_2139396 := by
    simpa [prefixWord, tailWord_2139396, baseEnd_2139396] using wordTrace_append hprefix tailTrace_2139396
  have hstable : (prefixWord ++ tailWord_2139396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139396).length < 2 ^ (prefixWord ++ tailWord_2139396).sum := by decide
  have hdescent : baseEnd_2139396 < baseStart_2139396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139402 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2139402 : Nat := 118140960795 + 2139402 * 2 ^ 59
def prefixEnd_2139402 : Nat := 4983230072969 + 3 ^ 40 * 2139402 * 2
def baseEnd_2139402 : Nat := 1098541539190343813536075

theorem tailTrace_2139402 : CollatzResearch.WordTrace tailWord_2139402 prefixEnd_2139402 1098541539190343813536075 := by
  unfold tailWord_2139402
  simp only [CollatzResearch.WordTrace]
  refine ⟨19507600348829852404315115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52020267596879606411506973 19507600348829852404315115)
  ·
    refine ⟨29261400523244778606472673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19507600348829852404315115 29261400523244778606472673)
    ·
      refine ⟨21946050392433583954854505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29261400523244778606472673 21946050392433583954854505)
      ·
        refine ⟨16459537794325187966140879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21946050392433583954854505 16459537794325187966140879)
        ·
          refine ⟨24689306691487781949211319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16459537794325187966140879 24689306691487781949211319)
          ·
            refine ⟨37033960037231672923816979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24689306691487781949211319 37033960037231672923816979)
            ·
              refine ⟨55550940055847509385725469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37033960037231672923816979 55550940055847509385725469)
              ·
                refine ⟨20831602520942816019647051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55550940055847509385725469 20831602520942816019647051)
                ·
                  refine ⟨31247403781414224029470577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20831602520942816019647051 31247403781414224029470577)
                  ·
                    refine ⟨23435552836060668022102933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31247403781414224029470577 23435552836060668022102933)
                    ·
                      refine ⟨1098541539190343813536075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23435552836060668022102933 1098541539190343813536075)
                      ·
                        rfl

theorem cell23_2139402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2139402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139402 prefixEnd_2139402 := by exact prefixLift 2139402
  have htrace : WordTrace (prefixWord ++ tailWord_2139402) baseStart_2139402 baseEnd_2139402 := by
    simpa [prefixWord, tailWord_2139402, baseEnd_2139402] using wordTrace_append hprefix tailTrace_2139402
  have hstable : (prefixWord ++ tailWord_2139402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139402).length < 2 ^ (prefixWord ++ tailWord_2139402).sum := by decide
  have hdescent : baseEnd_2139402 < baseStart_2139402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139403 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 1, 4]
def baseStart_2139403 : Nat := 118140960795 + 2139403 * 2 ^ 59
def prefixEnd_2139403 : Nat := 4983230072969 + 3 ^ 40 * 2139403 * 2
def baseEnd_2139403 : Nat := 366180684223666103207857

theorem tailTrace_2139403 : CollatzResearch.WordTrace tailWord_2139403 prefixEnd_2139403 366180684223666103207857 := by
  unfold tailWord_2139403
  simp only [CollatzResearch.WordTrace]
  refine ⟨78030437868315786788046863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52020291912210524525364575 78030437868315786788046863)
  ·
    refine ⟨117045656802473680182070295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78030437868315786788046863 117045656802473680182070295)
    ·
      refine ⟨175568485203710520273105443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117045656802473680182070295 175568485203710520273105443)
      ·
        refine ⟨263352727805565780409658165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175568485203710520273105443 263352727805565780409658165)
        ·
          refine ⟨24689318231771791913405453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263352727805565780409658165 24689318231771791913405453)
          ·
            refine ⟨9258494336914421967527045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24689318231771791913405453 9258494336914421967527045)
            ·
              refine ⟨1735967688171454118911321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9258494336914421967527045 1735967688171454118911321)
              ·
                refine ⟨1301975766128590589183491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735967688171454118911321 1301975766128590589183491)
                ·
                  refine ⟨1952963649192885883775237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301975766128590589183491 1952963649192885883775237)
                  ·
                    refine ⟨366180684223666103207857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1952963649192885883775237 366180684223666103207857)
                    ·
                      rfl

theorem cell23_2139403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 4].length) (baseStart_2139403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139403 prefixEnd_2139403 := by exact prefixLift 2139403
  have htrace : WordTrace (prefixWord ++ tailWord_2139403) baseStart_2139403 baseEnd_2139403 := by
    simpa [prefixWord, tailWord_2139403, baseEnd_2139403] using wordTrace_append hprefix tailTrace_2139403
  have hstable : (prefixWord ++ tailWord_2139403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139403).length < 2 ^ (prefixWord ++ tailWord_2139403).sum := by decide
  have hdescent : baseEnd_2139403 < baseStart_2139403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139410 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2139410 : Nat := 118140960795 + 2139410 * 2 ^ 59
def prefixEnd_2139410 : Nat := 4983230072969 + 3 ^ 40 * 2139410 * 2
def baseEnd_2139410 : Nat := 1098545647035579782236039

theorem tailTrace_2139410 : CollatzResearch.WordTrace tailWord_2139410 prefixEnd_2139410 1098545647035579782236039 := by
  unfold tailWord_2139410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19507673294822606745887921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52020462119526951322367789 19507673294822606745887921)
  ·
    refine ⟨14630754971116955059415941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19507673294822606745887921 14630754971116955059415941)
    ·
      refine ⟨2743266557084429073640489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14630754971116955059415941 2743266557084429073640489)
      ·
        refine ⟨2057449917813321805230367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2743266557084429073640489 2057449917813321805230367)
        ·
          refine ⟨3086174876719982707845551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057449917813321805230367 3086174876719982707845551)
          ·
            refine ⟨4629262315079974061768327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086174876719982707845551 4629262315079974061768327)
            ·
              refine ⟨6943893472619961092652491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629262315079974061768327 6943893472619961092652491)
              ·
                refine ⟨10415840208929941638978737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943893472619961092652491 10415840208929941638978737)
                ·
                  refine ⟨7811880156697456229234053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10415840208929941638978737 7811880156697456229234053)
                  ·
                    refine ⟨1464727529380773042981385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7811880156697456229234053 1464727529380773042981385)
                    ·
                      refine ⟨1098545647035579782236039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464727529380773042981385 1098545647035579782236039)
                      ·
                        rfl

theorem cell23_2139410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2139410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139410 prefixEnd_2139410 := by exact prefixLift 2139410
  have htrace : WordTrace (prefixWord ++ tailWord_2139410) baseStart_2139410 baseEnd_2139410 := by
    simpa [prefixWord, tailWord_2139410, baseEnd_2139410] using wordTrace_append hprefix tailTrace_2139410
  have hstable : (prefixWord ++ tailWord_2139410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139410).length < 2 ^ (prefixWord ++ tailWord_2139410).sum := by decide
  have hdescent : baseEnd_2139410 < baseStart_2139410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139419 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 1, 5, 2]
def baseStart_2139419 : Nat := 118140960795 + 2139419 * 2 ^ 59
def prefixEnd_2139419 : Nat := 4983230072969 + 3 ^ 40 * 2139419 * 2
def baseEnd_2139419 : Nat := 1098550268361470247023497

theorem tailTrace_2139419 : CollatzResearch.WordTrace tailWord_2139419 prefixEnd_2139419 1098550268361470247023497 := by
  unfold tailWord_2139419
  simp only [CollatzResearch.WordTrace]
  refine ⟨78031021436257821520629311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52020680957505214347086207 78031021436257821520629311)
  ·
    refine ⟨117046532154386732280943967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78031021436257821520629311 117046532154386732280943967)
    ·
      refine ⟨175569798231580098421415951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117046532154386732280943967 175569798231580098421415951)
      ·
        refine ⟨263354697347370147632123927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175569798231580098421415951 263354697347370147632123927)
        ·
          refine ⟨395032046021055221448185891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263354697347370147632123927 395032046021055221448185891)
          ·
            refine ⟨592548069031582832172278837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395032046021055221448185891 592548069031582832172278837)
            ·
              refine ⟨55551381471710890516151141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 592548069031582832172278837 55551381471710890516151141)
              ·
                refine ⟨10415884025945791971778339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55551381471710890516151141 10415884025945791971778339)
                ·
                  refine ⟨15623826038918687957667509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10415884025945791971778339 15623826038918687957667509)
                  ·
                    refine ⟨1464733691148626996031329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15623826038918687957667509 1464733691148626996031329)
                    ·
                      refine ⟨1098550268361470247023497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464733691148626996031329 1098550268361470247023497)
                      ·
                        rfl

theorem cell23_2139419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5, 2].length) (baseStart_2139419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139419 prefixEnd_2139419 := by exact prefixLift 2139419
  have htrace : WordTrace (prefixWord ++ tailWord_2139419) baseStart_2139419 baseEnd_2139419 := by
    simpa [prefixWord, tailWord_2139419, baseEnd_2139419] using wordTrace_append hprefix tailTrace_2139419
  have hstable : (prefixWord ++ tailWord_2139419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139419).length < 2 ^ (prefixWord ++ tailWord_2139419).sum := by decide
  have hdescent : baseEnd_2139419 < baseStart_2139419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139429 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_2139429 : Nat := 118140960795 + 2139429 * 2 ^ 59
def prefixEnd_2139429 : Nat := 4983230072969 + 3 ^ 40 * 2139429 * 2
def baseEnd_2139429 : Nat := 366185134389338402632817

theorem tailTrace_2139429 : CollatzResearch.WordTrace tailWord_2139429 prefixEnd_2139429 366185134389338402632817 := by
  unfold tailWord_2139429
  simp only [CollatzResearch.WordTrace]
  refine ⟨78031386166221593228493341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52020924110814395485662227 78031386166221593228493341)
  ·
    refine ⟨29261769812333097460685003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78031386166221593228493341 29261769812333097460685003)
    ·
      refine ⟨43892654718499646191027505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29261769812333097460685003 43892654718499646191027505)
      ·
        refine ⟨32919491038874734643270629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43892654718499646191027505 32919491038874734643270629)
        ·
          refine ⟨6172404569789012745613243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32919491038874734643270629 6172404569789012745613243)
          ·
            refine ⟨9258606854683519118419865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6172404569789012745613243 9258606854683519118419865)
            ·
              refine ⟨6943955141012639338814899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9258606854683519118419865 6943955141012639338814899)
              ·
                refine ⟨10415932711518959008222349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6943955141012639338814899 10415932711518959008222349)
                ·
                  refine ⟨3905974766819609628083381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10415932711518959008222349 3905974766819609628083381)
                  ·
                    refine ⟨366185134389338402632817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3905974766819609628083381 366185134389338402632817)
                    ·
                      rfl

theorem cell23_2139429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_2139429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139429 prefixEnd_2139429 := by exact prefixLift 2139429
  have htrace : WordTrace (prefixWord ++ tailWord_2139429) baseStart_2139429 baseEnd_2139429 := by
    simpa [prefixWord, tailWord_2139429, baseEnd_2139429] using wordTrace_append hprefix tailTrace_2139429
  have hstable : (prefixWord ++ tailWord_2139429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139429).length < 2 ^ (prefixWord ++ tailWord_2139429).sum := by decide
  have hdescent : baseEnd_2139429 < baseStart_2139429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139443 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 1, 1, 3]
def baseStart_2139443 : Nat := 118140960795 + 2139443 * 2 ^ 59
def prefixEnd_2139443 : Nat := 4983230072969 + 3 ^ 40 * 2139443 * 2
def baseEnd_2139443 : Nat := 1098562591897178153123387

theorem tailTrace_2139443 : CollatzResearch.WordTrace tailWord_2139443 prefixEnd_2139443 1098562591897178153123387 := by
  unfold tailWord_2139443
  simp only [CollatzResearch.WordTrace]
  refine ⟨78031896788170873619502983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52021264525447249079668655 78031896788170873619502983)
  ·
    refine ⟨117047845182256310429254475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78031896788170873619502983 117047845182256310429254475)
    ·
      refine ⟨175571767773384465643881713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117047845182256310429254475 175571767773384465643881713)
      ·
        refine ⟨131678825830038349232911285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175571767773384465643881713 131678825830038349232911285)
        ·
          refine ⟨12344889921566095240585433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131678825830038349232911285 12344889921566095240585433)
          ·
            refine ⟨9258667441174571430439075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12344889921566095240585433 9258667441174571430439075)
            ·
              refine ⟨13888001161761857145658613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9258667441174571430439075 13888001161761857145658613)
              ·
                refine ⟨1302000108915174107405495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13888001161761857145658613 1302000108915174107405495)
                ·
                  refine ⟨1953000163372761161108243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302000108915174107405495 1953000163372761161108243)
                  ·
                    refine ⟨2929500245059141741662365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953000163372761161108243 2929500245059141741662365)
                    ·
                      refine ⟨1098562591897178153123387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929500245059141741662365 1098562591897178153123387)
                      ·
                        rfl

theorem cell23_2139443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 1, 3].length) (baseStart_2139443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139443 prefixEnd_2139443 := by exact prefixLift 2139443
  have htrace : WordTrace (prefixWord ++ tailWord_2139443) baseStart_2139443 baseEnd_2139443 := by
    simpa [prefixWord, tailWord_2139443, baseEnd_2139443] using wordTrace_append hprefix tailTrace_2139443
  have hstable : (prefixWord ++ tailWord_2139443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139443).length < 2 ^ (prefixWord ++ tailWord_2139443).sum := by decide
  have hdescent : baseEnd_2139443 < baseStart_2139443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139460 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2139460 : Nat := 118140960795 + 2139460 * 2 ^ 59
def prefixEnd_2139460 : Nat := 4983230072969 + 3 ^ 40 * 2139460 * 2
def baseEnd_2139460 : Nat := 1098571321068304586610809

theorem tailTrace_2139460 : CollatzResearch.WordTrace tailWord_2139460 prefixEnd_2139460 1098571321068304586610809 := by
  unfold tailWord_2139460
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016258414554642761435917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52021677886072857015247889 39016258414554642761435917)
  ·
    refine ⟨14631096905457991035538469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39016258414554642761435917 14631096905457991035538469)
    ·
      refine ⟨2743330669773373319163463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14631096905457991035538469 2743330669773373319163463)
      ·
        refine ⟨4114996004660059978745195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743330669773373319163463 4114996004660059978745195)
        ·
          refine ⟨6172494006990089968117793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114996004660059978745195 6172494006990089968117793)
          ·
            refine ⟨4629370505242567476088345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6172494006990089968117793 4629370505242567476088345)
            ·
              refine ⟨3472027878931925607066259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4629370505242567476088345 3472027878931925607066259)
              ·
                refine ⟨5208041818397888410599389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472027878931925607066259 5208041818397888410599389)
                ·
                  refine ⟨1953015681899208153974771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5208041818397888410599389 1953015681899208153974771)
                  ·
                    refine ⟨2929523522848812230962157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953015681899208153974771 2929523522848812230962157)
                    ·
                      refine ⟨1098571321068304586610809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929523522848812230962157 1098571321068304586610809)
                      ·
                        rfl

theorem cell23_2139460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2139460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139460 prefixEnd_2139460 := by exact prefixLift 2139460
  have htrace : WordTrace (prefixWord ++ tailWord_2139460) baseStart_2139460 baseEnd_2139460 := by
    simpa [prefixWord, tailWord_2139460, baseEnd_2139460] using wordTrace_append hprefix tailTrace_2139460
  have hstable : (prefixWord ++ tailWord_2139460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139460).length < 2 ^ (prefixWord ++ tailWord_2139460).sum := by decide
  have hdescent : baseEnd_2139460 < baseStart_2139460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139472 : List Nat := [2, 1, 1, 1, 1, 5, 2, 10]
def baseStart_2139472 : Nat := 118140960795 + 2139472 * 2 ^ 59
def prefixEnd_2139472 : Nat := 4983230072969 + 3 ^ 40 * 2139472 * 2
def baseEnd_2139472 : Nat := 40688054919857723691139

theorem tailTrace_2139472 : CollatzResearch.WordTrace tailWord_2139472 prefixEnd_2139472 40688054919857723691139 := by
  unfold tailWord_2139472
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016477252532905786154335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52021969670043874381539113 39016477252532905786154335)
  ·
    refine ⟨58524715878799358679231503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39016477252532905786154335 58524715878799358679231503)
    ·
      refine ⟨87787073818199038018847255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58524715878799358679231503 87787073818199038018847255)
      ·
        refine ⟨131680610727298557028270883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87787073818199038018847255 131680610727298557028270883)
        ·
          refine ⟨197520916090947835542406325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131680610727298557028270883 197520916090947835542406325)
          ·
            refine ⟨18517585883526359582100593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197520916090947835542406325 18517585883526359582100593)
            ·
              refine ⟨13888189412644769686575445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18517585883526359582100593 13888189412644769686575445)
              ·
                refine ⟨40688054919857723691139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13888189412644769686575445 40688054919857723691139)
                ·
                  rfl

theorem cell23_2139472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 10].length) (baseStart_2139472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139472 prefixEnd_2139472 := by exact prefixLift 2139472
  have htrace : WordTrace (prefixWord ++ tailWord_2139472) baseStart_2139472 baseEnd_2139472 := by
    simpa [prefixWord, tailWord_2139472, baseEnd_2139472] using wordTrace_append hprefix tailTrace_2139472
  have hstable : (prefixWord ++ tailWord_2139472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139472).length < 2 ^ (prefixWord ++ tailWord_2139472).sum := by decide
  have hdescent : baseEnd_2139472 < baseStart_2139472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139479 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_2139479 : Nat := 118140960795 + 2139479 * 2 ^ 59
def prefixEnd_2139479 : Nat := 4983230072969 + 3 ^ 40 * 2139479 * 2
def baseEnd_2139479 : Nat := 1098581077200740012273221

theorem tailTrace_2139479 : CollatzResearch.WordTrace tailWord_2139479 prefixEnd_2139479 1098581077200740012273221 := by
  unfold tailWord_2139479
  simp only [CollatzResearch.WordTrace]
  refine ⟨78033209816040451767813491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52022139877360301178542327 78033209816040451767813491)
  ·
    refine ⟨117049814724060677651720237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78033209816040451767813491 117049814724060677651720237)
    ·
      refine ⟨43893680521522754119395089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117049814724060677651720237 43893680521522754119395089)
      ·
        refine ⟨32920260391142065589546317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43893680521522754119395089 32920260391142065589546317)
        ·
          refine ⟨12345097646678274596079869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32920260391142065589546317 12345097646678274596079869)
          ·
            refine ⟨4629411617504352973529951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12345097646678274596079869 4629411617504352973529951)
            ·
              refine ⟨6944117426256529460294927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629411617504352973529951 6944117426256529460294927)
              ·
                refine ⟨10416176139384794190442391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6944117426256529460294927 10416176139384794190442391)
                ·
                  refine ⟨15624264209077191285663587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10416176139384794190442391 15624264209077191285663587)
                  ·
                    refine ⟨23436396313615786928495381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15624264209077191285663587 23436396313615786928495381)
                    ·
                      refine ⟨1098581077200740012273221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23436396313615786928495381 1098581077200740012273221)
                      ·
                        rfl

theorem cell23_2139479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_2139479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139479 prefixEnd_2139479 := by exact prefixLift 2139479
  have htrace : WordTrace (prefixWord ++ tailWord_2139479) baseStart_2139479 baseEnd_2139479 := by
    simpa [prefixWord, tailWord_2139479, baseEnd_2139479] using wordTrace_append hprefix tailTrace_2139479
  have hstable : (prefixWord ++ tailWord_2139479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139479).length < 2 ^ (prefixWord ++ tailWord_2139479).sum := by decide
  have hdescent : baseEnd_2139479 < baseStart_2139479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139516 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_2139516 : Nat := 118140960795 + 2139516 * 2 ^ 59
def prefixEnd_2139516 : Nat := 4983230072969 + 3 ^ 40 * 2139516 * 2
def baseEnd_2139516 : Nat := 1098600075984956367510551

theorem tailTrace_2139516 : CollatzResearch.WordTrace tailWord_2139516 prefixEnd_2139516 1098600075984956367510551 := by
  unfold tailWord_2139516
  simp only [CollatzResearch.WordTrace]
  refine ⟨39017279658453203543455201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52023039544604271391273601 39017279658453203543455201)
  ·
    refine ⟨29262959743839902657591401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39017279658453203543455201 29262959743839902657591401)
    ·
      refine ⟨21947219807879926993193551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29262959743839902657591401 21947219807879926993193551)
      ·
        refine ⟨32920829711819890489790327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21947219807879926993193551 32920829711819890489790327)
        ·
          refine ⟨49381244567729835734685491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32920829711819890489790327 49381244567729835734685491)
          ·
            refine ⟨74071866851594753602028237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49381244567729835734685491 74071866851594753602028237)
            ·
              refine ⟨27776950069348032600760589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74071866851594753602028237 27776950069348032600760589)
              ·
                refine ⟨10416356276005512225285221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27776950069348032600760589 10416356276005512225285221)
                ·
                  refine ⟨1953066801751033542240979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10416356276005512225285221 1953066801751033542240979)
                  ·
                    refine ⟨2929600202626550313361469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953066801751033542240979 2929600202626550313361469)
                    ·
                      refine ⟨1098600075984956367510551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929600202626550313361469 1098600075984956367510551)
                      ·
                        rfl

theorem cell23_2139516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_2139516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139516 prefixEnd_2139516 := by exact prefixLift 2139516
  have htrace : WordTrace (prefixWord ++ tailWord_2139516) baseStart_2139516 baseEnd_2139516 := by
    simpa [prefixWord, tailWord_2139516, baseEnd_2139516] using wordTrace_append hprefix tailTrace_2139516
  have hstable : (prefixWord ++ tailWord_2139516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139516).length < 2 ^ (prefixWord ++ tailWord_2139516).sum := by decide
  have hdescent : baseEnd_2139516 < baseStart_2139516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139517 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_2139517 : Nat := 118140960795 + 2139517 * 2 ^ 59
def prefixEnd_2139517 : Nat := 4983230072969 + 3 ^ 40 * 2139517 * 2
def baseEnd_2139517 : Nat := 1098600589465610863598047

theorem tailTrace_2139517 : CollatzResearch.WordTrace tailWord_2139517 prefixEnd_2139517 1098600589465610863598047 := by
  unfold tailWord_2139517
  simp only [CollatzResearch.WordTrace]
  refine ⟨78034595789902784257696805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52023063859935189505131203 78034595789902784257696805)
  ·
    refine ⟨14631486710606772048318151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78034595789902784257696805 14631486710606772048318151)
    ·
      refine ⟨21947230065910158072477227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14631486710606772048318151 21947230065910158072477227)
      ·
        refine ⟨32920845098865237108715841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21947230065910158072477227 32920845098865237108715841)
        ·
          refine ⟨24690633824148927831536881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32920845098865237108715841 24690633824148927831536881)
          ·
            refine ⟨18517975368111695873652661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24690633824148927831536881 18517975368111695873652661)
            ·
              refine ⟨1736060190760471488154937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18517975368111695873652661 1736060190760471488154937)
              ·
                refine ⟨1302045143070353616116203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736060190760471488154937 1302045143070353616116203)
                ·
                  refine ⟨1953067714605530424174305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302045143070353616116203 1953067714605530424174305)
                  ·
                    refine ⟨1464800785954147818130729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953067714605530424174305 1464800785954147818130729)
                    ·
                      refine ⟨1098600589465610863598047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464800785954147818130729 1098600589465610863598047)
                      ·
                        rfl

theorem cell23_2139517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_2139517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139517 prefixEnd_2139517 := by exact prefixLift 2139517
  have htrace : WordTrace (prefixWord ++ tailWord_2139517) baseStart_2139517 baseEnd_2139517 := by
    simpa [prefixWord, tailWord_2139517, baseEnd_2139517] using wordTrace_append hprefix tailTrace_2139517
  have hstable : (prefixWord ++ tailWord_2139517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139517).length < 2 ^ (prefixWord ++ tailWord_2139517).sum := by decide
  have hdescent : baseEnd_2139517 < baseStart_2139517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139550 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2139550 : Nat := 118140960795 + 2139550 * 2 ^ 59
def prefixEnd_2139550 : Nat := 4983230072969 + 3 ^ 40 * 2139550 * 2
def baseEnd_2139550 : Nat := 1098617534327209234485395

theorem tailTrace_2139550 : CollatzResearch.WordTrace tailWord_2139550 prefixEnd_2139550 1098617534327209234485395 := by
  unfold tailWord_2139550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9754474924847903861706013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52023866265855487262432069 9754474924847903861706013)
  ·
    refine ⟨3657928096817963948139755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9754474924847903861706013 3657928096817963948139755)
    ·
      refine ⟨5486892145226945922209633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3657928096817963948139755 5486892145226945922209633)
      ·
        refine ⟨4115169108920209441657225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5486892145226945922209633 4115169108920209441657225)
        ·
          refine ⟨3086376831690157081242919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4115169108920209441657225 3086376831690157081242919)
          ·
            refine ⟨4629565247535235621864379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086376831690157081242919 4629565247535235621864379)
            ·
              refine ⟨6944347871302853432796569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629565247535235621864379 6944347871302853432796569)
              ·
                refine ⟨5208260903477140074597427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944347871302853432796569 5208260903477140074597427)
                ·
                  refine ⟨7812391355215710111896141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208260903477140074597427 7812391355215710111896141)
                  ·
                    refine ⟨2929646758205891291961053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7812391355215710111896141 2929646758205891291961053)
                    ·
                      refine ⟨1098617534327209234485395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929646758205891291961053 1098617534327209234485395)
                      ·
                        rfl

theorem cell23_2139550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2139550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139550 prefixEnd_2139550 := by exact prefixLift 2139550
  have htrace : WordTrace (prefixWord ++ tailWord_2139550) baseStart_2139550 baseEnd_2139550 := by
    simpa [prefixWord, tailWord_2139550, baseEnd_2139550] using wordTrace_append hprefix tailTrace_2139550
  have hstable : (prefixWord ++ tailWord_2139550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139550).length < 2 ^ (prefixWord ++ tailWord_2139550).sum := by decide
  have hdescent : baseEnd_2139550 < baseStart_2139550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139596 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 7]
def baseStart_2139596 : Nat := 118140960795 + 2139596 * 2 ^ 59
def prefixEnd_2139596 : Nat := 4983230072969 + 3 ^ 40 * 2139596 * 2
def baseEnd_2139596 : Nat := 122071239381924006056687

theorem tailTrace_2139596 : CollatzResearch.WordTrace tailWord_2139596 prefixEnd_2139596 122071239381924006056687 := by
  unfold tailWord_2139596
  simp only [CollatzResearch.WordTrace]
  refine ⟨39018738578308290374911321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52024984771077720499881761 39018738578308290374911321)
  ·
    refine ⟨29264053933731217781183491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39018738578308290374911321 29264053933731217781183491)
    ·
      refine ⟨43896080900596826671775237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29264053933731217781183491 43896080900596826671775237)
      ·
        refine ⟨8230515168861905000957857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43896080900596826671775237 8230515168861905000957857)
        ·
          refine ⟨6172886376646428750718393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8230515168861905000957857 6172886376646428750718393)
          ·
            refine ⟨4629664782484821563038795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6172886376646428750718393 4629664782484821563038795)
            ·
              refine ⟨6944497173727232344558193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629664782484821563038795 6944497173727232344558193)
              ·
                refine ⟨5208372880295424258418645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944497173727232344558193 5208372880295424258418645)
                ·
                  refine ⟨122071239381924006056687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5208372880295424258418645 122071239381924006056687)
                  ·
                    rfl

theorem cell23_2139596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_2139596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139596 prefixEnd_2139596 := by exact prefixLift 2139596
  have htrace : WordTrace (prefixWord ++ tailWord_2139596) baseStart_2139596 baseEnd_2139596 := by
    simpa [prefixWord, tailWord_2139596, baseEnd_2139596] using wordTrace_append hprefix tailTrace_2139596
  have hstable : (prefixWord ++ tailWord_2139596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139596).length < 2 ^ (prefixWord ++ tailWord_2139596).sum := by decide
  have hdescent : baseEnd_2139596 < baseStart_2139596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139613 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 5]
def baseStart_2139613 : Nat := 118140960795 + 2139613 * 2 ^ 59
def prefixEnd_2139613 : Nat := 4983230072969 + 3 ^ 40 * 2139613 * 2
def baseEnd_2139613 : Nat := 122072209289826943110845

theorem tailTrace_2139613 : CollatzResearch.WordTrace tailWord_2139613 prefixEnd_2139613 122072209289826943110845 := by
  unfold tailWord_2139613
  simp only [CollatzResearch.WordTrace]
  refine ⟨78038097197554992653191493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52025398131703328435460995 78038097197554992653191493)
  ·
    refine ⟨14632143224541561122473405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78038097197554992653191493 14632143224541561122473405)
    ·
      refine ⟨5487053709203085420927527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14632143224541561122473405 5487053709203085420927527)
      ·
        refine ⟨8230580563804628131391291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5487053709203085420927527 8230580563804628131391291)
        ·
          refine ⟨12345870845706942197086937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8230580563804628131391291 12345870845706942197086937)
          ·
            refine ⟨9259403134280206647815203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12345870845706942197086937 9259403134280206647815203)
            ·
              refine ⟨13889104701420309971722805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9259403134280206647815203 13889104701420309971722805)
              ·
                refine ⟨1302103565758154059849013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13889104701420309971722805 1302103565758154059849013)
                ·
                  refine ⟨122072209289826943110845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302103565758154059849013 122072209289826943110845)
                  ·
                    rfl

theorem cell23_2139613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_2139613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139613 prefixEnd_2139613 := by exact prefixLift 2139613
  have htrace : WordTrace (prefixWord ++ tailWord_2139613) baseStart_2139613 baseEnd_2139613 := by
    simpa [prefixWord, tailWord_2139613, baseEnd_2139613] using wordTrace_append hprefix tailTrace_2139613
  have hstable : (prefixWord ++ tailWord_2139613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139613).length < 2 ^ (prefixWord ++ tailWord_2139613).sum := by decide
  have hdescent : baseEnd_2139613 < baseStart_2139613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139616 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 7, 2]
def baseStart_2139616 : Nat := 118140960795 + 2139616 * 2 ^ 59
def prefixEnd_2139616 : Nat := 4983230072969 + 3 ^ 40 * 2139616 * 2
def baseEnd_2139616 : Nat := 1098651424050405976260091

theorem tailTrace_2139616 : CollatzResearch.WordTrace tailWord_2139616 prefixEnd_2139616 1098651424050405976260091 := by
  unfold tailWord_2139616
  simp only [CollatzResearch.WordTrace]
  refine ⟨39019103308272062082775351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52025471077696082777033801 39019103308272062082775351)
  ·
    refine ⟨58528654962408093124163027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39019103308272062082775351 58528654962408093124163027)
    ·
      refine ⟨87792982443612139686244541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58528654962408093124163027 87792982443612139686244541)
      ·
        refine ⟨32922368416354552382341703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87792982443612139686244541 32922368416354552382341703)
        ·
          refine ⟨49383552624531828573512555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32922368416354552382341703 49383552624531828573512555)
          ·
            refine ⟨74075328936797742860268833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49383552624531828573512555 74075328936797742860268833)
            ·
              refine ⟨55556496702598307145201625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74075328936797742860268833 55556496702598307145201625)
              ·
                refine ⟨41667372526948730358901219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55556496702598307145201625 41667372526948730358901219)
                ·
                  refine ⟨62501058790423095538351829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41667372526948730358901219 62501058790423095538351829)
                  ·
                    refine ⟨1464868565400541301680121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 62501058790423095538351829 1464868565400541301680121)
                    ·
                      refine ⟨1098651424050405976260091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464868565400541301680121 1098651424050405976260091)
                      ·
                        rfl

theorem cell23_2139616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_2139616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139616 prefixEnd_2139616 := by exact prefixLift 2139616
  have htrace : WordTrace (prefixWord ++ tailWord_2139616) baseStart_2139616 baseEnd_2139616 := by
    simpa [prefixWord, tailWord_2139616, baseEnd_2139616] using wordTrace_append hprefix tailTrace_2139616
  have hstable : (prefixWord ++ tailWord_2139616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139616).length < 2 ^ (prefixWord ++ tailWord_2139616).sum := by decide
  have hdescent : baseEnd_2139616 < baseStart_2139616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139703 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 6]
def baseStart_2139703 : Nat := 118140960795 + 2139703 * 2 ^ 59
def prefixEnd_2139703 : Nat := 4983230072969 + 3 ^ 40 * 2139703 * 2
def baseEnd_2139703 : Nat := 122077344096371903985799

theorem tailTrace_2139703 : CollatzResearch.WordTrace tailWord_2139703 prefixEnd_2139703 122077344096371903985799 := by
  unfold tailWord_2139703
  simp only [CollatzResearch.WordTrace]
  refine ⟨78041379767228938023967763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52027586511485958682645175 78041379767228938023967763)
  ·
    refine ⟨117062069650843407035951645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78041379767228938023967763 117062069650843407035951645)
    ·
      refine ⟨43898276119066277638481867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117062069650843407035951645 43898276119066277638481867)
      ·
        refine ⟨65847414178599416457722801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43898276119066277638481867 65847414178599416457722801)
        ·
          refine ⟨49385560633949562343292101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65847414178599416457722801 49385560633949562343292101)
          ·
            refine ⟨9259792618865542939367269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49385560633949562343292101 9259792618865542939367269)
            ·
              refine ⟨1736211116037289301131363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9259792618865542939367269 1736211116037289301131363)
              ·
                refine ⟨2604316674055933951697045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736211116037289301131363 2604316674055933951697045)
                ·
                  refine ⟨122077344096371903985799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2604316674055933951697045 122077344096371903985799)
                  ·
                    rfl

theorem cell23_2139703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 6].length) (baseStart_2139703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139703 prefixEnd_2139703 := by exact prefixLift 2139703
  have htrace : WordTrace (prefixWord ++ tailWord_2139703) baseStart_2139703 baseEnd_2139703 := by
    simpa [prefixWord, tailWord_2139703, baseEnd_2139703] using wordTrace_append hprefix tailTrace_2139703
  have hstable : (prefixWord ++ tailWord_2139703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139703).length < 2 ^ (prefixWord ++ tailWord_2139703).sum := by decide
  have hdescent : baseEnd_2139703 < baseStart_2139703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139747 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 1, 1, 3]
def baseStart_2139747 : Nat := 118140960795 + 2139747 * 2 ^ 59
def prefixEnd_2139747 : Nat := 4983230072969 + 3 ^ 40 * 2139747 * 2
def baseEnd_2139747 : Nat := 1098718690016144963721989

theorem tailTrace_2139747 : CollatzResearch.WordTrace tailWord_2139747 prefixEnd_2139747 1098718690016144963721989 := by
  unfold tailWord_2139747
  simp only [CollatzResearch.WordTrace]
  refine ⟨78042984579069533538569495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52028656386046355692379663 78042984579069533538569495)
  ·
    refine ⟨117064476868604300307854243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78042984579069533538569495 117064476868604300307854243)
    ·
      refine ⟨175596715302906450461781365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117064476868604300307854243 175596715302906450461781365)
      ·
        refine ⟨16462192059647479730792003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175596715302906450461781365 16462192059647479730792003)
        ·
          refine ⟨24693288089471219596188005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16462192059647479730792003 24693288089471219596188005)
          ·
            refine ⟨4629991516775853674285251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24693288089471219596188005 4629991516775853674285251)
            ·
              refine ⟨6944987275163780511427877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629991516775853674285251 6944987275163780511427877)
              ·
                refine ⟨1302185114093208845892727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6944987275163780511427877 1302185114093208845892727)
                ·
                  refine ⟨1953277671139813268839091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302185114093208845892727 1953277671139813268839091)
                  ·
                    refine ⟨2929916506709719903258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953277671139813268839091 2929916506709719903258637)
                    ·
                      refine ⟨1098718690016144963721989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2929916506709719903258637 1098718690016144963721989)
                      ·
                        rfl

theorem cell23_2139747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_2139747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139747 prefixEnd_2139747 := by exact prefixLift 2139747
  have htrace : WordTrace (prefixWord ++ tailWord_2139747) baseStart_2139747 baseEnd_2139747 := by
    simpa [prefixWord, tailWord_2139747, baseEnd_2139747] using wordTrace_append hprefix tailTrace_2139747
  have hstable : (prefixWord ++ tailWord_2139747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139747).length < 2 ^ (prefixWord ++ tailWord_2139747).sum := by decide
  have hdescent : baseEnd_2139747 < baseStart_2139747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139756 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_2139756 : Nat := 118140960795 + 2139756 * 2 ^ 59
def prefixEnd_2139756 : Nat := 4983230072969 + 3 ^ 40 * 2139756 * 2
def baseEnd_2139756 : Nat := 1098723311342035428509447

theorem tailTrace_2139756 : CollatzResearch.WordTrace tailWord_2139756 prefixEnd_2139756 1098723311342035428509447 := by
  unfold tailWord_2139756
  simp only [CollatzResearch.WordTrace]
  refine ⟨39021656418018464037823561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52028875224024618717098081 39021656418018464037823561)
  ·
    refine ⟨29266242313513848028367671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39021656418018464037823561 29266242313513848028367671)
    ·
      refine ⟨43899363470270772042551507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29266242313513848028367671 43899363470270772042551507)
      ·
        refine ⟨65849045205406158063827261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43899363470270772042551507 65849045205406158063827261)
        ·
          refine ⟨24693391952027309273935223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65849045205406158063827261 24693391952027309273935223)
          ·
            refine ⟨37040087928040963910902835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24693391952027309273935223 37040087928040963910902835)
            ·
              refine ⟨55560131892061445866354253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37040087928040963910902835 55560131892061445866354253)
              ·
                refine ⟨20835049459523042199882845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55560131892061445866354253 20835049459523042199882845)
                ·
                  refine ⟨7813143547321140824956067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20835049459523042199882845 7813143547321140824956067)
                  ·
                    refine ⟨11719715320981711237434101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7813143547321140824956067 11719715320981711237434101)
                    ·
                      refine ⟨1098723311342035428509447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11719715320981711237434101 1098723311342035428509447)
                      ·
                        rfl

theorem cell23_2139756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_2139756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139756 prefixEnd_2139756 := by exact prefixLift 2139756
  have htrace : WordTrace (prefixWord ++ tailWord_2139756) baseStart_2139756 baseEnd_2139756 := by
    simpa [prefixWord, tailWord_2139756, baseEnd_2139756] using wordTrace_append hprefix tailTrace_2139756
  have hstable : (prefixWord ++ tailWord_2139756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139756).length < 2 ^ (prefixWord ++ tailWord_2139756).sum := by decide
  have hdescent : baseEnd_2139756 < baseStart_2139756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139783 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_2139783 : Nat := 118140960795 + 2139783 * 2 ^ 59
def prefixEnd_2139783 : Nat := 4983230072969 + 3 ^ 40 * 2139783 * 2
def baseEnd_2139783 : Nat := 1098737175319706822871823

theorem tailTrace_2139783 : CollatzResearch.WordTrace tailWord_2139783 prefixEnd_2139783 1098737175319706822871823 := by
  unfold tailWord_2139783
  simp only [CollatzResearch.WordTrace]
  refine ⟨78044297606939111686880003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52029531737959407791253335 78044297606939111686880003)
  ·
    refine ⟨117066446410408667530320005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78044297606939111686880003 117066446410408667530320005)
    ·
      refine ⟨21949958701951625161935001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117066446410408667530320005 21949958701951625161935001)
      ·
        refine ⟨16462469026463718871451251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21949958701951625161935001 16462469026463718871451251)
        ·
          refine ⟨24693703539695578307176877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16462469026463718871451251 24693703539695578307176877)
          ·
            refine ⟨9260138827385841865191329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24693703539695578307176877 9260138827385841865191329)
            ·
              refine ⟨6945104120539381398893497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9260138827385841865191329 6945104120539381398893497)
              ·
                refine ⟨5208828090404536049170123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945104120539381398893497 5208828090404536049170123)
                ·
                  refine ⟨7813242135606804073755185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208828090404536049170123 7813242135606804073755185)
                  ·
                    refine ⟨5859931601705103055316389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7813242135606804073755185 5859931601705103055316389)
                    ·
                      refine ⟨1098737175319706822871823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5859931601705103055316389 1098737175319706822871823)
                      ·
                        rfl

theorem cell23_2139783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_2139783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139783 prefixEnd_2139783 := by exact prefixLift 2139783
  have htrace : WordTrace (prefixWord ++ tailWord_2139783) baseStart_2139783 baseEnd_2139783 := by
    simpa [prefixWord, tailWord_2139783, baseEnd_2139783] using wordTrace_append hprefix tailTrace_2139783
  have hstable : (prefixWord ++ tailWord_2139783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139783).length < 2 ^ (prefixWord ++ tailWord_2139783).sum := by decide
  have hdescent : baseEnd_2139783 < baseStart_2139783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139784 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 1, 5]
def baseStart_2139784 : Nat := 118140960795 + 2139784 * 2 ^ 59
def prefixEnd_2139784 : Nat := 4983230072969 + 3 ^ 40 * 2139784 * 2
def baseEnd_2139784 : Nat := 366245896266787106319773

theorem tailTrace_2139784 : CollatzResearch.WordTrace tailWord_2139784 prefixEnd_2139784 366245896266787106319773 := by
  unfold tailWord_2139784
  simp only [CollatzResearch.WordTrace]
  refine ⟨39022167039967744428833203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52029556053290325905110937 39022167039967744428833203)
  ·
    refine ⟨58533250559951616643249805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39022167039967744428833203 58533250559951616643249805)
    ·
      refine ⟨21949968959981856241218677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58533250559951616643249805 21949968959981856241218677)
      ·
        refine ⟨2057809589998299022614251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21949968959981856241218677 2057809589998299022614251)
        ·
          refine ⟨3086714384997448533921377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057809589998299022614251 3086714384997448533921377)
          ·
            refine ⟨2315035788748086400441033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3086714384997448533921377 2315035788748086400441033)
            ·
              refine ⟨1736276841561064800330775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315035788748086400441033 1736276841561064800330775)
              ·
                refine ⟨2604415262341597200496163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736276841561064800330775 2604415262341597200496163)
                ·
                  refine ⟨3906622893512395800744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604415262341597200496163 3906622893512395800744245)
                  ·
                    refine ⟨366245896266787106319773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3906622893512395800744245 366245896266787106319773)
                    ·
                      rfl

theorem cell23_2139784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_2139784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139784 prefixEnd_2139784 := by exact prefixLift 2139784
  have htrace : WordTrace (prefixWord ++ tailWord_2139784) baseStart_2139784 baseEnd_2139784 := by
    simpa [prefixWord, tailWord_2139784, baseEnd_2139784] using wordTrace_append hprefix tailTrace_2139784
  have hstable : (prefixWord ++ tailWord_2139784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139784).length < 2 ^ (prefixWord ++ tailWord_2139784).sum := by decide
  have hdescent : baseEnd_2139784 < baseStart_2139784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139804 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2139804 : Nat := 118140960795 + 2139804 * 2 ^ 59
def prefixEnd_2139804 : Nat := 4983230072969 + 3 ^ 40 * 2139804 * 2
def baseEnd_2139804 : Nat := 1098747958413451240709227

theorem tailTrace_2139804 : CollatzResearch.WordTrace tailWord_2139804 prefixEnd_2139804 1098747958413451240709227 := by
  unfold tailWord_2139804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39022531769931516136697233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52030042359908688182262977 39022531769931516136697233)
  ·
    refine ⟨29266898827448637102522925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39022531769931516136697233 29266898827448637102522925)
    ·
      refine ⟨10975087060293238913446097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29266898827448637102522925 10975087060293238913446097)
      ·
        refine ⟨8231315295219929185084573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10975087060293238913446097 8231315295219929185084573)
        ·
          refine ⟨3086743235707473444406715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8231315295219929185084573 3086743235707473444406715)
          ·
            refine ⟨4630114853561210166610073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086743235707473444406715 4630114853561210166610073)
            ·
              refine ⟨3472586140170907624957555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4630114853561210166610073 3472586140170907624957555)
              ·
                refine ⟨5208879210256361437436333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472586140170907624957555 5208879210256361437436333)
                ·
                  refine ⟨1953329703846135539038625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5208879210256361437436333 1953329703846135539038625)
                  ·
                    refine ⟨1464997277884601654278969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953329703846135539038625 1464997277884601654278969)
                    ·
                      refine ⟨1098747958413451240709227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1464997277884601654278969 1098747958413451240709227)
                      ·
                        rfl

theorem cell23_2139804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2139804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139804 prefixEnd_2139804 := by exact prefixLift 2139804
  have htrace : WordTrace (prefixWord ++ tailWord_2139804) baseStart_2139804 baseEnd_2139804 := by
    simpa [prefixWord, tailWord_2139804, baseEnd_2139804] using wordTrace_append hprefix tailTrace_2139804
  have hstable : (prefixWord ++ tailWord_2139804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139804).length < 2 ^ (prefixWord ++ tailWord_2139804).sum := by decide
  have hdescent : baseEnd_2139804 < baseStart_2139804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139856 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_2139856 : Nat := 118140960795 + 2139856 * 2 ^ 59
def prefixEnd_2139856 : Nat := 4983230072969 + 3 ^ 40 * 2139856 * 2
def baseEnd_2139856 : Nat := 1098774659407485037258987

theorem tailTrace_2139856 : CollatzResearch.WordTrace tailWord_2139856 prefixEnd_2139856 1098774659407485037258987 := by
  unfold tailWord_2139856
  simp only [CollatzResearch.WordTrace]
  refine ⟨39023480067837322577143711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52031306757116430102858281 39023480067837322577143711)
  ·
    refine ⟨58535220101755983865715567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39023480067837322577143711 58535220101755983865715567)
    ·
      refine ⟨87802830152633975798573351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58535220101755983865715567 87802830152633975798573351)
      ·
        refine ⟨131704245228950963697860027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87802830152633975798573351 131704245228950963697860027)
        ·
          refine ⟨197556367843426445546790041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131704245228950963697860027 197556367843426445546790041)
          ·
            refine ⟨148167275882569834160092531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197556367843426445546790041 148167275882569834160092531)
            ·
              refine ⟨222250913823854751240138797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148167275882569834160092531 222250913823854751240138797)
              ·
                refine ⟨83344092683945531715052049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222250913823854751240138797 83344092683945531715052049)
                ·
                  refine ⟨62508069512959148786289037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83344092683945531715052049 62508069512959148786289037)
                  ·
                    refine ⟨23440526067359680794858389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62508069512959148786289037 23440526067359680794858389)
                    ·
                      refine ⟨1098774659407485037258987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23440526067359680794858389 1098774659407485037258987)
                      ·
                        rfl

theorem cell23_2139856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_2139856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139856 prefixEnd_2139856 := by exact prefixLift 2139856
  have htrace : WordTrace (prefixWord ++ tailWord_2139856) baseStart_2139856 baseEnd_2139856 := by
    simpa [prefixWord, tailWord_2139856, baseEnd_2139856] using wordTrace_append hprefix tailTrace_2139856
  have hstable : (prefixWord ++ tailWord_2139856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139856).length < 2 ^ (prefixWord ++ tailWord_2139856).sum := by decide
  have hdescent : baseEnd_2139856 < baseStart_2139856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139863 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_2139863 : Nat := 118140960795 + 2139863 * 2 ^ 59
def prefixEnd_2139863 : Nat := 4983230072969 + 3 ^ 40 * 2139863 * 2
def baseEnd_2139863 : Nat := 1098778253772066509871455

theorem tailTrace_2139863 : CollatzResearch.WordTrace tailWord_2139863 prefixEnd_2139863 1098778253772066509871455 := by
  unfold tailWord_2139863
  simp only [CollatzResearch.WordTrace]
  refine ⟨78047215446649285349792243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52031476964432856899861495 78047215446649285349792243)
  ·
    refine ⟨117070823169973928024688365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78047215446649285349792243 117070823169973928024688365)
    ·
      refine ⟨43901558688740223009258137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117070823169973928024688365 43901558688740223009258137)
      ·
        refine ⟨32926169016555167256943603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43901558688740223009258137 32926169016555167256943603)
        ·
          refine ⟨49389253524832750885415405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32926169016555167256943603 49389253524832750885415405)
          ·
            refine ⟨18520970071812281582030777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49389253524832750885415405 18520970071812281582030777)
            ·
              refine ⟨13890727553859211186523083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18520970071812281582030777 13890727553859211186523083)
              ·
                refine ⟨20836091330788816779784625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13890727553859211186523083 20836091330788816779784625)
                ·
                  refine ⟨15627068498091612584838469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20836091330788816779784625 15627068498091612584838469)
                  ·
                    refine ⟨2930075343392177359657213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15627068498091612584838469 2930075343392177359657213)
                    ·
                      refine ⟨1098778253772066509871455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930075343392177359657213 1098778253772066509871455)
                      ·
                        rfl

theorem cell23_2139863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_2139863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139863 prefixEnd_2139863 := by exact prefixLift 2139863
  have htrace : WordTrace (prefixWord ++ tailWord_2139863) baseStart_2139863 baseEnd_2139863 := by
    simpa [prefixWord, tailWord_2139863, baseEnd_2139863] using wordTrace_append hprefix tailTrace_2139863
  have hstable : (prefixWord ++ tailWord_2139863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139863).length < 2 ^ (prefixWord ++ tailWord_2139863).sum := by decide
  have hdescent : baseEnd_2139863 < baseStart_2139863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139900 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 5]
def baseStart_2139900 : Nat := 118140960795 + 2139900 * 2 ^ 59
def prefixEnd_2139900 : Nat := 4983230072969 + 3 ^ 40 * 2139900 * 2
def baseEnd_2139900 : Nat := 122088583617364762789865

theorem tailTrace_2139900 : CollatzResearch.WordTrace tailWord_2139900 prefixEnd_2139900 122088583617364762789865 := by
  unfold tailWord_2139900
  simp only [CollatzResearch.WordTrace]
  refine ⟨39024282473757620334444577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52032376631676827112592769 39024282473757620334444577)
  ·
    refine ⟨29268211855318215250833433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39024282473757620334444577 29268211855318215250833433)
    ·
      refine ⟨21951158891488661438125075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29268211855318215250833433 21951158891488661438125075)
      ·
        refine ⟨32926738337232992157187613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21951158891488661438125075 32926738337232992157187613)
        ·
          refine ⟨12347526876462372058945355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32926738337232992157187613 12347526876462372058945355)
          ·
            refine ⟨18521290314693558088418033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12347526876462372058945355 18521290314693558088418033)
            ·
              refine ⟨13890967736020168566313525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18521290314693558088418033 13890967736020168566313525)
              ·
                refine ⟨1302278225251890803091893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13890967736020168566313525 1302278225251890803091893)
                ·
                  refine ⟨122088583617364762789865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302278225251890803091893 122088583617364762789865)
                  ·
                    rfl

theorem cell23_2139900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_2139900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139900 prefixEnd_2139900 := by exact prefixLift 2139900
  have htrace : WordTrace (prefixWord ++ tailWord_2139900) baseStart_2139900 baseEnd_2139900 := by
    simpa [prefixWord, tailWord_2139900, baseEnd_2139900] using wordTrace_append hprefix tailTrace_2139900
  have hstable : (prefixWord ++ tailWord_2139900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139900).length < 2 ^ (prefixWord ++ tailWord_2139900).sum := by decide
  have hdescent : baseEnd_2139900 < baseStart_2139900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139911 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2139911 : Nat := 118140960795 + 2139911 * 2 ^ 59
def prefixEnd_2139911 : Nat := 4983230072969 + 3 ^ 40 * 2139911 * 2
def baseEnd_2139911 : Nat := 1098802900843482322071235

theorem tailTrace_2139911 : CollatzResearch.WordTrace tailWord_2139911 prefixEnd_2139911 1098802900843482322071235 := by
  unfold tailWord_2139911
  simp only [CollatzResearch.WordTrace]
  refine ⟨78048966150475389547539587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52032644100316926365026391 78048966150475389547539587)
  ·
    refine ⟨117073449225713084321309381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78048966150475389547539587 117073449225713084321309381)
    ·
      refine ⟨21951271729821203310245509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117073449225713084321309381 21951271729821203310245509)
      ·
        refine ⟨4115863449341475620671033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21951271729821203310245509 4115863449341475620671033)
        ·
          refine ⟨3086897587006106715503275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4115863449341475620671033 3086897587006106715503275)
          ·
            refine ⟨4630346380509160073254913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086897587006106715503275 4630346380509160073254913)
            ·
              refine ⟨3472759785381870054941185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4630346380509160073254913 3472759785381870054941185)
              ·
                refine ⟨2604569839036402541205889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3472759785381870054941185 2604569839036402541205889)
                ·
                  refine ⟨1953427379277301905904417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2604569839036402541205889 1953427379277301905904417)
                  ·
                    refine ⟨1465070534457976429428313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953427379277301905904417 1465070534457976429428313)
                    ·
                      refine ⟨1098802900843482322071235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465070534457976429428313 1098802900843482322071235)
                      ·
                        rfl

theorem cell23_2139911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2139911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139911 prefixEnd_2139911 := by exact prefixLift 2139911
  have htrace : WordTrace (prefixWord ++ tailWord_2139911) baseStart_2139911 baseEnd_2139911 := by
    simpa [prefixWord, tailWord_2139911, baseEnd_2139911] using wordTrace_append hprefix tailTrace_2139911
  have hstable : (prefixWord ++ tailWord_2139911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139911).length < 2 ^ (prefixWord ++ tailWord_2139911).sum := by decide
  have hdescent : baseEnd_2139911 < baseStart_2139911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139934 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2139934 : Nat := 118140960795 + 2139934 * 2 ^ 59
def prefixEnd_2139934 : Nat := 4983230072969 + 3 ^ 40 * 2139934 * 2
def baseEnd_2139934 : Nat := 122090523433170636898181

theorem tailTrace_2139934 : CollatzResearch.WordTrace tailWord_2139934 prefixEnd_2139934 122090523433170636898181 := by
  unfold tailWord_2139934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9756225628674008059453357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52033203352928042983751237 9756225628674008059453357)
  ·
    refine ⟨3658584610752753022295009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9756225628674008059453357 3658584610752753022295009)
    ·
      refine ⟨2743938458064564766721257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3658584610752753022295009 2743938458064564766721257)
      ·
        refine ⟨2057953843548423575040943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2743938458064564766721257 2057953843548423575040943)
        ·
          refine ⟨3086930765322635362561415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057953843548423575040943 3086930765322635362561415)
          ·
            refine ⟨4630396147983953043842123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086930765322635362561415 4630396147983953043842123)
            ·
              refine ⟨6945594221975929565763185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630396147983953043842123 6945594221975929565763185)
              ·
                refine ⟨5209195666481947174322389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945594221975929565763185 5209195666481947174322389)
                ·
                  refine ⟨122090523433170636898181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5209195666481947174322389 122090523433170636898181)
                  ·
                    rfl

theorem cell23_2139934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2139934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139934 prefixEnd_2139934 := by exact prefixLift 2139934
  have htrace : WordTrace (prefixWord ++ tailWord_2139934) baseStart_2139934 baseEnd_2139934 := by
    simpa [prefixWord, tailWord_2139934, baseEnd_2139934] using wordTrace_append hprefix tailTrace_2139934
  have hstable : (prefixWord ++ tailWord_2139934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139934).length < 2 ^ (prefixWord ++ tailWord_2139934).sum := by decide
  have hdescent : baseEnd_2139934 < baseStart_2139934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139973 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 8]
def baseStart_2139973 : Nat := 118140960795 + 2139973 * 2 ^ 59
def prefixEnd_2139973 : Nat := 4983230072969 + 3 ^ 40 * 2139973 * 2
def baseEnd_2139973 : Nat := 122092748516006786610661

theorem tailTrace_2139973 : CollatzResearch.WordTrace tailWord_2139973 prefixEnd_2139973 122092748516006786610661 := by
  unfold tailWord_2139973
  simp only [CollatzResearch.WordTrace]
  refine ⟨78051227476250774136296573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52034151650833849424197715 78051227476250774136296573)
  ·
    refine ⟨29269210303594040301111215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78051227476250774136296573 29269210303594040301111215)
    ·
      refine ⟨43903815455391060451666823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29269210303594040301111215 43903815455391060451666823)
      ·
        refine ⟨65855723183086590677500235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43903815455391060451666823 65855723183086590677500235)
        ·
          refine ⟨98783584774629886016250353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65855723183086590677500235 98783584774629886016250353)
          ·
            refine ⟨74087688580972414512187765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98783584774629886016250353 74087688580972414512187765)
            ·
              refine ⟨6945720804466163860517603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74087688580972414512187765 6945720804466163860517603)
              ·
                refine ⟨10418581206699245790776405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6945720804466163860517603 10418581206699245790776405)
                ·
                  refine ⟨122092748516006786610661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10418581206699245790776405 122092748516006786610661)
                  ·
                    rfl

theorem cell23_2139973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_2139973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139973 prefixEnd_2139973 := by exact prefixLift 2139973
  have htrace : WordTrace (prefixWord ++ tailWord_2139973) baseStart_2139973 baseEnd_2139973 := by
    simpa [prefixWord, tailWord_2139973, baseEnd_2139973] using wordTrace_append hprefix tailTrace_2139973
  have hstable : (prefixWord ++ tailWord_2139973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139973).length < 2 ^ (prefixWord ++ tailWord_2139973).sum := by decide
  have hdescent : baseEnd_2139973 < baseStart_2139973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139977 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 1, 4]
def baseStart_2139977 : Nat := 118140960795 + 2139977 * 2 ^ 59
def prefixEnd_2139977 : Nat := 4983230072969 + 3 ^ 40 * 2139977 * 2
def baseEnd_2139977 : Nat := 366278930188893021281977

theorem tailTrace_2139977 : CollatzResearch.WordTrace tailWord_2139977 prefixEnd_2139977 366278930188893021281977 := by
  unfold tailWord_2139977
  simp only [CollatzResearch.WordTrace]
  refine ⟨78051373368236282819442185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52034248912157521879628123 78051373368236282819442185)
  ·
    refine ⟨58538530026177212114581639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78051373368236282819442185 58538530026177212114581639)
    ·
      refine ⟨87807795039265818171872459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58538530026177212114581639 87807795039265818171872459)
      ·
        refine ⟨131711692558898727257808689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87807795039265818171872459 131711692558898727257808689)
        ·
          refine ⟨98783769419174045443356517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131711692558898727257808689 98783769419174045443356517)
          ·
            refine ⟨18521956766095133520629347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98783769419174045443356517 18521956766095133520629347)
            ·
              refine ⟨27782935149142700280944021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18521956766095133520629347 27782935149142700280944021)
              ·
                refine ⟨1302325085116064075669251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27782935149142700280944021 1302325085116064075669251)
                ·
                  refine ⟨1953487627674096113503877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302325085116064075669251 1953487627674096113503877)
                  ·
                    refine ⟨366278930188893021281977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1953487627674096113503877 366278930188893021281977)
                    ·
                      rfl

theorem cell23_2139977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 4].length) (baseStart_2139977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139977 prefixEnd_2139977 := by exact prefixLift 2139977
  have htrace : WordTrace (prefixWord ++ tailWord_2139977) baseStart_2139977 baseEnd_2139977 := by
    simpa [prefixWord, tailWord_2139977, baseEnd_2139977] using wordTrace_append hprefix tailTrace_2139977
  have hstable : (prefixWord ++ tailWord_2139977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139977).length < 2 ^ (prefixWord ++ tailWord_2139977).sum := by decide
  have hdescent : baseEnd_2139977 < baseStart_2139977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139993 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_2139993 : Nat := 118140960795 + 2139993 * 2 ^ 59
def prefixEnd_2139993 : Nat := 4983230072969 + 3 ^ 40 * 2139993 * 2
def baseEnd_2139993 : Nat := 1098845006257151001245857

theorem tailTrace_2139993 : CollatzResearch.WordTrace tailWord_2139993 prefixEnd_2139993 1098845006257151001245857 := by
  unfold tailWord_2139993
  simp only [CollatzResearch.WordTrace]
  refine ⟨78051956936178317552024633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52034637957452211701349755 78051956936178317552024633)
  ·
    refine ⟨58538967702133738164018475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78051956936178317552024633 58538967702133738164018475)
    ·
      refine ⟨87808451553200607246027713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58538967702133738164018475 87808451553200607246027713)
      ·
        refine ⟨65856338664900455434520785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87808451553200607246027713 65856338664900455434520785)
        ·
          refine ⟨49392253998675341575890589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65856338664900455434520785 49392253998675341575890589)
          ·
            refine ⟨18522095249503253090958971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49392253998675341575890589 18522095249503253090958971)
            ·
              refine ⟨27783142874254879636438457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18522095249503253090958971 27783142874254879636438457)
              ·
                refine ⟨20837357155691159727328843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27783142874254879636438457 20837357155691159727328843)
                ·
                  refine ⟨31256035733536739590993265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20837357155691159727328843 31256035733536739590993265)
                  ·
                    refine ⟨23442026800152554693244949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31256035733536739590993265 23442026800152554693244949)
                    ·
                      refine ⟨1098845006257151001245857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23442026800152554693244949 1098845006257151001245857)
                      ·
                        rfl

theorem cell23_2139993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_2139993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2139993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2139993 prefixEnd_2139993 := by exact prefixLift 2139993
  have htrace : WordTrace (prefixWord ++ tailWord_2139993) baseStart_2139993 baseEnd_2139993 := by
    simpa [prefixWord, tailWord_2139993, baseEnd_2139993] using wordTrace_append hprefix tailTrace_2139993
  have hstable : (prefixWord ++ tailWord_2139993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139993).length < 2 ^ (prefixWord ++ tailWord_2139993).sum := by decide
  have hdescent : baseEnd_2139993 < baseStart_2139993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140057 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 4]
def baseStart_2140057 : Nat := 118140960795 + 2140057 * 2 ^ 59
def prefixEnd_2140057 : Nat := 4983230072969 + 3 ^ 40 * 2140057 * 2
def baseEnd_2140057 : Nat := 1098877869019038750845563

theorem tailTrace_2140057 : CollatzResearch.WordTrace tailWord_2140057 prefixEnd_2140057 1098877869019038750845563 := by
  unfold tailWord_2140057
  simp only [CollatzResearch.WordTrace]
  refine ⟨78054291207946456482354425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52036194138630970988236283 78054291207946456482354425)
  ·
    refine ⟨58540718405959842361765819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78054291207946456482354425 58540718405959842361765819)
    ·
      refine ⟨87811077608939763542648729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58540718405959842361765819 87811077608939763542648729)
      ·
        refine ⟨65858308206704822656986547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87811077608939763542648729 65858308206704822656986547)
        ·
          refine ⟨98787462310057233985479821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65858308206704822656986547 98787462310057233985479821)
          ·
            refine ⟨37045298366271462744554933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98787462310057233985479821 37045298366271462744554933)
            ·
              refine ⟨3472996721837949632302025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37045298366271462744554933 3472996721837949632302025)
              ·
                refine ⟨2604747541378462224226519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3472996721837949632302025 2604747541378462224226519)
                ·
                  refine ⟨3907121312067693336339779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604747541378462224226519 3907121312067693336339779)
                  ·
                    refine ⟨5860681968101540004509669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3907121312067693336339779 5860681968101540004509669)
                    ·
                      refine ⟨1098877869019038750845563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5860681968101540004509669 1098877869019038750845563)
                      ·
                        rfl

theorem cell23_2140057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_2140057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140057 prefixEnd_2140057 := by exact prefixLift 2140057
  have htrace : WordTrace (prefixWord ++ tailWord_2140057) baseStart_2140057 baseEnd_2140057 := by
    simpa [prefixWord, tailWord_2140057, baseEnd_2140057] using wordTrace_append hprefix tailTrace_2140057
  have hstable : (prefixWord ++ tailWord_2140057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140057).length < 2 ^ (prefixWord ++ tailWord_2140057).sum := by decide
  have hdescent : baseEnd_2140057 < baseStart_2140057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140107 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 3]
def baseStart_2140107 : Nat := 118140960795 + 2140107 * 2 ^ 59
def prefixEnd_2140107 : Nat := 4983230072969 + 3 ^ 40 * 2140107 * 2
def baseEnd_2140107 : Nat := 1098903543051763555220333

theorem tailTrace_2140107 : CollatzResearch.WordTrace tailWord_2140107 prefixEnd_2140107 1098903543051763555220333 := by
  unfold tailWord_2140107
  simp only [CollatzResearch.WordTrace]
  refine ⟨78056114857765315021674575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52037409905176876681116383 78056114857765315021674575)
  ·
    refine ⟨117084172286647972532511863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78056114857765315021674575 117084172286647972532511863)
    ·
      refine ⟨175626258429971958798767795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117084172286647972532511863 175626258429971958798767795)
      ·
        refine ⟨263439387644957938198151693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175626258429971958798767795 263439387644957938198151693)
        ·
          refine ⟨98789770366859226824306885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263439387644957938198151693 98789770366859226824306885)
          ·
            refine ⟨18523081943786105029557541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98789770366859226824306885 18523081943786105029557541)
            ·
              refine ⟨3473077864459894693042039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18523081943786105029557541 3473077864459894693042039)
              ·
                refine ⟨5209616796689842039563059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473077864459894693042039 5209616796689842039563059)
                ·
                  refine ⟨7814425195034763059344589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209616796689842039563059 7814425195034763059344589)
                  ·
                    refine ⟨2930409448138036147254221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7814425195034763059344589 2930409448138036147254221)
                    ·
                      refine ⟨1098903543051763555220333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930409448138036147254221 1098903543051763555220333)
                      ·
                        rfl

theorem cell23_2140107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 3].length) (baseStart_2140107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140107 prefixEnd_2140107 := by exact prefixLift 2140107
  have htrace : WordTrace (prefixWord ++ tailWord_2140107) baseStart_2140107 baseEnd_2140107 := by
    simpa [prefixWord, tailWord_2140107, baseEnd_2140107] using wordTrace_append hprefix tailTrace_2140107
  have hstable : (prefixWord ++ tailWord_2140107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140107).length < 2 ^ (prefixWord ++ tailWord_2140107).sum := by decide
  have hdescent : baseEnd_2140107 < baseStart_2140107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140110 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2140110 : Nat := 118140960795 + 2140110 * 2 ^ 59
def prefixEnd_2140110 : Nat := 4983230072969 + 3 ^ 40 * 2140110 * 2
def baseEnd_2140110 : Nat := 366301694497909014494273

theorem tailTrace_2140110 : CollatzResearch.WordTrace tailWord_2140110 prefixEnd_2140110 366301694497909014494273 := by
  unfold tailWord_2140110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757028034594305816754223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52037482851169631022689189 9757028034594305816754223)
  ·
    refine ⟨14635542051891458725131335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9757028034594305816754223 14635542051891458725131335)
    ·
      refine ⟨21953313077837188087697003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14635542051891458725131335 21953313077837188087697003)
      ·
        refine ⟨32929969616755782131545505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21953313077837188087697003 32929969616755782131545505)
        ·
          refine ⟨24697477212566836598659129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32929969616755782131545505 24697477212566836598659129)
          ·
            refine ⟨18523107909425127448994347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24697477212566836598659129 18523107909425127448994347)
            ·
              refine ⟨27784661864137691173491521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18523107909425127448994347 27784661864137691173491521)
              ·
                refine ⟨20838496398103268380118641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27784661864137691173491521 20838496398103268380118641)
                ·
                  refine ⟨15628872298577451285088981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20838496398103268380118641 15628872298577451285088981)
                  ·
                    refine ⟨366301694497909014494273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15628872298577451285088981 366301694497909014494273)
                    ·
                      rfl

theorem cell23_2140110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2140110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140110 prefixEnd_2140110 := by exact prefixLift 2140110
  have htrace : WordTrace (prefixWord ++ tailWord_2140110) baseStart_2140110 baseEnd_2140110 := by
    simpa [prefixWord, tailWord_2140110, baseEnd_2140110] using wordTrace_append hprefix tailTrace_2140110
  have hstable : (prefixWord ++ tailWord_2140110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140110).length < 2 ^ (prefixWord ++ tailWord_2140110).sum := by decide
  have hdescent : baseEnd_2140110 < baseStart_2140110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140114 : List Nat := [3, 2, 2, 3, 2, 1, 3, 7]
def baseStart_2140114 : Nat := 118140960795 + 2140114 * 2 ^ 59
def prefixEnd_2140114 : Nat := 4983230072969 + 3 ^ 40 * 2140114 * 2
def baseEnd_2140114 : Nat := 40700264348753519549363

theorem tailTrace_2140114 : CollatzResearch.WordTrace tailWord_2140114 prefixEnd_2140114 40700264348753519549363 := by
  unfold tailWord_2140114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19514092542184988804294849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52037580112493303478119597 19514092542184988804294849)
  ·
    refine ⟨14635569406638741603221137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19514092542184988804294849 14635569406638741603221137)
    ·
      refine ⟨10976677054979056202415853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14635569406638741603221137 10976677054979056202415853)
      ·
        refine ⟨4116253895617146075905945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10976677054979056202415853 4116253895617146075905945)
        ·
          refine ⟨3087190421712859556929459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116253895617146075905945 3087190421712859556929459)
          ·
            refine ⟨4630785632569289335394189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087190421712859556929459 4630785632569289335394189)
            ·
              refine ⟨1736544612213483500772821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4630785632569289335394189 1736544612213483500772821)
              ·
                refine ⟨40700264348753519549363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1736544612213483500772821 40700264348753519549363)
                ·
                  rfl

theorem cell23_2140114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_2140114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140114 prefixEnd_2140114 := by exact prefixLift 2140114
  have htrace : WordTrace (prefixWord ++ tailWord_2140114) baseStart_2140114 baseEnd_2140114 := by
    simpa [prefixWord, tailWord_2140114, baseEnd_2140114] using wordTrace_append hprefix tailTrace_2140114
  have hstable : (prefixWord ++ tailWord_2140114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140114).length < 2 ^ (prefixWord ++ tailWord_2140114).sum := by decide
  have hdescent : baseEnd_2140114 < baseStart_2140114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140120 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2140120 : Nat := 118140960795 + 2140120 * 2 ^ 59
def prefixEnd_2140120 : Nat := 4983230072969 + 3 ^ 40 * 2140120 * 2
def baseEnd_2140120 : Nat := 1098910218300272004357773

theorem tailTrace_2140120 : CollatzResearch.WordTrace tailWord_2140120 prefixEnd_2140120 1098910218300272004357773 := by
  unfold tailWord_2140120
  simp only [CollatzResearch.WordTrace]
  refine ⟨39028294503359109120948907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52037726004478812161265209 39028294503359109120948907)
  ·
    refine ⟨58542441755038663681423361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39028294503359109120948907 58542441755038663681423361)
    ·
      refine ⟨43906831316278997761067521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58542441755038663681423361 43906831316278997761067521)
      ·
        refine ⟨32930123487209248320800641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43906831316278997761067521 32930123487209248320800641)
        ·
          refine ⟨24697592615406936240600481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32930123487209248320800641 24697592615406936240600481)
          ·
            refine ⟨18523194461555202180450361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24697592615406936240600481 18523194461555202180450361)
            ·
              refine ⟨13892395846166401635337771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18523194461555202180450361 13892395846166401635337771)
              ·
                refine ⟨20838593769249602453006657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13892395846166401635337771 20838593769249602453006657)
                ·
                  refine ⟨15628945326937201839754993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20838593769249602453006657 15628945326937201839754993)
                  ·
                    refine ⟨11721708995202901379816245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15628945326937201839754993 11721708995202901379816245)
                    ·
                      refine ⟨1098910218300272004357773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11721708995202901379816245 1098910218300272004357773)
                      ·
                        rfl

theorem cell23_2140120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2140120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140120 prefixEnd_2140120 := by exact prefixLift 2140120
  have htrace : WordTrace (prefixWord ++ tailWord_2140120) baseStart_2140120 baseEnd_2140120 := by
    simpa [prefixWord, tailWord_2140120, baseEnd_2140120] using wordTrace_append hprefix tailTrace_2140120
  have hstable : (prefixWord ++ tailWord_2140120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140120).length < 2 ^ (prefixWord ++ tailWord_2140120).sum := by decide
  have hdescent : baseEnd_2140120 < baseStart_2140120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140125 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_2140125 : Nat := 118140960795 + 2140125 * 2 ^ 59
def prefixEnd_2140125 : Nat := 4983230072969 + 3 ^ 40 * 2140125 * 2
def baseEnd_2140125 : Nat := 1098912785703544484795251

theorem tailTrace_2140125 : CollatzResearch.WordTrace tailWord_2140125 prefixEnd_2140125 1098912785703544484795251 := by
  unfold tailWord_2140125
  simp only [CollatzResearch.WordTrace]
  refine ⟨78056771371700104095829829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52037847581133402730553219 78056771371700104095829829)
  ·
    refine ⟨14635644632193769517968093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78056771371700104095829829 14635644632193769517968093)
    ·
      refine ⟨5488366737072663569238035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14635644632193769517968093 5488366737072663569238035)
      ·
        refine ⟨8232550105608995353857053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488366737072663569238035 8232550105608995353857053)
        ·
          refine ⟨3087206289603373257696395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8232550105608995353857053 3087206289603373257696395)
          ·
            refine ⟨4630809434405059886544593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087206289603373257696395 4630809434405059886544593)
            ·
              refine ⟨3473107075803794914908445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4630809434405059886544593 3473107075803794914908445)
              ·
                refine ⟨1302415153426423093090667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3473107075803794914908445 1302415153426423093090667)
                ·
                  refine ⟨1953622730139634639636001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302415153426423093090667 1953622730139634639636001)
                  ·
                    refine ⟨1465217047604725979727001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953622730139634639636001 1465217047604725979727001)
                    ·
                      refine ⟨1098912785703544484795251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465217047604725979727001 1098912785703544484795251)
                      ·
                        rfl

theorem cell23_2140125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_2140125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140125 prefixEnd_2140125 := by exact prefixLift 2140125
  have htrace : WordTrace (prefixWord ++ tailWord_2140125) baseStart_2140125 baseEnd_2140125 := by
    simpa [prefixWord, tailWord_2140125, baseEnd_2140125] using wordTrace_append hprefix tailTrace_2140125
  have hstable : (prefixWord ++ tailWord_2140125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140125).length < 2 ^ (prefixWord ++ tailWord_2140125).sum := by decide
  have hdescent : baseEnd_2140125 < baseStart_2140125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140147 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 3, 4, 2]
def baseStart_2140147 : Nat := 118140960795 + 2140147 * 2 ^ 59
def prefixEnd_2140147 : Nat := 4983230072969 + 3 ^ 40 * 2140147 * 2
def baseEnd_2140147 : Nat := 1098924082277943398720149

theorem tailTrace_2140147 : CollatzResearch.WordTrace tailWord_2140147 prefixEnd_2140147 1098924082277943398720149 := by
  unfold tailWord_2140147
  simp only [CollatzResearch.WordTrace]
  refine ⟨78057573777620401853130695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52038382518413601235420463 78057573777620401853130695)
  ·
    refine ⟨117086360666430602779696043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78057573777620401853130695 117086360666430602779696043)
    ·
      refine ⟨175629540999645904169544065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117086360666430602779696043 175629540999645904169544065)
      ·
        refine ⟨131722155749734428127158049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175629540999645904169544065 131722155749734428127158049)
        ·
          refine ⟨98791616812300821095368537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131722155749734428127158049 98791616812300821095368537)
          ·
            refine ⟨74093712609225615821526403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98791616812300821095368537 74093712609225615821526403)
            ·
              refine ⟨111140568913838423732289605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74093712609225615821526403 111140568913838423732289605)
              ·
                refine ⟨20838856671344704449804301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111140568913838423732289605 20838856671344704449804301)
                ·
                  refine ⟨7814571251754264168676613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20838856671344704449804301 7814571251754264168676613)
                  ·
                    refine ⟨1465232109703924531626865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7814571251754264168676613 1465232109703924531626865)
                    ·
                      refine ⟨1098924082277943398720149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465232109703924531626865 1098924082277943398720149)
                      ·
                        rfl

theorem cell23_2140147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4, 2].length) (baseStart_2140147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140147 prefixEnd_2140147 := by exact prefixLift 2140147
  have htrace : WordTrace (prefixWord ++ tailWord_2140147) baseStart_2140147 baseEnd_2140147 := by
    simpa [prefixWord, tailWord_2140147, baseEnd_2140147] using wordTrace_append hprefix tailTrace_2140147
  have hstable : (prefixWord ++ tailWord_2140147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140147).length < 2 ^ (prefixWord ++ tailWord_2140147).sum := by decide
  have hdescent : baseEnd_2140147 < baseStart_2140147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140160 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_2140160 : Nat := 118140960795 + 2140160 * 2 ^ 59
def prefixEnd_2140160 : Nat := 4983230072969 + 3 ^ 40 * 2140160 * 2
def baseEnd_2140160 : Nat := 1098930757526451847857589

theorem tailTrace_2140160 : CollatzResearch.WordTrace tailWord_2140160 prefixEnd_2140160 1098930757526451847857589 := by
  unfold tailWord_2140160
  simp only [CollatzResearch.WordTrace]
  refine ⟨39029023963286652536676967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52038698617715536715569289 39029023963286652536676967)
  ·
    refine ⟨58543535944929978805015451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39029023963286652536676967 58543535944929978805015451)
    ·
      refine ⟨87815303917394968207523177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58543535944929978805015451 87815303917394968207523177)
      ·
        refine ⟨65861477938046226155642383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87815303917394968207523177 65861477938046226155642383)
        ·
          refine ⟨98792216907069339233463575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65861477938046226155642383 98792216907069339233463575)
          ·
            refine ⟨148188325360604008850195363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98792216907069339233463575 148188325360604008850195363)
            ·
              refine ⟨222282488040906013275293045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148188325360604008850195363 222282488040906013275293045)
              ·
                refine ⟨20838983253834938744558723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222282488040906013275293045 20838983253834938744558723)
                ·
                  refine ⟨31258474880752408116838085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20838983253834938744558723 31258474880752408116838085)
                  ·
                    refine ⟨5860964040141076521907141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31258474880752408116838085 5860964040141076521907141)
                    ·
                      refine ⟨1098930757526451847857589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5860964040141076521907141 1098930757526451847857589)
                      ·
                        rfl

theorem cell23_2140160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_2140160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140160 prefixEnd_2140160 := by exact prefixLift 2140160
  have htrace : WordTrace (prefixWord ++ tailWord_2140160) baseStart_2140160 baseEnd_2140160 := by
    simpa [prefixWord, tailWord_2140160, baseEnd_2140160] using wordTrace_append hprefix tailTrace_2140160
  have hstable : (prefixWord ++ tailWord_2140160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140160).length < 2 ^ (prefixWord ++ tailWord_2140160).sum := by decide
  have hdescent : baseEnd_2140160 < baseStart_2140160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140187 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 5]
def baseStart_2140187 : Nat := 118140960795 + 2140187 * 2 ^ 59
def prefixEnd_2140187 : Nat := 4983230072969 + 3 ^ 40 * 2140187 * 2
def baseEnd_2140187 : Nat := 122104957944902582468885

theorem tailTrace_2140187 : CollatzResearch.WordTrace tailWord_2140187 prefixEnd_2140187 122104957944902582468885 := by
  unfold tailWord_2140187
  simp only [CollatzResearch.WordTrace]
  refine ⟨78059032697475488684586815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52039355131650325789724543 78059032697475488684586815)
  ·
    refine ⟨117088549046213233026880223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78059032697475488684586815 117088549046213233026880223)
    ·
      refine ⟨175632823569319849540320335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117088549046213233026880223 175632823569319849540320335)
      ·
        refine ⟨263449235353979774310480503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175632823569319849540320335 263449235353979774310480503)
        ·
          refine ⟨395173853030969661465720755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263449235353979774310480503 395173853030969661465720755)
          ·
            refine ⟨592760779546454492198581133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395173853030969661465720755 592760779546454492198581133)
            ·
              refine ⟨222285292329920434574467925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 592760779546454492198581133 222285292329920434574467925)
              ·
                refine ⟨1302452884745627546334773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 222285292329920434574467925 1302452884745627546334773)
                ·
                  refine ⟨122104957944902582468885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302452884745627546334773 122104957944902582468885)
                  ·
                    rfl

theorem cell23_2140187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 5].length) (baseStart_2140187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140187 prefixEnd_2140187 := by exact prefixLift 2140187
  have htrace : WordTrace (prefixWord ++ tailWord_2140187) baseStart_2140187 baseEnd_2140187 := by
    simpa [prefixWord, tailWord_2140187, baseEnd_2140187] using wordTrace_append hprefix tailTrace_2140187
  have hstable : (prefixWord ++ tailWord_2140187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140187).length < 2 ^ (prefixWord ++ tailWord_2140187).sum := by decide
  have hdescent : baseEnd_2140187 < baseStart_2140187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140214 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2140214 : Nat := 118140960795 + 2140214 * 2 ^ 59
def prefixEnd_2140214 : Nat := 4983230072969 + 3 ^ 40 * 2140214 * 2
def baseEnd_2140214 : Nat := 1098958485481794636582341

theorem tailTrace_2140214 : CollatzResearch.WordTrace tailWord_2140214 prefixEnd_2140214 1098958485481794636582341 := by
  unfold tailWord_2140214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878751091773604518488731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52040011645585114863879797 4878751091773604518488731)
  ·
    refine ⟨7318126637660406777733097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4878751091773604518488731 7318126637660406777733097)
    ·
      refine ⟨5488594978245305083299823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7318126637660406777733097 5488594978245305083299823)
      ·
        refine ⟨8232892467367957624949735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488594978245305083299823 8232892467367957624949735)
        ·
          refine ⟨12349338701051936437424603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8232892467367957624949735 12349338701051936437424603)
          ·
            refine ⟨18524008051577904656136905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12349338701051936437424603 18524008051577904656136905)
            ·
              refine ⟨13893006038683428492102679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18524008051577904656136905 13893006038683428492102679)
              ·
                refine ⟨20839509058025142738154019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13893006038683428492102679 20839509058025142738154019)
                ·
                  refine ⟨31259263587037714107231029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20839509058025142738154019 31259263587037714107231029)
                  ·
                    refine ⟨2930555961284785697552909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31259263587037714107231029 2930555961284785697552909)
                    ·
                      refine ⟨1098958485481794636582341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930555961284785697552909 1098958485481794636582341)
                      ·
                        rfl

theorem cell23_2140214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2140214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140214 prefixEnd_2140214 := by exact prefixLift 2140214
  have htrace : WordTrace (prefixWord ++ tailWord_2140214) baseStart_2140214 baseEnd_2140214 := by
    simpa [prefixWord, tailWord_2140214, baseEnd_2140214] using wordTrace_append hprefix tailTrace_2140214
  have hstable : (prefixWord ++ tailWord_2140214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140214).length < 2 ^ (prefixWord ++ tailWord_2140214).sum := by decide
  have hdescent : baseEnd_2140214 < baseStart_2140214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140240 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_2140240 : Nat := 118140960795 + 2140240 * 2 ^ 59
def prefixEnd_2140240 : Nat := 4983230072969 + 3 ^ 40 * 2140240 * 2
def baseEnd_2140240 : Nat := 1098971835978811534857221

theorem tailTrace_2140240 : CollatzResearch.WordTrace tailWord_2140240 prefixEnd_2140240 1098971835978811534857221 := by
  unfold tailWord_2140240
  simp only [CollatzResearch.WordTrace]
  refine ⟨39030482883141739368133087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52040643844188985824177449 39030482883141739368133087)
  ·
    refine ⟨58545724324712609052199631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39030482883141739368133087 58545724324712609052199631)
    ·
      refine ⟨87818586487068913578299447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58545724324712609052199631 87818586487068913578299447)
      ·
        refine ⟨131727879730603370367449171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87818586487068913578299447 131727879730603370367449171)
        ·
          refine ⟨197591819595905055551173757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131727879730603370367449171 197591819595905055551173757)
          ·
            refine ⟨74096932348464395831690159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197591819595905055551173757 74096932348464395831690159)
            ·
              refine ⟨111145398522696593747535239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74096932348464395831690159 111145398522696593747535239)
              ·
                refine ⟨166718097784044890621302859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111145398522696593747535239 166718097784044890621302859)
                ·
                  refine ⟨250077146676067335931954289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166718097784044890621302859 250077146676067335931954289)
                  ·
                    refine ⟨187557860007050501948965717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250077146676067335931954289 187557860007050501948965717)
                    ·
                      refine ⟨1098971835978811534857221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 187557860007050501948965717 1098971835978811534857221)
                      ·
                        rfl

theorem cell23_2140240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_2140240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140240 prefixEnd_2140240 := by exact prefixLift 2140240
  have htrace : WordTrace (prefixWord ++ tailWord_2140240) baseStart_2140240 baseEnd_2140240 := by
    simpa [prefixWord, tailWord_2140240, baseEnd_2140240] using wordTrace_append hprefix tailTrace_2140240
  have hstable : (prefixWord ++ tailWord_2140240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140240).length < 2 ^ (prefixWord ++ tailWord_2140240).sum := by decide
  have hdescent : baseEnd_2140240 < baseStart_2140240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140257 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_2140257 : Nat := 118140960795 + 2140257 * 2 ^ 59
def prefixEnd_2140257 : Nat := 4983230072969 + 3 ^ 40 * 2140257 * 2
def baseEnd_2140257 : Nat := 1098980565149937968344643

theorem tailTrace_2140257 : CollatzResearch.WordTrace tailWord_2140257 prefixEnd_2140257 1098980565149937968344643 := by
  unfold tailWord_2140257
  simp only [CollatzResearch.WordTrace]
  refine ⟨78061585807221890639635025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52041057204814593759756683 78061585807221890639635025)
  ·
    refine ⟨58546189355416417979726269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78061585807221890639635025 58546189355416417979726269)
    ·
      refine ⟨21954821008281156742397351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58546189355416417979726269 21954821008281156742397351)
      ·
        refine ⟨32932231512421735113596027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21954821008281156742397351 32932231512421735113596027)
        ·
          refine ⟨49398347268632602670394041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32932231512421735113596027 49398347268632602670394041)
          ·
            refine ⟨37048760451474452002795531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49398347268632602670394041 37048760451474452002795531)
            ·
              refine ⟨55573140677211678004193297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37048760451474452002795531 55573140677211678004193297)
              ·
                refine ⟨41679855507908758503144973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55573140677211678004193297 41679855507908758503144973)
                ·
                  refine ⟨15629945815465784438679365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41679855507908758503144973 15629945815465784438679365)
                  ·
                    refine ⟨2930614840399834582252381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15629945815465784438679365 2930614840399834582252381)
                    ·
                      refine ⟨1098980565149937968344643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930614840399834582252381 1098980565149937968344643)
                      ·
                        rfl

theorem cell23_2140257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_2140257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140257 prefixEnd_2140257 := by exact prefixLift 2140257
  have htrace : WordTrace (prefixWord ++ tailWord_2140257) baseStart_2140257 baseEnd_2140257 := by
    simpa [prefixWord, tailWord_2140257, baseEnd_2140257] using wordTrace_append hprefix tailTrace_2140257
  have hstable : (prefixWord ++ tailWord_2140257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140257).length < 2 ^ (prefixWord ++ tailWord_2140257).sum := by decide
  have hdescent : baseEnd_2140257 < baseStart_2140257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140291 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 3]
def baseStart_2140291 : Nat := 118140960795 + 2140291 * 2 ^ 59
def prefixEnd_2140291 : Nat := 4983230072969 + 3 ^ 40 * 2140291 * 2
def baseEnd_2140291 : Nat := 1098998023492190835319487

theorem tailTrace_2140291 : CollatzResearch.WordTrace tailWord_2140291 prefixEnd_2140291 1098998023492190835319487 := by
  unfold tailWord_2140291
  simp only [CollatzResearch.WordTrace]
  refine ⟨78062825889098714446372727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52041883926065809630915151 78062825889098714446372727)
  ·
    refine ⟨117094238833648071669559091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78062825889098714446372727 117094238833648071669559091)
    ·
      refine ⟨175641358250472107504338637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117094238833648071669559091 175641358250472107504338637)
      ·
        refine ⟨65865509343927040314126989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175641358250472107504338637 65865509343927040314126989)
        ·
          refine ⟨24699566003972640117797621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65865509343927040314126989 24699566003972640117797621)
          ·
            refine ⟨2315584312872435011043527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24699566003972640117797621 2315584312872435011043527)
            ·
              refine ⟨3473376469308652516565291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315584312872435011043527 3473376469308652516565291)
              ·
                refine ⟨5210064703962978774847937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473376469308652516565291 5210064703962978774847937)
                ·
                  refine ⟨3907548527972234081135953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5210064703962978774847937 3907548527972234081135953)
                  ·
                    refine ⟨2930661395979175560851965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3907548527972234081135953 2930661395979175560851965)
                    ·
                      refine ⟨1098998023492190835319487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930661395979175560851965 1098998023492190835319487)
                      ·
                        rfl

theorem cell23_2140291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_2140291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140291 prefixEnd_2140291 := by exact prefixLift 2140291
  have htrace : WordTrace (prefixWord ++ tailWord_2140291) baseStart_2140291 baseEnd_2140291 := by
    simpa [prefixWord, tailWord_2140291, baseEnd_2140291] using wordTrace_append hprefix tailTrace_2140291
  have hstable : (prefixWord ++ tailWord_2140291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140291).length < 2 ^ (prefixWord ++ tailWord_2140291).sum := by decide
  have hdescent : baseEnd_2140291 < baseStart_2140291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140298 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_2140298 : Nat := 118140960795 + 2140298 * 2 ^ 59
def prefixEnd_2140298 : Nat := 4983230072969 + 3 ^ 40 * 2140298 * 2
def baseEnd_2140298 : Nat := 366333872618924102643985

theorem tailTrace_2140298 : CollatzResearch.WordTrace tailWord_2140298 prefixEnd_2140298 366333872618924102643985 := by
  unfold tailWord_2140298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19515770300018338660469387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52042054133382236427918365 19515770300018338660469387)
  ·
    refine ⟨29273655450027507990704081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19515770300018338660469387 29273655450027507990704081)
    ·
      refine ⟨21955241587520630993028061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29273655450027507990704081 21955241587520630993028061)
      ·
        refine ⟨8233215595320236622385523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21955241587520630993028061 8233215595320236622385523)
        ·
          refine ⟨12349823392980354933578285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8233215595320236622385523 12349823392980354933578285)
          ·
            refine ⟨4631183772367633100091857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12349823392980354933578285 4631183772367633100091857)
            ·
              refine ⟨3473387829275724825068893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631183772367633100091857 3473387829275724825068893)
              ·
                refine ⟨1302520435978396809400835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3473387829275724825068893 1302520435978396809400835)
                ·
                  refine ⟨1953780653967595214101253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302520435978396809400835 1953780653967595214101253)
                  ·
                    refine ⟨366333872618924102643985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1953780653967595214101253 366333872618924102643985)
                    ·
                      rfl

theorem cell23_2140298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_2140298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140298 prefixEnd_2140298 := by exact prefixLift 2140298
  have htrace : WordTrace (prefixWord ++ tailWord_2140298) baseStart_2140298 baseEnd_2140298 := by
    simpa [prefixWord, tailWord_2140298, baseEnd_2140298] using wordTrace_append hprefix tailTrace_2140298
  have hstable : (prefixWord ++ tailWord_2140298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140298).length < 2 ^ (prefixWord ++ tailWord_2140298).sum := by decide
  have hdescent : baseEnd_2140298 < baseStart_2140298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140304 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 5, 1, 3]
def baseStart_2140304 : Nat := 118140960795 + 2140304 * 2 ^ 59
def prefixEnd_2140304 : Nat := 4983230072969 + 3 ^ 40 * 2140304 * 2
def baseEnd_2140304 : Nat := 1099004698740699284456927

theorem tailTrace_2140304 : CollatzResearch.WordTrace tailWord_2140304 prefixEnd_2140304 1099004698740699284456927 := by
  unfold tailWord_2140304
  simp only [CollatzResearch.WordTrace]
  refine ⟨39031650019025808833297983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52042200025367745111063977 39031650019025808833297983)
  ·
    refine ⟨58547475028538713249946975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39031650019025808833297983 58547475028538713249946975)
    ·
      refine ⟨87821212542808069874920463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58547475028538713249946975 87821212542808069874920463)
      ·
        refine ⟨131731818814212104812380695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87821212542808069874920463 131731818814212104812380695)
        ·
          refine ⟨197597728221318157218571043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131731818814212104812380695 197597728221318157218571043)
          ·
            refine ⟨296396592331977235827856565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197597728221318157218571043 296396592331977235827856565)
            ·
              refine ⟨27787180531122865858861553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296396592331977235827856565 27787180531122865858861553)
              ·
                refine ⟨20840385398342149394146165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27787180531122865858861553 20840385398342149394146165)
                ·
                  refine ⟨1953786131094576505701203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20840385398342149394146165 1953786131094576505701203)
                  ·
                    refine ⟨2930679196641864758551805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953786131094576505701203 2930679196641864758551805)
                    ·
                      refine ⟨1099004698740699284456927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930679196641864758551805 1099004698740699284456927)
                      ·
                        rfl

theorem cell23_2140304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_2140304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140304 prefixEnd_2140304 := by exact prefixLift 2140304
  have htrace : WordTrace (prefixWord ++ tailWord_2140304) baseStart_2140304 baseEnd_2140304 := by
    simpa [prefixWord, tailWord_2140304, baseEnd_2140304] using wordTrace_append hprefix tailTrace_2140304
  have hstable : (prefixWord ++ tailWord_2140304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140304).length < 2 ^ (prefixWord ++ tailWord_2140304).sum := by decide
  have hdescent : baseEnd_2140304 < baseStart_2140304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140311 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 6]
def baseStart_2140311 : Nat := 118140960795 + 2140311 * 2 ^ 59
def prefixEnd_2140311 : Nat := 4983230072969 + 3 ^ 40 * 2140311 * 2
def baseEnd_2140311 : Nat := 122112032567253417452155

theorem tailTrace_2140311 : CollatzResearch.WordTrace tailWord_2140311 prefixEnd_2140311 122112032567253417452155 := by
  unfold tailWord_2140311
  simp only [CollatzResearch.WordTrace]
  refine ⟨78063555349026257862100787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52042370232684171908067191 78063555349026257862100787)
  ·
    refine ⟨117095333023539386793151181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78063555349026257862100787 117095333023539386793151181)
    ·
      refine ⟨43910749883827270047431693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117095333023539386793151181 43910749883827270047431693)
      ·
        refine ⟨16466531206435226267786885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43910749883827270047431693 16466531206435226267786885)
        ·
          refine ⟨3087474601206604925210041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16466531206435226267786885 3087474601206604925210041)
          ·
            refine ⟨2315605950904953693907531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3087474601206604925210041 2315605950904953693907531)
            ·
              refine ⟨3473408926357430540861297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315605950904953693907531 3473408926357430540861297)
              ·
                refine ⟨2605056694768072905645973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473408926357430540861297 2605056694768072905645973)
                ·
                  refine ⟨122112032567253417452155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2605056694768072905645973 122112032567253417452155)
                  ·
                    rfl

theorem cell23_2140311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 6].length) (baseStart_2140311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140311 prefixEnd_2140311 := by exact prefixLift 2140311
  have htrace : WordTrace (prefixWord ++ tailWord_2140311) baseStart_2140311 baseEnd_2140311 := by
    simpa [prefixWord, tailWord_2140311, baseEnd_2140311] using wordTrace_append hprefix tailTrace_2140311
  have hstable : (prefixWord ++ tailWord_2140311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140311).length < 2 ^ (prefixWord ++ tailWord_2140311).sum := by decide
  have hdescent : baseEnd_2140311 < baseStart_2140311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140321 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2140321 : Nat := 118140960795 + 2140321 * 2 ^ 59
def prefixEnd_2140321 : Nat := 4983230072969 + 3 ^ 40 * 2140321 * 2
def baseEnd_2140321 : Nat := 1099013427911825717944349

theorem tailTrace_2140321 : CollatzResearch.WordTrace tailWord_2140321 prefixEnd_2140321 1099013427911825717944349 := by
  unfold tailWord_2140321
  simp only [CollatzResearch.WordTrace]
  refine ⟨78063920078990029569964817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52042613385993353046643211 78063920078990029569964817)
  ·
    refine ⟨58547940059242522177473613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78063920078990029569964817 58547940059242522177473613)
    ·
      refine ⟨21955477522215945816552605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58547940059242522177473613 21955477522215945816552605)
      ·
        refine ⟨8233304070830979681207227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21955477522215945816552605 8233304070830979681207227)
        ·
          refine ⟨12349956106246469521810841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8233304070830979681207227 12349956106246469521810841)
          ·
            refine ⟨9262467079684852141358131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12349956106246469521810841 9262467079684852141358131)
            ·
              refine ⟨13893700619527278212037197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9262467079684852141358131 13893700619527278212037197)
              ·
                refine ⟨5210137732322729329513949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13893700619527278212037197 5210137732322729329513949)
                ·
                  refine ⟨1953801649621023498567731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5210137732322729329513949 1953801649621023498567731)
                  ·
                    refine ⟨2930702474431535247851597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953801649621023498567731 2930702474431535247851597)
                    ·
                      refine ⟨1099013427911825717944349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930702474431535247851597 1099013427911825717944349)
                      ·
                        rfl

theorem cell23_2140321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2140321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140321 prefixEnd_2140321 := by exact prefixLift 2140321
  have htrace : WordTrace (prefixWord ++ tailWord_2140321) baseStart_2140321 baseEnd_2140321 := by
    simpa [prefixWord, tailWord_2140321, baseEnd_2140321] using wordTrace_append hprefix tailTrace_2140321
  have hstable : (prefixWord ++ tailWord_2140321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140321).length < 2 ^ (prefixWord ++ tailWord_2140321).sum := by decide
  have hdescent : baseEnd_2140321 < baseStart_2140321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140344 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 6, 2]
def baseStart_2140344 : Nat := 118140960795 + 2140344 * 2 ^ 59
def prefixEnd_2140344 : Nat := 4983230072969 + 3 ^ 40 * 2140344 * 2
def baseEnd_2140344 : Nat := 1099025237966879127956743

theorem tailTrace_2140344 : CollatzResearch.WordTrace tailWord_2140344 prefixEnd_2140344 1099025237966879127956743 := by
  unfold tailWord_2140344
  simp only [CollatzResearch.WordTrace]
  refine ⟨39032379478953352249026043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52043172638604469665368057 39032379478953352249026043)
  ·
    refine ⟨58548569218430028373539065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39032379478953352249026043 58548569218430028373539065)
    ·
      refine ⟨43911426913822521280154299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58548569218430028373539065 43911426913822521280154299)
      ·
        refine ⟨65867140370733781920231449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43911426913822521280154299 65867140370733781920231449)
        ·
          refine ⟨49400355278050336440173587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65867140370733781920231449 49400355278050336440173587)
          ·
            refine ⟨74100532917075504660260381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49400355278050336440173587 74100532917075504660260381)
            ·
              refine ⟨27787699843903314247597643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74100532917075504660260381 27787699843903314247597643)
              ·
                refine ⟨41681549765854971371396465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27787699843903314247597643 41681549765854971371396465)
                ·
                  refine ⟨31261162324391228528547349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41681549765854971371396465 31261162324391228528547349)
                  ·
                    refine ⟨1465366983955838837275657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31261162324391228528547349 1465366983955838837275657)
                    ·
                      refine ⟨1099025237966879127956743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465366983955838837275657 1099025237966879127956743)
                      ·
                        rfl

theorem cell23_2140344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_2140344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140344 prefixEnd_2140344 := by exact prefixLift 2140344
  have htrace : WordTrace (prefixWord ++ tailWord_2140344) baseStart_2140344 baseEnd_2140344 := by
    simpa [prefixWord, tailWord_2140344, baseEnd_2140344] using wordTrace_append hprefix tailTrace_2140344
  have hstable : (prefixWord ++ tailWord_2140344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140344).length < 2 ^ (prefixWord ++ tailWord_2140344).sum := by decide
  have hdescent : baseEnd_2140344 < baseStart_2140344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140347 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5]
def baseStart_2140347 : Nat := 118140960795 + 2140347 * 2 ^ 59
def prefixEnd_2140347 : Nat := 4983230072969 + 3 ^ 40 * 2140347 * 2
def baseEnd_2140347 : Nat := 1099026778408842616219229

theorem tailTrace_2140347 : CollatzResearch.WordTrace tailWord_2140347 prefixEnd_2140347 1099026778408842616219229 := by
  unfold tailWord_2140347
  simp only [CollatzResearch.WordTrace]
  refine ⟨78064868376895836010411295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52043245584597224006940863 78064868376895836010411295)
  ·
    refine ⟨117097302565343754015616943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78064868376895836010411295 117097302565343754015616943)
    ·
      refine ⟨175645953848015631023425415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117097302565343754015616943 175645953848015631023425415)
      ·
        refine ⟨263468930772023446535138123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175645953848015631023425415 263468930772023446535138123)
        ·
          refine ⟨395203396158035169802707185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263468930772023446535138123 395203396158035169802707185)
          ·
            refine ⟨296402547118526377352030389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395203396158035169802707185 296402547118526377352030389)
            ·
              refine ⟨27787738792361847876752849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 296402547118526377352030389 27787738792361847876752849)
              ·
                refine ⟨20840804094271385907564637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27787738792361847876752849 20840804094271385907564637)
                ·
                  refine ⟨7815301535351769715336739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20840804094271385907564637 7815301535351769715336739)
                  ·
                    refine ⟨11722952303027654573005109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7815301535351769715336739 11722952303027654573005109)
                    ·
                      refine ⟨1099026778408842616219229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11722952303027654573005109 1099026778408842616219229)
                      ·
                        rfl

theorem cell23_2140347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_2140347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140347 prefixEnd_2140347 := by exact prefixLift 2140347
  have htrace : WordTrace (prefixWord ++ tailWord_2140347) baseStart_2140347 baseEnd_2140347 := by
    simpa [prefixWord, tailWord_2140347, baseEnd_2140347] using wordTrace_append hprefix tailTrace_2140347
  have hstable : (prefixWord ++ tailWord_2140347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140347).length < 2 ^ (prefixWord ++ tailWord_2140347).sum := by decide
  have hdescent : baseEnd_2140347 < baseStart_2140347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140378 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2]
def baseStart_2140378 : Nat := 118140960795 + 2140378 * 2 ^ 59
def prefixEnd_2140378 : Nat := 4983230072969 + 3 ^ 40 * 2140378 * 2
def baseEnd_2140378 : Nat := 1099042696309131994931587

theorem tailTrace_2140378 : CollatzResearch.WordTrace tailWord_2140378 prefixEnd_2140378 1099042696309131994931587 := by
  unfold tailWord_2140378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19516499759945882076197447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52043999359855685536526525 19516499759945882076197447)
  ·
    refine ⟨29274749639918823114296171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19516499759945882076197447 29274749639918823114296171)
    ·
      refine ⟨43912124459878234671444257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29274749639918823114296171 43912124459878234671444257)
      ·
        refine ⟨32934093344908676003583193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43912124459878234671444257 32934093344908676003583193)
        ·
          refine ⟨24700570008681507002687395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32934093344908676003583193 24700570008681507002687395)
          ·
            refine ⟨37050855013022260504031093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24700570008681507002687395 37050855013022260504031093)
            ·
              refine ⟨3473517657470836922252915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37050855013022260504031093 3473517657470836922252915)
              ·
                refine ⟨5210276486206255383379373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473517657470836922252915 5210276486206255383379373)
                ·
                  refine ⟨1953853682327345768767265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5210276486206255383379373 1953853682327345768767265)
                  ·
                    refine ⟨1465390261745509326575449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1953853682327345768767265 1465390261745509326575449)
                    ·
                      refine ⟨1099042696309131994931587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465390261745509326575449 1099042696309131994931587)
                      ·
                        rfl

theorem cell23_2140378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_2140378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140378 prefixEnd_2140378 := by exact prefixLift 2140378
  have htrace : WordTrace (prefixWord ++ tailWord_2140378) baseStart_2140378 baseEnd_2140378 := by
    simpa [prefixWord, tailWord_2140378, baseEnd_2140378] using wordTrace_append hprefix tailTrace_2140378
  have hstable : (prefixWord ++ tailWord_2140378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140378).length < 2 ^ (prefixWord ++ tailWord_2140378).sum := by decide
  have hdescent : baseEnd_2140378 < baseStart_2140378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140381 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2140381 : Nat := 118140960795 + 2140381 * 2 ^ 59
def prefixEnd_2140381 : Nat := 4983230072969 + 3 ^ 40 * 2140381 * 2
def baseEnd_2140381 : Nat := 1099044236751095483194073

theorem tailTrace_2140381 : CollatzResearch.WordTrace tailWord_2140381 prefixEnd_2140381 1099044236751095483194073 := by
  unfold tailWord_2140381
  simp only [CollatzResearch.WordTrace]
  refine ⟨78066108458772659817148997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52044072305848439878099331 78066108458772659817148997)
  ·
    refine ⟨14637395336019873715715437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78066108458772659817148997 14637395336019873715715437)
    ·
      refine ⟨5489023251007452643393289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14637395336019873715715437 5489023251007452643393289)
      ·
        refine ⟨4116767438255589482544967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5489023251007452643393289 4116767438255589482544967)
        ·
          refine ⟨6175151157383384223817451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116767438255589482544967 6175151157383384223817451)
          ·
            refine ⟨9262726736075076335726177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175151157383384223817451 9262726736075076335726177)
            ·
              refine ⟨6947045052056307251794633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9262726736075076335726177 6947045052056307251794633)
              ·
                refine ⟨5210283789042230438845975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6947045052056307251794633 5210283789042230438845975)
                ·
                  refine ⟨7815425683563345658268963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5210283789042230438845975 7815425683563345658268963)
                  ·
                    refine ⟨11723138525345018487403445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7815425683563345658268963 11723138525345018487403445)
                    ·
                      refine ⟨1099044236751095483194073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11723138525345018487403445 1099044236751095483194073)
                      ·
                        rfl

theorem cell23_2140381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2140381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140381 prefixEnd_2140381 := by exact prefixLift 2140381
  have htrace : WordTrace (prefixWord ++ tailWord_2140381) baseStart_2140381 baseEnd_2140381 := by
    simpa [prefixWord, tailWord_2140381, baseEnd_2140381] using wordTrace_append hprefix tailTrace_2140381
  have hstable : (prefixWord ++ tailWord_2140381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140381).length < 2 ^ (prefixWord ++ tailWord_2140381).sum := by decide
  have hdescent : baseEnd_2140381 < baseStart_2140381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140428 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_2140428 : Nat := 118140960795 + 2140428 * 2 ^ 59
def prefixEnd_2140428 : Nat := 4983230072969 + 3 ^ 40 * 2140428 * 2
def baseEnd_2140428 : Nat := 1099068370341856799306357

theorem tailTrace_2140428 : CollatzResearch.WordTrace tailWord_2140428 prefixEnd_2140428 1099068370341856799306357 := by
  unfold tailWord_2140428
  simp only [CollatzResearch.WordTrace]
  refine ⟨39033911344801193422054969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52045215126401591229406625 39033911344801193422054969)
  ·
    refine ⟨29275433508600895066541227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39033911344801193422054969 29275433508600895066541227)
    ·
      refine ⟨43913150262901342599811841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29275433508600895066541227 43913150262901342599811841)
      ·
        refine ⟨32934862697176006949858881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43913150262901342599811841 32934862697176006949858881)
        ·
          refine ⟨24701147022882005212394161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32934862697176006949858881 24701147022882005212394161)
          ·
            refine ⟨18525860267161503909295621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24701147022882005212394161 18525860267161503909295621)
            ·
              refine ⟨3473598800092781982992929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18525860267161503909295621 3473598800092781982992929)
              ·
                refine ⟨2605199100069586487244697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473598800092781982992929 2605199100069586487244697)
                ·
                  refine ⟨1953899325052189865433523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605199100069586487244697 1953899325052189865433523)
                  ·
                    refine ⟨2930848987578284798150285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1953899325052189865433523 2930848987578284798150285)
                    ·
                      refine ⟨1099068370341856799306357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2930848987578284798150285 1099068370341856799306357)
                      ·
                        rfl

theorem cell23_2140428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_2140428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140428 prefixEnd_2140428 := by exact prefixLift 2140428
  have htrace : WordTrace (prefixWord ++ tailWord_2140428) baseStart_2140428 baseEnd_2140428 := by
    simpa [prefixWord, tailWord_2140428, baseEnd_2140428] using wordTrace_append hprefix tailTrace_2140428
  have hstable : (prefixWord ++ tailWord_2140428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140428).length < 2 ^ (prefixWord ++ tailWord_2140428).sum := by decide
  have hdescent : baseEnd_2140428 < baseStart_2140428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140504 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_2140504 : Nat := 118140960795 + 2140504 * 2 ^ 59
def prefixEnd_2140504 : Nat := 4983230072969 + 3 ^ 40 * 2140504 * 2
def baseEnd_2140504 : Nat := 366369131623866167318669

theorem tailTrace_2140504 : CollatzResearch.WordTrace tailWord_2140504 prefixEnd_2140504 366369131623866167318669 := by
  unfold tailWord_2140504
  simp only [CollatzResearch.WordTrace]
  refine ⟨39035297318663525911938283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52047063091551367882584377 39035297318663525911938283)
  ·
    refine ⟨58552945977995288867907425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39035297318663525911938283 58552945977995288867907425)
    ·
      refine ⟨43914709483496466650930569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58552945977995288867907425 43914709483496466650930569)
      ·
        refine ⟨32936032112622349988197927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43914709483496466650930569 32936032112622349988197927)
        ·
          refine ⟨49404048168933524982296891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32936032112622349988197927 49404048168933524982296891)
          ·
            refine ⟨74106072253400287473445337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49404048168933524982296891 74106072253400287473445337)
            ·
              refine ⟨55579554190050215605084003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74106072253400287473445337 55579554190050215605084003)
              ·
                refine ⟨83369331285075323407626005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55579554190050215605084003 83369331285075323407626005)
                ·
                  refine ⟨3907937403987905784732469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83369331285075323407626005 3907937403987905784732469)
                  ·
                    refine ⟨366369131623866167318669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3907937403987905784732469 366369131623866167318669)
                    ·
                      rfl

theorem cell23_2140504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_2140504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140504 prefixEnd_2140504 := by exact prefixLift 2140504
  have htrace : WordTrace (prefixWord ++ tailWord_2140504) baseStart_2140504 baseEnd_2140504 := by
    simpa [prefixWord, tailWord_2140504, baseEnd_2140504] using wordTrace_append hprefix tailTrace_2140504
  have hstable : (prefixWord ++ tailWord_2140504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140504).length < 2 ^ (prefixWord ++ tailWord_2140504).sum := by decide
  have hdescent : baseEnd_2140504 < baseStart_2140504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140511 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 2, 5, 2]
def baseStart_2140511 : Nat := 118140960795 + 2140511 * 2 ^ 59
def prefixEnd_2140511 : Nat := 4983230072969 + 3 ^ 40 * 2140511 * 2
def baseEnd_2140511 : Nat := 1099110989236179974568475

theorem tailTrace_2140511 : CollatzResearch.WordTrace tailWord_2140511 prefixEnd_2140511 1099110989236179974568475 := by
  unfold tailWord_2140511
  simp only [CollatzResearch.WordTrace]
  refine ⟨78070849948301692019381387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52047233298867794679587591 78070849948301692019381387)
  ·
    refine ⟨117106274922452538029072081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78070849948301692019381387 117106274922452538029072081)
    ·
      refine ⟨87829706191839403521804061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117106274922452538029072081 87829706191839403521804061)
      ·
        refine ⟨32936139821939776320676523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87829706191839403521804061 32936139821939776320676523)
        ·
          refine ⟨49404209732909664481014785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32936139821939776320676523 49404209732909664481014785)
          ·
            refine ⟨37053157299682248360761089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49404209732909664481014785 37053157299682248360761089)
            ·
              refine ⟨27789867974761686270570817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37053157299682248360761089 27789867974761686270570817)
              ·
                refine ⟨20842400981071264702928113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27789867974761686270570817 20842400981071264702928113)
                ·
                  refine ⟨15631800735803448527196085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20842400981071264702928113 15631800735803448527196085)
                  ·
                    refine ⟨1465481318981573299424633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15631800735803448527196085 1465481318981573299424633)
                    ·
                      refine ⟨1099110989236179974568475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465481318981573299424633 1099110989236179974568475)
                      ·
                        rfl

theorem cell23_2140511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_2140511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140511 prefixEnd_2140511 := by exact prefixLift 2140511
  have htrace : WordTrace (prefixWord ++ tailWord_2140511) baseStart_2140511 baseEnd_2140511 := by
    simpa [prefixWord, tailWord_2140511, baseEnd_2140511] using wordTrace_append hprefix tailTrace_2140511
  have hstable : (prefixWord ++ tailWord_2140511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140511).length < 2 ^ (prefixWord ++ tailWord_2140511).sum := by decide
  have hdescent : baseEnd_2140511 < baseStart_2140511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140541 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_2140541 : Nat := 118140960795 + 2140541 * 2 ^ 59
def prefixEnd_2140541 : Nat := 4983230072969 + 3 ^ 40 * 2140541 * 2
def baseEnd_2140541 : Nat := 1099126393655814857193337

theorem tailTrace_2140541 : CollatzResearch.WordTrace tailWord_2140541 prefixEnd_2140541 1099126393655814857193337 := by
  unfold tailWord_2140541
  simp only [CollatzResearch.WordTrace]
  refine ⟨78071944138193007142973477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52047962758795338095315651 78071944138193007142973477)
  ·
    refine ⟨14638489525911188839307527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78071944138193007142973477 14638489525911188839307527)
    ·
      refine ⟨21957734288866783258961291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14638489525911188839307527 21957734288866783258961291)
      ·
        refine ⟨32936601433300174888441937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21957734288866783258961291 32936601433300174888441937)
        ·
          refine ⟨24702451074975131166331453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32936601433300174888441937 24702451074975131166331453)
          ·
            refine ⟨9263419153115674187374295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24702451074975131166331453 9263419153115674187374295)
            ·
              refine ⟨13895128729673511281061443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9263419153115674187374295 13895128729673511281061443)
              ·
                refine ⟨20842693094510266921592165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13895128729673511281061443 20842693094510266921592165)
                ·
                  refine ⟨3908004955220675047798531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20842693094510266921592165 3908004955220675047798531)
                  ·
                    refine ⟨5862007432831012571697797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3908004955220675047798531 5862007432831012571697797)
                    ·
                      refine ⟨1099126393655814857193337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5862007432831012571697797 1099126393655814857193337)
                      ·
                        rfl

theorem cell23_2140541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_2140541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140541 prefixEnd_2140541 := by exact prefixLift 2140541
  have htrace : WordTrace (prefixWord ++ tailWord_2140541) baseStart_2140541 baseEnd_2140541 := by
    simpa [prefixWord, tailWord_2140541, baseEnd_2140541] using wordTrace_append hprefix tailTrace_2140541
  have hstable : (prefixWord ++ tailWord_2140541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140541).length < 2 ^ (prefixWord ++ tailWord_2140541).sum := by decide
  have hdescent : baseEnd_2140541 < baseStart_2140541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140608 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 3, 1, 3]
def baseStart_2140608 : Nat := 118140960795 + 2140608 * 2 ^ 59
def prefixEnd_2140608 : Nat := 4983230072969 + 3 ^ 40 * 2140608 * 2
def baseEnd_2140608 : Nat := 1099160796859666095055529

theorem tailTrace_2140608 : CollatzResearch.WordTrace tailWord_2140608 prefixEnd_2140608 1099160796859666095055529 := by
  unfold tailWord_2140608
  simp only [CollatzResearch.WordTrace]
  refine ⟨39037193914475138792831239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52049591885966851723774985 39037193914475138792831239)
  ·
    refine ⟨58555790871712708189246859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39037193914475138792831239 58555790871712708189246859)
    ·
      refine ⟨87833686307569062283870289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58555790871712708189246859 87833686307569062283870289)
      ·
        refine ⟨65875264730676796712902717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87833686307569062283870289 65875264730676796712902717)
        ·
          refine ⟨24703224274003798767338519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65875264730676796712902717 24703224274003798767338519)
          ·
            refine ⟨37054836411005698151007779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24703224274003798767338519 37054836411005698151007779)
            ·
              refine ⟨55582254616508547226511669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37054836411005698151007779 55582254616508547226511669)
              ·
                refine ⟨5210836370297676302485469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55582254616508547226511669 5210836370297676302485469)
                ·
                  refine ⟨1954063638861628613432051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5210836370297676302485469 1954063638861628613432051)
                  ·
                    refine ⟨2931095458292442920148077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954063638861628613432051 2931095458292442920148077)
                    ·
                      refine ⟨1099160796859666095055529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2931095458292442920148077 1099160796859666095055529)
                      ·
                        rfl

theorem cell23_2140608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_2140608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140608 prefixEnd_2140608 := by exact prefixLift 2140608
  have htrace : WordTrace (prefixWord ++ tailWord_2140608) baseStart_2140608 baseEnd_2140608 := by
    simpa [prefixWord, tailWord_2140608, baseEnd_2140608] using wordTrace_append hprefix tailTrace_2140608
  have hstable : (prefixWord ++ tailWord_2140608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140608).length < 2 ^ (prefixWord ++ tailWord_2140608).sum := by decide
  have hdescent : baseEnd_2140608 < baseStart_2140608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140609 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2140609 : Nat := 118140960795 + 2140609 * 2 ^ 59
def prefixEnd_2140609 : Nat := 4983230072969 + 3 ^ 40 * 2140609 * 2
def baseEnd_2140609 : Nat := 1099161310340320591143025

theorem tailTrace_2140609 : CollatzResearch.WordTrace tailWord_2140609 prefixEnd_2140609 1099161310340320591143025 := by
  unfold tailWord_2140609
  simp only [CollatzResearch.WordTrace]
  refine ⟨78074424301946654756448881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52049616201297769837632587 78074424301946654756448881)
  ·
    refine ⟨58555818226459991067336661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78074424301946654756448881 58555818226459991067336661)
    ·
      refine ⟨1372401989682656040640703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 58555818226459991067336661 1372401989682656040640703)
      ·
        refine ⟨2058602984523984060961055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372401989682656040640703 2058602984523984060961055)
        ·
          refine ⟨3087904476785976091441583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058602984523984060961055 3087904476785976091441583)
          ·
            refine ⟨4631856715178964137162375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087904476785976091441583 4631856715178964137162375)
            ·
              refine ⟨6947785072768446205743563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631856715178964137162375 6947785072768446205743563)
              ·
                refine ⟨10421677609152669308615345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6947785072768446205743563 10421677609152669308615345)
                ·
                  refine ⟨7816258206864501981461509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10421677609152669308615345 7816258206864501981461509)
                  ·
                    refine ⟨1465548413787094121524033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7816258206864501981461509 1465548413787094121524033)
                    ·
                      refine ⟨1099161310340320591143025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465548413787094121524033 1099161310340320591143025)
                      ·
                        rfl

theorem cell23_2140609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2140609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140609 prefixEnd_2140609 := by exact prefixLift 2140609
  have htrace : WordTrace (prefixWord ++ tailWord_2140609) baseStart_2140609 baseEnd_2140609 := by
    simpa [prefixWord, tailWord_2140609, baseEnd_2140609] using wordTrace_append hprefix tailTrace_2140609
  have hstable : (prefixWord ++ tailWord_2140609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140609).length < 2 ^ (prefixWord ++ tailWord_2140609).sum := by decide
  have hdescent : baseEnd_2140609 < baseStart_2140609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140618 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_2140618 : Nat := 118140960795 + 2140618 * 2 ^ 59
def prefixEnd_2140618 : Nat := 4983230072969 + 3 ^ 40 * 2140618 * 2
def baseEnd_2140618 : Nat := 1099165931666211055930483

theorem tailTrace_2140618 : CollatzResearch.WordTrace tailWord_2140618 prefixEnd_2140618 1099165931666211055930483 := by
  unfold tailWord_2140618
  simp only [CollatzResearch.WordTrace]
  refine ⟨19518688139728512323381627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52049835039276032862351005 19518688139728512323381627)
  ·
    refine ⟨29278032209592768485072441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19518688139728512323381627 29278032209592768485072441)
    ·
      refine ⟨21958524157194576363804331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29278032209592768485072441 21958524157194576363804331)
      ·
        refine ⟨32937786235791864545706497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21958524157194576363804331 32937786235791864545706497)
        ·
          refine ⟨24703339676843898409279873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32937786235791864545706497 24703339676843898409279873)
          ·
            refine ⟨18527504757632923806959905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24703339676843898409279873 18527504757632923806959905)
            ·
              refine ⟨13895628568224692855219929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18527504757632923806959905 13895628568224692855219929)
              ·
                refine ⟨10421721426168519641414947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13895628568224692855219929 10421721426168519641414947)
                ·
                  refine ⟨15632582139252779462122421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10421721426168519641414947 15632582139252779462122421)
                  ·
                    refine ⟨1465554575554948074573977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15632582139252779462122421 1465554575554948074573977)
                    ·
                      refine ⟨1099165931666211055930483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465554575554948074573977 1099165931666211055930483)
                      ·
                        rfl

theorem cell23_2140618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_2140618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140618 prefixEnd_2140618 := by exact prefixLift 2140618
  have htrace : WordTrace (prefixWord ++ tailWord_2140618) baseStart_2140618 baseEnd_2140618 := by
    simpa [prefixWord, tailWord_2140618, baseEnd_2140618] using wordTrace_append hprefix tailTrace_2140618
  have hstable : (prefixWord ++ tailWord_2140618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140618).length < 2 ^ (prefixWord ++ tailWord_2140618).sum := by decide
  have hdescent : baseEnd_2140618 < baseStart_2140618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140628 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2140628 : Nat := 118140960795 + 2140628 * 2 ^ 59
def prefixEnd_2140628 : Nat := 4983230072969 + 3 ^ 40 * 2140628 * 2
def baseEnd_2140628 : Nat := 366390355490918672268479

theorem tailTrace_2140628 : CollatzResearch.WordTrace tailWord_2140628 prefixEnd_2140628 366390355490918672268479 := by
  unfold tailWord_2140628
  simp only [CollatzResearch.WordTrace]
  refine ⟨39037558644438910500695269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52050078192585214000927025 39037558644438910500695269)
  ·
    refine ⟨7319542245832295718880363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39037558644438910500695269 7319542245832295718880363)
    ·
      refine ⟨10979313368748443578320545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7319542245832295718880363 10979313368748443578320545)
      ·
        refine ⟨8234485026561332683740409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10979313368748443578320545 8234485026561332683740409)
        ·
          refine ⟨6175863769920999512805307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8234485026561332683740409 6175863769920999512805307)
          ·
            refine ⟨9263795654881499269207961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175863769920999512805307 9263795654881499269207961)
            ·
              refine ⟨6947846741161124451905971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9263795654881499269207961 6947846741161124451905971)
              ·
                refine ⟨10421770111741686677858957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6947846741161124451905971 10421770111741686677858957)
                ·
                  refine ⟨3908163791903132504197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10421770111741686677858957 3908163791903132504197109)
                  ·
                    refine ⟨366390355490918672268479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3908163791903132504197109 366390355490918672268479)
                    ·
                      rfl

theorem cell23_2140628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2140628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140628 prefixEnd_2140628 := by exact prefixLift 2140628
  have htrace : WordTrace (prefixWord ++ tailWord_2140628) baseStart_2140628 baseEnd_2140628 := by
    simpa [prefixWord, tailWord_2140628, baseEnd_2140628] using wordTrace_append hprefix tailTrace_2140628
  have hstable : (prefixWord ++ tailWord_2140628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140628).length < 2 ^ (prefixWord ++ tailWord_2140628).sum := by decide
  have hdescent : baseEnd_2140628 < baseStart_2140628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140641 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2140641 : Nat := 118140960795 + 2140641 * 2 ^ 59
def prefixEnd_2140641 : Nat := 4983230072969 + 3 ^ 40 * 2140641 * 2
def baseEnd_2140641 : Nat := 366392580573754821980959

theorem tailTrace_2140641 : CollatzResearch.WordTrace tailWord_2140641 prefixEnd_2140641 366392580573754821980959 := by
  unfold tailWord_2140641
  simp only [CollatzResearch.WordTrace]
  refine ⟨78075591437830724221613777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52050394291887149481075851 78075591437830724221613777)
  ·
    refine ⟨58556693578373043166210333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78075591437830724221613777 58556693578373043166210333)
    ·
      refine ⟨21958760091889891187328875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58556693578373043166210333 21958760091889891187328875)
      ·
        refine ⟨32938140137834836780993313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21958760091889891187328875 32938140137834836780993313)
        ·
          refine ⟨24703605103376127585744985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32938140137834836780993313 24703605103376127585744985)
          ·
            refine ⟨18527703827532095689308739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24703605103376127585744985 18527703827532095689308739)
            ·
              refine ⟨27791555741298143533963109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18527703827532095689308739 27791555741298143533963109)
              ·
                refine ⟨5210916701493401912618083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27791555741298143533963109 5210916701493401912618083)
                ·
                  refine ⟨7816375052240102868927125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5210916701493401912618083 7816375052240102868927125)
                  ·
                    refine ⟨366392580573754821980959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7816375052240102868927125 366392580573754821980959)
                    ·
                      rfl

theorem cell23_2140641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2140641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140641 prefixEnd_2140641 := by exact prefixLift 2140641
  have htrace : WordTrace (prefixWord ++ tailWord_2140641) baseStart_2140641 baseEnd_2140641 := by
    simpa [prefixWord, tailWord_2140641, baseEnd_2140641] using wordTrace_append hprefix tailTrace_2140641
  have hstable : (prefixWord ++ tailWord_2140641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140641).length < 2 ^ (prefixWord ++ tailWord_2140641).sum := by decide
  have hdescent : baseEnd_2140641 < baseStart_2140641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140645 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_2140645 : Nat := 118140960795 + 2140645 * 2 ^ 59
def prefixEnd_2140645 : Nat := 4983230072969 + 3 ^ 40 * 2140645 * 2
def baseEnd_2140645 : Nat := 366393265214627483430953

theorem tailTrace_2140645 : CollatzResearch.WordTrace tailWord_2140645 prefixEnd_2140645 366393265214627483430953 := by
  unfold tailWord_2140645
  simp only [CollatzResearch.WordTrace]
  refine ⟨78075737329816232904759389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52050491553210821936506259 78075737329816232904759389)
  ·
    refine ⟨29278401498681087339284771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78075737329816232904759389 29278401498681087339284771)
    ·
      refine ⟨43917602248021631008927157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29278401498681087339284771 43917602248021631008927157)
      ·
        refine ⟨4117275210752027907086921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43917602248021631008927157 4117275210752027907086921)
        ·
          refine ⟨3087956408064020930315191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4117275210752027907086921 3087956408064020930315191)
          ·
            refine ⟨4631934612096031395472787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087956408064020930315191 4631934612096031395472787)
            ·
              refine ⟨6947901918144047093209181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631934612096031395472787 6947901918144047093209181)
              ·
                refine ⟨2605463219304017659953443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6947901918144047093209181 2605463219304017659953443)
                ·
                  refine ⟨3908194828956026489930165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605463219304017659953443 3908194828956026489930165)
                  ·
                    refine ⟨366393265214627483430953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3908194828956026489930165 366393265214627483430953)
                    ·
                      rfl

theorem cell23_2140645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_2140645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140645 prefixEnd_2140645 := by exact prefixLift 2140645
  have htrace : WordTrace (prefixWord ++ tailWord_2140645) baseStart_2140645 baseEnd_2140645 := by
    simpa [prefixWord, tailWord_2140645, baseEnd_2140645] using wordTrace_append hprefix tailTrace_2140645
  have hstable : (prefixWord ++ tailWord_2140645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140645).length < 2 ^ (prefixWord ++ tailWord_2140645).sum := by decide
  have hdescent : baseEnd_2140645 < baseStart_2140645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140651 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5]
def baseStart_2140651 : Nat := 118140960795 + 2140651 * 2 ^ 59
def prefixEnd_2140651 : Nat := 4983230072969 + 3 ^ 40 * 2140651 * 2
def baseEnd_2140651 : Nat := 1099182876527809426817831

theorem tailTrace_2140651 : CollatzResearch.WordTrace tailWord_2140651 prefixEnd_2140651 1099182876527809426817831 := by
  unfold tailWord_2140651
  simp only [CollatzResearch.WordTrace]
  refine ⟨78075956167794495929477807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52050637445196330619651871 78075956167794495929477807)
  ·
    refine ⟨117113934251691743894216711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78075956167794495929477807 117113934251691743894216711)
    ·
      refine ⟨175670901377537615841325067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117113934251691743894216711 175670901377537615841325067)
      ·
        refine ⟨263506352066306423761987601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175670901377537615841325067 263506352066306423761987601)
        ·
          refine ⟨197629764049729817821490701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263506352066306423761987601 197629764049729817821490701)
          ·
            refine ⟨74111161518648681683059013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197629764049729817821490701 74111161518648681683059013)
            ·
              refine ⟨13895842784746627815573565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74111161518648681683059013 13895842784746627815573565)
              ·
                refine ⟨5210941044279985430840087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13895842784746627815573565 5210941044279985430840087)
                ·
                  refine ⟨7816411566419978146260131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5210941044279985430840087 7816411566419978146260131)
                  ·
                    refine ⟨11724617349629967219390197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7816411566419978146260131 11724617349629967219390197)
                    ·
                      refine ⟨1099182876527809426817831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11724617349629967219390197 1099182876527809426817831)
                      ·
                        rfl

theorem cell23_2140651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].length) (baseStart_2140651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140651 prefixEnd_2140651 := by exact prefixLift 2140651
  have htrace : WordTrace (prefixWord ++ tailWord_2140651) baseStart_2140651 baseEnd_2140651 := by
    simpa [prefixWord, tailWord_2140651, baseEnd_2140651] using wordTrace_append hprefix tailTrace_2140651
  have hstable : (prefixWord ++ tailWord_2140651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140651).length < 2 ^ (prefixWord ++ tailWord_2140651).sum := by decide
  have hdescent : baseEnd_2140651 < baseStart_2140651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140665 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 3, 2, 2]
def baseStart_2140665 : Nat := 118140960795 + 2140665 * 2 ^ 59
def prefixEnd_2140665 : Nat := 4983230072969 + 3 ^ 40 * 2140665 * 2
def baseEnd_2140665 : Nat := 1099190065256972372042767

theorem tailTrace_2140665 : CollatzResearch.WordTrace tailWord_2140665 prefixEnd_2140665 1099190065256972372042767 := by
  unfold tailWord_2140665
  simp only [CollatzResearch.WordTrace]
  refine ⟨78076466789743776320487449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52050977859829184213658299 78076466789743776320487449)
  ·
    refine ⟨58557350092307832240365587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78076466789743776320487449 58557350092307832240365587)
    ·
      refine ⟨87836025138461748360548381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58557350092307832240365587 87836025138461748360548381)
      ·
        refine ⟨32938509426923155635205643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87836025138461748360548381 32938509426923155635205643)
        ·
          refine ⟨49407764140384733452808465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32938509426923155635205643 49407764140384733452808465)
          ·
            refine ⟨37055823105288550089606349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49407764140384733452808465 37055823105288550089606349)
            ·
              refine ⟨13895933664483206283602381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37055823105288550089606349 13895933664483206283602381)
              ·
                refine ⟨5210975124181202356350893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13895933664483206283602381 5210975124181202356350893)
                ·
                  refine ⟨1954115671567950883631585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5210975124181202356350893 1954115671567950883631585)
                  ·
                    refine ⟨1465586753675963162723689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1954115671567950883631585 1465586753675963162723689)
                    ·
                      refine ⟨1099190065256972372042767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465586753675963162723689 1099190065256972372042767)
                      ·
                        rfl

theorem cell23_2140665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_2140665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140665 prefixEnd_2140665 := by exact prefixLift 2140665
  have htrace : WordTrace (prefixWord ++ tailWord_2140665) baseStart_2140665 baseEnd_2140665 := by
    simpa [prefixWord, tailWord_2140665, baseEnd_2140665] using wordTrace_append hprefix tailTrace_2140665
  have hstable : (prefixWord ++ tailWord_2140665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140665).length < 2 ^ (prefixWord ++ tailWord_2140665).sum := by decide
  have hdescent : baseEnd_2140665 < baseStart_2140665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140675 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 2, 4]
def baseStart_2140675 : Nat := 118140960795 + 2140675 * 2 ^ 59
def prefixEnd_2140675 : Nat := 4983230072969 + 3 ^ 40 * 2140675 * 2
def baseEnd_2140675 : Nat := 366398400021172444305907

theorem tailTrace_2140675 : CollatzResearch.WordTrace tailWord_2140675 prefixEnd_2140675 366398400021172444305907 := by
  unfold tailWord_2140675
  simp only [CollatzResearch.WordTrace]
  refine ⟨78076831519707548028351479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52051221013138365352234319 78076831519707548028351479)
  ·
    refine ⟨117115247279561322042527219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78076831519707548028351479 117115247279561322042527219)
    ·
      refine ⟨175672870919341983063790829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117115247279561322042527219 175672870919341983063790829)
      ·
        refine ⟨65877326594753243648921561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175672870919341983063790829 65877326594753243648921561)
        ·
          refine ⟨49407994946064932736691171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65877326594753243648921561 49407994946064932736691171)
          ·
            refine ⟨74111992419097399105036757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49407994946064932736691171 74111992419097399105036757)
            ·
              refine ⟨1736999822322595291524299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74111992419097399105036757 1736999822322595291524299)
              ·
                refine ⟨2605499733483892937286449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736999822322595291524299 2605499733483892937286449)
                ·
                  refine ⟨1954124800112919702964837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605499733483892937286449 1954124800112919702964837)
                  ·
                    refine ⟨366398400021172444305907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954124800112919702964837 366398400021172444305907)
                    ·
                      rfl

theorem cell23_2140675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 4].length) (baseStart_2140675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140675 prefixEnd_2140675 := by exact prefixLift 2140675
  have htrace : WordTrace (prefixWord ++ tailWord_2140675) baseStart_2140675 baseEnd_2140675 := by
    simpa [prefixWord, tailWord_2140675, baseEnd_2140675] using wordTrace_append hprefix tailTrace_2140675
  have hstable : (prefixWord ++ tailWord_2140675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140675).length < 2 ^ (prefixWord ++ tailWord_2140675).sum := by decide
  have hdescent : baseEnd_2140675 < baseStart_2140675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140698 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_2140698 : Nat := 118140960795 + 2140698 * 2 ^ 59
def prefixEnd_2140698 : Nat := 4983230072969 + 3 ^ 40 * 2140698 * 2
def baseEnd_2140698 : Nat := 1099207010118570742930115

theorem tailTrace_2140698 : CollatzResearch.WordTrace tailWord_2140698 prefixEnd_2140698 1099207010118570742930115 := by
  unfold tailWord_2140698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19519417599656055739109687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52051780265749481970959165 19519417599656055739109687)
  ·
    refine ⟨29279126399484083608664531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19519417599656055739109687 29279126399484083608664531)
    ·
      refine ⟨43918689599226125412996797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29279126399484083608664531 43918689599226125412996797)
      ·
        refine ⟨16469508599709797029873799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43918689599226125412996797 16469508599709797029873799)
        ·
          refine ⟨24704262899564695544810699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16469508599709797029873799 24704262899564695544810699)
          ·
            refine ⟨37056394349347043317216049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24704262899564695544810699 37056394349347043317216049)
            ·
              refine ⟨27792295762010282487912037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37056394349347043317216049 27792295762010282487912037)
              ·
                refine ⟨5211055455376927966483507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27792295762010282487912037 5211055455376927966483507)
                ·
                  refine ⟨7816583183065391949725261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211055455376927966483507 7816583183065391949725261)
                  ·
                    refine ⟨2931218693649521981146973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7816583183065391949725261 2931218693649521981146973)
                    ·
                      refine ⟨1099207010118570742930115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2931218693649521981146973 1099207010118570742930115)
                      ·
                        rfl

theorem cell23_2140698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_2140698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140698 prefixEnd_2140698 := by exact prefixLift 2140698
  have htrace : WordTrace (prefixWord ++ tailWord_2140698) baseStart_2140698 baseEnd_2140698 := by
    simpa [prefixWord, tailWord_2140698, baseEnd_2140698] using wordTrace_append hprefix tailTrace_2140698
  have hstable : (prefixWord ++ tailWord_2140698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140698).length < 2 ^ (prefixWord ++ tailWord_2140698).sum := by decide
  have hdescent : baseEnd_2140698 < baseStart_2140698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140725 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_2140725 : Nat := 118140960795 + 2140725 * 2 ^ 59
def prefixEnd_2140725 : Nat := 4983230072969 + 3 ^ 40 * 2140725 * 2
def baseEnd_2140725 : Nat := 1099220874096242137292491

theorem tailTrace_2140725 : CollatzResearch.WordTrace tailWord_2140725 prefixEnd_2140725 1099220874096242137292491 := by
  unfold tailWord_2140725
  simp only [CollatzResearch.WordTrace]
  refine ⟨78078655169526406567671629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52052436779684271045114419 78078655169526406567671629)
  ·
    refine ⟨29279495688572402462876861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78078655169526406567671629 29279495688572402462876861)
    ·
      refine ⟨10979810883214650923578823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29279495688572402462876861 10979810883214650923578823)
      ·
        refine ⟨16469716324821976385368235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10979810883214650923578823 16469716324821976385368235)
        ·
          refine ⟨24704574487232964578052353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16469716324821976385368235 24704574487232964578052353)
          ·
            refine ⟨18528430865424723433539265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24704574487232964578052353 18528430865424723433539265)
            ·
              refine ⟨13896323149068542575154449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18528430865424723433539265 13896323149068542575154449)
              ·
                refine ⟨10422242361801406931365837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13896323149068542575154449 10422242361801406931365837)
                ·
                  refine ⟨3908340885675527599262189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10422242361801406931365837 3908340885675527599262189)
                  ·
                    refine ⟨1465627832128322849723321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3908340885675527599262189 1465627832128322849723321)
                    ·
                      refine ⟨1099220874096242137292491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465627832128322849723321 1099220874096242137292491)
                      ·
                        rfl

theorem cell23_2140725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_2140725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140725 prefixEnd_2140725 := by exact prefixLift 2140725
  have htrace : WordTrace (prefixWord ++ tailWord_2140725) baseStart_2140725 baseEnd_2140725 := by
    simpa [prefixWord, tailWord_2140725, baseEnd_2140725] using wordTrace_append hprefix tailTrace_2140725
  have hstable : (prefixWord ++ tailWord_2140725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140725).length < 2 ^ (prefixWord ++ tailWord_2140725).sum := by decide
  have hdescent : baseEnd_2140725 < baseStart_2140725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140732 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_2140732 : Nat := 118140960795 + 2140732 * 2 ^ 59
def prefixEnd_2140732 : Nat := 4983230072969 + 3 ^ 40 * 2140732 * 2
def baseEnd_2140732 : Nat := 1099224468460823609904959

theorem tailTrace_2140732 : CollatzResearch.WordTrace tailWord_2140732 prefixEnd_2140732 1099224468460823609904959 := by
  unfold tailWord_2140732
  simp only [CollatzResearch.WordTrace]
  refine ⟨39039455240250523381588225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52052606987000697842117633 39039455240250523381588225)
  ·
    refine ⟨29279591430187892536191169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39039455240250523381588225 29279591430187892536191169)
    ·
      refine ⟨21959693572640919402143377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29279591430187892536191169 21959693572640919402143377)
      ·
        refine ⟨16469770179480689551607533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21959693572640919402143377 16469770179480689551607533)
        ·
          refine ⟨6176163817305258581852825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16469770179480689551607533 6176163817305258581852825)
          ·
            refine ⟨4632122862978943936389619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6176163817305258581852825 4632122862978943936389619)
            ·
              refine ⟨6948184294468415904584429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632122862978943936389619 6948184294468415904584429)
              ·
                refine ⟨2605569110425655964219161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6948184294468415904584429 2605569110425655964219161)
                ·
                  refine ⟨1954176832819241973164371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605569110425655964219161 1954176832819241973164371)
                  ·
                    refine ⟨2931265249228862959746557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954176832819241973164371 2931265249228862959746557)
                    ·
                      refine ⟨1099224468460823609904959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2931265249228862959746557 1099224468460823609904959)
                      ·
                        rfl

theorem cell23_2140732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_2140732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140732 prefixEnd_2140732 := by exact prefixLift 2140732
  have htrace : WordTrace (prefixWord ++ tailWord_2140732) baseStart_2140732 baseEnd_2140732 := by
    simpa [prefixWord, tailWord_2140732, baseEnd_2140732] using wordTrace_append hprefix tailTrace_2140732
  have hstable : (prefixWord ++ tailWord_2140732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140732).length < 2 ^ (prefixWord ++ tailWord_2140732).sum := by decide
  have hdescent : baseEnd_2140732 < baseStart_2140732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140778 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_2140778 : Nat := 118140960795 + 2140778 * 2 ^ 59
def prefixEnd_2140778 : Nat := 4983230072969 + 3 ^ 40 * 2140778 * 2
def baseEnd_2140778 : Nat := 122138676507881158881083

theorem tailTrace_2140778 : CollatzResearch.WordTrace tailWord_2140778 prefixEnd_2140778 122138676507881158881083 := by
  unfold tailWord_2140778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19520147059583599154837747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52053725492222931079567325 19520147059583599154837747)
  ·
    refine ⟨29280220589375398732256621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19520147059583599154837747 29280220589375398732256621)
    ·
      refine ⟨10980082721015774524596233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29280220589375398732256621 10980082721015774524596233)
      ·
        refine ⟨8235062040761830893447175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10980082721015774524596233 8235062040761830893447175)
        ·
          refine ⟨12352593061142746340170763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8235062040761830893447175 12352593061142746340170763)
          ·
            refine ⟨18528889591714119510256145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12352593061142746340170763 18528889591714119510256145)
            ·
              refine ⟨13896667193785589632692109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18528889591714119510256145 13896667193785589632692109)
              ·
                refine ⟨5211250197669596112259541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13896667193785589632692109 5211250197669596112259541)
                ·
                  refine ⟨122138676507881158881083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5211250197669596112259541 122138676507881158881083)
                  ·
                    rfl

theorem cell23_2140778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_2140778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140778 prefixEnd_2140778 := by exact prefixLift 2140778
  have htrace : WordTrace (prefixWord ++ tailWord_2140778) baseStart_2140778 baseEnd_2140778 := by
    simpa [prefixWord, tailWord_2140778, baseEnd_2140778] using wordTrace_append hprefix tailTrace_2140778
  have hstable : (prefixWord ++ tailWord_2140778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140778).length < 2 ^ (prefixWord ++ tailWord_2140778).sum := by decide
  have hdescent : baseEnd_2140778 < baseStart_2140778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140789 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2140789 : Nat := 118140960795 + 2140789 * 2 ^ 59
def prefixEnd_2140789 : Nat := 4983230072969 + 3 ^ 40 * 2140789 * 2
def baseEnd_2140789 : Nat := 1099253736858129886892197

theorem tailTrace_2140789 : CollatzResearch.WordTrace tailWord_2140789 prefixEnd_2140789 1099253736858129886892197 := by
  unfold tailWord_2140789
  simp only [CollatzResearch.WordTrace]
  refine ⟨78080989441294545498001421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52053992960863030332000947 78080989441294545498001421)
  ·
    refine ⟨29280371040485454561750533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78080989441294545498001421 29280371040485454561750533)
    ·
      refine ⟨5490069570091022730328225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29280371040485454561750533 5490069570091022730328225)
      ·
        refine ⟨4117552177568267047746169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5490069570091022730328225 4117552177568267047746169)
        ·
          refine ⟨3088164133176200285809627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4117552177568267047746169 3088164133176200285809627)
          ·
            refine ⟨4632246199764300428714441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088164133176200285809627 4632246199764300428714441)
            ·
              refine ⟨3474184649823225321535831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4632246199764300428714441 3474184649823225321535831)
              ·
                refine ⟨5211276974734837982303747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3474184649823225321535831 5211276974734837982303747)
                ·
                  refine ⟨7816915462102256973455621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211276974734837982303747 7816915462102256973455621)
                  ·
                    refine ⟨1465671649144173182522929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7816915462102256973455621 1465671649144173182522929)
                    ·
                      refine ⟨1099253736858129886892197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465671649144173182522929 1099253736858129886892197)
                      ·
                        rfl

theorem cell23_2140789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2140789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140789 prefixEnd_2140789 := by exact prefixLift 2140789
  have htrace : WordTrace (prefixWord ++ tailWord_2140789) baseStart_2140789 baseEnd_2140789 := by
    simpa [prefixWord, tailWord_2140789, baseEnd_2140789] using wordTrace_append hprefix tailTrace_2140789
  have hstable : (prefixWord ++ tailWord_2140789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140789).length < 2 ^ (prefixWord ++ tailWord_2140789).sum := by decide
  have hdescent : baseEnd_2140789 < baseStart_2140789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140845 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2140845 : Nat := 118140960795 + 2140845 * 2 ^ 59
def prefixEnd_2140845 : Nat := 4983230072969 + 3 ^ 40 * 2140845 * 2
def baseEnd_2140845 : Nat := 1099282491774781667791939

theorem tailTrace_2140845 : CollatzResearch.WordTrace tailWord_2140845 prefixEnd_2140845 1099282491774781667791939 := by
  unfold tailWord_2140845
  simp only [CollatzResearch.WordTrace]
  refine ⟨78083031929091667062039989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52055354619394444708026659 78083031929091667062039989)
  ·
    refine ⟨7320284243352343787066249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78083031929091667062039989 7320284243352343787066249)
    ·
      refine ⟨5490213182514257840299687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7320284243352343787066249 5490213182514257840299687)
      ·
        refine ⟨8235319773771386760449531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5490213182514257840299687 8235319773771386760449531)
        ·
          refine ⟨12352979660657080140674297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8235319773771386760449531 12352979660657080140674297)
          ·
            refine ⟨9264734745492810105505723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12352979660657080140674297 9264734745492810105505723)
            ·
              refine ⟨13897102118239215158258585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9264734745492810105505723 13897102118239215158258585)
              ·
                refine ⟨10422826588679411368693939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13897102118239215158258585 10422826588679411368693939)
                ·
                  refine ⟨15634239883019117053040909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10422826588679411368693939 15634239883019117053040909)
                  ·
                    refine ⟨5862839956132168894890341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15634239883019117053040909 5862839956132168894890341)
                    ·
                      refine ⟨1099282491774781667791939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5862839956132168894890341 1099282491774781667791939)
                      ·
                        rfl

theorem cell23_2140845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2140845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140845 prefixEnd_2140845 := by exact prefixLift 2140845
  have htrace : WordTrace (prefixWord ++ tailWord_2140845) baseStart_2140845 baseEnd_2140845 := by
    simpa [prefixWord, tailWord_2140845, baseEnd_2140845] using wordTrace_append hprefix tailTrace_2140845
  have hstable : (prefixWord ++ tailWord_2140845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140845).length < 2 ^ (prefixWord ++ tailWord_2140845).sum := by decide
  have hdescent : baseEnd_2140845 < baseStart_2140845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140858 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_2140858 : Nat := 118140960795 + 2140858 * 2 ^ 59
def prefixEnd_2140858 : Nat := 4983230072969 + 3 ^ 40 * 2140858 * 2
def baseEnd_2140858 : Nat := 1099289167023290116929379

theorem tailTrace_2140858 : CollatzResearch.WordTrace tailWord_2140858 prefixEnd_2140858 1099289167023290116929379 := by
  unfold tailWord_2140858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19520876519511142570565807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52055670718696380188175485 19520876519511142570565807)
  ·
    refine ⟨29281314779266713855848711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19520876519511142570565807 29281314779266713855848711)
    ·
      refine ⟨43921972168900070783773067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29281314779266713855848711 43921972168900070783773067)
      ·
        refine ⟨65882958253350106175659601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43921972168900070783773067 65882958253350106175659601)
        ·
          refine ⟨49412218690012579631744701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65882958253350106175659601 49412218690012579631744701)
          ·
            refine ⟨18529582008754717361904263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49412218690012579631744701 18529582008754717361904263)
            ·
              refine ⟨27794373013132076042856395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18529582008754717361904263 27794373013132076042856395)
              ·
                refine ⟨41691559519698114064284593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27794373013132076042856395 41691559519698114064284593)
                ·
                  refine ⟨31268669639773585548213445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41691559519698114064284593 31268669639773585548213445)
                  ·
                    refine ⟨5862875557457547290290021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31268669639773585548213445 5862875557457547290290021)
                    ·
                      refine ⟨1099289167023290116929379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5862875557457547290290021 1099289167023290116929379)
                      ·
                        rfl

theorem cell23_2140858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_2140858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140858 prefixEnd_2140858 := by exact prefixLift 2140858
  have htrace : WordTrace (prefixWord ++ tailWord_2140858) baseStart_2140858 baseEnd_2140858 := by
    simpa [prefixWord, tailWord_2140858, baseEnd_2140858] using wordTrace_append hprefix tailTrace_2140858
  have hstable : (prefixWord ++ tailWord_2140858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140858).length < 2 ^ (prefixWord ++ tailWord_2140858).sum := by decide
  have hdescent : baseEnd_2140858 < baseStart_2140858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140889 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 1, 4]
def baseStart_2140889 : Nat := 118140960795 + 2140889 * 2 ^ 59
def prefixEnd_2140889 : Nat := 4983230072969 + 3 ^ 40 * 2140889 * 2
def baseEnd_2140889 : Nat := 366435028307859831880579

theorem tailTrace_2140889 : CollatzResearch.WordTrace tailWord_2140889 prefixEnd_2140889 366435028307859831880579 := by
  unfold tailWord_2140889
  simp only [CollatzResearch.WordTrace]
  refine ⟨78084636740932262576641721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52056424493954841717761147 78084636740932262576641721)
  ·
    refine ⟨58563477555699196932481291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78084636740932262576641721 58563477555699196932481291)
    ·
      refine ⟨87845216333548795398721937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58563477555699196932481291 87845216333548795398721937)
      ·
        refine ⟨65883912250161596549041453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87845216333548795398721937 65883912250161596549041453)
        ·
          refine ⟨24706467093810598705890545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65883912250161596549041453 24706467093810598705890545)
          ·
            refine ⟨18529850320357949029417909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24706467093810598705890545 18529850320357949029417909)
            ·
              refine ⟨1737173467533557721507929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18529850320357949029417909 1737173467533557721507929)
              ·
                refine ⟨1302880100650168291130947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737173467533557721507929 1302880100650168291130947)
                ·
                  refine ⟨1954320150975252436696421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302880100650168291130947 1954320150975252436696421)
                  ·
                    refine ⟨366435028307859831880579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954320150975252436696421 366435028307859831880579)
                    ·
                      rfl

theorem cell23_2140889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 4].length) (baseStart_2140889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140889 prefixEnd_2140889 := by exact prefixLift 2140889
  have htrace : WordTrace (prefixWord ++ tailWord_2140889) baseStart_2140889 baseEnd_2140889 := by
    simpa [prefixWord, tailWord_2140889, baseEnd_2140889] using wordTrace_append hprefix tailTrace_2140889
  have hstable : (prefixWord ++ tailWord_2140889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140889).length < 2 ^ (prefixWord ++ tailWord_2140889).sum := by decide
  have hdescent : baseEnd_2140889 < baseStart_2140889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140905 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 3, 5, 2]
def baseStart_2140905 : Nat := 118140960795 + 2140905 * 2 ^ 59
def prefixEnd_2140905 : Nat := 4983230072969 + 3 ^ 40 * 2140905 * 2
def baseEnd_2140905 : Nat := 1099313300614051433041663

theorem tailTrace_2140905 : CollatzResearch.WordTrace tailWord_2140905 prefixEnd_2140905 1099313300614051433041663 := by
  unfold tailWord_2140905
  simp only [CollatzResearch.WordTrace]
  refine ⟨78085220308874297309224169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52056813539249531539482779 78085220308874297309224169)
  ·
    refine ⟨58563915231655722981918127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78085220308874297309224169 58563915231655722981918127)
    ·
      refine ⟨87845872847483584472877191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58563915231655722981918127 87845872847483584472877191)
      ·
        refine ⟨131768809271225376709315787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87845872847483584472877191 131768809271225376709315787)
        ·
          refine ⟨197653213906838065063973681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131768809271225376709315787 197653213906838065063973681)
          ·
            refine ⟨148239910430128548797980261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197653213906838065063973681 148239910430128548797980261)
            ·
              refine ⟨27794983205649102899621299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148239910430128548797980261 27794983205649102899621299)
              ·
                refine ⟨41692474808473654349431949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27794983205649102899621299 41692474808473654349431949)
                ·
                  refine ⟨15634678053177620381036981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41692474808473654349431949 15634678053177620381036981)
                  ·
                    refine ⟨1465751067485401910722217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15634678053177620381036981 1465751067485401910722217)
                    ·
                      refine ⟨1099313300614051433041663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465751067485401910722217 1099313300614051433041663)
                      ·
                        rfl

theorem cell23_2140905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 5, 2].length) (baseStart_2140905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140905 prefixEnd_2140905 := by exact prefixLift 2140905
  have htrace : WordTrace (prefixWord ++ tailWord_2140905) baseStart_2140905 baseEnd_2140905 := by
    simpa [prefixWord, tailWord_2140905, baseEnd_2140905] using wordTrace_append hprefix tailTrace_2140905
  have hstable : (prefixWord ++ tailWord_2140905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140905).length < 2 ^ (prefixWord ++ tailWord_2140905).sum := by decide
  have hdescent : baseEnd_2140905 < baseStart_2140905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140922 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2]
def baseStart_2140922 : Nat := 118140960795 + 2140922 * 2 ^ 59
def prefixEnd_2140922 : Nat := 4983230072969 + 3 ^ 40 * 2140922 * 2
def baseEnd_2140922 : Nat := 1099322029785177866529085

theorem tailTrace_2140922 : CollatzResearch.WordTrace tailWord_2140922 prefixEnd_2140922 1099322029785177866529085 := by
  unfold tailWord_2140922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19521460087453177303148255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52057226899875139475062013 19521460087453177303148255)
  ·
    refine ⟨29282190131179765954722383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19521460087453177303148255 29282190131179765954722383)
    ·
      refine ⟨43923285196769648932083575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29282190131179765954722383 43923285196769648932083575)
      ·
        refine ⟨65884927795154473398125363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43923285196769648932083575 65884927795154473398125363)
        ·
          refine ⟨98827391692731710097188045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65884927795154473398125363 98827391692731710097188045)
          ·
            refine ⟨37060271884774391286445517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98827391692731710097188045 37060271884774391286445517)
            ·
              refine ⟨13897601956790396732417069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37060271884774391286445517 13897601956790396732417069)
              ·
                refine ⟨5211600733796398774656401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13897601956790396732417069 5211600733796398774656401)
                ·
                  refine ⟨3908700550347299080992301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5211600733796398774656401 3908700550347299080992301)
                  ·
                    refine ⟨1465762706380237155372113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3908700550347299080992301 1465762706380237155372113)
                    ·
                      refine ⟨1099322029785177866529085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465762706380237155372113 1099322029785177866529085)
                      ·
                        rfl

theorem cell23_2140922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_2140922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140922 prefixEnd_2140922 := by exact prefixLift 2140922
  have htrace : WordTrace (prefixWord ++ tailWord_2140922) baseStart_2140922 baseEnd_2140922 := by
    simpa [prefixWord, tailWord_2140922, baseEnd_2140922] using wordTrace_append hprefix tailTrace_2140922
  have hstable : (prefixWord ++ tailWord_2140922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140922).length < 2 ^ (prefixWord ++ tailWord_2140922).sum := by decide
  have hdescent : baseEnd_2140922 < baseStart_2140922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140929 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_2140929 : Nat := 118140960795 + 2140929 * 2 ^ 59
def prefixEnd_2140929 : Nat := 4983230072969 + 3 ^ 40 * 2140929 * 2
def baseEnd_2140929 : Nat := 1099325624149759339141553

theorem tailTrace_2140929 : CollatzResearch.WordTrace tailWord_2140929 prefixEnd_2140929 1099325624149759339141553 := by
  unfold tailWord_2140929
  simp only [CollatzResearch.WordTrace]
  refine ⟨78086095660787349408097841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52057397107191566272065227 78086095660787349408097841)
  ·
    refine ⟨58564571745590512056073381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78086095660787349408097841 58564571745590512056073381)
    ·
      refine ⟨10980857202298221010513759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58564571745590512056073381 10980857202298221010513759)
      ·
        refine ⟨16471285803447331515770639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10980857202298221010513759 16471285803447331515770639)
        ·
          refine ⟨24706928705170997273655959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16471285803447331515770639 24706928705170997273655959)
          ·
            refine ⟨37060393057756495910483939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24706928705170997273655959 37060393057756495910483939)
            ·
              refine ⟨55590589586634743865725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37060393057756495910483939 55590589586634743865725909)
              ·
                refine ⟨1302904443436751809352951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55590589586634743865725909 1302904443436751809352951)
                ·
                  refine ⟨1954356665155127714029427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302904443436751809352951 1954356665155127714029427)
                  ·
                    refine ⟨2931534997732691571044141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954356665155127714029427 2931534997732691571044141)
                    ·
                      refine ⟨1099325624149759339141553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2931534997732691571044141 1099325624149759339141553)
                      ·
                        rfl

theorem cell23_2140929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_2140929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140929 prefixEnd_2140929 := by exact prefixLift 2140929
  have htrace : WordTrace (prefixWord ++ tailWord_2140929) baseStart_2140929 baseEnd_2140929 := by
    simpa [prefixWord, tailWord_2140929, baseEnd_2140929] using wordTrace_append hprefix tailTrace_2140929
  have hstable : (prefixWord ++ tailWord_2140929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140929).length < 2 ^ (prefixWord ++ tailWord_2140929).sum := by decide
  have hdescent : baseEnd_2140929 < baseStart_2140929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140945 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 4, 4]
def baseStart_2140945 : Nat := 118140960795 + 2140945 * 2 ^ 59
def prefixEnd_2140945 : Nat := 4983230072969 + 3 ^ 40 * 2140945 * 2
def baseEnd_2140945 : Nat := 366444613280077092180493

theorem tailTrace_2140945 : CollatzResearch.WordTrace tailWord_2140945 prefixEnd_2140945 366444613280077092180493 := by
  unfold tailWord_2140945
  simp only [CollatzResearch.WordTrace]
  refine ⟨78086679228729384140680289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52057786152486256093786859 78086679228729384140680289)
  ·
    refine ⟨58565009421547038105510217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78086679228729384140680289 58565009421547038105510217)
    ·
      refine ⟨43923757066160278579132663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58565009421547038105510217 43923757066160278579132663)
      ·
        refine ⟨65885635599240417868698995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43923757066160278579132663 65885635599240417868698995)
        ·
          refine ⟨98828453398860626803048493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65885635599240417868698995 98828453398860626803048493)
          ·
            refine ⟨37060670024572735051143185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98828453398860626803048493 37060670024572735051143185)
            ·
              refine ⟨27795502518429551288357389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37060670024572735051143185 27795502518429551288357389)
              ·
                refine ⟨10423313444411081733134021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27795502518429551288357389 10423313444411081733134021)
                ·
                  refine ⟨1954371270827077824962629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10423313444411081733134021 1954371270827077824962629)
                  ·
                    refine ⟨366444613280077092180493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954371270827077824962629 366444613280077092180493)
                    ·
                      rfl

theorem cell23_2140945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_2140945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140945 prefixEnd_2140945 := by exact prefixLift 2140945
  have htrace : WordTrace (prefixWord ++ tailWord_2140945) baseStart_2140945 baseEnd_2140945 := by
    simpa [prefixWord, tailWord_2140945, baseEnd_2140945] using wordTrace_append hprefix tailTrace_2140945
  have hstable : (prefixWord ++ tailWord_2140945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140945).length < 2 ^ (prefixWord ++ tailWord_2140945).sum := by decide
  have hdescent : baseEnd_2140945 < baseStart_2140945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140962 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2140962 : Nat := 118140960795 + 2140962 * 2 ^ 59
def prefixEnd_2140962 : Nat := 4983230072969 + 3 ^ 40 * 2140962 * 2
def baseEnd_2140962 : Nat := 366447523003785903342967

theorem tailTrace_2140962 : CollatzResearch.WordTrace tailWord_2140962 prefixEnd_2140962 366447523003785903342967 := by
  unfold tailWord_2140962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19521824817416949011012285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52058199513111864029366093 19521824817416949011012285)
  ·
    refine ⟨7320684306531355879129607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19521824817416949011012285 7320684306531355879129607)
    ·
      refine ⟨10981026459797033818694411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7320684306531355879129607 10981026459797033818694411)
      ·
        refine ⟨16471539689695550728041617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10981026459797033818694411 16471539689695550728041617)
        ·
          refine ⟨12353654767271663046031213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16471539689695550728041617 12353654767271663046031213)
          ·
            refine ⟨4632620537726873642261705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12353654767271663046031213 4632620537726873642261705)
            ·
              refine ⟨3474465403295155231696279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4632620537726873642261705 3474465403295155231696279)
              ·
                refine ⟨5211698104942732847544419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3474465403295155231696279 5211698104942732847544419)
                ·
                  refine ⟨7817547157414099271316629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5211698104942732847544419 7817547157414099271316629)
                  ·
                    refine ⟨366447523003785903342967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7817547157414099271316629 366447523003785903342967)
                    ·
                      rfl

theorem cell23_2140962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2140962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140962 prefixEnd_2140962 := by exact prefixLift 2140962
  have htrace : WordTrace (prefixWord ++ tailWord_2140962) baseStart_2140962 baseEnd_2140962 := by
    simpa [prefixWord, tailWord_2140962, baseEnd_2140962] using wordTrace_append hprefix tailTrace_2140962
  have hstable : (prefixWord ++ tailWord_2140962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140962).length < 2 ^ (prefixWord ++ tailWord_2140962).sum := by decide
  have hdescent : baseEnd_2140962 < baseStart_2140962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140972 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_2140972 : Nat := 118140960795 + 2140972 * 2 ^ 59
def prefixEnd_2140972 : Nat := 4983230072969 + 3 ^ 40 * 2140972 * 2
def baseEnd_2140972 : Nat := 1099347703817902670903855

theorem tailTrace_2140972 : CollatzResearch.WordTrace tailWord_2140972 prefixEnd_2140972 1099347703817902670903855 := by
  unfold tailWord_2140972
  simp only [CollatzResearch.WordTrace]
  refine ⟨39043831999815783875956585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52058442666421045167942113 39043831999815783875956585)
  ·
    refine ⟨29282873999861837906967439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39043831999815783875956585 29282873999861837906967439)
    ·
      refine ⟨43924310999792756860451159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29282873999861837906967439 43924310999792756860451159)
      ·
        refine ⟨65886466499689135290676739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43924310999792756860451159 65886466499689135290676739)
        ·
          refine ⟨98829699749533702936015109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65886466499689135290676739 98829699749533702936015109)
          ·
            refine ⟨18530568703037569300502833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98829699749533702936015109 18530568703037569300502833)
            ·
              refine ⟨13897926527278176975377125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18530568703037569300502833 13897926527278176975377125)
              ·
                refine ⟨2605861223864658182883211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13897926527278176975377125 2605861223864658182883211)
                ·
                  refine ⟨3908791835796987274324817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605861223864658182883211 3908791835796987274324817)
                  ·
                    refine ⟨2931593876847740455743613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3908791835796987274324817 2931593876847740455743613)
                    ·
                      refine ⟨1099347703817902670903855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2931593876847740455743613 1099347703817902670903855)
                      ·
                        rfl

theorem cell23_2140972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_2140972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140972 prefixEnd_2140972 := by exact prefixLift 2140972
  have htrace : WordTrace (prefixWord ++ tailWord_2140972) baseStart_2140972 baseEnd_2140972 := by
    simpa [prefixWord, tailWord_2140972, baseEnd_2140972] using wordTrace_append hprefix tailTrace_2140972
  have hstable : (prefixWord ++ tailWord_2140972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140972).length < 2 ^ (prefixWord ++ tailWord_2140972).sum := by decide
  have hdescent : baseEnd_2140972 < baseStart_2140972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140986 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4]
def baseStart_2140986 : Nat := 118140960795 + 2140986 * 2 ^ 59
def prefixEnd_2140986 : Nat := 4983230072969 + 3 ^ 40 * 2140986 * 2
def baseEnd_2140986 : Nat := 1099354892547065616128791

theorem tailTrace_2140986 : CollatzResearch.WordTrace tailWord_2140986 prefixEnd_2140986 1099354892547065616128791 := by
  unfold tailWord_2140986
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522043655395212035730703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52058783081053898761948541 19522043655395212035730703)
  ·
    refine ⟨29283065483092818053596055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19522043655395212035730703 29283065483092818053596055)
    ·
      refine ⟨43924598224639227080394083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29283065483092818053596055 43924598224639227080394083)
      ·
        refine ⟨65886897336958840620591125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43924598224639227080394083 65886897336958840620591125)
        ·
          refine ⟨3088448312669945654090209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65886897336958840620591125 3088448312669945654090209)
          ·
            refine ⟨2316336234502459240567657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3088448312669945654090209 2316336234502459240567657)
            ·
              refine ⟨1737252175876844430425743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2316336234502459240567657 1737252175876844430425743)
              ·
                refine ⟨2605878263815266645638615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737252175876844430425743 2605878263815266645638615)
                ·
                  refine ⟨3908817395722899968457923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605878263815266645638615 3908817395722899968457923)
                  ·
                    refine ⟨5863226093584349952686885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3908817395722899968457923 5863226093584349952686885)
                    ·
                      refine ⟨1099354892547065616128791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5863226093584349952686885 1099354892547065616128791)
                      ·
                        rfl

theorem cell23_2140986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_2140986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140986 prefixEnd_2140986 := by exact prefixLift 2140986
  have htrace : WordTrace (prefixWord ++ tailWord_2140986) baseStart_2140986 baseEnd_2140986 := by
    simpa [prefixWord, tailWord_2140986, baseEnd_2140986] using wordTrace_append hprefix tailTrace_2140986
  have hstable : (prefixWord ++ tailWord_2140986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140986).length < 2 ^ (prefixWord ++ tailWord_2140986).sum := by decide
  have hdescent : baseEnd_2140986 < baseStart_2140986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140996 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2140996 : Nat := 118140960795 + 2140996 * 2 ^ 59
def prefixEnd_2140996 : Nat := 4983230072969 + 3 ^ 40 * 2140996 * 2
def baseEnd_2140996 : Nat := 366453342451203525667915

theorem tailTrace_2140996 : CollatzResearch.WordTrace tailWord_2140996 prefixEnd_2140996 366453342451203525667915 := by
  unfold tailWord_2140996
  simp only [CollatzResearch.WordTrace]
  refine ⟨39044269675772309925393421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52059026234363079900524561 39044269675772309925393421)
  ·
    refine ⟨14641601128414616222022533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39044269675772309925393421 14641601128414616222022533)
    ·
      refine ⟨2745300211577740541629225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14641601128414616222022533 2745300211577740541629225)
      ·
        refine ⟨2058975158683305406221919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2745300211577740541629225 2058975158683305406221919)
        ·
          refine ⟨3088462738024958109332879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058975158683305406221919 3088462738024958109332879)
          ·
            refine ⟨4632694107037437163999319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088462738024958109332879 4632694107037437163999319)
            ·
              refine ⟨6949041160556155745998979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632694107037437163999319 6949041160556155745998979)
              ·
                refine ⟨10423561740834233618998469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949041160556155745998979 10423561740834233618998469)
                ·
                  refine ⟨1954417826406418803562213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10423561740834233618998469 1954417826406418803562213)
                  ·
                    refine ⟨366453342451203525667915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954417826406418803562213 366453342451203525667915)
                    ·
                      rfl

theorem cell23_2140996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2140996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2140996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2140996 prefixEnd_2140996 := by exact prefixLift 2140996
  have htrace : WordTrace (prefixWord ++ tailWord_2140996) baseStart_2140996 baseEnd_2140996 := by
    simpa [prefixWord, tailWord_2140996, baseEnd_2140996] using wordTrace_append hprefix tailTrace_2140996
  have hstable : (prefixWord ++ tailWord_2140996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140996).length < 2 ^ (prefixWord ++ tailWord_2140996).sum := by decide
  have hdescent : baseEnd_2140996 < baseStart_2140996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141026 : List Nat := [3, 3, 2, 1, 4, 1, 2, 7]
def baseStart_2141026 : Nat := 118140960795 + 2141026 * 2 ^ 59
def prefixEnd_2141026 : Nat := 4983230072969 + 3 ^ 40 * 2141026 * 2
def baseEnd_2141026 : Nat := 40717608584194276282541

theorem tailTrace_2141026 : CollatzResearch.WordTrace tailWord_2141026 prefixEnd_2141026 40717608584194276282541 := by
  unfold tailWord_2141026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522408385358983743594733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52059755694290623316252621 19522408385358983743594733)
  ·
    refine ⟨7320903144509618903848025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19522408385358983743594733 7320903144509618903848025)
    ·
      refine ⟨5490677358382214177886019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7320903144509618903848025 5490677358382214177886019)
      ·
        refine ⟨8236016037573321266829029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5490677358382214177886019 8236016037573321266829029)
        ·
          refine ⟨1544253007044997737530443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8236016037573321266829029 1544253007044997737530443)
          ·
            refine ⟨2316379510567496606295665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544253007044997737530443 2316379510567496606295665)
            ·
              refine ⟨1737284632925622454721749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2316379510567496606295665 1737284632925622454721749)
              ·
                refine ⟨40717608584194276282541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1737284632925622454721749 40717608584194276282541)
                ·
                  rfl

theorem cell23_2141026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_2141026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141026 prefixEnd_2141026 := by exact prefixLift 2141026
  have htrace : WordTrace (prefixWord ++ tailWord_2141026) baseStart_2141026 baseEnd_2141026 := by
    simpa [prefixWord, tailWord_2141026, baseEnd_2141026] using wordTrace_append hprefix tailTrace_2141026
  have hstable : (prefixWord ++ tailWord_2141026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141026).length < 2 ^ (prefixWord ++ tailWord_2141026).sum := by decide
  have hdescent : baseEnd_2141026 < baseStart_2141026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
