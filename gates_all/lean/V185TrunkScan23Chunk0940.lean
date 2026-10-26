import V185TrunkScan23Chunk0939

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5563861 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5563861 : Nat := 118140960795 + 5563861 * 2 ^ 59
def prefixEnd_5563861 : Nat := 4983230072969 + 3 ^ 40 * 5563861 * 2
def baseEnd_5563861 : Nat := 2856934987805361101949775

theorem tailTrace_5563861 : CollatzResearch.WordTrace tailWord_5563861 prefixEnd_5563861 2856934987805361101949775 := by
  unfold tailWord_5563861
  simp only [CollatzResearch.WordTrace]
  refine ⟨202930682096089303652091437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135287121397392869101394291 202930682096089303652091437)
  ·
    refine ⟨76099005786033488869534289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202930682096089303652091437 76099005786033488869534289)
    ·
      refine ⟨57074254339525116652150717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76099005786033488869534289 57074254339525116652150717)
      ·
        refine ⟨21402845377321918744556519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57074254339525116652150717 21402845377321918744556519)
        ·
          refine ⟨32104268065982878116834779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21402845377321918744556519 32104268065982878116834779)
          ·
            refine ⟨48156402098974317175252169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32104268065982878116834779 48156402098974317175252169)
            ·
              refine ⟨36117301574230737881439127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48156402098974317175252169 36117301574230737881439127)
              ·
                refine ⟨54175952361346106822158691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36117301574230737881439127 54175952361346106822158691)
                ·
                  refine ⟨81263928542019160233238037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54175952361346106822158691 81263928542019160233238037)
                  ·
                    refine ⟨3809246650407148135933033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81263928542019160233238037 3809246650407148135933033)
                    ·
                      refine ⟨2856934987805361101949775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809246650407148135933033 2856934987805361101949775)
                      ·
                        rfl

theorem cell23_5563861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5563861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563861 prefixEnd_5563861 := by exact prefixLift 5563861
  have htrace : WordTrace (prefixWord ++ tailWord_5563861) baseStart_5563861 baseEnd_5563861 := by
    simpa [prefixWord, tailWord_5563861, baseEnd_5563861] using wordTrace_append hprefix tailTrace_5563861
  have hstable : (prefixWord ++ tailWord_5563861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563861).length < 2 ^ (prefixWord ++ tailWord_5563861).sum := by decide
  have hdescent : baseEnd_5563861 < baseStart_5563861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563864 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_5563864 : Nat := 118140960795 + 5563864 * 2 ^ 59
def prefixEnd_5563864 : Nat := 4983230072969 + 3 ^ 40 * 5563864 * 2
def baseEnd_5563864 : Nat := 2856936528247324590212261

theorem tailTrace_5563864 : CollatzResearch.WordTrace tailWord_5563864 prefixEnd_5563864 2856936528247324590212261 := by
  unfold tailWord_5563864
  simp only [CollatzResearch.WordTrace]
  refine ⟨101465395757539217582225323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135287194343385623442967097 101465395757539217582225323)
  ·
    refine ⟨152198093636308826373337985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101465395757539217582225323 152198093636308826373337985)
    ·
      refine ⟨114148570227231619780003489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152198093636308826373337985 114148570227231619780003489)
      ·
        refine ⟨85611427670423714835002617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114148570227231619780003489 85611427670423714835002617)
        ·
          refine ⟨64208570752817786126251963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85611427670423714835002617 64208570752817786126251963)
          ·
            refine ⟨96312856129226679189377945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64208570752817786126251963 96312856129226679189377945)
            ·
              refine ⟨72234642096920009392033459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96312856129226679189377945 72234642096920009392033459)
              ·
                refine ⟨108351963145380014088050189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72234642096920009392033459 108351963145380014088050189)
                ·
                  refine ⟨40631986179517505283018821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108351963145380014088050189 40631986179517505283018821)
                  ·
                    refine ⟨7618497408659532240566029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40631986179517505283018821 7618497408659532240566029)
                    ·
                      refine ⟨2856936528247324590212261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618497408659532240566029 2856936528247324590212261)
                      ·
                        rfl

theorem cell23_5563864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_5563864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563864 prefixEnd_5563864 := by exact prefixLift 5563864
  have htrace : WordTrace (prefixWord ++ tailWord_5563864) baseStart_5563864 baseEnd_5563864 := by
    simpa [prefixWord, tailWord_5563864, baseEnd_5563864] using wordTrace_append hprefix tailTrace_5563864
  have hstable : (prefixWord ++ tailWord_5563864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563864).length < 2 ^ (prefixWord ++ tailWord_5563864).sum := by decide
  have hdescent : baseEnd_5563864 < baseStart_5563864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563901 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 6]
def baseStart_5563901 : Nat := 118140960795 + 5563901 * 2 ^ 59
def prefixEnd_5563901 : Nat := 4983230072969 + 3 ^ 40 * 5563901 * 2
def baseEnd_5563901 : Nat := 317439503003504549494399

theorem tailTrace_5563901 : CollatzResearch.WordTrace tailWord_5563901 prefixEnd_5563901 317439503003504549494399 := by
  unfold tailWord_5563901
  simp only [CollatzResearch.WordTrace]
  refine ⟨202932141015944390483547557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135288094010629593655698371 202932141015944390483547557)
  ·
    refine ⟨38049776440489573215665167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202932141015944390483547557 38049776440489573215665167)
    ·
      refine ⟨57074664660734359823497751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38049776440489573215665167 57074664660734359823497751)
      ·
        refine ⟨85611996991101539735246627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57074664660734359823497751 85611996991101539735246627)
        ·
          refine ⟨128417995486652309602869941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85611996991101539735246627 128417995486652309602869941)
          ·
            refine ⟨12039187076873654025269057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128417995486652309602869941 12039187076873654025269057)
            ·
              refine ⟨9029390307655240518951793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12039187076873654025269057 9029390307655240518951793)
              ·
                refine ⟨6772042730741430389213845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9029390307655240518951793 6772042730741430389213845)
                ·
                  refine ⟨317439503003504549494399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6772042730741430389213845 317439503003504549494399)
                  ·
                    rfl

theorem cell23_5563901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_5563901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563901 prefixEnd_5563901 := by exact prefixLift 5563901
  have htrace : WordTrace (prefixWord ++ tailWord_5563901) baseStart_5563901 baseEnd_5563901 := by
    simpa [prefixWord, tailWord_5563901, baseEnd_5563901] using wordTrace_append hprefix tailTrace_5563901
  have hstable : (prefixWord ++ tailWord_5563901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563901).length < 2 ^ (prefixWord ++ tailWord_5563901).sum := by decide
  have hdescent : baseEnd_5563901 < baseStart_5563901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563905 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 1, 4]
def baseStart_5563905 : Nat := 118140960795 + 5563905 * 2 ^ 59
def prefixEnd_5563905 : Nat := 4983230072969 + 3 ^ 40 * 5563905 * 2
def baseEnd_5563905 : Nat := 952319193651386309933191

theorem tailTrace_5563905 : CollatzResearch.WordTrace tailWord_5563905 prefixEnd_5563905 952319193651386309933191 := by
  unfold tailWord_5563905
  simp only [CollatzResearch.WordTrace]
  refine ⟨202932286907929899166693169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135288191271953266111128779 202932286907929899166693169)
  ·
    refine ⟨152199215180947424375019877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202932286907929899166693169 152199215180947424375019877)
    ·
      refine ⟨28537352846427642070316227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152199215180947424375019877 28537352846427642070316227)
      ·
        refine ⟨42806029269641463105474341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28537352846427642070316227 42806029269641463105474341)
        ·
          refine ⟨8026130488057774332276439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42806029269641463105474341 8026130488057774332276439)
          ·
            refine ⟨12039195732086661498414659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8026130488057774332276439 12039195732086661498414659)
            ·
              refine ⟨18058793598129992247621989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12039195732086661498414659 18058793598129992247621989)
              ·
                refine ⟨3386023799649373546429123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18058793598129992247621989 3386023799649373546429123)
                ·
                  refine ⟨5079035699474060319643685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386023799649373546429123 5079035699474060319643685)
                  ·
                    refine ⟨952319193651386309933191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5079035699474060319643685 952319193651386309933191)
                    ·
                      rfl

theorem cell23_5563905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_5563905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563905 prefixEnd_5563905 := by exact prefixLift 5563905
  have htrace : WordTrace (prefixWord ++ tailWord_5563905) baseStart_5563905 baseEnd_5563905 := by
    simpa [prefixWord, tailWord_5563905, baseEnd_5563905] using wordTrace_append hprefix tailTrace_5563905
  have hstable : (prefixWord ++ tailWord_5563905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563905).length < 2 ^ (prefixWord ++ tailWord_5563905).sum := by decide
  have hdescent : baseEnd_5563905 < baseStart_5563905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563921 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 1, 5, 2]
def baseStart_5563921 : Nat := 118140960795 + 5563921 * 2 ^ 59
def prefixEnd_5563921 : Nat := 4983230072969 + 3 ^ 40 * 5563921 * 2
def baseEnd_5563921 : Nat := 2856965796644630867199499

theorem tailTrace_5563921 : CollatzResearch.WordTrace tailWord_5563921 prefixEnd_5563921 2856965796644630867199499 := by
  unfold tailWord_5563921
  simp only [CollatzResearch.WordTrace]
  refine ⟨202932870475871933899275617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135288580317247955932850411 202932870475871933899275617)
  ·
    refine ⟨152199652856903950424456713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202932870475871933899275617 152199652856903950424456713)
    ·
      refine ⟨114149739642677962818342535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152199652856903950424456713 114149739642677962818342535)
      ·
        refine ⟨171224609464016944227513803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114149739642677962818342535 171224609464016944227513803)
        ·
          refine ⟨256836914196025416341270705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171224609464016944227513803 256836914196025416341270705)
          ·
            refine ⟨192627685647019062255953029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256836914196025416341270705 192627685647019062255953029)
            ·
              refine ⟨36117691058816074172991193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192627685647019062255953029 36117691058816074172991193)
              ·
                refine ⟨27088268294112055629743395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36117691058816074172991193 27088268294112055629743395)
                ·
                  refine ⟨40632402441168083444615093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27088268294112055629743395 40632402441168083444615093)
                  ·
                    refine ⟨3809287728859507822932665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40632402441168083444615093 3809287728859507822932665)
                    ·
                      refine ⟨2856965796644630867199499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809287728859507822932665 2856965796644630867199499)
                      ·
                        rfl

theorem cell23_5563921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_5563921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563921 prefixEnd_5563921 := by exact prefixLift 5563921
  have htrace : WordTrace (prefixWord ++ tailWord_5563921) baseStart_5563921 baseEnd_5563921 := by
    simpa [prefixWord, tailWord_5563921, baseEnd_5563921] using wordTrace_append hprefix tailTrace_5563921
  have hstable : (prefixWord ++ tailWord_5563921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563921).length < 2 ^ (prefixWord ++ tailWord_5563921).sum := by decide
  have hdescent : baseEnd_5563921 < baseStart_5563921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563991 : List Nat := [1, 1, 3, 2, 2, 3, 4, 7]
def baseStart_5563991 : Nat := 118140960795 + 5563991 * 2 ^ 59
def prefixEnd_5563991 : Nat := 4983230072969 + 3 ^ 40 * 5563991 * 2
def baseEnd_5563991 : Nat := 105814879270016503456451

theorem tailTrace_5563991 : CollatzResearch.WordTrace tailWord_5563991 prefixEnd_5563991 105814879270016503456451 := by
  unfold tailWord_5563991
  simp only [CollatzResearch.WordTrace]
  refine ⟨202935423585618335854323827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135290282390412223902882551 202935423585618335854323827)
  ·
    refine ⟨304403135378427503781485741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202935423585618335854323827 304403135378427503781485741)
    ·
      refine ⟨114151175766910313918057153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304403135378427503781485741 114151175766910313918057153)
      ·
        refine ⟨85613381825182735438542865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114151175766910313918057153 85613381825182735438542865)
        ·
          refine ⟨64210036368887051578907149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85613381825182735438542865 64210036368887051578907149)
          ·
            refine ⟨24078763638332644342090181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64210036368887051578907149 24078763638332644342090181)
            ·
              refine ⟨4514768182187370814141909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24078763638332644342090181 4514768182187370814141909)
              ·
                refine ⟨105814879270016503456451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4514768182187370814141909 105814879270016503456451)
                ·
                  rfl

theorem cell23_5563991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 7].length) (baseStart_5563991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563991 prefixEnd_5563991 := by exact prefixLift 5563991
  have htrace : WordTrace (prefixWord ++ tailWord_5563991) baseStart_5563991 baseEnd_5563991 := by
    simpa [prefixWord, tailWord_5563991, baseEnd_5563991] using wordTrace_append hprefix tailTrace_5563991
  have hstable : (prefixWord ++ tailWord_5563991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563991).length < 2 ^ (prefixWord ++ tailWord_5563991).sum := by decide
  have hdescent : baseEnd_5563991 < baseStart_5563991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5563994 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_5563994 : Nat := 118140960795 + 5563994 * 2 ^ 59
def prefixEnd_5563994 : Nat := 4983230072969 + 3 ^ 40 * 5563994 * 2
def baseEnd_5563994 : Nat := 2857003280732409081586663

theorem tailTrace_5563994 : CollatzResearch.WordTrace tailWord_5563994 prefixEnd_5563994 2857003280732409081586663 := by
  unfold tailWord_5563994
  simp only [CollatzResearch.WordTrace]
  refine ⟨50733883251151866841670759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135290355336404978244455357 50733883251151866841670759)
  ·
    refine ⟨76100824876727800262506139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50733883251151866841670759 76100824876727800262506139)
    ·
      refine ⟨114151237315091700393759209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76100824876727800262506139 114151237315091700393759209)
      ·
        refine ⟨85613427986318775295319407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114151237315091700393759209 85613427986318775295319407)
        ·
          refine ⟨128420141979478162942979111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85613427986318775295319407 128420141979478162942979111)
          ·
            refine ⟨192630212969217244414468667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128420141979478162942979111 192630212969217244414468667)
            ·
              refine ⟨288945319453825866621703001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192630212969217244414468667 288945319453825866621703001)
              ·
                refine ⟨216708989590369399966277251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288945319453825866621703001 216708989590369399966277251)
                ·
                  refine ⟨325063484385554099949415877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216708989590369399966277251 325063484385554099949415877)
                  ·
                    refine ⟨60949403322291393740515477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325063484385554099949415877 60949403322291393740515477)
                    ·
                      refine ⟨2857003280732409081586663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60949403322291393740515477 2857003280732409081586663)
                      ·
                        rfl

theorem cell23_5563994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_5563994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5563994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5563994 prefixEnd_5563994 := by exact prefixLift 5563994
  have htrace : WordTrace (prefixWord ++ tailWord_5563994) baseStart_5563994 baseEnd_5563994 := by
    simpa [prefixWord, tailWord_5563994, baseEnd_5563994] using wordTrace_append hprefix tailTrace_5563994
  have hstable : (prefixWord ++ tailWord_5563994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5563994).length < 2 ^ (prefixWord ++ tailWord_5563994).sum := by decide
  have hdescent : baseEnd_5563994 < baseStart_5563994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5563994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564001 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_5564001 : Nat := 118140960795 + 5564001 * 2 ^ 59
def prefixEnd_5564001 : Nat := 4983230072969 + 3 ^ 40 * 5564001 * 2
def baseEnd_5564001 : Nat := 2857006875096990554199131

theorem tailTrace_5564001 : CollatzResearch.WordTrace tailWord_5564001 prefixEnd_5564001 2857006875096990554199131 := by
  unfold tailWord_5564001
  simp only [CollatzResearch.WordTrace]
  refine ⟨202935788315582107562187857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135290525543721405041458571 202935788315582107562187857)
  ·
    refine ⟨152201841236686580671640893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202935788315582107562187857 152201841236686580671640893)
    ·
      refine ⟨57075690463757467751865335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152201841236686580671640893 57075690463757467751865335)
      ·
        refine ⟨85613535695636201627798003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57075690463757467751865335 85613535695636201627798003)
        ·
          refine ⟨128420303543454302441697005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85613535695636201627798003 128420303543454302441697005)
          ·
            refine ⟨48157613828795363415636377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128420303543454302441697005 48157613828795363415636377)
            ·
              refine ⟨36118210371596522561727283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48157613828795363415636377 36118210371596522561727283)
              ·
                refine ⟨54177315557394783842590925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36118210371596522561727283 54177315557394783842590925)
                ·
                  refine ⟨20316493334023043940971597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54177315557394783842590925 20316493334023043940971597)
                  ·
                    refine ⟨7618685000258641477864349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20316493334023043940971597 7618685000258641477864349)
                    ·
                      refine ⟨2857006875096990554199131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618685000258641477864349 2857006875096990554199131)
                      ·
                        rfl

theorem cell23_5564001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_5564001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564001 prefixEnd_5564001 := by exact prefixLift 5564001
  have htrace : WordTrace (prefixWord ++ tailWord_5564001) baseStart_5564001 baseEnd_5564001 := by
    simpa [prefixWord, tailWord_5564001, baseEnd_5564001] using wordTrace_append hprefix tailTrace_5564001
  have hstable : (prefixWord ++ tailWord_5564001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564001).length < 2 ^ (prefixWord ++ tailWord_5564001).sum := by decide
  have hdescent : baseEnd_5564001 < baseStart_5564001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564011 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 9, 2]
def baseStart_5564011 : Nat := 118140960795 + 5564011 * 2 ^ 59
def prefixEnd_5564011 : Nat := 4983230072969 + 3 ^ 40 * 5564011 * 2
def baseEnd_5564011 : Nat := 2857012009903535515074085

theorem tailTrace_5564011 : CollatzResearch.WordTrace tailWord_5564011 prefixEnd_5564011 2857012009903535515074085 := by
  unfold tailWord_5564011
  simp only [CollatzResearch.WordTrace]
  refine ⟨202936153045545879270051887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135290768697030586180034591 202936153045545879270051887)
  ·
    refine ⟨304404229568318818905077831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202936153045545879270051887 304404229568318818905077831)
    ·
      refine ⟨456606344352478228357616747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304404229568318818905077831 456606344352478228357616747)
      ·
        refine ⟨684909516528717342536425121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456606344352478228357616747 684909516528717342536425121)
        ·
          refine ⟨513682137396538006902318841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 684909516528717342536425121 513682137396538006902318841)
          ·
            refine ⟨385261603047403505176739131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513682137396538006902318841 385261603047403505176739131)
            ·
              refine ⟨577892404571105257765108697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385261603047403505176739131 577892404571105257765108697)
              ·
                refine ⟨433419303428328943323831523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577892404571105257765108697 433419303428328943323831523)
                ·
                  refine ⟨650128955142493414985747285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433419303428328943323831523 650128955142493414985747285)
                  ·
                    refine ⟨3809349346538047353432113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 650128955142493414985747285 3809349346538047353432113)
                    ·
                      refine ⟨2857012009903535515074085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809349346538047353432113 2857012009903535515074085)
                      ·
                        rfl

theorem cell23_5564011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9, 2].length) (baseStart_5564011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564011 prefixEnd_5564011 := by exact prefixLift 5564011
  have htrace : WordTrace (prefixWord ++ tailWord_5564011) baseStart_5564011 baseEnd_5564011 := by
    simpa [prefixWord, tailWord_5564011, baseEnd_5564011] using wordTrace_append hprefix tailTrace_5564011
  have hstable : (prefixWord ++ tailWord_5564011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564011).length < 2 ^ (prefixWord ++ tailWord_5564011).sum := by decide
  have hdescent : baseEnd_5564011 < baseStart_5564011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564028 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_5564028 : Nat := 118140960795 + 5564028 * 2 ^ 59
def prefixEnd_5564028 : Nat := 4983230072969 + 3 ^ 40 * 5564028 * 2
def baseEnd_5564028 : Nat := 2857020739074661948561507

theorem tailTrace_5564028 : CollatzResearch.WordTrace tailWord_5564028 prefixEnd_5564028 2857020739074661948561507 := by
  unfold tailWord_5564028
  simp only [CollatzResearch.WordTrace]
  refine ⟨101468386543242145586710369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135291182057656194115613825 101468386543242145586710369)
  ·
    refine ⟨76101289907431609190032777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101468386543242145586710369 76101289907431609190032777)
    ·
      refine ⟨57075967430573706892524583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76101289907431609190032777 57075967430573706892524583)
      ·
        refine ⟨85613951145860560338786875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57075967430573706892524583 85613951145860560338786875)
        ·
          refine ⟨128420926718790840508180313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85613951145860560338786875 128420926718790840508180313)
          ·
            refine ⟨96315695039093130381135235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128420926718790840508180313 96315695039093130381135235)
            ·
              refine ⟨144473542558639695571702853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96315695039093130381135235 144473542558639695571702853)
              ·
                refine ⟨27088789229744942919694285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144473542558639695571702853 27088789229744942919694285)
                ·
                  refine ⟨10158295961154353594885357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27088789229744942919694285 10158295961154353594885357)
                  ·
                    refine ⟨3809360985432882598082009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10158295961154353594885357 3809360985432882598082009)
                    ·
                      refine ⟨2857020739074661948561507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809360985432882598082009 2857020739074661948561507)
                      ·
                        rfl

theorem cell23_5564028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_5564028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564028 prefixEnd_5564028 := by exact prefixLift 5564028
  have htrace : WordTrace (prefixWord ++ tailWord_5564028) baseStart_5564028 baseEnd_5564028 := by
    simpa [prefixWord, tailWord_5564028, baseEnd_5564028] using wordTrace_append hprefix tailTrace_5564028
  have hstable : (prefixWord ++ tailWord_5564028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564028).length < 2 ^ (prefixWord ++ tailWord_5564028).sum := by decide
  have hdescent : baseEnd_5564028 < baseStart_5564028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564092 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_5564092 : Nat := 118140960795 + 5564092 * 2 ^ 59
def prefixEnd_5564092 : Nat := 4983230072969 + 3 ^ 40 * 5564092 * 2
def baseEnd_5564092 : Nat := 2857053601836549698161213

theorem tailTrace_5564092 : CollatzResearch.WordTrace tailWord_5564092 prefixEnd_5564092 2857053601836549698161213 := by
  unfold tailWord_5564092
  simp only [CollatzResearch.WordTrace]
  refine ⟨101469553679126215051875265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135292738238834953402500353 101469553679126215051875265)
  ·
    refine ⟨76102165259344661288906449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101469553679126215051875265 76102165259344661288906449)
    ·
      refine ⟨57076623944508495966679837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76102165259344661288906449 57076623944508495966679837)
      ·
        refine ⟨21403733979190685987504939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57076623944508495966679837 21403733979190685987504939)
        ·
          refine ⟨32105600968786028981257409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21403733979190685987504939 32105600968786028981257409)
          ·
            refine ⟨24079200726589521735943057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32105600968786028981257409 24079200726589521735943057)
            ·
              refine ⟨18059400544942141301957293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24079200726589521735943057 18059400544942141301957293)
              ·
                refine ⟨6772275204353302988233985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18059400544942141301957293 6772275204353302988233985)
                ·
                  refine ⟨5079206403264977241175489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6772275204353302988233985 5079206403264977241175489)
                  ·
                    refine ⟨3809404802448732930881617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5079206403264977241175489 3809404802448732930881617)
                    ·
                      refine ⟨2857053601836549698161213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809404802448732930881617 2857053601836549698161213)
                      ·
                        rfl

theorem cell23_5564092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_5564092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564092 prefixEnd_5564092 := by exact prefixLift 5564092
  have htrace : WordTrace (prefixWord ++ tailWord_5564092) baseStart_5564092 baseEnd_5564092 := by
    simpa [prefixWord, tailWord_5564092, baseEnd_5564092] using wordTrace_append hprefix tailTrace_5564092
  have hstable : (prefixWord ++ tailWord_5564092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564092).length < 2 ^ (prefixWord ++ tailWord_5564092).sum := by decide
  have hdescent : baseEnd_5564092 < baseStart_5564092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564168 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_5564168 : Nat := 118140960795 + 5564168 * 2 ^ 59
def prefixEnd_5564168 : Nat := 4983230072969 + 3 ^ 40 * 5564168 * 2
def baseEnd_5564168 : Nat := 2857092626366291400810863

theorem tailTrace_5564168 : CollatzResearch.WordTrace tailWord_5564168 prefixEnd_5564168 2857092626366291400810863 := by
  unfold tailWord_5564168
  simp only [CollatzResearch.WordTrace]
  refine ⟨101470939652988547541758579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135294586203984730055678105 101470939652988547541758579)
  ·
    refine ⟨152206409479482821312637869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101470939652988547541758579 152206409479482821312637869)
    ·
      refine ⟨57077403554806057992239201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152206409479482821312637869 57077403554806057992239201)
      ·
        refine ⟨42808052666104543494179401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57077403554806057992239201 42808052666104543494179401)
        ·
          refine ⟨32106039499578407620634551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42808052666104543494179401 32106039499578407620634551)
          ·
            refine ⟨48159059249367611430951827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32106039499578407620634551 48159059249367611430951827)
            ·
              refine ⟨72238588874051417146427741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48159059249367611430951827 72238588874051417146427741)
              ·
                refine ⟨27089470827769281429910403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72238588874051417146427741 27089470827769281429910403)
                ·
                  refine ⟨40634206241653922144865605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27089470827769281429910403 40634206241653922144865605)
                  ·
                    refine ⟨7618913670310110402162301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40634206241653922144865605 7618913670310110402162301)
                    ·
                      refine ⟨2857092626366291400810863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7618913670310110402162301 2857092626366291400810863)
                      ·
                        rfl

theorem cell23_5564168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_5564168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564168 prefixEnd_5564168 := by exact prefixLift 5564168
  have htrace : WordTrace (prefixWord ++ tailWord_5564168) baseStart_5564168 baseEnd_5564168 := by
    simpa [prefixWord, tailWord_5564168, baseEnd_5564168] using wordTrace_append hprefix tailTrace_5564168
  have hstable : (prefixWord ++ tailWord_5564168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564168).length < 2 ^ (prefixWord ++ tailWord_5564168).sum := by decide
  have hdescent : baseEnd_5564168 < baseStart_5564168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564171 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 8]
def baseStart_5564171 : Nat := 118140960795 + 5564171 * 2 ^ 59
def prefixEnd_5564171 : Nat := 4983230072969 + 3 ^ 40 * 5564171 * 2
def baseEnd_5564171 : Nat := 317454907423139432119261

theorem tailTrace_5564171 : CollatzResearch.WordTrace tailWord_5564171 prefixEnd_5564171 317454907423139432119261 := by
  unfold tailWord_5564171
  simp only [CollatzResearch.WordTrace]
  refine ⟨202941988724966226595876367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135294659149977484397250911 202941988724966226595876367)
  ·
    refine ⟨304412983087449339893814551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202941988724966226595876367 304412983087449339893814551)
    ·
      refine ⟨456619474631174009840721827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304412983087449339893814551 456619474631174009840721827)
      ·
        refine ⟨684929211946761014761082741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456619474631174009840721827 684929211946761014761082741)
        ·
          refine ⟨64212113620008845133851507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 684929211946761014761082741 64212113620008845133851507)
          ·
            refine ⟨96318170430013267700777261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64212113620008845133851507 96318170430013267700777261)
            ·
              refine ⟨36119313911254975387791473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96318170430013267700777261 36119313911254975387791473)
              ·
                refine ⟨27089485433441231540843605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36119313911254975387791473 27089485433441231540843605)
                ·
                  refine ⟨317454907423139432119261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27089485433441231540843605 317454907423139432119261)
                  ·
                    rfl

theorem cell23_5564171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 8].length) (baseStart_5564171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564171 prefixEnd_5564171 := by exact prefixLift 5564171
  have htrace : WordTrace (prefixWord ++ tailWord_5564171) baseStart_5564171 baseEnd_5564171 := by
    simpa [prefixWord, tailWord_5564171, baseEnd_5564171] using wordTrace_append hprefix tailTrace_5564171
  have hstable : (prefixWord ++ tailWord_5564171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564171).length < 2 ^ (prefixWord ++ tailWord_5564171).sum := by decide
  have hdescent : baseEnd_5564171 < baseStart_5564171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564175 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 1, 4]
def baseStart_5564175 : Nat := 118140960795 + 5564175 * 2 ^ 59
def prefixEnd_5564175 : Nat := 4983230072969 + 3 ^ 40 * 5564175 * 2
def baseEnd_5564175 : Nat := 952365406910290957807777

theorem tailTrace_5564175 : CollatzResearch.WordTrace tailWord_5564175 prefixEnd_5564175 952365406910290957807777 := by
  unfold tailWord_5564175
  simp only [CollatzResearch.WordTrace]
  refine ⟨202942134616951735279021979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135294756411301156852681319 202942134616951735279021979)
  ·
    refine ⟨304413201925427602918532969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202942134616951735279021979 304413201925427602918532969)
    ·
      refine ⟨228309901444070702188899727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304413201925427602918532969 228309901444070702188899727)
      ·
        refine ⟨342464852166106053283349591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228309901444070702188899727 342464852166106053283349591)
        ·
          refine ⟨513697278249159079925024387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342464852166106053283349591 513697278249159079925024387)
          ·
            refine ⟨770545917373738619887536581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513697278249159079925024387 770545917373738619887536581)
            ·
              refine ⟨144477359507575991228913109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 770545917373738619887536581 144477359507575991228913109)
              ·
                refine ⟨3386188113458812294427651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144477359507575991228913109 3386188113458812294427651)
                ·
                  refine ⟨5079282170188218441641477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386188113458812294427651 5079282170188218441641477)
                  ·
                    refine ⟨952365406910290957807777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5079282170188218441641477 952365406910290957807777)
                    ·
                      rfl

theorem cell23_5564175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 4].length) (baseStart_5564175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564175 prefixEnd_5564175 := by exact prefixLift 5564175
  have htrace : WordTrace (prefixWord ++ tailWord_5564175) baseStart_5564175 baseEnd_5564175 := by
    simpa [prefixWord, tailWord_5564175, baseEnd_5564175] using wordTrace_append hprefix tailTrace_5564175
  have hstable : (prefixWord ++ tailWord_5564175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564175).length < 2 ^ (prefixWord ++ tailWord_5564175).sum := by decide
  have hdescent : baseEnd_5564175 < baseStart_5564175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564188 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 6]
def baseStart_5564188 : Nat := 118140960795 + 5564188 * 2 ^ 59
def prefixEnd_5564188 : Nat := 4983230072969 + 3 ^ 40 * 5564188 * 2
def baseEnd_5564188 : Nat := 317455877331042369173419

theorem tailTrace_5564188 : CollatzResearch.WordTrace tailWord_5564188 prefixEnd_5564188 317455877331042369173419 := by
  unfold tailWord_5564188
  simp only [CollatzResearch.WordTrace]
  refine ⟨101471304382952319249622609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135295072510603092332830145 101471304382952319249622609)
  ·
    refine ⟨76103478287214239437216957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101471304382952319249622609 76103478287214239437216957)
    ·
      refine ⟨28538804357705339788956359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76103478287214239437216957 28538804357705339788956359)
      ·
        refine ⟨42808206536558009683434539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28538804357705339788956359 42808206536558009683434539)
        ·
          refine ⟨64212309804837014525151809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42808206536558009683434539 64212309804837014525151809)
          ·
            refine ⟨48159232353627760893863857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64212309804837014525151809 48159232353627760893863857)
            ·
              refine ⟨36119424265220820670397893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48159232353627760893863857 36119424265220820670397893)
              ·
                refine ⟨6772392049728903875699605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36119424265220820670397893 6772392049728903875699605)
                ·
                  refine ⟨317455877331042369173419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6772392049728903875699605 317455877331042369173419)
                  ·
                    rfl

theorem cell23_5564188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_5564188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564188 prefixEnd_5564188 := by exact prefixLift 5564188
  have htrace : WordTrace (prefixWord ++ tailWord_5564188) baseStart_5564188 baseEnd_5564188 := by
    simpa [prefixWord, tailWord_5564188, baseEnd_5564188] using wordTrace_append hprefix tailTrace_5564188
  have hstable : (prefixWord ++ tailWord_5564188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564188).length < 2 ^ (prefixWord ++ tailWord_5564188).sum := by decide
  have hdescent : baseEnd_5564188 < baseStart_5564188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564242 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_5564242 : Nat := 118140960795 + 5564242 * 2 ^ 59
def prefixEnd_5564242 : Nat := 4983230072969 + 3 ^ 40 * 5564242 * 2
def baseEnd_5564242 : Nat := 2857130623934724111285523

theorem tailTrace_5564242 : CollatzResearch.WordTrace tailWord_5564242 prefixEnd_5564242 2857130623934724111285523 := by
  unfold tailWord_5564242
  simp only [CollatzResearch.WordTrace]
  refine ⟨50736144576927251430427745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135296385538472670481140653 50736144576927251430427745)
  ·
    refine ⟨38052108432695438572820809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50736144576927251430427745 38052108432695438572820809)
    ·
      refine ⟨28539081324521578929615607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38052108432695438572820809 28539081324521578929615607)
      ·
        refine ⟨42808621986782368394423411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28539081324521578929615607 42808621986782368394423411)
        ·
          refine ⟨64212932980173552591635117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42808621986782368394423411 64212932980173552591635117)
          ·
            refine ⟨24079849867565082221863169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64212932980173552591635117 24079849867565082221863169)
            ·
              refine ⟨18059887400673811666397377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24079849867565082221863169 18059887400673811666397377)
              ·
                refine ⟨13544915550505358749798033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18059887400673811666397377 13544915550505358749798033)
                ·
                  refine ⟨10158686662879019062348525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13544915550505358749798033 10158686662879019062348525)
                  ·
                    refine ⟨3809507498579632148380697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10158686662879019062348525 3809507498579632148380697)
                    ·
                      refine ⟨2857130623934724111285523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809507498579632148380697 2857130623934724111285523)
                      ·
                        rfl

theorem cell23_5564242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_5564242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564242 prefixEnd_5564242 := by exact prefixLift 5564242
  have htrace : WordTrace (prefixWord ++ tailWord_5564242) baseStart_5564242 baseEnd_5564242 := by
    simpa [prefixWord, tailWord_5564242, baseEnd_5564242] using wordTrace_append hprefix tailTrace_5564242
  have hstable : (prefixWord ++ tailWord_5564242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564242).length < 2 ^ (prefixWord ++ tailWord_5564242).sum := by decide
  have hdescent : baseEnd_5564242 < baseStart_5564242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564275 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 3]
def baseStart_5564275 : Nat := 118140960795 + 5564275 * 2 ^ 59
def prefixEnd_5564275 : Nat := 4983230072969 + 3 ^ 40 * 5564275 * 2
def baseEnd_5564275 : Nat := 2857147568796322482172871

theorem tailTrace_5564275 : CollatzResearch.WordTrace tailWord_5564275 prefixEnd_5564275 2857147568796322482172871 := by
  unfold tailWord_5564275
  simp only [CollatzResearch.WordTrace]
  refine ⟨202945781916589452357662279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135297187944392968238441519 202945781916589452357662279)
  ·
    refine ⟨304418672874884178536493419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202945781916589452357662279 304418672874884178536493419)
    ·
      refine ⟨456628009312326267804740129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304418672874884178536493419 456628009312326267804740129)
      ·
        refine ⟨342471006984244700853555097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456628009312326267804740129 342471006984244700853555097)
        ·
          refine ⟨256853255238183525640166323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342471006984244700853555097 256853255238183525640166323)
          ·
            refine ⟨385279882857275288460249485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256853255238183525640166323 385279882857275288460249485)
            ·
              refine ⟨144479956071478233172593557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385279882857275288460249485 144479956071478233172593557)
              ·
                refine ⟨6772497940850542179965323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144479956071478233172593557 6772497940850542179965323)
                ·
                  refine ⟨10158746911275813269947985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6772497940850542179965323 10158746911275813269947985)
                  ·
                    refine ⟨7619060183456859952460989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10158746911275813269947985 7619060183456859952460989)
                    ·
                      refine ⟨2857147568796322482172871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7619060183456859952460989 2857147568796322482172871)
                      ·
                        rfl

theorem cell23_5564275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_5564275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564275 prefixEnd_5564275 := by exact prefixLift 5564275
  have htrace : WordTrace (prefixWord ++ tailWord_5564275) baseStart_5564275 baseEnd_5564275 := by
    simpa [prefixWord, tailWord_5564275, baseEnd_5564275] using wordTrace_append hprefix tailTrace_5564275
  have hstable : (prefixWord ++ tailWord_5564275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564275).length < 2 ^ (prefixWord ++ tailWord_5564275).sum := by decide
  have hdescent : baseEnd_5564275 < baseStart_5564275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564286 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5564286 : Nat := 118140960795 + 5564286 * 2 ^ 59
def prefixEnd_5564286 : Nat := 4983230072969 + 3 ^ 40 * 5564286 * 2
def baseEnd_5564286 : Nat := 952384405694507313045107

theorem tailTrace_5564286 : CollatzResearch.WordTrace tailWord_5564286 prefixEnd_5564286 952384405694507313045107 := by
  unfold tailWord_5564286
  simp only [CollatzResearch.WordTrace]
  refine ⟨25368272889943700154539089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135297455413033067490875141 25368272889943700154539089)
  ·
    refine ⟨19026204667457775115904317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25368272889943700154539089 19026204667457775115904317)
    ·
      refine ⟨7134826750296665668464119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19026204667457775115904317 7134826750296665668464119)
      ·
        refine ⟨10702240125444998502696179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7134826750296665668464119 10702240125444998502696179)
        ·
          refine ⟨16053360188167497754044269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10702240125444998502696179 16053360188167497754044269)
          ·
            refine ⟨6020010070562811657766601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16053360188167497754044269 6020010070562811657766601)
            ·
              refine ⟨4515007552922108743324951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6020010070562811657766601 4515007552922108743324951)
              ·
                refine ⟨6772511329383163114987427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515007552922108743324951 6772511329383163114987427)
                ·
                  refine ⟨10158766994074744672481141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6772511329383163114987427 10158766994074744672481141)
                  ·
                    refine ⟨952384405694507313045107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10158766994074744672481141 952384405694507313045107)
                    ·
                      rfl

theorem cell23_5564286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5564286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564286 prefixEnd_5564286 := by exact prefixLift 5564286
  have htrace : WordTrace (prefixWord ++ tailWord_5564286) baseStart_5564286 baseEnd_5564286 := by
    simpa [prefixWord, tailWord_5564286, baseEnd_5564286] using wordTrace_append hprefix tailTrace_5564286
  have hstable : (prefixWord ++ tailWord_5564286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564286).length < 2 ^ (prefixWord ++ tailWord_5564286).sum := by decide
  have hdescent : baseEnd_5564286 < baseStart_5564286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564289 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5564289 : Nat := 118140960795 + 5564289 * 2 ^ 59
def prefixEnd_5564289 : Nat := 4983230072969 + 3 ^ 40 * 5564289 * 2
def baseEnd_5564289 : Nat := 2857154757525485427397807

theorem tailTrace_5564289 : CollatzResearch.WordTrace tailWord_5564289 prefixEnd_5564289 2857154757525485427397807 := by
  unfold tailWord_5564289
  simp only [CollatzResearch.WordTrace]
  refine ⟨202946292538538732748671921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135297528359025821832447947 202946292538538732748671921)
  ·
    refine ⟨152209719403904049561503941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202946292538538732748671921 152209719403904049561503941)
    ·
      refine ⟨28539322388232009292781989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152209719403904049561503941 28539322388232009292781989)
      ·
        refine ⟨5351122947793501742396623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28539322388232009292781989 5351122947793501742396623)
        ·
          refine ⟨8026684421690252613594935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351122947793501742396623 8026684421690252613594935)
          ·
            refine ⟨12040026632535378920392403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8026684421690252613594935 12040026632535378920392403)
            ·
              refine ⟨18060039948803068380588605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12040026632535378920392403 18060039948803068380588605)
              ·
                refine ⟨6772514980801150642720727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18060039948803068380588605 6772514980801150642720727)
                ·
                  refine ⟨10158772471201725964081091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6772514980801150642720727 10158772471201725964081091)
                  ·
                    refine ⟨15238158706802588946121637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10158772471201725964081091 15238158706802588946121637)
                    ·
                      refine ⟨2857154757525485427397807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15238158706802588946121637 2857154757525485427397807)
                      ·
                        rfl

theorem cell23_5564289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5564289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564289 prefixEnd_5564289 := by exact prefixLift 5564289
  have htrace : WordTrace (prefixWord ++ tailWord_5564289) baseStart_5564289 baseEnd_5564289 := by
    simpa [prefixWord, tailWord_5564289, baseEnd_5564289] using wordTrace_append hprefix tailTrace_5564289
  have hstable : (prefixWord ++ tailWord_5564289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564289).length < 2 ^ (prefixWord ++ tailWord_5564289).sum := by decide
  have hdescent : baseEnd_5564289 < baseStart_5564289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564306 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5564306 : Nat := 118140960795 + 5564306 * 2 ^ 59
def prefixEnd_5564306 : Nat := 4983230072969 + 3 ^ 40 * 5564306 * 2
def baseEnd_5564306 : Nat := 2857163486696611860885229

theorem tailTrace_5564306 : CollatzResearch.WordTrace tailWord_5564306 prefixEnd_5564306 2857163486696611860885229 := by
  unfold tailWord_5564306
  simp only [CollatzResearch.WordTrace]
  refine ⟨50736728144869286163010193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135297941719651429768027181 50736728144869286163010193)
  ·
    refine ⟨38052546108651964622257645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50736728144869286163010193 38052546108651964622257645)
    ·
      refine ⟨14269704790744486733346617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38052546108651964622257645 14269704790744486733346617)
      ·
        refine ⟨10702278593058365050009963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14269704790744486733346617 10702278593058365050009963)
        ·
          refine ⟨16053417889587547575014945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10702278593058365050009963 16053417889587547575014945)
          ·
            refine ⟨12040063417190660681261209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16053417889587547575014945 12040063417190660681261209)
            ·
              refine ⟨9030047562892995510945907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12040063417190660681261209 9030047562892995510945907)
              ·
                refine ⟨13545071344339493266418861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030047562892995510945907 13545071344339493266418861)
                ·
                  refine ⟨5079401754127309974907073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13545071344339493266418861 5079401754127309974907073)
                  ·
                    refine ⟨3809551315595482481180305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5079401754127309974907073 3809551315595482481180305)
                    ·
                      refine ⟨2857163486696611860885229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809551315595482481180305 2857163486696611860885229)
                      ·
                        rfl

theorem cell23_5564306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5564306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564306 prefixEnd_5564306 := by exact prefixLift 5564306
  have htrace : WordTrace (prefixWord ++ tailWord_5564306) baseStart_5564306 baseEnd_5564306 := by
    simpa [prefixWord, tailWord_5564306, baseEnd_5564306] using wordTrace_append hprefix tailTrace_5564306
  have hstable : (prefixWord ++ tailWord_5564306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564306).length < 2 ^ (prefixWord ++ tailWord_5564306).sum := by decide
  have hdescent : baseEnd_5564306 < baseStart_5564306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564319 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5564319 : Nat := 118140960795 + 5564319 * 2 ^ 59
def prefixEnd_5564319 : Nat := 4983230072969 + 3 ^ 40 * 5564319 * 2
def baseEnd_5564319 : Nat := 2857170161945120310022669

theorem tailTrace_5564319 : CollatzResearch.WordTrace tailWord_5564319 prefixEnd_5564319 2857170161945120310022669 := by
  unfold tailWord_5564319
  simp only [CollatzResearch.WordTrace]
  refine ⟨202947386728430047872264011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135298257818953365248176007 202947386728430047872264011)
  ·
    refine ⟨304421080092645071808396017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202947386728430047872264011 304421080092645071808396017)
    ·
      refine ⟨228315810069483803856297013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304421080092645071808396017 228315810069483803856297013)
      ·
        refine ⟨21404607194014106611527845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228315810069483803856297013 21404607194014106611527845)
        ·
          refine ⟨4013363848877644989661471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21404607194014106611527845 4013363848877644989661471)
          ·
            refine ⟨6020045773316467484492207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013363848877644989661471 6020045773316467484492207)
            ·
              refine ⟨9030068659974701226738311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020045773316467484492207 9030068659974701226738311)
              ·
                refine ⟨13545102989962051840107467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030068659974701226738311 13545102989962051840107467)
                ·
                  refine ⟨20317654484943077760161201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13545102989962051840107467 20317654484943077760161201)
                  ·
                    refine ⟨15238240863707308320120901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20317654484943077760161201 15238240863707308320120901)
                    ·
                      refine ⟨2857170161945120310022669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15238240863707308320120901 2857170161945120310022669)
                      ·
                        rfl

theorem cell23_5564319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5564319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564319 prefixEnd_5564319 := by exact prefixLift 5564319
  have htrace : WordTrace (prefixWord ++ tailWord_5564319) baseStart_5564319 baseEnd_5564319 := by
    simpa [prefixWord, tailWord_5564319, baseEnd_5564319] using wordTrace_append hprefix tailTrace_5564319
  have hstable : (prefixWord ++ tailWord_5564319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564319).length < 2 ^ (prefixWord ++ tailWord_5564319).sum := by decide
  have hdescent : baseEnd_5564319 < baseStart_5564319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564338 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_5564338 : Nat := 118140960795 + 5564338 * 2 ^ 59
def prefixEnd_5564338 : Nat := 4983230072969 + 3 ^ 40 * 5564338 * 2
def baseEnd_5564338 : Nat := 952393306025851911895027

theorem tailTrace_5564338 : CollatzResearch.WordTrace tailWord_5564338 prefixEnd_5564338 952393306025851911895027 := by
  unfold tailWord_5564338
  simp only [CollatzResearch.WordTrace]
  refine ⟨50737019928840303529301417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135298719810240809411470445 50737019928840303529301417)
  ·
    refine ⟨38052764946630227646976063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50737019928840303529301417 38052764946630227646976063)
    ·
      refine ⟨57079147419945341470464095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38052764946630227646976063 57079147419945341470464095)
      ·
        refine ⟨85618721129918012205696143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57079147419945341470464095 85618721129918012205696143)
        ·
          refine ⟨128428081694877018308544215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85618721129918012205696143 128428081694877018308544215)
          ·
            refine ⟨192642122542315527462816323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128428081694877018308544215 192642122542315527462816323)
            ·
              refine ⟨288963183813473291194224485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192642122542315527462816323 288963183813473291194224485)
              ·
                refine ⟨54180596965026242098917091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288963183813473291194224485 54180596965026242098917091)
                ·
                  refine ⟨81270895447539363148375637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54180596965026242098917091 81270895447539363148375637)
                  ·
                    refine ⟨952393306025851911895027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81270895447539363148375637 952393306025851911895027)
                    ·
                      rfl

theorem cell23_5564338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_5564338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564338 prefixEnd_5564338 := by exact prefixLift 5564338
  have htrace : WordTrace (prefixWord ++ tailWord_5564338) baseStart_5564338 baseEnd_5564338 := by
    simpa [prefixWord, tailWord_5564338, baseEnd_5564338] using wordTrace_append hprefix tailTrace_5564338
  have hstable : (prefixWord ++ tailWord_5564338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564338).length < 2 ^ (prefixWord ++ tailWord_5564338).sum := by decide
  have hdescent : baseEnd_5564338 < baseStart_5564338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564349 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_5564349 : Nat := 118140960795 + 5564349 * 2 ^ 59
def prefixEnd_5564349 : Nat := 4983230072969 + 3 ^ 40 * 5564349 * 2
def baseEnd_5564349 : Nat := 2857185566364755192647531

theorem tailTrace_5564349 : CollatzResearch.WordTrace tailWord_5564349 prefixEnd_5564349 2857185566364755192647531 := by
  unfold tailWord_5564349
  simp only [CollatzResearch.WordTrace]
  refine ⟨202948480918321362995856101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135298987278880908663904067 202948480918321362995856101)
  ·
    refine ⟨38052840172185255561723019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202948480918321362995856101 38052840172185255561723019)
    ·
      refine ⟨57079260258277883342584529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38052840172185255561723019 57079260258277883342584529)
      ·
        refine ⟨42809445193708412506938397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57079260258277883342584529 42809445193708412506938397)
        ·
          refine ⟨16053541947640654690101899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42809445193708412506938397 16053541947640654690101899)
          ·
            refine ⟨24080312921460982035152849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16053541947640654690101899 24080312921460982035152849)
            ·
              refine ⟨18060234691095736526364637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24080312921460982035152849 18060234691095736526364637)
              ·
                refine ⟨6772588009160901197386739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18060234691095736526364637 6772588009160901197386739)
                ·
                  refine ⟨10158882013741351796080109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6772588009160901197386739 10158882013741351796080109)
                  ·
                    refine ⟨3809580755153006923530041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10158882013741351796080109 3809580755153006923530041)
                    ·
                      refine ⟨2857185566364755192647531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809580755153006923530041 2857185566364755192647531)
                      ·
                        rfl

theorem cell23_5564349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_5564349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564349 prefixEnd_5564349 := by exact prefixLift 5564349
  have htrace : WordTrace (prefixWord ++ tailWord_5564349) baseStart_5564349 baseEnd_5564349 := by
    simpa [prefixWord, tailWord_5564349, baseEnd_5564349] using wordTrace_append hprefix tailTrace_5564349
  have hstable : (prefixWord ++ tailWord_5564349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564349).length < 2 ^ (prefixWord ++ tailWord_5564349).sum := by decide
  have hdescent : baseEnd_5564349 < baseStart_5564349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564435 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 4]
def baseStart_5564435 : Nat := 118140960795 + 5564435 * 2 ^ 59
def prefixEnd_5564435 : Nat := 4983230072969 + 3 ^ 40 * 5564435 * 2
def baseEnd_5564435 : Nat := 2857229725701041856172135

theorem tailTrace_5564435 : CollatzResearch.WordTrace tailWord_5564435 prefixEnd_5564435 2857229725701041856172135 := by
  unfold tailWord_5564435
  simp only [CollatzResearch.WordTrace]
  refine ⟨202951617596009799683486759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135301078397339866455657839 202951617596009799683486759)
  ·
    refine ⟨304427426394014699525230139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202951617596009799683486759 304427426394014699525230139)
    ·
      refine ⟨456641139591022049287845209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304427426394014699525230139 456641139591022049287845209)
      ·
        refine ⟨342480854693266536965883907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456641139591022049287845209 342480854693266536965883907)
        ·
          refine ⟨513721282039899805448825861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342480854693266536965883907 513721282039899805448825861)
          ·
            refine ⟨96322740382481213521654849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 513721282039899805448825861 96322740382481213521654849)
            ·
              refine ⟨72242055286860910141241137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96322740382481213521654849 72242055286860910141241137)
              ·
                refine ⟨54181541465145682605930853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72242055286860910141241137 54181541465145682605930853)
                ·
                  refine ⟨10159039024714815488612035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54181541465145682605930853 10159039024714815488612035)
                  ·
                    refine ⟨15238558537072223232918053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10159039024714815488612035 15238558537072223232918053)
                    ·
                      refine ⟨2857229725701041856172135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15238558537072223232918053 2857229725701041856172135)
                      ·
                        rfl

theorem cell23_5564435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_5564435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564435 prefixEnd_5564435 := by exact prefixLift 5564435
  have htrace : WordTrace (prefixWord ++ tailWord_5564435) baseStart_5564435 baseEnd_5564435 := by
    simpa [prefixWord, tailWord_5564435, baseEnd_5564435] using wordTrace_append hprefix tailTrace_5564435
  have hstable : (prefixWord ++ tailWord_5564435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564435).length < 2 ^ (prefixWord ++ tailWord_5564435).sum := by decide
  have hdescent : baseEnd_5564435 < baseStart_5564435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564449 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 2, 5]
def baseStart_5564449 : Nat := 118140960795 + 5564449 * 2 ^ 59
def prefixEnd_5564449 : Nat := 4983230072969 + 3 ^ 40 * 5564449 * 2
def baseEnd_5564449 : Nat := 952412304810068267132357

theorem tailTrace_5564449 : CollatzResearch.WordTrace tailWord_5564449 prefixEnd_5564449 952412304810068267132357 := by
  unfold tailWord_5564449
  simp only [CollatzResearch.WordTrace]
  refine ⟨202952128217959080074496401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135301418811972720049664267 202952128217959080074496401)
  ·
    refine ⟨152214096163469310055872301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202952128217959080074496401 152214096163469310055872301)
    ·
      refine ⟨57080286061300991270952113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152214096163469310055872301 57080286061300991270952113)
      ·
        refine ⟨42810214545975743453214085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57080286061300991270952113 42810214545975743453214085)
        ·
          refine ⟨8026915227370451897477641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42810214545975743453214085 8026915227370451897477641)
          ·
            refine ⟨6020186420527838923108231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8026915227370451897477641 6020186420527838923108231)
            ·
              refine ⟨9030279630791758384662347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020186420527838923108231 9030279630791758384662347)
              ·
                refine ⟨13545419446187637576993521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030279630791758384662347 13545419446187637576993521)
                ·
                  refine ⟨10159064584640728182745141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13545419446187637576993521 10159064584640728182745141)
                  ·
                    refine ⟨952412304810068267132357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10159064584640728182745141 952412304810068267132357)
                    ·
                      rfl

theorem cell23_5564449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_5564449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564449 prefixEnd_5564449 := by exact prefixLift 5564449
  have htrace : WordTrace (prefixWord ++ tailWord_5564449) baseStart_5564449 baseEnd_5564449 := by
    simpa [prefixWord, tailWord_5564449, baseEnd_5564449] using wordTrace_append hprefix tailTrace_5564449
  have hstable : (prefixWord ++ tailWord_5564449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564449).length < 2 ^ (prefixWord ++ tailWord_5564449).sum := by decide
  have hdescent : baseEnd_5564449 < baseStart_5564449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564465 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_5564465 : Nat := 118140960795 + 5564465 * 2 ^ 59
def prefixEnd_5564465 : Nat := 4983230072969 + 3 ^ 40 * 5564465 * 2
def baseEnd_5564465 : Nat := 2857245130120676738796997

theorem tailTrace_5564465 : CollatzResearch.WordTrace tailWord_5564465 prefixEnd_5564465 2857245130120676738796997 := by
  unfold tailWord_5564465
  simp only [CollatzResearch.WordTrace]
  refine ⟨202952711785901114807078849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135301807857267409871385899 202952711785901114807078849)
  ·
    refine ⟨152214533839425836105309137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202952711785901114807078849 152214533839425836105309137)
    ·
      refine ⟨114160900379569377078981853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152214533839425836105309137 114160900379569377078981853)
      ·
        refine ⟨42810337642338516404618195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114160900379569377078981853 42810337642338516404618195)
        ·
          refine ⟨64215506463507774606927293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42810337642338516404618195 64215506463507774606927293)
          ·
            refine ⟨24080814923815415477597735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64215506463507774606927293 24080814923815415477597735)
            ·
              refine ⟨36121222385723123216396603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24080814923815415477597735 36121222385723123216396603)
              ·
                refine ⟨54181833578584684824594905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36121222385723123216396603 54181833578584684824594905)
                ·
                  refine ⟨40636375183938513618446179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54181833578584684824594905 40636375183938513618446179)
                  ·
                    refine ⟨60954562775907770427669269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40636375183938513618446179 60954562775907770427669269)
                    ·
                      refine ⟨2857245130120676738796997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60954562775907770427669269 2857245130120676738796997)
                      ·
                        rfl

theorem cell23_5564465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_5564465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564465 prefixEnd_5564465 := by exact prefixLift 5564465
  have htrace : WordTrace (prefixWord ++ tailWord_5564465) baseStart_5564465 baseEnd_5564465 := by
    simpa [prefixWord, tailWord_5564465, baseEnd_5564465] using wordTrace_append hprefix tailTrace_5564465
  have hstable : (prefixWord ++ tailWord_5564465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564465).length < 2 ^ (prefixWord ++ tailWord_5564465).sum := by decide
  have hdescent : baseEnd_5564465 < baseStart_5564465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564479 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 1, 4]
def baseStart_5564479 : Nat := 118140960795 + 5564479 * 2 ^ 59
def prefixEnd_5564479 : Nat := 4983230072969 + 3 ^ 40 * 5564479 * 2
def baseEnd_5564479 : Nat := 952417439616613228007311

theorem tailTrace_5564479 : CollatzResearch.WordTrace tailWord_5564479 prefixEnd_5564479 952417439616613228007311 := by
  unfold tailWord_5564479
  simp only [CollatzResearch.WordTrace]
  refine ⟨202953222407850395198088491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135302148271900263465392327 202953222407850395198088491)
  ·
    refine ⟨304429833611775592797132737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202953222407850395198088491 304429833611775592797132737)
    ·
      refine ⟨228322375208831694597849553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304429833611775592797132737 228322375208831694597849553)
      ·
        refine ⟨171241781406623770948387165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228322375208831694597849553 171241781406623770948387165)
        ·
          refine ⟨64215668027483914105645187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171241781406623770948387165 64215668027483914105645187)
          ·
            refine ⟨96323502041225871158467781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64215668027483914105645187 96323502041225871158467781)
            ·
              refine ⟨18060656632729850842212709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96323502041225871158467781 18060656632729850842212709)
              ·
                refine ⟨3386373118636847032914883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18060656632729850842212709 3386373118636847032914883)
                ·
                  refine ⟨5079559677955270549372325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386373118636847032914883 5079559677955270549372325)
                  ·
                    refine ⟨952417439616613228007311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5079559677955270549372325 952417439616613228007311)
                    ·
                      rfl

theorem cell23_5564479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 4].length) (baseStart_5564479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564479 prefixEnd_5564479 := by exact prefixLift 5564479
  have htrace : WordTrace (prefixWord ++ tailWord_5564479) baseStart_5564479 baseEnd_5564479 := by
    simpa [prefixWord, tailWord_5564479, baseEnd_5564479] using wordTrace_append hprefix tailTrace_5564479
  have hstable : (prefixWord ++ tailWord_5564479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564479).length < 2 ^ (prefixWord ++ tailWord_5564479).sum := by decide
  have hdescent : baseEnd_5564479 < baseStart_5564479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564486 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5564486 : Nat := 118140960795 + 5564486 * 2 ^ 59
def prefixEnd_5564486 : Nat := 4983230072969 + 3 ^ 40 * 5564486 * 2
def baseEnd_5564486 : Nat := 2857255913214421156634401

theorem tailTrace_5564486 : CollatzResearch.WordTrace tailWord_5564486 prefixEnd_5564486 2857255913214421156634401 := by
  unfold tailWord_5564486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342296178713282356049791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135302318479216690262395541 6342296178713282356049791)
  ·
    refine ⟨9513444268069923534074687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6342296178713282356049791 9513444268069923534074687)
    ·
      refine ⟨14270166402104885301112031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9513444268069923534074687 14270166402104885301112031)
      ·
        refine ⟨21405249603157327951668047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14270166402104885301112031 21405249603157327951668047)
        ·
          refine ⟨32107874404735991927502071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21405249603157327951668047 32107874404735991927502071)
          ·
            refine ⟨48161811607103987891253107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32107874404735991927502071 48161811607103987891253107)
            ·
              refine ⟨72242717410655981836879661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48161811607103987891253107 72242717410655981836879661)
              ·
                refine ⟨27091019028995993188829873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72242717410655981836879661 27091019028995993188829873)
                ·
                  refine ⟨20318264271746994891622405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27091019028995993188829873 20318264271746994891622405)
                  ·
                    refine ⟨3809674550952561542179201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20318264271746994891622405 3809674550952561542179201)
                    ·
                      refine ⟨2857255913214421156634401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809674550952561542179201 2857255913214421156634401)
                      ·
                        rfl

theorem cell23_5564486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5564486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564486 prefixEnd_5564486 := by exact prefixLift 5564486
  have htrace : WordTrace (prefixWord ++ tailWord_5564486) baseStart_5564486 baseEnd_5564486 := by
    simpa [prefixWord, tailWord_5564486, baseEnd_5564486] using wordTrace_append hprefix tailTrace_5564486
  have hstable : (prefixWord ++ tailWord_5564486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564486).length < 2 ^ (prefixWord ++ tailWord_5564486).sum := by decide
  have hdescent : baseEnd_5564486 < baseStart_5564486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564529 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 2, 3, 2]
def baseStart_5564529 : Nat := 118140960795 + 5564529 * 2 ^ 59
def prefixEnd_5564529 : Nat := 4983230072969 + 3 ^ 40 * 5564529 * 2
def baseEnd_5564529 : Nat := 2857277992882564488396703

theorem tailTrace_5564529 : CollatzResearch.WordTrace tailWord_5564529 prefixEnd_5564529 2857277992882564488396703 := by
  unfold tailWord_5564529
  simp only [CollatzResearch.WordTrace]
  refine ⟨202955046057669253737408641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135303364038446169158272427 202955046057669253737408641)
  ·
    refine ⟨152216284543251940303056481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202955046057669253737408641 152216284543251940303056481)
    ·
      refine ⟨114162213407438955227292361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152216284543251940303056481 114162213407438955227292361)
      ·
        refine ⟨85621660055579216420469271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114162213407438955227292361 85621660055579216420469271)
        ·
          refine ⟨128432490083368824630703907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85621660055579216420469271 128432490083368824630703907)
          ·
            refine ⟨192648735125053236946055861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128432490083368824630703907 192648735125053236946055861)
            ·
              refine ⟨18060818917973740963692737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192648735125053236946055861 18060818917973740963692737)
              ·
                refine ⟨13545614188480305722769553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18060818917973740963692737 13545614188480305722769553)
                ·
                  refine ⟨10159210641360229292077165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13545614188480305722769553 10159210641360229292077165)
                  ·
                    refine ⟨3809703990510085984528937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10159210641360229292077165 3809703990510085984528937)
                    ·
                      refine ⟨2857277992882564488396703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809703990510085984528937 2857277992882564488396703)
                      ·
                        rfl

theorem cell23_5564529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_5564529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564529 prefixEnd_5564529 := by exact prefixLift 5564529
  have htrace : WordTrace (prefixWord ++ tailWord_5564529) baseStart_5564529 baseEnd_5564529 := by
    simpa [prefixWord, tailWord_5564529, baseEnd_5564529] using wordTrace_append hprefix tailTrace_5564529
  have hstable : (prefixWord ++ tailWord_5564529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564529).length < 2 ^ (prefixWord ++ tailWord_5564529).sum := by decide
  have hdescent : baseEnd_5564529 < baseStart_5564529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564565 : List Nat := [1, 3, 2, 1, 1, 1, 3, 11]
def baseStart_5564565 : Nat := 118140960795 + 5564565 * 2 ^ 59
def prefixEnd_5564565 : Nat := 4983230072969 + 3 ^ 40 * 5564565 * 2
def baseEnd_5564565 : Nat := 105825795488375049909131

theorem tailTrace_5564565 : CollatzResearch.WordTrace tailWord_5564565 prefixEnd_5564565 105825795488375049909131 := by
  unfold tailWord_5564565
  simp only [CollatzResearch.WordTrace]
  refine ⟨202956359085538831885719149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135304239390359221257146099 202956359085538831885719149)
  ·
    refine ⟨76108634657077061957144681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202956359085538831885719149 76108634657077061957144681)
    ·
      refine ⟨57081475992807796467858511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76108634657077061957144681 57081475992807796467858511)
      ·
        refine ⟨85622213989211694701787767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57081475992807796467858511 85622213989211694701787767)
        ·
          refine ⟨128433320983817542052681651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85622213989211694701787767 128433320983817542052681651)
          ·
            refine ⟨192649981475726313079022477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128433320983817542052681651 192649981475726313079022477)
            ·
              refine ⟨72243743053397367404633429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192649981475726313079022477 72243743053397367404633429)
              ·
                refine ⟨105825795488375049909131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 72243743053397367404633429 105825795488375049909131)
                ·
                  rfl

theorem cell23_5564565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 11].length) (baseStart_5564565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564565 prefixEnd_5564565 := by exact prefixLift 5564565
  have htrace : WordTrace (prefixWord ++ tailWord_5564565) baseStart_5564565 baseEnd_5564565 := by
    simpa [prefixWord, tailWord_5564565, baseEnd_5564565] using wordTrace_append hprefix tailTrace_5564565
  have hstable : (prefixWord ++ tailWord_5564565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564565).length < 2 ^ (prefixWord ++ tailWord_5564565).sum := by decide
  have hdescent : baseEnd_5564565 < baseStart_5564565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564576 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 1, 1, 4]
def baseStart_5564576 : Nat := 118140960795 + 5564576 * 2 ^ 59
def prefixEnd_5564576 : Nat := 4983230072969 + 3 ^ 40 * 5564576 * 2
def baseEnd_5564576 : Nat := 2857302126473325804508987

theorem tailTrace_5564576 : CollatzResearch.WordTrace tailWord_5564576 prefixEnd_5564576 2857302126473325804508987 := by
  unfold tailWord_5564576
  simp only [CollatzResearch.WordTrace]
  refine ⟨101478380144249490382184791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135304506858999320509579721 101478380144249490382184791)
  ·
    refine ⟨152217570216374235573277187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101478380144249490382184791 152217570216374235573277187)
    ·
      refine ⟨228326355324561353359915781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152217570216374235573277187 228326355324561353359915781)
      ·
        refine ⟨42811191623355253754984209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228326355324561353359915781 42811191623355253754984209)
        ·
          refine ⟨32108393717516440316238157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42811191623355253754984209 32108393717516440316238157)
          ·
            refine ⟨12040647644068665118589309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32108393717516440316238157 12040647644068665118589309)
            ·
              refine ⟨4515242866525749419470991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12040647644068665118589309 4515242866525749419470991)
              ·
                refine ⟨6772864299788624129206487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515242866525749419470991 6772864299788624129206487)
                ·
                  refine ⟨10159296449682936193809731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6772864299788624129206487 10159296449682936193809731)
                  ·
                    refine ⟨15238944674524404290714597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10159296449682936193809731 15238944674524404290714597)
                    ·
                      refine ⟨2857302126473325804508987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15238944674524404290714597 2857302126473325804508987)
                      ·
                        rfl

theorem cell23_5564576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_5564576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564576 prefixEnd_5564576 := by exact prefixLift 5564576
  have htrace : WordTrace (prefixWord ++ tailWord_5564576) baseStart_5564576 baseEnd_5564576 := by
    simpa [prefixWord, tailWord_5564576, baseEnd_5564576] using wordTrace_append hprefix tailTrace_5564576
  have hstable : (prefixWord ++ tailWord_5564576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564576).length < 2 ^ (prefixWord ++ tailWord_5564576).sum := by decide
  have hdescent : baseEnd_5564576 < baseStart_5564576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564606 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_5564606 : Nat := 118140960795 + 5564606 * 2 ^ 59
def prefixEnd_5564606 : Nat := 4983230072969 + 3 ^ 40 * 5564606 * 2
def baseEnd_5564606 : Nat := 2857317530892960687133849

theorem tailTrace_5564606 : CollatzResearch.WordTrace tailWord_5564606 prefixEnd_5564606 2857317530892960687133849 := by
  unfold tailWord_5564606
  simp only [CollatzResearch.WordTrace]
  refine ⟨25369731809798786985995209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135305236318926863925307781 25369731809798786985995209)
  ·
    refine ⟨19027298857349090239496407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25369731809798786985995209 19027298857349090239496407)
    ·
      refine ⟨28540948286023635359244611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19027298857349090239496407 28540948286023635359244611)
      ·
        refine ⟨42811422429035453038866917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28540948286023635359244611 42811422429035453038866917)
        ·
          refine ⟨8027141705444147444787547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42811422429035453038866917 8027141705444147444787547)
          ·
            refine ⟨12040712558166221167181321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027141705444147444787547 12040712558166221167181321)
            ·
              refine ⟨9030534418624665875385991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12040712558166221167181321 9030534418624665875385991)
              ·
                refine ⟨13545801627936998813078987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030534418624665875385991 13545801627936998813078987)
                ·
                  refine ⟨20318702441905498219618481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13545801627936998813078987 20318702441905498219618481)
                  ·
                    refine ⟨15239026831429123664713861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20318702441905498219618481 15239026831429123664713861)
                    ·
                      refine ⟨2857317530892960687133849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15239026831429123664713861 2857317530892960687133849)
                      ·
                        rfl

theorem cell23_5564606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_5564606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564606 prefixEnd_5564606 := by exact prefixLift 5564606
  have htrace : WordTrace (prefixWord ++ tailWord_5564606) baseStart_5564606 baseEnd_5564606 := by
    simpa [prefixWord, tailWord_5564606, baseEnd_5564606] using wordTrace_append hprefix tailTrace_5564606
  have hstable : (prefixWord ++ tailWord_5564606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564606).length < 2 ^ (prefixWord ++ tailWord_5564606).sum := by decide
  have hdescent : baseEnd_5564606 < baseStart_5564606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564610 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5564610 : Nat := 118140960795 + 5564610 * 2 ^ 59
def prefixEnd_5564610 : Nat := 4983230072969 + 3 ^ 40 * 5564610 * 2
def baseEnd_5564610 : Nat := 2857319584815578671483831

theorem tailTrace_5564610 : CollatzResearch.WordTrace tailWord_5564610 prefixEnd_5564610 2857319584815578671483831 := by
  unfold tailWord_5564610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50739500092593951142776821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135305333580250536380738189 50739500092593951142776821)
  ·
    refine ⟨4756828133680682919635327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50739500092593951142776821 4756828133680682919635327)
    ·
      refine ⟨7135242200521024379452991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756828133680682919635327 7135242200521024379452991)
      ·
        refine ⟨10702863300781536569179487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135242200521024379452991 10702863300781536569179487)
        ·
          refine ⟨16054294951172304853769231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10702863300781536569179487 16054294951172304853769231)
          ·
            refine ⟨24081442426758457280653847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16054294951172304853769231 24081442426758457280653847)
            ·
              refine ⟨36122163640137685920980771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24081442426758457280653847 36122163640137685920980771)
              ·
                refine ⟨54183245460206528881471157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36122163640137685920980771 54183245460206528881471157)
                ·
                  refine ⟨5079679261894362082637921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54183245460206528881471157 5079679261894362082637921)
                  ·
                    refine ⟨3809759446420771561978441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5079679261894362082637921 3809759446420771561978441)
                    ·
                      refine ⟨2857319584815578671483831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809759446420771561978441 2857319584815578671483831)
                      ·
                        rfl

theorem cell23_5564610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5564610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564610 prefixEnd_5564610 := by exact prefixLift 5564610
  have htrace : WordTrace (prefixWord ++ tailWord_5564610) baseStart_5564610 baseEnd_5564610 := by
    simpa [prefixWord, tailWord_5564610, baseEnd_5564610] using wordTrace_append hprefix tailTrace_5564610
  have hstable : (prefixWord ++ tailWord_5564610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564610).length < 2 ^ (prefixWord ++ tailWord_5564610).sum := by decide
  have hdescent : baseEnd_5564610 < baseStart_5564610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564619 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 3, 3, 2]
def baseStart_5564619 : Nat := 118140960795 + 5564619 * 2 ^ 59
def prefixEnd_5564619 : Nat := 4983230072969 + 3 ^ 40 * 5564619 * 2
def baseEnd_5564619 : Nat := 2857324206141469136271289

theorem tailTrace_5564619 : CollatzResearch.WordTrace tailWord_5564619 prefixEnd_5564619 2857324206141469136271289 := by
  unfold tailWord_5564619
  simp only [CollatzResearch.WordTrace]
  refine ⟨202958328627343199108184911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135305552418228799405456607 202958328627343199108184911)
  ·
    refine ⟨304437492941014798662277367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202958328627343199108184911 304437492941014798662277367)
    ·
      refine ⟨456656239411522197993416051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304437492941014798662277367 456656239411522197993416051)
      ·
        refine ⟨684984359117283296990124077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456656239411522197993416051 684984359117283296990124077)
        ·
          refine ⟨256869134668981236371296529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684984359117283296990124077 256869134668981236371296529)
          ·
            refine ⟨192651851001735927278472397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256869134668981236371296529 192651851001735927278472397)
            ·
              refine ⟨72244444125650972729427149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192651851001735927278472397 72244444125650972729427149)
              ·
                refine ⟨27091666547119114773535181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72244444125650972729427149 27091666547119114773535181)
                ·
                  refine ⟨10159374955169668040075693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27091666547119114773535181 10159374955169668040075693)
                  ·
                    refine ⟨3809765608188625515028385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10159374955169668040075693 3809765608188625515028385)
                    ·
                      refine ⟨2857324206141469136271289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809765608188625515028385 2857324206141469136271289)
                      ·
                        rfl

theorem cell23_5564619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3, 2].length) (baseStart_5564619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564619 prefixEnd_5564619 := by exact prefixLift 5564619
  have htrace : WordTrace (prefixWord ++ tailWord_5564619) baseStart_5564619 baseEnd_5564619 := by
    simpa [prefixWord, tailWord_5564619, baseEnd_5564619] using wordTrace_append hprefix tailTrace_5564619
  have hstable : (prefixWord ++ tailWord_5564619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564619).length < 2 ^ (prefixWord ++ tailWord_5564619).sum := by decide
  have hdescent : baseEnd_5564619 < baseStart_5564619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564630 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5564630 : Nat := 118140960795 + 5564630 * 2 ^ 59
def prefixEnd_5564630 : Nat := 4983230072969 + 3 ^ 40 * 5564630 * 2
def baseEnd_5564630 : Nat := 2857329854428668593233739

theorem tailTrace_5564630 : CollatzResearch.WordTrace tailWord_5564630 prefixEnd_5564630 2857329854428668593233739 := by
  unfold tailWord_5564630
  simp only [CollatzResearch.WordTrace]
  refine ⟨12684920614393959249177209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135305819886868898657890229 12684920614393959249177209)
  ·
    refine ⟨9513690460795469436882907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12684920614393959249177209 9513690460795469436882907)
    ·
      refine ⟨14270535691193204155324361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9513690460795469436882907 14270535691193204155324361)
      ·
        refine ⟨10702901768394903116493271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14270535691193204155324361 10702901768394903116493271)
        ·
          refine ⟨16054352652592354674739907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10702901768394903116493271 16054352652592354674739907)
          ·
            refine ⟨24081528978888532012109861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16054352652592354674739907 24081528978888532012109861)
            ·
              refine ⟨4515286683541599752270599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24081528978888532012109861 4515286683541599752270599)
              ·
                refine ⟨6772930025312399628405899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515286683541599752270599 6772930025312399628405899)
                ·
                  refine ⟨10159395037968599442608849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6772930025312399628405899 10159395037968599442608849)
                  ·
                    refine ⟨7619546278476449581956637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10159395037968599442608849 7619546278476449581956637)
                    ·
                      refine ⟨2857329854428668593233739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7619546278476449581956637 2857329854428668593233739)
                      ·
                        rfl

theorem cell23_5564630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5564630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564630 prefixEnd_5564630 := by exact prefixLift 5564630
  have htrace : WordTrace (prefixWord ++ tailWord_5564630) baseStart_5564630 baseEnd_5564630 := by
    simpa [prefixWord, tailWord_5564630, baseEnd_5564630] using wordTrace_append hprefix tailTrace_5564630
  have hstable : (prefixWord ++ tailWord_5564630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564630).length < 2 ^ (prefixWord ++ tailWord_5564630).sum := by decide
  have hdescent : baseEnd_5564630 < baseStart_5564630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564643 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5564643 : Nat := 118140960795 + 5564643 * 2 ^ 59
def prefixEnd_5564643 : Nat := 4983230072969 + 3 ^ 40 * 5564643 * 2
def baseEnd_5564643 : Nat := 2857336529677177042371179

theorem tailTrace_5564643 : CollatzResearch.WordTrace tailWord_5564643 prefixEnd_5564643 2857336529677177042371179 := by
  unfold tailWord_5564643
  simp only [CollatzResearch.WordTrace]
  refine ⟨202959203979256251207058583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135306135986170834138039055 202959203979256251207058583)
  ·
    refine ⟨304438805968884376810587875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202959203979256251207058583 304438805968884376810587875)
    ·
      refine ⟨456658208953326565215881813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304438805968884376810587875 456658208953326565215881813)
      ·
        refine ⟨5351463386171795686123615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 456658208953326565215881813 5351463386171795686123615)
        ·
          refine ⟨8027195079257693529185423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351463386171795686123615 8027195079257693529185423)
          ·
            refine ⟨12040792618886540293778135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027195079257693529185423 12040792618886540293778135)
            ·
              refine ⟨18061188928329810440667203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12040792618886540293778135 18061188928329810440667203)
              ·
                refine ⟨27091783392494715661000805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18061188928329810440667203 27091783392494715661000805)
                ·
                  refine ⟨5079709386092759186437651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27091783392494715661000805 5079709386092759186437651)
                  ·
                    refine ⟨7619564079139138779656477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5079709386092759186437651 7619564079139138779656477)
                    ·
                      refine ⟨2857336529677177042371179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7619564079139138779656477 2857336529677177042371179)
                      ·
                        rfl

theorem cell23_5564643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5564643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564643 prefixEnd_5564643 := by exact prefixLift 5564643
  have htrace : WordTrace (prefixWord ++ tailWord_5564643) baseStart_5564643 baseEnd_5564643 := by
    simpa [prefixWord, tailWord_5564643, baseEnd_5564643] using wordTrace_append hprefix tailTrace_5564643
  have hstable : (prefixWord ++ tailWord_5564643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564643).length < 2 ^ (prefixWord ++ tailWord_5564643).sum := by decide
  have hdescent : baseEnd_5564643 < baseStart_5564643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564666 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2]
def baseStart_5564666 : Nat := 118140960795 + 5564666 * 2 ^ 59
def prefixEnd_5564666 : Nat := 4983230072969 + 3 ^ 40 * 5564666 * 2
def baseEnd_5564666 : Nat := 2857348339732230452383573

theorem tailTrace_5564666 : CollatzResearch.WordTrace tailWord_5564666 prefixEnd_5564666 2857348339732230452383573 := by
  unfold tailWord_5564666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50740010714543231533786463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135306695238781950756763901 50740010714543231533786463)
  ·
    refine ⟨76110016071814847300679695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50740010714543231533786463 76110016071814847300679695)
    ·
      refine ⟨114165024107722270951019543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76110016071814847300679695 114165024107722270951019543)
      ·
        refine ⟨171247536161583406426529315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114165024107722270951019543 171247536161583406426529315)
        ·
          refine ⟨256871304242375109639793973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171247536161583406426529315 256871304242375109639793973)
          ·
            refine ⟨24081684772722666528730685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256871304242375109639793973 24081684772722666528730685)
            ·
              refine ⟨9030631789770999948274007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24081684772722666528730685 9030631789770999948274007)
              ·
                refine ⟨13545947684656499922411011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030631789770999948274007 13545947684656499922411011)
                ·
                  refine ⟨20318921526984749883616517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13545947684656499922411011 20318921526984749883616517)
                  ·
                    refine ⟨3809797786309640603178097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20318921526984749883616517 3809797786309640603178097)
                    ·
                      refine ⟨2857348339732230452383573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809797786309640603178097 2857348339732230452383573)
                      ·
                        rfl

theorem cell23_5564666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_5564666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564666 prefixEnd_5564666 := by exact prefixLift 5564666
  have htrace : WordTrace (prefixWord ++ tailWord_5564666) baseStart_5564666 baseEnd_5564666 := by
    simpa [prefixWord, tailWord_5564666, baseEnd_5564666] using wordTrace_append hprefix tailTrace_5564666
  have hstable : (prefixWord ++ tailWord_5564666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564666).length < 2 ^ (prefixWord ++ tailWord_5564666).sum := by decide
  have hdescent : baseEnd_5564666 < baseStart_5564666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564672 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 7]
def baseStart_5564672 : Nat := 118140960795 + 5564672 * 2 ^ 59
def prefixEnd_5564672 : Nat := 4983230072969 + 3 ^ 40 * 5564672 * 2
def baseEnd_5564672 : Nat := 317483491179573047656505

theorem tailTrace_5564672 : CollatzResearch.WordTrace tailWord_5564672 prefixEnd_5564672 317483491179573047656505 := by
  unfold tailWord_5564672
  simp only [CollatzResearch.WordTrace]
  refine ⟨101480130848075594579932135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135306841130767459439909513 101480130848075594579932135)
  ·
    refine ⟨152220196272113391869898203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101480130848075594579932135 152220196272113391869898203)
    ·
      refine ⟨228330294408170087804847305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152220196272113391869898203 228330294408170087804847305)
      ·
        refine ⟨171247720806127565853635479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228330294408170087804847305 171247720806127565853635479)
        ·
          refine ⟨256871581209191348780453219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171247720806127565853635479 256871581209191348780453219)
          ·
            refine ⟨385307371813787023170679829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256871581209191348780453219 385307371813787023170679829)
            ·
              refine ⟨18061283053771266711125617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 385307371813787023170679829 18061283053771266711125617)
              ·
                refine ⟨13545962290328450033344213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18061283053771266711125617 13545962290328450033344213)
                ·
                  refine ⟨317483491179573047656505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13545962290328450033344213 317483491179573047656505)
                  ·
                    rfl

theorem cell23_5564672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_5564672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564672 prefixEnd_5564672 := by exact prefixLift 5564672
  have htrace : WordTrace (prefixWord ++ tailWord_5564672) baseStart_5564672 baseEnd_5564672 := by
    simpa [prefixWord, tailWord_5564672, baseEnd_5564672] using wordTrace_append hprefix tailTrace_5564672
  have hstable : (prefixWord ++ tailWord_5564672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564672).length < 2 ^ (prefixWord ++ tailWord_5564672).sum := by decide
  have hdescent : baseEnd_5564672 < baseStart_5564672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564706 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_5564706 : Nat := 118140960795 + 5564706 * 2 ^ 59
def prefixEnd_5564706 : Nat := 4983230072969 + 3 ^ 40 * 5564706 * 2
def baseEnd_5564706 : Nat := 317485430995378921764821

theorem tailTrace_5564706 : CollatzResearch.WordTrace tailWord_5564706 prefixEnd_5564706 317485430995378921764821 := by
  unfold tailWord_5564706
  simp only [CollatzResearch.WordTrace]
  refine ⟨50740375444507003241650493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135307667852018675311067981 50740375444507003241650493)
  ·
    refine ⟨19027640791690126215618935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50740375444507003241650493 19027640791690126215618935)
    ·
      refine ⟨28541461187535189323428403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19027640791690126215618935 28541461187535189323428403)
      ·
        refine ⟨42812191781302783985142605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28541461187535189323428403 42812191781302783985142605)
        ·
          refine ⟨16054571917988543994428477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42812191781302783985142605 16054571917988543994428477)
          ·
            refine ⟨6020464469245703997910679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16054571917988543994428477 6020464469245703997910679)
            ·
              refine ⟨9030696703868555996866019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020464469245703997910679 9030696703868555996866019)
              ·
                refine ⟨13546045055802833995299029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030696703868555996866019 13546045055802833995299029)
                ·
                  refine ⟨317485430995378921764821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13546045055802833995299029 317485430995378921764821)
                  ·
                    rfl

theorem cell23_5564706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_5564706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564706 prefixEnd_5564706 := by exact prefixLift 5564706
  have htrace : WordTrace (prefixWord ++ tailWord_5564706) baseStart_5564706 baseEnd_5564706 := by
    simpa [prefixWord, tailWord_5564706, baseEnd_5564706] using wordTrace_append hprefix tailTrace_5564706
  have hstable : (prefixWord ++ tailWord_5564706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564706).length < 2 ^ (prefixWord ++ tailWord_5564706).sum := by decide
  have hdescent : baseEnd_5564706 < baseStart_5564706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564711 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5564711 : Nat := 118140960795 + 5564711 * 2 ^ 59
def prefixEnd_5564711 : Nat := 4983230072969 + 3 ^ 40 * 5564711 * 2
def baseEnd_5564711 : Nat := 2857371446361682776320867

theorem tailTrace_5564711 : CollatzResearch.WordTrace tailWord_5564711 prefixEnd_5564711 2857371446361682776320867 := by
  unfold tailWord_5564711
  simp only [CollatzResearch.WordTrace]
  refine ⟨202961684143009898820533987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135307789428673265880355991 202961684143009898820533987)
  ·
    refine ⟨304442526214514848230800981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202961684143009898820533987 304442526214514848230800981)
    ·
      refine ⟨3567685854076345877704699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 304442526214514848230800981 3567685854076345877704699)
      ·
        refine ⟨5351528781114518816557049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567685854076345877704699 5351528781114518816557049)
        ·
          refine ⟨4013646585835889112417787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5351528781114518816557049 4013646585835889112417787)
          ·
            refine ⟨6020469878753833668626681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013646585835889112417787 6020469878753833668626681)
            ·
              refine ⟨4515352409065375251470011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6020469878753833668626681 4515352409065375251470011)
              ·
                refine ⟨6773028613598062877205017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515352409065375251470011 6773028613598062877205017)
                ·
                  refine ⟨5079771460198547157903763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773028613598062877205017 5079771460198547157903763)
                  ·
                    refine ⟨7619657190297820736855645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5079771460198547157903763 7619657190297820736855645)
                    ·
                      refine ⟨2857371446361682776320867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7619657190297820736855645 2857371446361682776320867)
                      ·
                        rfl

theorem cell23_5564711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5564711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564711 prefixEnd_5564711 := by exact prefixLift 5564711
  have htrace : WordTrace (prefixWord ++ tailWord_5564711) baseStart_5564711 baseEnd_5564711 := by
    simpa [prefixWord, tailWord_5564711, baseEnd_5564711] using wordTrace_append hprefix tailTrace_5564711
  have hstable : (prefixWord ++ tailWord_5564711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564711).length < 2 ^ (prefixWord ++ tailWord_5564711).sum := by decide
  have hdescent : baseEnd_5564711 < baseStart_5564711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564717 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5564717 : Nat := 118140960795 + 5564717 * 2 ^ 59
def prefixEnd_5564717 : Nat := 4983230072969 + 3 ^ 40 * 5564717 * 2
def baseEnd_5564717 : Nat := 2857374527245609752845839

theorem tailTrace_5564717 : CollatzResearch.WordTrace tailWord_5564717 prefixEnd_5564717 2857374527245609752845839 := by
  unfold tailWord_5564717
  simp only [CollatzResearch.WordTrace]
  refine ⟨202961902980988161845252405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135307935320658774563501603 202961902980988161845252405)
  ·
    refine ⟨19027678404467640172992413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202961902980988161845252405 19027678404467640172992413)
    ·
      refine ⟨7135379401675365064872155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19027678404467640172992413 7135379401675365064872155)
      ·
        refine ⟨10703069102513047597308233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135379401675365064872155 10703069102513047597308233)
        ·
          refine ⟨8027301826884785697981175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10703069102513047597308233 8027301826884785697981175)
          ·
            refine ⟨12040952740327178546971763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027301826884785697981175 12040952740327178546971763)
            ·
              refine ⟨18061429110490767820457645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12040952740327178546971763 18061429110490767820457645)
              ·
                refine ⟨6773035916434037932671617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18061429110490767820457645 6773035916434037932671617)
                ·
                  refine ⟨5079776937325528449503713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773035916434037932671617 5079776937325528449503713)
                  ·
                    refine ⟨3809832702994146337127785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5079776937325528449503713 3809832702994146337127785)
                    ·
                      refine ⟨2857374527245609752845839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3809832702994146337127785 2857374527245609752845839)
                      ·
                        rfl

theorem cell23_5564717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5564717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564717 prefixEnd_5564717 := by exact prefixLift 5564717
  have htrace : WordTrace (prefixWord ++ tailWord_5564717) baseStart_5564717 baseEnd_5564717 := by
    simpa [prefixWord, tailWord_5564717, baseEnd_5564717] using wordTrace_append hprefix tailTrace_5564717
  have hstable : (prefixWord ++ tailWord_5564717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564717).length < 2 ^ (prefixWord ++ tailWord_5564717).sum := by decide
  have hdescent : baseEnd_5564717 < baseStart_5564717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564739 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 4]
def baseStart_5564739 : Nat := 118140960795 + 5564739 * 2 ^ 59
def prefixEnd_5564739 : Nat := 4983230072969 + 3 ^ 40 * 5564739 * 2
def baseEnd_5564739 : Nat := 2857385823820008666770737

theorem tailTrace_5564739 : CollatzResearch.WordTrace tailWord_5564739 prefixEnd_5564739 2857385823820008666770737 := by
  unfold tailWord_5564739
  simp only [CollatzResearch.WordTrace]
  refine ⟨202962705386908459602553271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135308470257938973068368847 202962705386908459602553271)
  ·
    refine ⟨304444058080362689403829907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202962705386908459602553271 304444058080362689403829907)
    ·
      refine ⟨456666087120544034105744861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304444058080362689403829907 456666087120544034105744861)
      ·
        refine ⟨171249782670204012789654323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456666087120544034105744861 171249782670204012789654323)
        ·
          refine ⟨256874674005306019184481485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171249782670204012789654323 256874674005306019184481485)
          ·
            refine ⟨96328002751989757194180557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256874674005306019184481485 96328002751989757194180557)
            ·
              refine ⟨36123001031996158947817709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96328002751989757194180557 36123001031996158947817709)
              ·
                refine ⟨13546125386998559605431641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36123001031996158947817709 13546125386998559605431641)
                ·
                  refine ⟨10159594040248919704073731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13546125386998559605431641 10159594040248919704073731)
                  ·
                    refine ⟨15239391060373379556110597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10159594040248919704073731 15239391060373379556110597)
                    ·
                      refine ⟨2857385823820008666770737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15239391060373379556110597 2857385823820008666770737)
                      ·
                        rfl

theorem cell23_5564739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_5564739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564739 prefixEnd_5564739 := by exact prefixLift 5564739
  have htrace : WordTrace (prefixWord ++ tailWord_5564739) baseStart_5564739 baseEnd_5564739 := by
    simpa [prefixWord, tailWord_5564739, baseEnd_5564739] using wordTrace_append hprefix tailTrace_5564739
  have hstable : (prefixWord ++ tailWord_5564739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564739).length < 2 ^ (prefixWord ++ tailWord_5564739).sum := by decide
  have hdescent : baseEnd_5564739 < baseStart_5564739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564756 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_5564756 : Nat := 118140960795 + 5564756 * 2 ^ 59
def prefixEnd_5564756 : Nat := 4983230072969 + 3 ^ 40 * 5564756 * 2
def baseEnd_5564756 : Nat := 2857394552991135100258159

theorem tailTrace_5564756 : CollatzResearch.WordTrace tailWord_5564756 prefixEnd_5564756 2857394552991135100258159 := by
  unfold tailWord_5564756
  simp only [CollatzResearch.WordTrace]
  refine ⟨101481662713923435752961061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135308883618564581003948081 101481662713923435752961061)
  ·
    refine ⟨19027811758860644203680199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101481662713923435752961061 19027811758860644203680199)
    ·
      refine ⟨28541717638290966305520299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19027811758860644203680199 28541717638290966305520299)
      ·
        refine ⟨42812576457436449458280449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28541717638290966305520299 42812576457436449458280449)
        ·
          refine ⟨32109432343077337093710337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42812576457436449458280449 32109432343077337093710337)
          ·
            refine ⟨24082074257308002820282753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32109432343077337093710337 24082074257308002820282753)
            ·
              refine ⟨18061555692981002115212065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24082074257308002820282753 18061555692981002115212065)
              ·
                refine ⟨13546166769735751586409049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18061555692981002115212065 13546166769735751586409049)
                ·
                  refine ⟨10159625077301813689806787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13546166769735751586409049 10159625077301813689806787)
                  ·
                    refine ⟨15239437615952720534710181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10159625077301813689806787 15239437615952720534710181)
                    ·
                      refine ⟨2857394552991135100258159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15239437615952720534710181 2857394552991135100258159)
                      ·
                        rfl

theorem cell23_5564756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_5564756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564756 prefixEnd_5564756 := by exact prefixLift 5564756
  have htrace : WordTrace (prefixWord ++ tailWord_5564756) baseStart_5564756 baseEnd_5564756 := by
    simpa [prefixWord, tailWord_5564756, baseEnd_5564756] using wordTrace_append hprefix tailTrace_5564756
  have hstable : (prefixWord ++ tailWord_5564756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564756).length < 2 ^ (prefixWord ++ tailWord_5564756).sum := by decide
  have hdescent : baseEnd_5564756 < baseStart_5564756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564830 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_5564830 : Nat := 118140960795 + 5564830 * 2 ^ 59
def prefixEnd_5564830 : Nat := 4983230072969 + 3 ^ 40 * 5564830 * 2
def baseEnd_5564830 : Nat := 317492505617729756748091

theorem tailTrace_5564830 : CollatzResearch.WordTrace tailWord_5564830 prefixEnd_5564830 317492505617729756748091 := by
  unfold tailWord_5564830
  simp only [CollatzResearch.WordTrace]
  refine ⟨25370753053697347768014493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135310682953052521429410629 25370753053697347768014493)
  ·
    refine ⟨9514032395136505413005435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25370753053697347768014493 9514032395136505413005435)
    ·
      refine ⟨14271048592704758119508153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9514032395136505413005435 14271048592704758119508153)
      ·
        refine ⟨10703286444528568589631115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14271048592704758119508153 10703286444528568589631115)
        ·
          refine ⟨16054929666792852884446673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10703286444528568589631115 16054929666792852884446673)
          ·
            refine ⟨12041197250094639663335005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16054929666792852884446673 12041197250094639663335005)
            ·
              refine ⟨4515448968785489873750627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12041197250094639663335005 4515448968785489873750627)
              ·
                refine ⟨6773173453178234810625941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515448968785489873750627 6773173453178234810625941)
                ·
                  refine ⟨317492505617729756748091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6773173453178234810625941 317492505617729756748091)
                  ·
                    rfl

theorem cell23_5564830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_5564830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564830 prefixEnd_5564830 := by exact prefixLift 5564830
  have htrace : WordTrace (prefixWord ++ tailWord_5564830) baseStart_5564830 baseEnd_5564830 := by
    simpa [prefixWord, tailWord_5564830, baseEnd_5564830] using wordTrace_append hprefix tailTrace_5564830
  have hstable : (prefixWord ++ tailWord_5564830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564830).length < 2 ^ (prefixWord ++ tailWord_5564830).sum := by decide
  have hdescent : baseEnd_5564830 < baseStart_5564830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564840 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5564840 : Nat := 118140960795 + 5564840 * 2 ^ 59
def prefixEnd_5564840 : Nat := 4983230072969 + 3 ^ 40 * 5564840 * 2
def baseEnd_5564840 : Nat := 2857437685366112771607773

theorem tailTrace_5564840 : CollatzResearch.WordTrace tailWord_5564840 prefixEnd_5564840 2857437685366112771607773 := by
  unfold tailWord_5564840
  simp only [CollatzResearch.WordTrace]
  refine ⟨101483194579771276925989987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135310926106361702567986649 101483194579771276925989987)
  ·
    refine ⟨152224791869656915388984981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101483194579771276925989987 152224791869656915388984981)
    ·
      refine ⟨7135537118890167908858671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152224791869656915388984981 7135537118890167908858671)
      ·
        refine ⟨10703305678335251863288007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135537118890167908858671 10703305678335251863288007)
        ·
          refine ⟨16054958517502877794932011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10703305678335251863288007 16054958517502877794932011)
          ·
            refine ⟨24082437776254316692398017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16054958517502877794932011 24082437776254316692398017)
            ·
              refine ⟨18061828332190737519298513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24082437776254316692398017 18061828332190737519298513)
              ·
                refine ⟨13546371249143053139473885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18061828332190737519298513 13546371249143053139473885)
                ·
                  refine ⟨5079889218428644927302707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13546371249143053139473885 5079889218428644927302707)
                  ·
                    refine ⟨7619833827642967390954061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5079889218428644927302707 7619833827642967390954061)
                    ·
                      refine ⟨2857437685366112771607773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7619833827642967390954061 2857437685366112771607773)
                      ·
                        rfl

theorem cell23_5564840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5564840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564840 prefixEnd_5564840 := by exact prefixLift 5564840
  have htrace : WordTrace (prefixWord ++ tailWord_5564840) baseStart_5564840 baseEnd_5564840 := by
    simpa [prefixWord, tailWord_5564840, baseEnd_5564840] using wordTrace_append hprefix tailTrace_5564840
  have hstable : (prefixWord ++ tailWord_5564840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564840).length < 2 ^ (prefixWord ++ tailWord_5564840).sum := by decide
  have hdescent : baseEnd_5564840 < baseStart_5564840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564857 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5564857 : Nat := 118140960795 + 5564857 * 2 ^ 59
def prefixEnd_5564857 : Nat := 4983230072969 + 3 ^ 40 * 5564857 * 2
def baseEnd_5564857 : Nat := 2857446414537239205095195

theorem tailTrace_5564857 : CollatzResearch.WordTrace tailWord_5564857 prefixEnd_5564857 2857446414537239205095195 := by
  unfold tailWord_5564857
  simp only [CollatzResearch.WordTrace]
  refine ⟨202967009200480965755348825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135311339466987310503565883 202967009200480965755348825)
  ·
    refine ⟨152225256900360724316511619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202967009200480965755348825 152225256900360724316511619)
    ·
      refine ⟨228337885350541086474767429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152225256900360724316511619 228337885350541086474767429)
      ·
        refine ⟨42813353503226453714018893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228337885350541086474767429 42813353503226453714018893)
        ·
          refine ⟨16055007563709920142757085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42813353503226453714018893 16055007563709920142757085)
          ·
            refine ⟨6020627836391220053533907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16055007563709920142757085 6020627836391220053533907)
            ·
              refine ⟨9030941754586830080300861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020627836391220053533907 9030941754586830080300861)
              ·
                refine ⟨3386603157970061280112823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9030941754586830080300861 3386603157970061280112823)
                ·
                  refine ⟨5079904736955091920169235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386603157970061280112823 5079904736955091920169235)
                  ·
                    refine ⟨7619857105432637880253853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5079904736955091920169235 7619857105432637880253853)
                    ·
                      refine ⟨2857446414537239205095195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7619857105432637880253853 2857446414537239205095195)
                      ·
                        rfl

theorem cell23_5564857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5564857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564857 prefixEnd_5564857 := by exact prefixLift 5564857
  have htrace : WordTrace (prefixWord ++ tailWord_5564857) baseStart_5564857 baseEnd_5564857 := by
    simpa [prefixWord, tailWord_5564857, baseEnd_5564857] using wordTrace_append hprefix tailTrace_5564857
  have hstable : (prefixWord ++ tailWord_5564857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564857).length < 2 ^ (prefixWord ++ tailWord_5564857).sum := by decide
  have hdescent : baseEnd_5564857 < baseStart_5564857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564889 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_5564889 : Nat := 118140960795 + 5564889 * 2 ^ 59
def prefixEnd_5564889 : Nat := 4983230072969 + 3 ^ 40 * 5564889 * 2
def baseEnd_5564889 : Nat := 2857462845918183079895047

theorem tailTrace_5564889 : CollatzResearch.WordTrace tailWord_5564889 prefixEnd_5564889 2857462845918183079895047 := by
  unfold tailWord_5564889
  simp only [CollatzResearch.WordTrace]
  refine ⟨202968176336365035220513721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135312117557576690147009147 202968176336365035220513721)
  ·
    refine ⟨152226132252273776415385291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202968176336365035220513721 152226132252273776415385291)
    ·
      refine ⟨228339198378410664623077937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152226132252273776415385291 228339198378410664623077937)
      ·
        refine ⟨171254398783807998467308453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228339198378410664623077937 171254398783807998467308453)
        ·
          refine ⟨32110199771963999712620335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171254398783807998467308453 32110199771963999712620335)
          ·
            refine ⟨48165299657945999568930503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32110199771963999712620335 48165299657945999568930503)
            ·
              refine ⟨72247949486918999353395755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48165299657945999568930503 72247949486918999353395755)
              ·
                refine ⟨108371924230378499030093633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72247949486918999353395755 108371924230378499030093633)
                ·
                  refine ⟨81278943172783874272570225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108371924230378499030093633 81278943172783874272570225)
                  ·
                    refine ⟨60959207379587905704427669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81278943172783874272570225 60959207379587905704427669)
                    ·
                      refine ⟨2857462845918183079895047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60959207379587905704427669 2857462845918183079895047)
                      ·
                        rfl

theorem cell23_5564889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_5564889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564889 prefixEnd_5564889 := by exact prefixLift 5564889
  have htrace : WordTrace (prefixWord ++ tailWord_5564889) baseStart_5564889 baseEnd_5564889 := by
    simpa [prefixWord, tailWord_5564889, baseEnd_5564889] using wordTrace_append hprefix tailTrace_5564889
  have hstable : (prefixWord ++ tailWord_5564889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564889).length < 2 ^ (prefixWord ++ tailWord_5564889).sum := by decide
  have hdescent : baseEnd_5564889 < baseStart_5564889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564896 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_5564896 : Nat := 118140960795 + 5564896 * 2 ^ 59
def prefixEnd_5564896 : Nat := 4983230072969 + 3 ^ 40 * 5564896 * 2
def baseEnd_5564896 : Nat := 2857466440282764552507515

theorem tailTrace_5564896 : CollatzResearch.WordTrace tailWord_5564896 prefixEnd_5564896 2857466440282764552507515 := by
  unfold tailWord_5564896
  simp only [CollatzResearch.WordTrace]
  refine ⟨101484215823669837708009271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135312287764893116944012361 101484215823669837708009271)
  ·
    refine ⟨152226323735504756562013907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101484215823669837708009271 152226323735504756562013907)
    ·
      refine ⟨228339485603257134843020861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152226323735504756562013907 228339485603257134843020861)
      ·
        refine ⟨85627307101221425566132823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228339485603257134843020861 85627307101221425566132823)
        ·
          refine ⟨128440960651832138349199235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85627307101221425566132823 128440960651832138349199235)
          ·
            refine ⟨192661440977748207523798853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128440960651832138349199235 192661440977748207523798853)
            ·
              refine ⟨36124020183327788910712285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192661440977748207523798853 36124020183327788910712285)
              ·
                refine ⟨13546507568747920841517107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36124020183327788910712285 13546507568747920841517107)
                ·
                  refine ⟨20319761353121881262275661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13546507568747920841517107 20319761353121881262275661)
                  ·
                    refine ⟨7619910507420705473353373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20319761353121881262275661 7619910507420705473353373)
                    ·
                      refine ⟨2857466440282764552507515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7619910507420705473353373 2857466440282764552507515)
                      ·
                        rfl

theorem cell23_5564896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_5564896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564896 prefixEnd_5564896 := by exact prefixLift 5564896
  have htrace : WordTrace (prefixWord ++ tailWord_5564896) baseStart_5564896 baseEnd_5564896 := by
    simpa [prefixWord, tailWord_5564896, baseEnd_5564896] using wordTrace_append hprefix tailTrace_5564896
  have hstable : (prefixWord ++ tailWord_5564896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564896).length < 2 ^ (prefixWord ++ tailWord_5564896).sum := by decide
  have hdescent : baseEnd_5564896 < baseStart_5564896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564917 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5564917 : Nat := 118140960795 + 5564917 * 2 ^ 59
def prefixEnd_5564917 : Nat := 4983230072969 + 3 ^ 40 * 5564917 * 2
def baseEnd_5564917 : Nat := 2857477223376508970344919

theorem tailTrace_5564917 : CollatzResearch.WordTrace tailWord_5564917 prefixEnd_5564917 2857477223376508970344919 := by
  unfold tailWord_5564917
  simp only [CollatzResearch.WordTrace]
  refine ⟨202969197580263596002533005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135312798386842397335022003 202969197580263596002533005)
  ·
    refine ⟨76113449092598848500949877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202969197580263596002533005 76113449092598848500949877)
    ·
      refine ⟨7135635852431142046964051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76113449092598848500949877 7135635852431142046964051)
      ·
        refine ⟨10703453778646713070446077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135635852431142046964051 10703453778646713070446077)
        ·
          refine ⟨4013795166992517401417279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10703453778646713070446077 4013795166992517401417279)
          ·
            refine ⟨6020692750488776102125919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013795166992517401417279 6020692750488776102125919)
            ·
              refine ⟨9031039125733164153188879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020692750488776102125919 9031039125733164153188879)
              ·
                refine ⟨13546558688599746229783319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031039125733164153188879 13546558688599746229783319)
                ·
                  refine ⟨20319838032899619344674979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13546558688599746229783319 20319838032899619344674979)
                  ·
                    refine ⟨30479757049349429017012469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20319838032899619344674979 30479757049349429017012469)
                    ·
                      refine ⟨2857477223376508970344919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30479757049349429017012469 2857477223376508970344919)
                      ·
                        rfl

theorem cell23_5564917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5564917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564917 prefixEnd_5564917 := by exact prefixLift 5564917
  have htrace : WordTrace (prefixWord ++ tailWord_5564917) baseStart_5564917 baseEnd_5564917 := by
    simpa [prefixWord, tailWord_5564917, baseEnd_5564917] using wordTrace_append hprefix tailTrace_5564917
  have hstable : (prefixWord ++ tailWord_5564917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564917).length < 2 ^ (prefixWord ++ tailWord_5564917).sum := by decide
  have hdescent : baseEnd_5564917 < baseStart_5564917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564970 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5564970 : Nat := 118140960795 + 5564970 * 2 ^ 59
def prefixEnd_5564970 : Nat := 4983230072969 + 3 ^ 40 * 5564970 * 2
def baseEnd_5564970 : Nat := 2857504437851197262982175

theorem tailTrace_5564970 : CollatzResearch.WordTrace tailWord_5564970 prefixEnd_5564970 2857504437851197262982175 := by
  unfold tailWord_5564970
  simp only [CollatzResearch.WordTrace]
  refine ⟨50742782662267896513553091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135314087099381057369474909 50742782662267896513553091)
  ·
    refine ⟨76114173993401844770329637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50742782662267896513553091 76114173993401844770329637)
    ·
      refine ⟨14271407623762845894436807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76114173993401844770329637 14271407623762845894436807)
      ·
        refine ⟨21407111435644268841655211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14271407623762845894436807 21407111435644268841655211)
        ·
          refine ⟨32110667153466403262482817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21407111435644268841655211 32110667153466403262482817)
          ·
            refine ⟨24083000365099802446862113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32110667153466403262482817 24083000365099802446862113)
            ·
              refine ⟨18062250273824851835146585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24083000365099802446862113 18062250273824851835146585)
              ·
                refine ⟨13546687705368638876359939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18062250273824851835146585 13546687705368638876359939)
                ·
                  refine ⟨20320031558052958314539909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13546687705368638876359939 20320031558052958314539909)
                  ·
                    refine ⟨3810005917134929683976233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20320031558052958314539909 3810005917134929683976233)
                    ·
                      refine ⟨2857504437851197262982175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810005917134929683976233 2857504437851197262982175)
                      ·
                        rfl

theorem cell23_5564970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5564970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564970 prefixEnd_5564970 := by exact prefixLift 5564970
  have htrace : WordTrace (prefixWord ++ tailWord_5564970) baseStart_5564970 baseEnd_5564970 := by
    simpa [prefixWord, tailWord_5564970, baseEnd_5564970] using wordTrace_append hprefix tailTrace_5564970
  have hstable : (prefixWord ++ tailWord_5564970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564970).length < 2 ^ (prefixWord ++ tailWord_5564970).sum := by decide
  have hdescent : baseEnd_5564970 < baseStart_5564970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5564993 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 7]
def baseStart_5564993 : Nat := 118140960795 + 5564993 * 2 ^ 59
def prefixEnd_5564993 : Nat := 4983230072969 + 3 ^ 40 * 5564993 * 2
def baseEnd_5564993 : Nat := 317501805322916741443841

theorem tailTrace_5564993 : CollatzResearch.WordTrace tailWord_5564993 prefixEnd_5564993 317501805322916741443841 := by
  unfold tailWord_5564993
  simp only [CollatzResearch.WordTrace]
  refine ⟨202971969527988260982299633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135314646351992173988199755 202971969527988260982299633)
  ·
    refine ⟨152228977145991195736724725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202971969527988260982299633 152228977145991195736724725)
    ·
      refine ⟨14271466607436674600317943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152228977145991195736724725 14271466607436674600317943)
      ·
        refine ⟨21407199911155011900476915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14271466607436674600317943 21407199911155011900476915)
        ·
          refine ⟨32110799866732517850715373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21407199911155011900476915 32110799866732517850715373)
          ·
            refine ⟨12041549950024694194018265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32110799866732517850715373 12041549950024694194018265)
            ·
              refine ⟨9031162462518520645513699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12041549950024694194018265 9031162462518520645513699)
              ·
                refine ⟨13546743693777780968270549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031162462518520645513699 13546743693777780968270549)
                ·
                  refine ⟨317501805322916741443841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13546743693777780968270549 317501805322916741443841)
                  ·
                    rfl

theorem cell23_5564993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 7].length) (baseStart_5564993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5564993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5564993 prefixEnd_5564993 := by exact prefixLift 5564993
  have htrace : WordTrace (prefixWord ++ tailWord_5564993) baseStart_5564993 baseEnd_5564993 := by
    simpa [prefixWord, tailWord_5564993, baseEnd_5564993] using wordTrace_append hprefix tailTrace_5564993
  have hstable : (prefixWord ++ tailWord_5564993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5564993).length < 2 ^ (prefixWord ++ tailWord_5564993).sum := by decide
  have hdescent : baseEnd_5564993 < baseStart_5564993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5564993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565006 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_5565006 : Nat := 118140960795 + 5565006 * 2 ^ 59
def prefixEnd_5565006 : Nat := 4983230072969 + 3 ^ 40 * 5565006 * 2
def baseEnd_5565006 : Nat := 952507641051586374044003

theorem tailTrace_5565006 : CollatzResearch.WordTrace tailWord_5565006 prefixEnd_5565006 952507641051586374044003 := by
  unfold tailWord_5565006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25371555459617645525315359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135314962451294109468348581 25371555459617645525315359)
  ·
    refine ⟨38057333189426468287973039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25371555459617645525315359 38057333189426468287973039)
    ·
      refine ⟨57085999784139702431959559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38057333189426468287973039 57085999784139702431959559)
      ·
        refine ⟨85628999676209553647939339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57085999784139702431959559 85628999676209553647939339)
        ·
          refine ⟨128443499514314330471909009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85628999676209553647939339 128443499514314330471909009)
          ·
            refine ⟨96332624635735747853931757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128443499514314330471909009 96332624635735747853931757)
            ·
              refine ⟨36124734238400905445224409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96332624635735747853931757 36124734238400905445224409)
              ·
                refine ⟨27093550678800679083918307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36124734238400905445224409 27093550678800679083918307)
                ·
                  refine ⟨40640326018201018625877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27093550678800679083918307 40640326018201018625877461)
                  ·
                    refine ⟨952507641051586374044003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40640326018201018625877461 952507641051586374044003)
                    ·
                      rfl

theorem cell23_5565006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_5565006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565006 prefixEnd_5565006 := by exact prefixLift 5565006
  have htrace : WordTrace (prefixWord ++ tailWord_5565006) baseStart_5565006 baseEnd_5565006 := by
    simpa [prefixWord, tailWord_5565006, baseEnd_5565006] using wordTrace_append hprefix tailTrace_5565006
  have hstable : (prefixWord ++ tailWord_5565006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565006).length < 2 ^ (prefixWord ++ tailWord_5565006).sum := by decide
  have hdescent : baseEnd_5565006 < baseStart_5565006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565013 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_5565013 : Nat := 118140960795 + 5565013 * 2 ^ 59
def prefixEnd_5565013 : Nat := 4983230072969 + 3 ^ 40 * 5565013 * 2
def baseEnd_5565013 : Nat := 2857526517519340594744477

theorem tailTrace_5565013 : CollatzResearch.WordTrace tailWord_5565013 prefixEnd_5565013 2857526517519340594744477 := by
  unfold tailWord_5565013
  simp only [CollatzResearch.WordTrace]
  refine ⟨202972698987915804398027693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135315132658610536265351795 202972698987915804398027693)
  ·
    refine ⟨76114762120468426649260385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202972698987915804398027693 76114762120468426649260385)
    ·
      refine ⟨57086071590351319986945289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76114762120468426649260385 57086071590351319986945289)
      ·
        refine ⟨42814553692763489990208967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57086071590351319986945289 42814553692763489990208967)
        ·
          refine ⟨64221830539145234985313451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42814553692763489990208967 64221830539145234985313451)
          ·
            refine ⟨96332745808717852477970177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64221830539145234985313451 96332745808717852477970177)
            ·
              refine ⟨72249559356538389358477633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96332745808717852477970177 72249559356538389358477633)
              ·
                refine ⟨54187169517403792018858225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72249559356538389358477633 54187169517403792018858225)
                ·
                  refine ⟨40640377138052844014143669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54187169517403792018858225 40640377138052844014143669)
                  ·
                    refine ⟨3810035356692454126325969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40640377138052844014143669 3810035356692454126325969)
                    ·
                      refine ⟨2857526517519340594744477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810035356692454126325969 2857526517519340594744477)
                      ·
                        rfl

theorem cell23_5565013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_5565013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565013 prefixEnd_5565013 := by exact prefixLift 5565013
  have htrace : WordTrace (prefixWord ++ tailWord_5565013) baseStart_5565013 baseEnd_5565013 := by
    simpa [prefixWord, tailWord_5565013, baseEnd_5565013] using wordTrace_append hprefix tailTrace_5565013
  have hstable : (prefixWord ++ tailWord_5565013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565013).length < 2 ^ (prefixWord ++ tailWord_5565013).sum := by decide
  have hdescent : baseEnd_5565013 < baseStart_5565013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565043 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 2, 4, 2]
def baseStart_5565043 : Nat := 118140960795 + 5565043 * 2 ^ 59
def prefixEnd_5565043 : Nat := 4983230072969 + 3 ^ 40 * 5565043 * 2
def baseEnd_5565043 : Nat := 2857541921938975477369339

theorem tailTrace_5565043 : CollatzResearch.WordTrace tailWord_5565043 prefixEnd_5565043 2857541921938975477369339 := by
  unfold tailWord_5565043
  simp only [CollatzResearch.WordTrace]
  refine ⟨202973793177807119521619783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135315862118538079681079855 202973793177807119521619783)
  ·
    refine ⟨304460689766710679282429675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202973793177807119521619783 304460689766710679282429675)
    ·
      refine ⟨456691034650066018923644513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304460689766710679282429675 456691034650066018923644513)
      ·
        refine ⟨342518275987549514192733385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456691034650066018923644513 342518275987549514192733385)
        ·
          refine ⟨256888706990662135644550039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342518275987549514192733385 256888706990662135644550039)
          ·
            refine ⟨385333060485993203466825059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256888706990662135644550039 385333060485993203466825059)
            ·
              refine ⟨577999590728989805200237589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385333060485993203466825059 577999590728989805200237589)
              ·
                refine ⟨27093730815421397118761137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 577999590728989805200237589 27093730815421397118761137)
                ·
                  refine ⟨20320298111566047839070853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27093730815421397118761137 20320298111566047839070853)
                  ·
                    refine ⟨3810055895918633969825785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20320298111566047839070853 3810055895918633969825785)
                    ·
                      refine ⟨2857541921938975477369339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810055895918633969825785 2857541921938975477369339)
                      ·
                        rfl

theorem cell23_5565043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4, 2].length) (baseStart_5565043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565043 prefixEnd_5565043 := by exact prefixLift 5565043
  have htrace : WordTrace (prefixWord ++ tailWord_5565043) baseStart_5565043 baseEnd_5565043 := by
    simpa [prefixWord, tailWord_5565043, baseEnd_5565043] using wordTrace_append hprefix tailTrace_5565043
  have hstable : (prefixWord ++ tailWord_5565043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565043).length < 2 ^ (prefixWord ++ tailWord_5565043).sum := by decide
  have hdescent : baseEnd_5565043 < baseStart_5565043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565063 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_5565063 : Nat := 118140960795 + 5565063 * 2 ^ 59
def prefixEnd_5565063 : Nat := 4983230072969 + 3 ^ 40 * 5565063 * 2
def baseEnd_5565063 : Nat := 2857552191552065399119247

theorem tailTrace_5565063 : CollatzResearch.WordTrace tailWord_5565063 prefixEnd_5565063 2857552191552065399119247 := by
  unfold tailWord_5565063
  simp only [CollatzResearch.WordTrace]
  refine ⟨202974522637734662937347843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135316348425156441958231895 202974522637734662937347843)
  ·
    refine ⟨304461783956601994406021765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202974522637734662937347843 304461783956601994406021765)
    ·
      refine ⟨57086584491862873951129081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304461783956601994406021765 57086584491862873951129081)
      ·
        refine ⟨42814938368897155463346811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57086584491862873951129081 42814938368897155463346811)
        ·
          refine ⟨64222407553345733195020217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42814938368897155463346811 64222407553345733195020217)
          ·
            refine ⟨48166805665009299896265163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64222407553345733195020217 48166805665009299896265163)
            ·
              refine ⟨72250208497513949844397745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48166805665009299896265163 72250208497513949844397745)
              ·
                refine ⟨54187656373135462383298309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72250208497513949844397745 54187656373135462383298309)
                ·
                  refine ⟨10160185569962899196868433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54187656373135462383298309 10160185569962899196868433)
                  ·
                    refine ⟨7620139177472174397651325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10160185569962899196868433 7620139177472174397651325)
                    ·
                      refine ⟨2857552191552065399119247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620139177472174397651325 2857552191552065399119247)
                      ·
                        rfl

theorem cell23_5565063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_5565063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565063 prefixEnd_5565063 := by exact prefixLift 5565063
  have htrace : WordTrace (prefixWord ++ tailWord_5565063) baseStart_5565063 baseEnd_5565063 := by
    simpa [prefixWord, tailWord_5565063, baseEnd_5565063] using wordTrace_append hprefix tailTrace_5565063
  have hstable : (prefixWord ++ tailWord_5565063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565063).length < 2 ^ (prefixWord ++ tailWord_5565063).sum := by decide
  have hdescent : baseEnd_5565063 < baseStart_5565063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565080 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5565080 : Nat := 118140960795 + 5565080 * 2 ^ 59
def prefixEnd_5565080 : Nat := 4983230072969 + 3 ^ 40 * 5565080 * 2
def baseEnd_5565080 : Nat := 2857560920723191832606669

theorem tailTrace_5565080 : CollatzResearch.WordTrace tailWord_5565080 prefixEnd_5565080 2857560920723191832606669 := by
  unfold tailWord_5565080
  simp only [CollatzResearch.WordTrace]
  refine ⟨101487571339336537420358347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135316761785782049893811129 101487571339336537420358347)
  ·
    refine ⟨152231357009004806130537521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101487571339336537420358347 152231357009004806130537521)
    ·
      refine ⟨114173517756753604597903141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152231357009004806130537521 114173517756753604597903141)
      ·
        refine ⟨21407534579391300862106839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114173517756753604597903141 21407534579391300862106839)
        ·
          refine ⟨32111301869086951293160259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21407534579391300862106839 32111301869086951293160259)
          ·
            refine ⟨48166952803630426939740389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32111301869086951293160259 48166952803630426939740389)
            ·
              refine ⟨9031303650680705051201323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48166952803630426939740389 9031303650680705051201323)
              ·
                refine ⟨13546955476021057576801985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031303650680705051201323 13546955476021057576801985)
                ·
                  refine ⟨10160216607015793182601489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13546955476021057576801985 10160216607015793182601489)
                  ·
                    refine ⟨7620162455261844886951117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10160216607015793182601489 7620162455261844886951117)
                    ·
                      refine ⟨2857560920723191832606669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620162455261844886951117 2857560920723191832606669)
                      ·
                        rfl

theorem cell23_5565080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5565080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565080 prefixEnd_5565080 := by exact prefixLift 5565080
  have htrace : WordTrace (prefixWord ++ tailWord_5565080) baseStart_5565080 baseEnd_5565080 := by
    simpa [prefixWord, tailWord_5565080, baseEnd_5565080] using wordTrace_append hprefix tailTrace_5565080
  have hstable : (prefixWord ++ tailWord_5565080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565080).length < 2 ^ (prefixWord ++ tailWord_5565080).sum := by decide
  have hdescent : baseEnd_5565080 < baseStart_5565080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565143 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 1, 6]
def baseStart_5565143 : Nat := 118140960795 + 5565143 * 2 ^ 59
def prefixEnd_5565143 : Nat := 4983230072969 + 3 ^ 40 * 5565143 * 2
def baseEnd_5565143 : Nat := 952531090001475028706293

theorem tailTrace_5565143 : CollatzResearch.WordTrace tailWord_5565143 prefixEnd_5565143 952531090001475028706293 := by
  unfold tailWord_5565143
  simp only [CollatzResearch.WordTrace]
  refine ⟨202977440477444836600260083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135318293651629891066840055 202977440477444836600260083)
  ·
    refine ⟨304466160716167254900390125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202977440477444836600260083 304466160716167254900390125)
    ·
      refine ⟨114174810268562720587646297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304466160716167254900390125 114174810268562720587646297)
      ·
        refine ⟨85631107701422040440734723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114174810268562720587646297 85631107701422040440734723)
        ·
          refine ⟨128446661552133060661102085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85631107701422040440734723 128446661552133060661102085)
          ·
            refine ⟨24083749041024948873956641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128446661552133060661102085 24083749041024948873956641)
            ·
              refine ⟨18062811780768711655467481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24083749041024948873956641 18062811780768711655467481)
              ·
                refine ⟨13547108835576533741600611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18062811780768711655467481 13547108835576533741600611)
                ·
                  refine ⟨20320663253364800612400917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13547108835576533741600611 20320663253364800612400917)
                  ·
                    refine ⟨952531090001475028706293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20320663253364800612400917 952531090001475028706293)
                    ·
                      rfl

theorem cell23_5565143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_5565143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565143 prefixEnd_5565143 := by exact prefixLift 5565143
  have htrace : WordTrace (prefixWord ++ tailWord_5565143) baseStart_5565143 baseEnd_5565143 := by
    simpa [prefixWord, tailWord_5565143, baseEnd_5565143] using wordTrace_append hprefix tailTrace_5565143
  have hstable : (prefixWord ++ tailWord_5565143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565143).length < 2 ^ (prefixWord ++ tailWord_5565143).sum := by decide
  have hdescent : baseEnd_5565143 < baseStart_5565143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565144 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 1, 1, 3]
def baseStart_5565144 : Nat := 118140960795 + 5565144 * 2 ^ 59
def prefixEnd_5565144 : Nat := 4983230072969 + 3 ^ 40 * 5565144 * 2
def baseEnd_5565144 : Nat := 2857593783485079582206375

theorem tailTrace_5565144 : CollatzResearch.WordTrace tailWord_5565144 prefixEnd_5565144 2857593783485079582206375 := by
  unfold tailWord_5565144
  simp only [CollatzResearch.WordTrace]
  refine ⟨101488738475220606885523243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135318317966960809180697657 101488738475220606885523243)
  ·
    refine ⟨152233107712830910328284865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101488738475220606885523243 152233107712830910328284865)
    ·
      refine ⟨114174830784623182746213649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152233107712830910328284865 114174830784623182746213649)
      ·
        refine ⟨85631123088467387059660237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114174830784623182746213649 85631123088467387059660237)
        ·
          refine ⟨32111671158175270147372589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85631123088467387059660237 32111671158175270147372589)
          ·
            refine ⟨12041876684315726305264721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32111671158175270147372589 12041876684315726305264721)
            ·
              refine ⟨9031407513236794728948541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12041876684315726305264721 9031407513236794728948541)
              ·
                refine ⟨3386777817463798023355703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9031407513236794728948541 3386777817463798023355703)
                ·
                  refine ⟨5080166726195697035033555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386777817463798023355703 5080166726195697035033555)
                  ·
                    refine ⟨7620250089293545552550333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080166726195697035033555 7620250089293545552550333)
                    ·
                      refine ⟨2857593783485079582206375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620250089293545552550333 2857593783485079582206375)
                      ·
                        rfl

theorem cell23_5565144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_5565144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565144 prefixEnd_5565144 := by exact prefixLift 5565144
  have htrace : WordTrace (prefixWord ++ tailWord_5565144) baseStart_5565144 baseEnd_5565144 := by
    simpa [prefixWord, tailWord_5565144, baseEnd_5565144] using wordTrace_append hprefix tailTrace_5565144
  have hstable : (prefixWord ++ tailWord_5565144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565144).length < 2 ^ (prefixWord ++ tailWord_5565144).sum := by decide
  have hdescent : baseEnd_5565144 < baseStart_5565144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565167 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 3, 2, 2]
def baseStart_5565167 : Nat := 118140960795 + 5565167 * 2 ^ 59
def prefixEnd_5565167 : Nat := 4983230072969 + 3 ^ 40 * 5565167 * 2
def baseEnd_5565167 : Nat := 2857605593540132992218769

theorem tailTrace_5565167 : CollatzResearch.WordTrace tailWord_5565167 prefixEnd_5565167 2857605593540132992218769 := by
  unfold tailWord_5565167
  simp only [CollatzResearch.WordTrace]
  refine ⟨202978315829357888699133755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135318877219571925799422503 202978315829357888699133755)
  ·
    refine ⟨304467473744036833048700633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202978315829357888699133755 304467473744036833048700633)
    ·
      refine ⟨228350605308027624786525475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304467473744036833048700633 228350605308027624786525475)
      ·
        refine ⟨342525907962041437179788213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228350605308027624786525475 342525907962041437179788213)
        ·
          refine ⟨32111803871441384735605145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 342525907962041437179788213 32111803871441384735605145)
          ·
            refine ⟨24083852903581038551703859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32111803871441384735605145 24083852903581038551703859)
            ·
              refine ⟨36125779355371557827555789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24083852903581038551703859 36125779355371557827555789)
              ·
                refine ⟨13547167258264334185333421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36125779355371557827555789 13547167258264334185333421)
                ·
                  refine ⟨5080187721849125319500033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13547167258264334185333421 5080187721849125319500033)
                  ·
                    refine ⟨3810140791386843989625025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080187721849125319500033 3810140791386843989625025)
                    ·
                      refine ⟨2857605593540132992218769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810140791386843989625025 2857605593540132992218769)
                      ·
                        rfl

theorem cell23_5565167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 2, 2].length) (baseStart_5565167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565167 prefixEnd_5565167 := by exact prefixLift 5565167
  have htrace : WordTrace (prefixWord ++ tailWord_5565167) baseStart_5565167 baseEnd_5565167 := by
    simpa [prefixWord, tailWord_5565167, baseEnd_5565167] using wordTrace_append hprefix tailTrace_5565167
  have hstable : (prefixWord ++ tailWord_5565167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565167).length < 2 ^ (prefixWord ++ tailWord_5565167).sum := by decide
  have hdescent : baseEnd_5565167 < baseStart_5565167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565170 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5565170 : Nat := 118140960795 + 5565170 * 2 ^ 59
def prefixEnd_5565170 : Nat := 4983230072969 + 3 ^ 40 * 5565170 * 2
def baseEnd_5565170 : Nat := 2857607133982096480481255

theorem tailTrace_5565170 : CollatzResearch.WordTrace tailWord_5565170 prefixEnd_5565170 2857607133982096480481255 := by
  unfold tailWord_5565170
  simp only [CollatzResearch.WordTrace]
  refine ⟨50744606312086755052873241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135318950165564680140995309 50744606312086755052873241)
  ·
    refine ⟨38058454734065066289654931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50744606312086755052873241 38058454734065066289654931)
    ·
      refine ⟨57087682101097599434482397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38058454734065066289654931 57087682101097599434482397)
      ·
        refine ⟨21407880787911599787930899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57087682101097599434482397 21407880787911599787930899)
        ·
          refine ⟨32111821181867399681896349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21407880787911599787930899 32111821181867399681896349)
          ·
            refine ⟨12041932943200274880711131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32111821181867399681896349 12041932943200274880711131)
            ·
              refine ⟨18062899414800412321066697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12041932943200274880711131 18062899414800412321066697)
              ·
                refine ⟨13547174561100309240800023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18062899414800412321066697 13547174561100309240800023)
                ·
                  refine ⟨20320761841650463861200035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13547174561100309240800023 20320761841650463861200035)
                  ·
                    refine ⟨30481142762475695791800053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20320761841650463861200035 30481142762475695791800053)
                    ·
                      refine ⟨2857607133982096480481255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30481142762475695791800053 2857607133982096480481255)
                      ·
                        rfl

theorem cell23_5565170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5565170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565170 prefixEnd_5565170 := by exact prefixLift 5565170
  have htrace : WordTrace (prefixWord ++ tailWord_5565170) baseStart_5565170 baseEnd_5565170 := by
    simpa [prefixWord, tailWord_5565170, baseEnd_5565170] using wordTrace_append hprefix tailTrace_5565170
  have hstable : (prefixWord ++ tailWord_5565170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565170).length < 2 ^ (prefixWord ++ tailWord_5565170).sum := by decide
  have hdescent : baseEnd_5565170 < baseStart_5565170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565180 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_5565180 : Nat := 118140960795 + 5565180 * 2 ^ 59
def prefixEnd_5565180 : Nat := 4983230072969 + 3 ^ 40 * 5565180 * 2
def baseEnd_5565180 : Nat := 2857612268788641441356209

theorem tailTrace_5565180 : CollatzResearch.WordTrace tailWord_5565180 prefixEnd_5565180 2857612268788641441356209 := by
  unfold tailWord_5565180
  simp only [CollatzResearch.WordTrace]
  refine ⟨101489394989155395959678497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135319193318873861279571329 101489394989155395959678497)
  ·
    refine ⟨76117046241866546969758873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101489394989155395959678497 76117046241866546969758873)
    ·
      refine ⟨57087784681399910227319155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76117046241866546969758873 57087784681399910227319155)
      ·
        refine ⟨85631677022099865340978733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57087784681399910227319155 85631677022099865340978733)
        ·
          refine ⟨32111878883287449502867025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85631677022099865340978733 32111878883287449502867025)
          ·
            refine ⟨24083909162465587127150269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32111878883287449502867025 24083909162465587127150269)
            ·
              refine ⟨9031465935924595172681351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24083909162465587127150269 9031465935924595172681351)
              ·
                refine ⟨13547198903886892759022027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031465935924595172681351 13547198903886892759022027)
                ·
                  refine ⟨20320798355830339138533041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13547198903886892759022027 20320798355830339138533041)
                  ·
                    refine ⟨15240598766872754353899781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20320798355830339138533041 15240598766872754353899781)
                    ·
                      refine ⟨2857612268788641441356209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15240598766872754353899781 2857612268788641441356209)
                      ·
                        rfl

theorem cell23_5565180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_5565180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565180 prefixEnd_5565180 := by exact prefixLift 5565180
  have htrace : WordTrace (prefixWord ++ tailWord_5565180) baseStart_5565180 baseEnd_5565180 := by
    simpa [prefixWord, tailWord_5565180, baseEnd_5565180] using wordTrace_append hprefix tailTrace_5565180
  have hstable : (prefixWord ++ tailWord_5565180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565180).length < 2 ^ (prefixWord ++ tailWord_5565180).sum := by decide
  have hdescent : baseEnd_5565180 < baseStart_5565180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565217 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_5565217 : Nat := 118140960795 + 5565217 * 2 ^ 59
def prefixEnd_5565217 : Nat := 4983230072969 + 3 ^ 40 * 5565217 * 2
def baseEnd_5565217 : Nat := 2857631267572857796593539

theorem tailTrace_5565217 : CollatzResearch.WordTrace tailWord_5565217 prefixEnd_5565217 2857631267572857796593539 := by
  unfold tailWord_5565217
  simp only [CollatzResearch.WordTrace]
  refine ⟨202980139479176747238453905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135320092986117831492302603 202980139479176747238453905)
  ·
    refine ⟨152235104609382560428840429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202980139479176747238453905 152235104609382560428840429)
    ·
      refine ⟨57088164228518460160815161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152235104609382560428840429 57088164228518460160815161)
      ·
        refine ⟨42816123171388845120611371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57088164228518460160815161 42816123171388845120611371)
        ·
          refine ⟨64224184757083267680917057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42816123171388845120611371 64224184757083267680917057)
          ·
            refine ⟨48168138567812450760687793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64224184757083267680917057 48168138567812450760687793)
            ·
              refine ⟨36126103925859338070515845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48168138567812450760687793 36126103925859338070515845)
              ·
                refine ⟨6773644486098625888221721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36126103925859338070515845 6773644486098625888221721)
                ·
                  refine ⟨5080233364573969416166291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773644486098625888221721 5080233364573969416166291)
                  ·
                    refine ⟨7620350046860954124249437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080233364573969416166291 7620350046860954124249437)
                    ·
                      refine ⟨2857631267572857796593539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620350046860954124249437 2857631267572857796593539)
                      ·
                        rfl

theorem cell23_5565217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_5565217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565217 prefixEnd_5565217 := by exact prefixLift 5565217
  have htrace : WordTrace (prefixWord ++ tailWord_5565217) baseStart_5565217 baseEnd_5565217 := by
    simpa [prefixWord, tailWord_5565217, baseEnd_5565217] using wordTrace_append hprefix tailTrace_5565217
  have hstable : (prefixWord ++ tailWord_5565217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565217).length < 2 ^ (prefixWord ++ tailWord_5565217).sum := by decide
  have hdescent : baseEnd_5565217 < baseStart_5565217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565218 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_5565218 : Nat := 118140960795 + 5565218 * 2 ^ 59
def prefixEnd_5565218 : Nat := 4983230072969 + 3 ^ 40 * 5565218 * 2
def baseEnd_5565218 : Nat := 2857631781053512292681035

theorem tailTrace_5565218 : CollatzResearch.WordTrace tailWord_5565218 prefixEnd_5565218 2857631781053512292681035 := by
  unfold tailWord_5565218
  simp only [CollatzResearch.WordTrace]
  refine ⟨50745043988043281102310077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135320117301448749606160205 50745043988043281102310077)
  ·
    refine ⟨19029391495516230413366279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50745043988043281102310077 19029391495516230413366279)
    ·
      refine ⟨28544087243274345620049419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19029391495516230413366279 28544087243274345620049419)
      ·
        refine ⟨42816130864911518430074129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28544087243274345620049419 42816130864911518430074129)
        ·
          refine ⟨32112098148683638822555597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42816130864911518430074129 32112098148683638822555597)
          ·
            refine ⟨12042036805756364558458349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32112098148683638822555597 12042036805756364558458349)
            ·
              refine ⟨4515763802158636709421881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12042036805756364558458349 4515763802158636709421881)
              ·
                refine ⟨3386822851618977532066411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4515763802158636709421881 3386822851618977532066411)
                ·
                  refine ⟨5080234277428466298099617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386822851618977532066411 5080234277428466298099617)
                  ·
                    refine ⟨3810175708071349723574713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080234277428466298099617 3810175708071349723574713)
                    ·
                      refine ⟨2857631781053512292681035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810175708071349723574713 2857631781053512292681035)
                      ·
                        rfl

theorem cell23_5565218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_5565218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565218 prefixEnd_5565218 := by exact prefixLift 5565218
  have htrace : WordTrace (prefixWord ++ tailWord_5565218) baseStart_5565218 baseEnd_5565218 := by
    simpa [prefixWord, tailWord_5565218, baseEnd_5565218] using wordTrace_append hprefix tailTrace_5565218
  have hstable : (prefixWord ++ tailWord_5565218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565218).length < 2 ^ (prefixWord ++ tailWord_5565218).sum := by decide
  have hdescent : baseEnd_5565218 < baseStart_5565218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565233 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_5565233 : Nat := 118140960795 + 5565233 * 2 ^ 59
def prefixEnd_5565233 : Nat := 4983230072969 + 3 ^ 40 * 5565233 * 2
def baseEnd_5565233 : Nat := 952546494421109911331155

theorem tailTrace_5565233 : CollatzResearch.WordTrace tailWord_5565233 prefixEnd_5565233 952546494421109911331155 := by
  unfold tailWord_5565233
  simp only [CollatzResearch.WordTrace]
  refine ⟨202980723047118781971036353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135320482031412521314024235 202980723047118781971036353)
  ·
    refine ⟨152235542285339086478277265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202980723047118781971036353 152235542285339086478277265)
    ·
      refine ⟨114176656714004314858707949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152235542285339086478277265 114176656714004314858707949)
      ·
        refine ⟨42816246267751618072015481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114176656714004314858707949 42816246267751618072015481)
        ·
          refine ⟨32112184700813713554011611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42816246267751618072015481 32112184700813713554011611)
          ·
            refine ⟨48168277051220570331017417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32112184700813713554011611 48168277051220570331017417)
            ·
              refine ⟨36126207788415427748263063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48168277051220570331017417 36126207788415427748263063)
              ·
                refine ⟨54189311682623141622394595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36126207788415427748263063 54189311682623141622394595)
                ·
                  refine ⟨81283967523934712433591893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54189311682623141622394595 81283967523934712433591893)
                  ·
                    refine ⟨952546494421109911331155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81283967523934712433591893 952546494421109911331155)
                    ·
                      rfl

theorem cell23_5565233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_5565233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565233 prefixEnd_5565233 := by exact prefixLift 5565233
  have htrace : WordTrace (prefixWord ++ tailWord_5565233) baseStart_5565233 baseEnd_5565233 := by
    simpa [prefixWord, tailWord_5565233, baseEnd_5565233] using wordTrace_append hprefix tailTrace_5565233
  have hstable : (prefixWord ++ tailWord_5565233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565233).length < 2 ^ (prefixWord ++ tailWord_5565233).sum := by decide
  have hdescent : baseEnd_5565233 < baseStart_5565233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565238 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5565238 : Nat := 118140960795 + 5565238 * 2 ^ 59
def prefixEnd_5565238 : Nat := 4983230072969 + 3 ^ 40 * 5565238 * 2
def baseEnd_5565238 : Nat := 2857642050666602214430943

theorem tailTrace_5565238 : CollatzResearch.WordTrace tailWord_5565238 prefixEnd_5565238 2857642050666602214430943 := by
  unfold tailWord_5565238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686306588256291739060523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135320603608067111883312245 12686306588256291739060523)
  ·
    refine ⟨19029459882384437608590785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12686306588256291739060523 19029459882384437608590785)
    ·
      refine ⟨14272094911788328206443089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19029459882384437608590785 14272094911788328206443089)
      ·
        refine ⟨10704071183841246154832317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14272094911788328206443089 10704071183841246154832317)
        ·
          refine ⟨4014026693940467308062119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10704071183841246154832317 4014026693940467308062119)
          ·
            refine ⟨6021040040910700962093179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014026693940467308062119 6021040040910700962093179)
            ·
              refine ⟨9031560061366051443139769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021040040910700962093179 9031560061366051443139769)
              ·
                refine ⟨6773670046024538582354827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9031560061366051443139769 6773670046024538582354827)
                ·
                  refine ⟨10160505069036807873532241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6773670046024538582354827 10160505069036807873532241)
                  ·
                    refine ⟨7620378801777605905149181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10160505069036807873532241 7620378801777605905149181)
                    ·
                      refine ⟨2857642050666602214430943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620378801777605905149181 2857642050666602214430943)
                      ·
                        rfl

theorem cell23_5565238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5565238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565238 prefixEnd_5565238 := by exact prefixLift 5565238
  have htrace : WordTrace (prefixWord ++ tailWord_5565238) baseStart_5565238 baseEnd_5565238 := by
    simpa [prefixWord, tailWord_5565238, baseEnd_5565238] using wordTrace_append hprefix tailTrace_5565238
  have hstable : (prefixWord ++ tailWord_5565238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565238).length < 2 ^ (prefixWord ++ tailWord_5565238).sum := by decide
  have hdescent : baseEnd_5565238 < baseStart_5565238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565253 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_5565253 : Nat := 118140960795 + 5565253 * 2 ^ 59
def prefixEnd_5565253 : Nat := 4983230072969 + 3 ^ 40 * 5565253 * 2
def baseEnd_5565253 : Nat := 2857649752876419655743373

theorem tailTrace_5565253 : CollatzResearch.WordTrace tailWord_5565253 prefixEnd_5565253 2857649752876419655743373 := by
  unfold tailWord_5565253
  simp only [CollatzResearch.WordTrace]
  refine ⟨202981452507046325386764413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135320968338030883591176275 202981452507046325386764413)
  ·
    refine ⟨76118044690142372020036655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202981452507046325386764413 76118044690142372020036655)
    ·
      refine ⟨114177067035213558030054983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76118044690142372020036655 114177067035213558030054983)
      ·
        refine ⟨171265600552820337045082475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114177067035213558030054983 171265600552820337045082475)
        ·
          refine ⟨256898400829230505567623713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171265600552820337045082475 256898400829230505567623713)
          ·
            refine ⟨192673800621922879175717785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256898400829230505567623713 192673800621922879175717785)
            ·
              refine ⟨144505350466442159381788339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192673800621922879175717785 144505350466442159381788339)
              ·
                refine ⟨216758025699663239072682509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144505350466442159381788339 216758025699663239072682509)
                ·
                  refine ⟨81284259637373714652255941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216758025699663239072682509 81284259637373714652255941)
                  ·
                    refine ⟨15240798682007571497297989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81284259637373714652255941 15240798682007571497297989)
                    ·
                      refine ⟨2857649752876419655743373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15240798682007571497297989 2857649752876419655743373)
                      ·
                        rfl

theorem cell23_5565253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_5565253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565253 prefixEnd_5565253 := by exact prefixLift 5565253
  have htrace : WordTrace (prefixWord ++ tailWord_5565253) baseStart_5565253 baseEnd_5565253 := by
    simpa [prefixWord, tailWord_5565253, baseEnd_5565253] using wordTrace_append hprefix tailTrace_5565253
  have hstable : (prefixWord ++ tailWord_5565253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565253).length < 2 ^ (prefixWord ++ tailWord_5565253).sum := by decide
  have hdescent : baseEnd_5565253 < baseStart_5565253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565257 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 1, 4, 2]
def baseStart_5565257 : Nat := 118140960795 + 5565257 * 2 ^ 59
def prefixEnd_5565257 : Nat := 4983230072969 + 3 ^ 40 * 5565257 * 2
def baseEnd_5565257 : Nat := 2857651806799037640093355

theorem tailTrace_5565257 : CollatzResearch.WordTrace tailWord_5565257 prefixEnd_5565257 2857651806799037640093355 := by
  unfold tailWord_5565257
  simp only [CollatzResearch.WordTrace]
  refine ⟨202981598399031834069910025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135321065599354556046606683 202981598399031834069910025)
  ·
    refine ⟨152236198799273875552432519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202981598399031834069910025 152236198799273875552432519)
    ·
      refine ⟨228354298198910813328648779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152236198799273875552432519 228354298198910813328648779)
      ·
        refine ⟨342531447298366219992973169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228354298198910813328648779 342531447298366219992973169)
        ·
          refine ⟨256898585473774664994729877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342531447298366219992973169 256898585473774664994729877)
          ·
            refine ⟨12042121194083187421627963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 256898585473774664994729877 12042121194083187421627963)
            ·
              refine ⟨18063181791124781132441945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12042121194083187421627963 18063181791124781132441945)
              ·
                refine ⟨13547386343343585849331459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18063181791124781132441945 13547386343343585849331459)
                ·
                  refine ⟨20321079515015378773997189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13547386343343585849331459 20321079515015378773997189)
                  ·
                    refine ⟨3810202409065383520124473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20321079515015378773997189 3810202409065383520124473)
                    ·
                      refine ⟨2857651806799037640093355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810202409065383520124473 2857651806799037640093355)
                      ·
                        rfl

theorem cell23_5565257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 4, 2].length) (baseStart_5565257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565257 prefixEnd_5565257 := by exact prefixLift 5565257
  have htrace : WordTrace (prefixWord ++ tailWord_5565257) baseStart_5565257 baseEnd_5565257 := by
    simpa [prefixWord, tailWord_5565257, baseEnd_5565257] using wordTrace_append hprefix tailTrace_5565257
  have hstable : (prefixWord ++ tailWord_5565257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565257).length < 2 ^ (prefixWord ++ tailWord_5565257).sum := by decide
  have hdescent : baseEnd_5565257 < baseStart_5565257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565260 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5565260 : Nat := 118140960795 + 5565260 * 2 ^ 59
def prefixEnd_5565260 : Nat := 4983230072969 + 3 ^ 40 * 5565260 * 2
def baseEnd_5565260 : Nat := 2857653347241001128355841

theorem tailTrace_5565260 : CollatzResearch.WordTrace tailWord_5565260 prefixEnd_5565260 2857653347241001128355841 := by
  unfold tailWord_5565260
  simp only [CollatzResearch.WordTrace]
  refine ⟨101490853909010482791134617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135321138545347310388179489 101490853909010482791134617)
  ·
    refine ⟨76118140431757862093350963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101490853909010482791134617 76118140431757862093350963)
    ·
      refine ⟨114177210647636793140026445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76118140431757862093350963 114177210647636793140026445)
      ·
        refine ⟨42816453992863797427509917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114177210647636793140026445 42816453992863797427509917)
        ·
          refine ⟨16056170247323924035316219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42816453992863797427509917 16056170247323924035316219)
          ·
            refine ⟨24084255370985886052974329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16056170247323924035316219 24084255370985886052974329)
            ·
              refine ⟨18063191528239414539730747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24084255370985886052974329 18063191528239414539730747)
              ·
                refine ⟨27094787292359121809596121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18063191528239414539730747 27094787292359121809596121)
                ·
                  refine ⟨20321090469269341357197091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27094787292359121809596121 20321090469269341357197091)
                  ·
                    refine ⟨30481635703904012035795637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20321090469269341357197091 30481635703904012035795637)
                    ·
                      refine ⟨2857653347241001128355841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30481635703904012035795637 2857653347241001128355841)
                      ·
                        rfl

theorem cell23_5565260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5565260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565260 prefixEnd_5565260 := by exact prefixLift 5565260
  have htrace : WordTrace (prefixWord ++ tailWord_5565260) baseStart_5565260 baseEnd_5565260 := by
    simpa [prefixWord, tailWord_5565260, baseEnd_5565260] using wordTrace_append hprefix tailTrace_5565260
  have hstable : (prefixWord ++ tailWord_5565260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565260).length < 2 ^ (prefixWord ++ tailWord_5565260).sum := by decide
  have hdescent : baseEnd_5565260 < baseStart_5565260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565274 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2]
def baseStart_5565274 : Nat := 118140960795 + 5565274 * 2 ^ 59
def prefixEnd_5565274 : Nat := 4983230072969 + 3 ^ 40 * 5565274 * 2
def baseEnd_5565274 : Nat := 2857660535970164073580777

theorem tailTrace_5565274 : CollatzResearch.WordTrace tailWord_5565274 prefixEnd_5565274 2857660535970164073580777 := by
  unfold tailWord_5565274
  simp only [CollatzResearch.WordTrace]
  refine ⟨50745554609992561493319719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135321478959980163982185917 50745554609992561493319719)
  ·
    refine ⟨76118331914988842239979579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50745554609992561493319719 76118331914988842239979579)
    ·
      refine ⟨114177497872483263359969369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76118331914988842239979579 114177497872483263359969369)
      ·
        refine ⟨85633123404362447519977027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114177497872483263359969369 85633123404362447519977027)
        ·
          refine ⟨128449685106543671279965541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85633123404362447519977027 128449685106543671279965541)
          ·
            refine ⟨24084315957476938364993539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128449685106543671279965541 24084315957476938364993539)
            ·
              refine ⟨36126473936215407547490309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24084315957476938364993539 36126473936215407547490309)
              ·
                refine ⟨6773713863040388915154433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36126473936215407547490309 6773713863040388915154433)
                ·
                  refine ⟨5080285397280291686365825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773713863040388915154433 5080285397280291686365825)
                  ·
                    refine ⟨3810214047960218764774369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080285397280291686365825 3810214047960218764774369)
                    ·
                      refine ⟨2857660535970164073580777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810214047960218764774369 2857660535970164073580777)
                      ·
                        rfl

theorem cell23_5565274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_5565274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565274 prefixEnd_5565274 := by exact prefixLift 5565274
  have htrace : WordTrace (prefixWord ++ tailWord_5565274) baseStart_5565274 baseEnd_5565274 := by
    simpa [prefixWord, tailWord_5565274, baseEnd_5565274] using wordTrace_append hprefix tailTrace_5565274
  have hstable : (prefixWord ++ tailWord_5565274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565274).length < 2 ^ (prefixWord ++ tailWord_5565274).sum := by decide
  have hdescent : baseEnd_5565274 < baseStart_5565274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565303 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_5565303 : Nat := 118140960795 + 5565303 * 2 ^ 59
def prefixEnd_5565303 : Nat := 4983230072969 + 3 ^ 40 * 5565303 * 2
def baseEnd_5565303 : Nat := 2857675426909144460118143

theorem tailTrace_5565303 : CollatzResearch.WordTrace tailWord_5565303 prefixEnd_5565303 2857675426909144460118143 := by
  unfold tailWord_5565303
  simp only [CollatzResearch.WordTrace]
  refine ⟨202983276156865183926084563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135322184104576789284056375 202983276156865183926084563)
  ·
    refine ⟨304474914235297775889126845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202983276156865183926084563 304474914235297775889126845)
    ·
      refine ⟨114178092838236665958422567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304474914235297775889126845 114178092838236665958422567)
      ·
        refine ⟨171267139257354998937633851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114178092838236665958422567 171267139257354998937633851)
        ·
          refine ⟨256900708886032498406450777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171267139257354998937633851 256900708886032498406450777)
          ·
            refine ⟨192675531664524373804838083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256900708886032498406450777 192675531664524373804838083)
            ·
              refine ⟨289013297496786560707257125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192675531664524373804838083 289013297496786560707257125)
              ·
                refine ⟨54189993280647480132610711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289013297496786560707257125 54189993280647480132610711)
                ·
                  refine ⟨81284989920971220198916067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54189993280647480132610711 81284989920971220198916067)
                  ·
                    refine ⟨121927484881456830298374101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81284989920971220198916067 121927484881456830298374101)
                    ·
                      refine ⟨2857675426909144460118143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121927484881456830298374101 2857675426909144460118143)
                      ·
                        rfl

theorem cell23_5565303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_5565303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565303 prefixEnd_5565303 := by exact prefixLift 5565303
  have htrace : WordTrace (prefixWord ++ tailWord_5565303) baseStart_5565303 baseEnd_5565303 := by
    simpa [prefixWord, tailWord_5565303, baseEnd_5565303] using wordTrace_append hprefix tailTrace_5565303
  have hstable : (prefixWord ++ tailWord_5565303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565303).length < 2 ^ (prefixWord ++ tailWord_5565303).sum := by decide
  have hdescent : baseEnd_5565303 < baseStart_5565303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565347 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 2, 4, 2]
def baseStart_5565347 : Nat := 118140960795 + 5565347 * 2 ^ 59
def prefixEnd_5565347 : Nat := 4983230072969 + 3 ^ 40 * 5565347 * 2
def baseEnd_5565347 : Nat := 2857698020057942287967941

theorem tailTrace_5565347 : CollatzResearch.WordTrace tailWord_5565347 prefixEnd_5565347 2857698020057942287967941 := by
  unfold tailWord_5565347
  simp only [CollatzResearch.WordTrace]
  refine ⟨202984880968705779440686295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135323253979137186293790863 202984880968705779440686295)
  ·
    refine ⟨304477321453058669161029443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202984880968705779440686295 304477321453058669161029443)
    ·
      refine ⟨456715982179588003741544165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304477321453058669161029443 456715982179588003741544165)
      ·
        refine ⟨85634246658672750701539531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 456715982179588003741544165 85634246658672750701539531)
        ·
          refine ⟨128451369988009126052309297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85634246658672750701539531 128451369988009126052309297)
          ·
            refine ⟨96338527491006844539231973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128451369988009126052309297 96338527491006844539231973)
            ·
              refine ⟨18063473904563783351105995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96338527491006844539231973 18063473904563783351105995)
              ·
                refine ⟨27095210856845675026658993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18063473904563783351105995 27095210856845675026658993)
                ·
                  refine ⟨20321408142634256269994245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27095210856845675026658993 20321408142634256269994245)
                  ·
                    refine ⟨3810264026743923050623921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20321408142634256269994245 3810264026743923050623921)
                    ·
                      refine ⟨2857698020057942287967941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810264026743923050623921 2857698020057942287967941)
                      ·
                        rfl

theorem cell23_5565347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_5565347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565347 prefixEnd_5565347 := by exact prefixLift 5565347
  have htrace : WordTrace (prefixWord ++ tailWord_5565347) baseStart_5565347 baseEnd_5565347 := by
    simpa [prefixWord, tailWord_5565347, baseEnd_5565347] using wordTrace_append hprefix tailTrace_5565347
  have hstable : (prefixWord ++ tailWord_5565347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565347).length < 2 ^ (prefixWord ++ tailWord_5565347).sum := by decide
  have hdescent : baseEnd_5565347 < baseStart_5565347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565364 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5565364 : Nat := 118140960795 + 5565364 * 2 ^ 59
def prefixEnd_5565364 : Nat := 4983230072969 + 3 ^ 40 * 5565364 * 2
def baseEnd_5565364 : Nat := 2857706749229068721455363

theorem tailTrace_5565364 : CollatzResearch.WordTrace tailWord_5565364 prefixEnd_5565364 2857706749229068721455363 := by
  unfold tailWord_5565364
  simp only [CollatzResearch.WordTrace]
  refine ⟨101492750504822095672027573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135323667339762794229370097 101492750504822095672027573)
  ·
    refine ⟨9514945359827071469252585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101492750504822095672027573 9514945359827071469252585)
    ·
      refine ⟨7136209019870303601939439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9514945359827071469252585 7136209019870303601939439)
      ·
        refine ⟨10704313529805455402909159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136209019870303601939439 10704313529805455402909159)
        ·
          refine ⟨16056470294708183104363739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10704313529805455402909159 16056470294708183104363739)
          ·
            refine ⟨24084705442062274656545609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16056470294708183104363739 24084705442062274656545609)
            ·
              refine ⟨18063529081546705992409207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24084705442062274656545609 18063529081546705992409207)
              ·
                refine ⟨27095293622320058988613811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18063529081546705992409207 27095293622320058988613811)
                ·
                  refine ⟨40642940433480088482920717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27095293622320058988613811 40642940433480088482920717)
                  ·
                    refine ⟨15241102662555033181095269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40642940433480088482920717 15241102662555033181095269)
                    ·
                      refine ⟨2857706749229068721455363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15241102662555033181095269 2857706749229068721455363)
                      ·
                        rfl

theorem cell23_5565364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5565364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565364 prefixEnd_5565364 := by exact prefixLift 5565364
  have htrace : WordTrace (prefixWord ++ tailWord_5565364) baseStart_5565364 baseEnd_5565364 := by
    simpa [prefixWord, tailWord_5565364, baseEnd_5565364] using wordTrace_append hprefix tailTrace_5565364
  have hstable : (prefixWord ++ tailWord_5565364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565364).length < 2 ^ (prefixWord ++ tailWord_5565364).sum := by decide
  have hdescent : baseEnd_5565364 < baseStart_5565364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565382 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_5565382 : Nat := 118140960795 + 5565382 * 2 ^ 59
def prefixEnd_5565382 : Nat := 4983230072969 + 3 ^ 40 * 5565382 * 2
def baseEnd_5565382 : Nat := 317523999097872183447809

theorem tailTrace_5565382 : CollatzResearch.WordTrace tailWord_5565382 prefixEnd_5565382 317523999097872183447809 := by
  unfold tailWord_5565382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343317422611843138069075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135324105015719320278806933 6343317422611843138069075)
  ·
    refine ⟨9514976133917764707103613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343317422611843138069075 9514976133917764707103613)
    ·
      refine ⟨3568116050219161765163855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9514976133917764707103613 3568116050219161765163855)
      ·
        refine ⟨5352174075328742647745783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568116050219161765163855 5352174075328742647745783)
        ·
          refine ⟨8028261112993113971618675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5352174075328742647745783 8028261112993113971618675)
          ·
            refine ⟨12042391669489670957428013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8028261112993113971618675 12042391669489670957428013)
            ·
              refine ⟨4515896876058626609035505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12042391669489670957428013 4515896876058626609035505)
              ·
                refine ⟨3386922657043969956776629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4515896876058626609035505 3386922657043969956776629)
                ·
                  refine ⟨317523999097872183447809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3386922657043969956776629 317523999097872183447809)
                  ·
                    rfl

theorem cell23_5565382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_5565382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565382 prefixEnd_5565382 := by exact prefixLift 5565382
  have htrace : WordTrace (prefixWord ++ tailWord_5565382) baseStart_5565382 baseEnd_5565382 := by
    simpa [prefixWord, tailWord_5565382, baseEnd_5565382] using wordTrace_append hprefix tailTrace_5565382
  have hstable : (prefixWord ++ tailWord_5565382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565382).length < 2 ^ (prefixWord ++ tailWord_5565382).sum := by decide
  have hdescent : baseEnd_5565382 < baseStart_5565382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565384 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_5565384 : Nat := 118140960795 + 5565384 * 2 ^ 59
def prefixEnd_5565384 : Nat := 4983230072969 + 3 ^ 40 * 5565384 * 2
def baseEnd_5565384 : Nat := 2857717018842158643205271

theorem tailTrace_5565384 : CollatzResearch.WordTrace tailWord_5565384 prefixEnd_5565384 2857717018842158643205271 := by
  unfold tailWord_5565384
  simp only [CollatzResearch.WordTrace]
  refine ⟨101493115234785867379891603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135324153646381156506522137 101493115234785867379891603)
  ·
    refine ⟨152239672852178801069837405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101493115234785867379891603 152239672852178801069837405)
    ·
      refine ⟨57089877319567050401189027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152239672852178801069837405 57089877319567050401189027)
      ·
        refine ⟨85634815979350575601783541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57089877319567050401189027 85634815979350575601783541)
        ·
          refine ⟨8028263998064116462667207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85634815979350575601783541 8028263998064116462667207)
          ·
            refine ⟨12042395997096174694000811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8028263998064116462667207 12042395997096174694000811)
            ·
              refine ⟨18063593995644262041001217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12042395997096174694000811 18063593995644262041001217)
              ·
                refine ⟨13547695496733196530750913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18063593995644262041001217 13547695496733196530750913)
                ·
                  refine ⟨10160771622549897398063185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13547695496733196530750913 10160771622549897398063185)
                  ·
                    refine ⟨7620578716912423048547389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10160771622549897398063185 7620578716912423048547389)
                    ·
                      refine ⟨2857717018842158643205271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620578716912423048547389 2857717018842158643205271)
                      ·
                        rfl

theorem cell23_5565384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_5565384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565384 prefixEnd_5565384 := by exact prefixLift 5565384
  have htrace : WordTrace (prefixWord ++ tailWord_5565384) baseStart_5565384 baseEnd_5565384 := by
    simpa [prefixWord, tailWord_5565384, baseEnd_5565384] using wordTrace_append hprefix tailTrace_5565384
  have hstable : (prefixWord ++ tailWord_5565384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565384).length < 2 ^ (prefixWord ++ tailWord_5565384).sum := by decide
  have hdescent : baseEnd_5565384 < baseStart_5565384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565391 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 1, 4]
def baseStart_5565391 : Nat := 118140960795 + 5565391 * 2 ^ 59
def prefixEnd_5565391 : Nat := 4983230072969 + 3 ^ 40 * 5565391 * 2
def baseEnd_5565391 : Nat := 952573537735580038605913

theorem tailTrace_5565391 : CollatzResearch.WordTrace tailWord_5565391 prefixEnd_5565391 952573537735580038605913 := by
  unfold tailWord_5565391
  simp only [CollatzResearch.WordTrace]
  refine ⟨202986485780546374955288027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135324323853697583303525351 202986485780546374955288027)
  ·
    refine ⟨304479728670819562432932041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202986485780546374955288027 304479728670819562432932041)
    ·
      refine ⟨228359796503114671824699031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304479728670819562432932041 228359796503114671824699031)
      ·
        refine ⟨342539694754672007737048547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228359796503114671824699031 342539694754672007737048547)
        ·
          refine ⟨513809542132008011605572821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342539694754672007737048547 513809542132008011605572821)
          ·
            refine ⟨12042411143718937772005613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 513809542132008011605572821 12042411143718937772005613)
            ·
              refine ⟨4515904178894601664502105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12042411143718937772005613 4515904178894601664502105)
              ·
                refine ⟨3386928134170951248376579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4515904178894601664502105 3386928134170951248376579)
                ·
                  refine ⟨5080392201256426872564869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386928134170951248376579 5080392201256426872564869)
                  ·
                    refine ⟨952573537735580038605913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080392201256426872564869 952573537735580038605913)
                    ·
                      rfl

theorem cell23_5565391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 4].length) (baseStart_5565391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565391 prefixEnd_5565391 := by exact prefixLift 5565391
  have htrace : WordTrace (prefixWord ++ tailWord_5565391) baseStart_5565391 baseEnd_5565391 := by
    simpa [prefixWord, tailWord_5565391, baseEnd_5565391] using wordTrace_append hprefix tailTrace_5565391
  have hstable : (prefixWord ++ tailWord_5565391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565391).length < 2 ^ (prefixWord ++ tailWord_5565391).sum := by decide
  have hdescent : baseEnd_5565391 < baseStart_5565391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565442 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5565442 : Nat := 118140960795 + 5565442 * 2 ^ 59
def prefixEnd_5565442 : Nat := 4983230072969 + 3 ^ 40 * 5565442 * 2
def baseEnd_5565442 : Nat := 952582266906706472093335

theorem tailTrace_5565442 : CollatzResearch.WordTrace tailWord_5565442 prefixEnd_5565442 952582266906706472093335 := by
  unfold tailWord_5565442
  simp only [CollatzResearch.WordTrace]
  refine ⟨50747086475840402666348645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135325563935574407110263053 50747086475840402666348645)
  ·
    refine ⟨9515078714220075499940371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50747086475840402666348645 9515078714220075499940371)
    ·
      refine ⟨14272618071330113249910557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515078714220075499940371 14272618071330113249910557)
      ·
        refine ⟨5352231776748792468716459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14272618071330113249910557 5352231776748792468716459)
        ·
          refine ⟨8028347665123188703074689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5352231776748792468716459 8028347665123188703074689)
          ·
            refine ⟨6021260748842391527306017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8028347665123188703074689 6021260748842391527306017)
            ·
              refine ⟨4515945561631793645479513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6021260748842391527306017 4515945561631793645479513)
              ·
                refine ⟨3386959171223845234109635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4515945561631793645479513 3386959171223845234109635)
                ·
                  refine ⟨5080438756835767851164453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386959171223845234109635 5080438756835767851164453)
                  ·
                    refine ⟨952582266906706472093335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080438756835767851164453 952582266906706472093335)
                    ·
                      rfl

theorem cell23_5565442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5565442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565442 prefixEnd_5565442 := by exact prefixLift 5565442
  have htrace : WordTrace (prefixWord ++ tailWord_5565442) baseStart_5565442 baseEnd_5565442 := by
    simpa [prefixWord, tailWord_5565442, baseEnd_5565442] using wordTrace_append hprefix tailTrace_5565442
  have hstable : (prefixWord ++ tailWord_5565442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565442).length < 2 ^ (prefixWord ++ tailWord_5565442).sum := by decide
  have hdescent : baseEnd_5565442 < baseStart_5565442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565448 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_5565448 : Nat := 118140960795 + 5565448 * 2 ^ 59
def prefixEnd_5565448 : Nat := 4983230072969 + 3 ^ 40 * 5565448 * 2
def baseEnd_5565448 : Nat := 2857749881604046392804977

theorem tailTrace_5565448 : CollatzResearch.WordTrace tailWord_5565448 prefixEnd_5565448 2857749881604046392804977 := by
  unfold tailWord_5565448
  simp only [CollatzResearch.WordTrace]
  refine ⟨101494282370669936845056499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135325709827559915793408665 101494282370669936845056499)
  ·
    refine ⟨152241423556004905267584749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101494282370669936845056499 152241423556004905267584749)
    ·
      refine ⟨57090533833501839475344281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152241423556004905267584749 57090533833501839475344281)
      ·
        refine ⟨42817900375126379606508211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57090533833501839475344281 42817900375126379606508211)
        ·
          refine ⟨64226850562689569409762317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42817900375126379606508211 64226850562689569409762317)
          ·
            refine ⟨24085068961008588528660869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64226850562689569409762317 24085068961008588528660869)
            ·
              refine ⟨4515950430189110349123913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24085068961008588528660869 4515950430189110349123913)
              ·
                refine ⟨3386962822641832761842935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4515950430189110349123913 3386962822641832761842935)
                ·
                  refine ⟨5080444233962749142764403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386962822641832761842935 5080444233962749142764403)
                  ·
                    refine ⟨7620666350944123714146605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080444233962749142764403 7620666350944123714146605)
                    ·
                      refine ⟨2857749881604046392804977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620666350944123714146605 2857749881604046392804977)
                      ·
                        rfl

theorem cell23_5565448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_5565448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565448 prefixEnd_5565448 := by exact prefixLift 5565448
  have htrace : WordTrace (prefixWord ++ tailWord_5565448) baseStart_5565448 baseEnd_5565448 := by
    simpa [prefixWord, tailWord_5565448, baseEnd_5565448] using wordTrace_append hprefix tailTrace_5565448
  have hstable : (prefixWord ++ tailWord_5565448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565448).length < 2 ^ (prefixWord ++ tailWord_5565448).sum := by decide
  have hdescent : baseEnd_5565448 < baseStart_5565448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565464 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 2, 4]
def baseStart_5565464 : Nat := 118140960795 + 5565464 * 2 ^ 59
def prefixEnd_5565464 : Nat := 4983230072969 + 3 ^ 40 * 5565464 * 2
def baseEnd_5565464 : Nat := 952586032431506110068301

theorem tailTrace_5565464 : CollatzResearch.WordTrace tailWord_5565464 prefixEnd_5565464 952586032431506110068301 := by
  unfold tailWord_5565464
  simp only [CollatzResearch.WordTrace]
  refine ⟨101494574154640954211347723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135326098872854605615130297 101494574154640954211347723)
  ·
    refine ⟨152241861231961431317021585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101494574154640954211347723 152241861231961431317021585)
    ·
      refine ⟨114181395923971073487766189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152241861231961431317021585 114181395923971073487766189)
      ·
        refine ⟨42818023471489152557912321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114181395923971073487766189 42818023471489152557912321)
        ·
          refine ⟨32113517603616864418434241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42818023471489152557912321 32113517603616864418434241)
          ·
            refine ⟨24085138202712648313825681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32113517603616864418434241 24085138202712648313825681)
            ·
              refine ⟨18063853652034486235369261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24085138202712648313825681 18063853652034486235369261)
              ·
                refine ⟨6773945119512932338263473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18063853652034486235369261 6773945119512932338263473)
                ·
                  refine ⟨5080458839634699253697605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773945119512932338263473 5080458839634699253697605)
                  ·
                    refine ⟨952586032431506110068301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080458839634699253697605 952586032431506110068301)
                    ·
                      rfl

theorem cell23_5565464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_5565464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565464 prefixEnd_5565464 := by exact prefixLift 5565464
  have htrace : WordTrace (prefixWord ++ tailWord_5565464) baseStart_5565464 baseEnd_5565464 := by
    simpa [prefixWord, tailWord_5565464, baseEnd_5565464] using wordTrace_append hprefix tailTrace_5565464
  have hstable : (prefixWord ++ tailWord_5565464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565464).length < 2 ^ (prefixWord ++ tailWord_5565464).sum := by decide
  have hdescent : baseEnd_5565464 < baseStart_5565464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565471 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 3, 2, 2]
def baseStart_5565471 : Nat := 118140960795 + 5565471 * 2 ^ 59
def prefixEnd_5565471 : Nat := 4983230072969 + 3 ^ 40 * 5565471 * 2
def baseEnd_5565471 : Nat := 2857761691659099802817371

theorem tailTrace_5565471 : CollatzResearch.WordTrace tailWord_5565471 prefixEnd_5565471 2857761691659099802817371 := by
  unfold tailWord_5565471
  simp only [CollatzResearch.WordTrace]
  refine ⟨202989403620256548618200267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135326269080171032412133511 202989403620256548618200267)
  ·
    refine ⟨304484105430384822927300401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202989403620256548618200267 304484105430384822927300401)
    ·
      refine ⟨228363079072788617195475301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304484105430384822927300401 228363079072788617195475301)
      ·
        refine ⟨42818077326147865724151619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228363079072788617195475301 42818077326147865724151619)
        ·
          refine ⟨64227115989221798586227429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42818077326147865724151619 64227115989221798586227429)
          ·
            refine ⟨12042584247979087234917643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64227115989221798586227429 12042584247979087234917643)
            ·
              refine ⟨18063876371968630852376465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12042584247979087234917643 18063876371968630852376465)
              ·
                refine ⟨13547907278976473139282349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18063876371968630852376465 13547907278976473139282349)
                ·
                  refine ⟨5080465229616177427230881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13547907278976473139282349 5080465229616177427230881)
                  ·
                    refine ⟨3810348922212133070423161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080465229616177427230881 3810348922212133070423161)
                    ·
                      refine ⟨2857761691659099802817371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810348922212133070423161 2857761691659099802817371)
                      ·
                        rfl

theorem cell23_5565471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_5565471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565471 prefixEnd_5565471 := by exact prefixLift 5565471
  have htrace : WordTrace (prefixWord ++ tailWord_5565471) baseStart_5565471 baseEnd_5565471 := by
    simpa [prefixWord, tailWord_5565471, baseEnd_5565471] using wordTrace_append hprefix tailTrace_5565471
  have hstable : (prefixWord ++ tailWord_5565471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565471).length < 2 ^ (prefixWord ++ tailWord_5565471).sum := by decide
  have hdescent : baseEnd_5565471 < baseStart_5565471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565474 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_5565474 : Nat := 118140960795 + 5565474 * 2 ^ 59
def prefixEnd_5565474 : Nat := 4983230072969 + 3 ^ 40 * 5565474 * 2
def baseEnd_5565474 : Nat := 2857763232101063291079857

theorem tailTrace_5565474 : CollatzResearch.WordTrace tailWord_5565474 prefixEnd_5565474 2857763232101063291079857 := by
  unfold tailWord_5565474
  simp only [CollatzResearch.WordTrace]
  refine ⟨50747378259811420032639869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135326342026163786753706317 50747378259811420032639869)
  ·
    refine ⟨19030266847429282512239951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50747378259811420032639869 19030266847429282512239951)
    ·
      refine ⟨28545400271143923768359927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19030266847429282512239951 28545400271143923768359927)
      ·
        refine ⟨42818100406715885652539891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28545400271143923768359927 42818100406715885652539891)
        ·
          refine ⟨64227150610073828478809837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42818100406715885652539891 64227150610073828478809837)
          ·
            refine ⟨24085181478777685679553689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64227150610073828478809837 24085181478777685679553689)
            ·
              refine ⟨18063886109083264259665267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24085181478777685679553689 18063886109083264259665267)
              ·
                refine ⟨27095829163624896389497901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18063886109083264259665267 27095829163624896389497901)
                ·
                  refine ⟨10160935936359336146061713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27095829163624896389497901 10160935936359336146061713)
                  ·
                    refine ⟨7620701952269502109546285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10160935936359336146061713 7620701952269502109546285)
                    ·
                      refine ⟨2857763232101063291079857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620701952269502109546285 2857763232101063291079857)
                      ·
                        rfl

theorem cell23_5565474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_5565474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565474 prefixEnd_5565474 := by exact prefixLift 5565474
  have htrace : WordTrace (prefixWord ++ tailWord_5565474) baseStart_5565474 baseEnd_5565474 := by
    simpa [prefixWord, tailWord_5565474, baseEnd_5565474] using wordTrace_append hprefix tailTrace_5565474
  have hstable : (prefixWord ++ tailWord_5565474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565474).length < 2 ^ (prefixWord ++ tailWord_5565474).sum := by decide
  have hdescent : baseEnd_5565474 < baseStart_5565474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565477 : List Nat := [1, 3, 1, 2, 2, 2, 5, 7]
def baseStart_5565477 : Nat := 118140960795 + 5565477 * 2 ^ 59
def prefixEnd_5565477 : Nat := 4983230072969 + 3 ^ 40 * 5565477 * 2
def baseEnd_5565477 : Nat := 105843139723815806642309

theorem tailTrace_5565477 : CollatzResearch.WordTrace tailWord_5565477 prefixEnd_5565477 105843139723815806642309 := by
  unfold tailWord_5565477
  simp only [CollatzResearch.WordTrace]
  refine ⟨202989622458234811642918685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135326414972156541095279123 202989622458234811642918685)
  ·
    refine ⟨76121108421838054366094507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202989622458234811642918685 76121108421838054366094507)
    ·
      refine ⟨114181662632757081549141761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76121108421838054366094507 114181662632757081549141761)
      ·
        refine ⟨85636246974567811161856321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114181662632757081549141761 85636246974567811161856321)
        ·
          refine ⟨64227185230925858371392241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85636246974567811161856321 64227185230925858371392241)
          ·
            refine ⟨48170388923194393778544181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64227185230925858371392241 48170388923194393778544181)
            ·
              refine ⟨4515973961549474416738517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48170388923194393778544181 4515973961549474416738517)
              ·
                refine ⟨105843139723815806642309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4515973961549474416738517 105843139723815806642309)
                ·
                  rfl

theorem cell23_5565477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 7].length) (baseStart_5565477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565477 prefixEnd_5565477 := by exact prefixLift 5565477
  have htrace : WordTrace (prefixWord ++ tailWord_5565477) baseStart_5565477 baseEnd_5565477 := by
    simpa [prefixWord, tailWord_5565477, baseEnd_5565477] using wordTrace_append hprefix tailTrace_5565477
  have hstable : (prefixWord ++ tailWord_5565477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565477).length < 2 ^ (prefixWord ++ tailWord_5565477).sum := by decide
  have hdescent : baseEnd_5565477 < baseStart_5565477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565488 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 1, 2, 2]
def baseStart_5565488 : Nat := 118140960795 + 5565488 * 2 ^ 59
def prefixEnd_5565488 : Nat := 4983230072969 + 3 ^ 40 * 5565488 * 2
def baseEnd_5565488 : Nat := 2857770420830226236304793

theorem tailTrace_5565488 : CollatzResearch.WordTrace tailWord_5565488 prefixEnd_5565488 2857770420830226236304793 := by
  unfold tailWord_5565488
  simp only [CollatzResearch.WordTrace]
  refine ⟨101495011830597480260784559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135326682440796640347712745 101495011830597480260784559)
  ·
    refine ⟨152242517745896220391176839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101495011830597480260784559 152242517745896220391176839)
    ·
      refine ⟨228363776618844330586765259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152242517745896220391176839 228363776618844330586765259)
      ·
        refine ⟨342545664928266495880147889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228363776618844330586765259 342545664928266495880147889)
        ·
          refine ⟨256909248696199871910110917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342545664928266495880147889 256909248696199871910110917)
          ·
            refine ⟨48170484130537475983145797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256909248696199871910110917 48170484130537475983145797)
            ·
              refine ⟨9031965774475776746839837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48170484130537475983145797 9031965774475776746839837)
              ·
                refine ⟨3386987165428416280064939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9031965774475776746839837 3386987165428416280064939)
                ·
                  refine ⟨5080480748142624420097409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386987165428416280064939 5080480748142624420097409)
                  ·
                    refine ⟨3810360561106968315073057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080480748142624420097409 3810360561106968315073057)
                    ·
                      refine ⟨2857770420830226236304793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810360561106968315073057 2857770420830226236304793)
                      ·
                        rfl

theorem cell23_5565488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 2, 2].length) (baseStart_5565488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565488 prefixEnd_5565488 := by exact prefixLift 5565488
  have htrace : WordTrace (prefixWord ++ tailWord_5565488) baseStart_5565488 baseEnd_5565488 := by
    simpa [prefixWord, tailWord_5565488, baseEnd_5565488] using wordTrace_append hprefix tailTrace_5565488
  have hstable : (prefixWord ++ tailWord_5565488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565488).length < 2 ^ (prefixWord ++ tailWord_5565488).sum := by decide
  have hdescent : baseEnd_5565488 < baseStart_5565488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565504 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 4, 1, 3]
def baseStart_5565504 : Nat := 118140960795 + 5565504 * 2 ^ 59
def prefixEnd_5565504 : Nat := 4983230072969 + 3 ^ 40 * 5565504 * 2
def baseEnd_5565504 : Nat := 2857778636520698173704719

theorem tailTrace_5565504 : CollatzResearch.WordTrace tailWord_5565504 prefixEnd_5565504 2857778636520698173704719 := by
  unfold tailWord_5565504
  simp only [CollatzResearch.WordTrace]
  refine ⟨101495303614568497627075783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135327071486091330169434377 101495303614568497627075783)
  ·
    refine ⟨152242955421852746440613675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101495303614568497627075783 152242955421852746440613675)
    ·
      refine ⟨228364433132779119660920513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152242955421852746440613675 228364433132779119660920513)
      ·
        refine ⟨171273324849584339745690385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228364433132779119660920513 171273324849584339745690385)
        ·
          refine ⟨128454993637188254809267789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171273324849584339745690385 128454993637188254809267789)
          ·
            refine ⟨48170622613945595553475421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128454993637188254809267789 48170622613945595553475421)
            ·
              refine ⟨18063983480229598332553283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48170622613945595553475421 18063983480229598332553283)
              ·
                refine ⟨27095975220344397498829925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18063983480229598332553283 27095975220344397498829925)
                ·
                  refine ⟨5080495353814574531030611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27095975220344397498829925 5080495353814574531030611)
                  ·
                    refine ⟨7620743030721861796545917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080495353814574531030611 7620743030721861796545917)
                    ·
                      refine ⟨2857778636520698173704719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7620743030721861796545917 2857778636520698173704719)
                      ·
                        rfl

theorem cell23_5565504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_5565504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565504 prefixEnd_5565504 := by exact prefixLift 5565504
  have htrace : WordTrace (prefixWord ++ tailWord_5565504) baseStart_5565504 baseEnd_5565504 := by
    simpa [prefixWord, tailWord_5565504, baseEnd_5565504] using wordTrace_append hprefix tailTrace_5565504
  have hstable : (prefixWord ++ tailWord_5565504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565504).length < 2 ^ (prefixWord ++ tailWord_5565504).sum := by decide
  have hdescent : baseEnd_5565504 < baseStart_5565504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565514 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_5565514 : Nat := 118140960795 + 5565514 * 2 ^ 59
def prefixEnd_5565514 : Nat := 4983230072969 + 3 ^ 40 * 5565514 * 2
def baseEnd_5565514 : Nat := 2857783771327243134579673

theorem tailTrace_5565514 : CollatzResearch.WordTrace tailWord_5565514 prefixEnd_5565514 2857783771327243134579673 := by
  unfold tailWord_5565514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50747742989775191740503899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135327314639400511308010397 50747742989775191740503899)
  ·
    refine ⟨76121614484662787610755849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50747742989775191740503899 76121614484662787610755849)
    ·
      refine ⟨57091210863497090708066887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76121614484662787610755849 57091210863497090708066887)
      ·
        refine ⟨85636816295245636062100331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57091210863497090708066887 85636816295245636062100331)
        ·
          refine ⟨128455224442868454093150497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85636816295245636062100331 128455224442868454093150497)
          ·
            refine ⟨96341418332151340569862873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128455224442868454093150497 96341418332151340569862873)
            ·
              refine ⟨72256063749113505427397155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96341418332151340569862873 72256063749113505427397155)
              ·
                refine ⟨108384095623670258141095733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72256063749113505427397155 108384095623670258141095733)
                ·
                  refine ⟨10161008964719086700727725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108384095623670258141095733 10161008964719086700727725)
                  ·
                    refine ⟨3810378361769657512772897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10161008964719086700727725 3810378361769657512772897)
                    ·
                      refine ⟨2857783771327243134579673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810378361769657512772897 2857783771327243134579673)
                      ·
                        rfl

theorem cell23_5565514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_5565514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565514 prefixEnd_5565514 := by exact prefixLift 5565514
  have htrace : WordTrace (prefixWord ++ tailWord_5565514) baseStart_5565514 baseEnd_5565514 := by
    simpa [prefixWord, tailWord_5565514, baseEnd_5565514] using wordTrace_append hprefix tailTrace_5565514
  have hstable : (prefixWord ++ tailWord_5565514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565514).length < 2 ^ (prefixWord ++ tailWord_5565514).sum := by decide
  have hdescent : baseEnd_5565514 < baseStart_5565514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565578 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_5565578 : Nat := 118140960795 + 5565578 * 2 ^ 59
def prefixEnd_5565578 : Nat := 4983230072969 + 3 ^ 40 * 5565578 * 2
def baseEnd_5565578 : Nat := 2857816634089130884179379

theorem tailTrace_5565578 : CollatzResearch.WordTrace tailWord_5565578 prefixEnd_5565578 2857816634089130884179379 := by
  unfold tailWord_5565578
  simp only [CollatzResearch.WordTrace]
  refine ⟨50748326557717226473086347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135328870820579270594896925 50748326557717226473086347)
  ·
    refine ⟨76122489836575839709629521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50748326557717226473086347 76122489836575839709629521)
    ·
      refine ⟨57091867377431879782222141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76122489836575839709629521 57091867377431879782222141)
      ·
        refine ⟨21409450266536954918333303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57091867377431879782222141 21409450266536954918333303)
        ·
          refine ⟨32114175399805432377499955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21409450266536954918333303 32114175399805432377499955)
          ·
            refine ⟨48171263099708148566249933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32114175399805432377499955 48171263099708148566249933)
            ·
              refine ⟨18064223662390555712343725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48171263099708148566249933 18064223662390555712343725)
              ·
                refine ⟨6774083873396458392128897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18064223662390555712343725 6774083873396458392128897)
                ·
                  refine ⟨5080562905047343794096673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6774083873396458392128897 5080562905047343794096673)
                  ·
                    refine ⟨3810422178785507845572505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080562905047343794096673 3810422178785507845572505)
                    ·
                      refine ⟨2857816634089130884179379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810422178785507845572505 2857816634089130884179379)
                      ·
                        rfl

theorem cell23_5565578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_5565578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565578 prefixEnd_5565578 := by exact prefixLift 5565578
  have htrace : WordTrace (prefixWord ++ tailWord_5565578) baseStart_5565578 baseEnd_5565578 := by
    simpa [prefixWord, tailWord_5565578, baseEnd_5565578] using wordTrace_append hprefix tailTrace_5565578
  have hstable : (prefixWord ++ tailWord_5565578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565578).length < 2 ^ (prefixWord ++ tailWord_5565578).sum := by decide
  have hdescent : baseEnd_5565578 < baseStart_5565578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565618 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_5565618 : Nat := 118140960795 + 5565618 * 2 ^ 59
def prefixEnd_5565618 : Nat := 4983230072969 + 3 ^ 40 * 5565618 * 2
def baseEnd_5565618 : Nat := 317537463701701191964355

theorem tailTrace_5565618 : CollatzResearch.WordTrace tailWord_5565618 prefixEnd_5565618 317537463701701191964355 := by
  unfold tailWord_5565618
  simp only [CollatzResearch.WordTrace]
  refine ⟨50748691287680998180950377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135329843433815995149201005 50748691287680998180950377)
  ·
    refine ⟨38061518465760748635712783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50748691287680998180950377 38061518465760748635712783)
    ·
      refine ⟨57092277698641122953569175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38061518465760748635712783 57092277698641122953569175)
      ·
        refine ⟨85638416547961684430353763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57092277698641122953569175 85638416547961684430353763)
        ·
          refine ⟨128457624821942526645530645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85638416547961684430353763 128457624821942526645530645)
          ·
            refine ⟨6021451163528555936509249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128457624821942526645530645 6021451163528555936509249)
            ·
              refine ⟨4516088372646416952381937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6021451163528555936509249 4516088372646416952381937)
              ·
                refine ⟨3387066279484812714286453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4516088372646416952381937 3387066279484812714286453)
                ·
                  refine ⟨317537463701701191964355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387066279484812714286453 317537463701701191964355)
                  ·
                    rfl

theorem cell23_5565618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_5565618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565618 prefixEnd_5565618 := by exact prefixLift 5565618
  have htrace : WordTrace (prefixWord ++ tailWord_5565618) baseStart_5565618 baseEnd_5565618 := by
    simpa [prefixWord, tailWord_5565618, baseEnd_5565618] using wordTrace_append hprefix tailTrace_5565618
  have hstable : (prefixWord ++ tailWord_5565618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565618).length < 2 ^ (prefixWord ++ tailWord_5565618).sum := by decide
  have hdescent : baseEnd_5565618 < baseStart_5565618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565647 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_5565647 : Nat := 118140960795 + 5565647 * 2 ^ 59
def prefixEnd_5565647 : Nat := 4983230072969 + 3 ^ 40 * 5565647 * 2
def baseEnd_5565647 : Nat := 2857852064254291114216561

theorem tailTrace_5565647 : CollatzResearch.WordTrace tailWord_5565647 prefixEnd_5565647 2857852064254291114216561 := by
  unfold tailWord_5565647
  simp only [CollatzResearch.WordTrace]
  refine ⟨202995822867618930676607195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135330548578412620451071463 202995822867618930676607195)
  ·
    refine ⟨304493734301428396014910793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202995822867618930676607195 304493734301428396014910793)
    ·
      refine ⟨228370300726071297011183095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304493734301428396014910793 228370300726071297011183095)
      ·
        refine ⟨342555451089106945516774643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228370300726071297011183095 342555451089106945516774643)
        ·
          refine ⟨513833176633660418275161965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342555451089106945516774643 513833176633660418275161965)
          ·
            refine ⟨192687441237622656853185737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513833176633660418275161965 192687441237622656853185737)
            ·
              refine ⟨144515580928216992639889303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192687441237622656853185737 144515580928216992639889303)
              ·
                refine ⟨216773371392325488959833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144515580928216992639889303 216773371392325488959833955)
                ·
                  refine ⟨325160057088488233439750933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216773371392325488959833955 325160057088488233439750933)
                  ·
                    refine ⟨15241877676022885942488325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 325160057088488233439750933 15241877676022885942488325)
                    ·
                      refine ⟨2857852064254291114216561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15241877676022885942488325 2857852064254291114216561)
                      ·
                        rfl

theorem cell23_5565647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_5565647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565647 prefixEnd_5565647 := by exact prefixLift 5565647
  have htrace : WordTrace (prefixWord ++ tailWord_5565647) baseStart_5565647 baseEnd_5565647 := by
    simpa [prefixWord, tailWord_5565647, baseEnd_5565647] using wordTrace_append hprefix tailTrace_5565647
  have hstable : (prefixWord ++ tailWord_5565647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565647).length < 2 ^ (prefixWord ++ tailWord_5565647).sum := by decide
  have hdescent : baseEnd_5565647 < baseStart_5565647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565657 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 8]
def baseStart_5565657 : Nat := 118140960795 + 5565657 * 2 ^ 59
def prefixEnd_5565657 : Nat := 4983230072969 + 3 ^ 40 * 5565657 * 2
def baseEnd_5565657 : Nat := 317539688784537341676835

theorem tailTrace_5565657 : CollatzResearch.WordTrace tailWord_5565657 prefixEnd_5565657 317539688784537341676835 := by
  unfold tailWord_5565657
  simp only [CollatzResearch.WordTrace]
  refine ⟨202996187597582702384471225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135330791731721801589647483 202996187597582702384471225)
  ·
    refine ⟨152247140698187026788353419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202996187597582702384471225 152247140698187026788353419)
    ·
      refine ⟨228370711047280540182530129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152247140698187026788353419 228370711047280540182530129)
      ·
        refine ⟨171278033285460405136897597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228370711047280540182530129 171278033285460405136897597)
        ·
          refine ⟨64229262482047651926336599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171278033285460405136897597 64229262482047651926336599)
          ·
            refine ⟨96343893723071477889504899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64229262482047651926336599 96343893723071477889504899)
            ·
              refine ⟨144515840584607216834257349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96343893723071477889504899 144515840584607216834257349)
              ·
                refine ⟨27096720109613853156423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144515840584607216834257349 27096720109613853156423253)
                ·
                  refine ⟨317539688784537341676835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27096720109613853156423253 317539688784537341676835)
                  ·
                    rfl

theorem cell23_5565657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_5565657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565657 prefixEnd_5565657 := by exact prefixLift 5565657
  have htrace : WordTrace (prefixWord ++ tailWord_5565657) baseStart_5565657 baseEnd_5565657 := by
    simpa [prefixWord, tailWord_5565657, baseEnd_5565657] using wordTrace_append hprefix tailTrace_5565657
  have hstable : (prefixWord ++ tailWord_5565657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565657).length < 2 ^ (prefixWord ++ tailWord_5565657).sum := by decide
  have hdescent : baseEnd_5565657 < baseStart_5565657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565674 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_5565674 : Nat := 118140960795 + 5565674 * 2 ^ 59
def prefixEnd_5565674 : Nat := 4983230072969 + 3 ^ 40 * 5565674 * 2
def baseEnd_5565674 : Nat := 317540658692440278730993

theorem tailTrace_5565674 : CollatzResearch.WordTrace tailWord_5565674 prefixEnd_5565674 317540658692440278730993 := by
  unfold tailWord_5565674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50749201909630278571960019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135331205092347409525226717 50749201909630278571960019)
  ·
    refine ⟨76123802864445417857940029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50749201909630278571960019 76123802864445417857940029)
    ·
      refine ⟨28546426074167031696727511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76123802864445417857940029 28546426074167031696727511)
      ·
        refine ⟨42819639111250547545091267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28546426074167031696727511 42819639111250547545091267)
        ·
          refine ⟨64229458666875821317636901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42819639111250547545091267 64229458666875821317636901)
          ·
            refine ⟨12043023500039216497056919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64229458666875821317636901 12043023500039216497056919)
            ·
              refine ⟨18064535250058824745585379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12043023500039216497056919 18064535250058824745585379)
              ·
                refine ⟨27096802875088237118378069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18064535250058824745585379 27096802875088237118378069)
                ·
                  refine ⟨317540658692440278730993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27096802875088237118378069 317540658692440278730993)
                  ·
                    rfl

theorem cell23_5565674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_5565674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565674 prefixEnd_5565674 := by exact prefixLift 5565674
  have htrace : WordTrace (prefixWord ++ tailWord_5565674) baseStart_5565674 baseEnd_5565674 := by
    simpa [prefixWord, tailWord_5565674, baseEnd_5565674] using wordTrace_append hprefix tailTrace_5565674
  have hstable : (prefixWord ++ tailWord_5565674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565674).length < 2 ^ (prefixWord ++ tailWord_5565674).sum := by decide
  have hdescent : baseEnd_5565674 < baseStart_5565674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565678 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_5565678 : Nat := 118140960795 + 5565678 * 2 ^ 59
def prefixEnd_5565678 : Nat := 4983230072969 + 3 ^ 40 * 5565678 * 2
def baseEnd_5565678 : Nat := 952622660718193497642973

theorem tailTrace_5565678 : CollatzResearch.WordTrace tailWord_5565678 prefixEnd_5565678 952622660718193497642973 := by
  unfold tailWord_5565678
  simp only [CollatzResearch.WordTrace]
  refine ⟨25374619191313327871373211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135331302353671081980657125 25374619191313327871373211)
  ·
    refine ⟨38061928786969991807059817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25374619191313327871373211 38061928786969991807059817)
    ·
      refine ⟨28546446590227493855294863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38061928786969991807059817 28546446590227493855294863)
      ·
        refine ⟨42819669885341240782942295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28546446590227493855294863 42819669885341240782942295)
        ·
          refine ⟨64229504828011861174413443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42819669885341240782942295 64229504828011861174413443)
          ·
            refine ⟨96344257242017791761620165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64229504828011861174413443 96344257242017791761620165)
            ·
              refine ⟨18064548232878335955303781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96344257242017791761620165 18064548232878335955303781)
              ·
                refine ⟨3387102793664687991619459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18064548232878335955303781 3387102793664687991619459)
                ·
                  refine ⟨5080654190497031987429189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387102793664687991619459 5080654190497031987429189)
                  ·
                    refine ⟨952622660718193497642973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080654190497031987429189 952622660718193497642973)
                    ·
                      rfl

theorem cell23_5565678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_5565678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565678 prefixEnd_5565678 := by exact prefixLift 5565678
  have htrace : WordTrace (prefixWord ++ tailWord_5565678) baseStart_5565678 baseEnd_5565678 := by
    simpa [prefixWord, tailWord_5565678, baseEnd_5565678] using wordTrace_append hprefix tailTrace_5565678
  have hstable : (prefixWord ++ tailWord_5565678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565678).length < 2 ^ (prefixWord ++ tailWord_5565678).sum := by decide
  have hdescent : baseEnd_5565678 < baseStart_5565678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565701 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_5565701 : Nat := 118140960795 + 5565701 * 2 ^ 59
def prefixEnd_5565701 : Nat := 4983230072969 + 3 ^ 40 * 5565701 * 2
def baseEnd_5565701 : Nat := 2857879792209633902941313

theorem tailTrace_5565701 : CollatzResearch.WordTrace tailWord_5565701 prefixEnd_5565701 2857879792209633902941313 := by
  unfold tailWord_5565701
  simp only [CollatzResearch.WordTrace]
  refine ⟨202997792409423297899072957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135331861606282198599381971 202997792409423297899072957)
  ·
    refine ⟨76124172153533736712152359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202997792409423297899072957 76124172153533736712152359)
    ·
      refine ⟨114186258230300605068228539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76124172153533736712152359 114186258230300605068228539)
      ·
        refine ⟨171279387345450907602342809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114186258230300605068228539 171279387345450907602342809)
        ·
          refine ⟨128459540509088180701757107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171279387345450907602342809 128459540509088180701757107)
          ·
            refine ⟨192689310763632271052635661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128459540509088180701757107 192689310763632271052635661)
            ·
              refine ⟨72258491536362101644738373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192689310763632271052635661 72258491536362101644738373)
              ·
                refine ⟨13548467163067894058388445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72258491536362101644738373 13548467163067894058388445)
                ·
                  refine ⟨5080675186150460271895667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13548467163067894058388445 5080675186150460271895667)
                  ·
                    refine ⟨7621012779225690407843501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080675186150460271895667 7621012779225690407843501)
                    ·
                      refine ⟨2857879792209633902941313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7621012779225690407843501 2857879792209633902941313)
                      ·
                        rfl

theorem cell23_5565701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_5565701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565701 prefixEnd_5565701 := by exact prefixLift 5565701
  have htrace : WordTrace (prefixWord ++ tailWord_5565701) baseStart_5565701 baseEnd_5565701 := by
    simpa [prefixWord, tailWord_5565701, baseEnd_5565701] using wordTrace_append hprefix tailTrace_5565701
  have hstable : (prefixWord ++ tailWord_5565701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565701).length < 2 ^ (prefixWord ++ tailWord_5565701).sum := by decide
  have hdescent : baseEnd_5565701 < baseStart_5565701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565744 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_5565744 : Nat := 118140960795 + 5565744 * 2 ^ 59
def prefixEnd_5565744 : Nat := 4983230072969 + 3 ^ 40 * 5565744 * 2
def baseEnd_5565744 : Nat := 2857901871877777234703615

theorem tailTrace_5565744 : CollatzResearch.WordTrace tailWord_5565744 prefixEnd_5565744 2857901871877777234703615 := by
  unfold tailWord_5565744
  simp only [CollatzResearch.WordTrace]
  refine ⟨101499680374133758121444143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135332907165511677495258857 101499680374133758121444143)
  ·
    refine ⟨152249520561200637182166215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101499680374133758121444143 152249520561200637182166215)
    ·
      refine ⟨228374280841800955773249323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152249520561200637182166215 228374280841800955773249323)
      ·
        refine ⟨342561421262701433659873985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228374280841800955773249323 342561421262701433659873985)
        ·
          refine ⟨256921065947026075244905489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342561421262701433659873985 256921065947026075244905489)
          ·
            refine ⟨192690799460269556433679117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256921065947026075244905489 192690799460269556433679117)
            ·
              refine ⟨72259049797601083662629669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192690799460269556433679117 72259049797601083662629669)
              ·
                refine ⟨13548571837050203186743063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72259049797601083662629669 13548571837050203186743063)
                ·
                  refine ⟨20322857755575304780114595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13548571837050203186743063 20322857755575304780114595)
                  ·
                    refine ⟨30484286633362957170171893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20322857755575304780114595 30484286633362957170171893)
                    ·
                      refine ⟨2857901871877777234703615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30484286633362957170171893 2857901871877777234703615)
                      ·
                        rfl

theorem cell23_5565744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_5565744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565744 prefixEnd_5565744 := by exact prefixLift 5565744
  have htrace : WordTrace (prefixWord ++ tailWord_5565744) baseStart_5565744 baseEnd_5565744 := by
    simpa [prefixWord, tailWord_5565744, baseEnd_5565744] using wordTrace_append hprefix tailTrace_5565744
  have hstable : (prefixWord ++ tailWord_5565744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565744).length < 2 ^ (prefixWord ++ tailWord_5565744).sum := by decide
  have hdescent : baseEnd_5565744 < baseStart_5565744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565754 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_5565754 : Nat := 118140960795 + 5565754 * 2 ^ 59
def prefixEnd_5565754 : Nat := 4983230072969 + 3 ^ 40 * 5565754 * 2
def baseEnd_5565754 : Nat := 2857907006684322195578569

theorem tailTrace_5565754 : CollatzResearch.WordTrace tailWord_5565754 prefixEnd_5565754 2857907006684322195578569 := by
  unfold tailWord_5565754
  simp only [CollatzResearch.WordTrace]
  refine ⟨50749931369557821987688079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135333150318820858633834877 50749931369557821987688079)
  ·
    refine ⟨76124897054336732981532119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50749931369557821987688079 76124897054336732981532119)
    ·
      refine ⟨114187345581505099472298179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76124897054336732981532119 114187345581505099472298179)
      ·
        refine ⟨171281018372257649208447269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114187345581505099472298179 171281018372257649208447269)
        ·
          refine ⟨32115190944798309226583863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171281018372257649208447269 32115190944798309226583863)
          ·
            refine ⟨48172786417197463839875795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32115190944798309226583863 48172786417197463839875795)
            ·
              refine ⟨72259179625796195759813693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48172786417197463839875795 72259179625796195759813693)
              ·
                refine ⟨27097192359673573409930135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72259179625796195759813693 27097192359673573409930135)
                ·
                  refine ⟨40645788539510360114895203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27097192359673573409930135 40645788539510360114895203)
                  ·
                    refine ⟨60968682809265540172342805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40645788539510360114895203 60968682809265540172342805)
                    ·
                      refine ⟨2857907006684322195578569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60968682809265540172342805 2857907006684322195578569)
                      ·
                        rfl

theorem cell23_5565754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_5565754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565754 prefixEnd_5565754 := by exact prefixLift 5565754
  have htrace : WordTrace (prefixWord ++ tailWord_5565754) baseStart_5565754 baseEnd_5565754 := by
    simpa [prefixWord, tailWord_5565754, baseEnd_5565754] using wordTrace_append hprefix tailTrace_5565754
  have hstable : (prefixWord ++ tailWord_5565754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565754).length < 2 ^ (prefixWord ++ tailWord_5565754).sum := by decide
  have hdescent : baseEnd_5565754 < baseStart_5565754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565792 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 1, 2, 2]
def baseStart_5565792 : Nat := 118140960795 + 5565792 * 2 ^ 59
def prefixEnd_5565792 : Nat := 4983230072969 + 3 ^ 40 * 5565792 * 2
def baseEnd_5565792 : Nat := 2857926518949193046903395

theorem tailTrace_5565792 : CollatzResearch.WordTrace tailWord_5565792 prefixEnd_5565792 2857926518949193046903395 := by
  unfold tailWord_5565792
  simp only [CollatzResearch.WordTrace]
  refine ⟨101500555726046810220317815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135334074301395746960423753 101500555726046810220317815)
  ·
    refine ⟨152250833589070215330476723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101500555726046810220317815 152250833589070215330476723)
    ·
      refine ⟨228376250383605322995715085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152250833589070215330476723 228376250383605322995715085)
      ·
        refine ⟨85641093893851996123393157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228376250383605322995715085 85641093893851996123393157)
        ·
          refine ⟨16057705105097249273136217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85641093893851996123393157 16057705105097249273136217)
          ·
            refine ⟨12043278828822936954852163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16057705105097249273136217 12043278828822936954852163)
            ·
              refine ⟨18064918243234405432278245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12043278828822936954852163 18064918243234405432278245)
              ·
                refine ⟨3387172170606451018552171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18064918243234405432278245 3387172170606451018552171)
                ·
                  refine ⟨5080758255909676527828257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387172170606451018552171 5080758255909676527828257)
                  ·
                    refine ⟨3810568691932257395871193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080758255909676527828257 3810568691932257395871193)
                    ·
                      refine ⟨2857926518949193046903395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810568691932257395871193 2857926518949193046903395)
                      ·
                        rfl

theorem cell23_5565792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_5565792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565792 prefixEnd_5565792 := by exact prefixLift 5565792
  have htrace : WordTrace (prefixWord ++ tailWord_5565792) baseStart_5565792 baseEnd_5565792 := by
    simpa [prefixWord, tailWord_5565792, baseEnd_5565792] using wordTrace_append hprefix tailTrace_5565792
  have hstable : (prefixWord ++ tailWord_5565792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565792).length < 2 ^ (prefixWord ++ tailWord_5565792).sum := by decide
  have hdescent : baseEnd_5565792 < baseStart_5565792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565808 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 2, 1, 3]
def baseStart_5565808 : Nat := 118140960795 + 5565808 * 2 ^ 59
def prefixEnd_5565808 : Nat := 4983230072969 + 3 ^ 40 * 5565808 * 2
def baseEnd_5565808 : Nat := 2857934734639664984303321

theorem tailTrace_5565808 : CollatzResearch.WordTrace tailWord_5565808 prefixEnd_5565808 2857934734639664984303321 := by
  unfold tailWord_5565808
  simp only [CollatzResearch.WordTrace]
  refine ⟨101500847510017827586609039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135334463346690436782145385 101500847510017827586609039)
  ·
    refine ⟨152251271265026741379913559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101500847510017827586609039 152251271265026741379913559)
    ·
      refine ⟨228376906897540112069870339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152251271265026741379913559 228376906897540112069870339)
      ·
        refine ⟨342565360346310168104805509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228376906897540112069870339 342565360346310168104805509)
        ·
          refine ⟨64231005064933156519651033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342565360346310168104805509 64231005064933156519651033)
          ·
            refine ⟨48173253798699867389738275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64231005064933156519651033 48173253798699867389738275)
            ·
              refine ⟨72259880698049801084607413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48173253798699867389738275 72259880698049801084607413)
              ·
                refine ⟨6774363815442168851681945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72259880698049801084607413 6774363815442168851681945)
                ·
                  refine ⟨5080772861581626638761459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6774363815442168851681945 5080772861581626638761459)
                  ·
                    refine ⟨7621159292372439958142189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080772861581626638761459 7621159292372439958142189)
                    ·
                      refine ⟨2857934734639664984303321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7621159292372439958142189 2857934734639664984303321)
                      ·
                        rfl

theorem cell23_5565808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_5565808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565808 prefixEnd_5565808 := by exact prefixLift 5565808
  have htrace : WordTrace (prefixWord ++ tailWord_5565808) baseStart_5565808 baseEnd_5565808 := by
    simpa [prefixWord, tailWord_5565808, baseEnd_5565808] using wordTrace_append hprefix tailTrace_5565808
  have hstable : (prefixWord ++ tailWord_5565808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565808).length < 2 ^ (prefixWord ++ tailWord_5565808).sum := by decide
  have hdescent : baseEnd_5565808 < baseStart_5565808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565826 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5565826 : Nat := 118140960795 + 5565826 * 2 ^ 59
def prefixEnd_5565826 : Nat := 4983230072969 + 3 ^ 40 * 5565826 * 2
def baseEnd_5565826 : Nat := 2857943977291445913878239

theorem tailTrace_5565826 : CollatzResearch.WordTrace tailWord_5565826 prefixEnd_5565826 2857943977291445913878239 := by
  unfold tailWord_5565826
  simp only [CollatzResearch.WordTrace]
  refine ⟨50750587883492611061843333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135334901022646962831582221 50750587883492611061843333)
  ·
    refine ⟨9515735228154864574095625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50750587883492611061843333 9515735228154864574095625)
    ·
      refine ⟨7136801421116148430571719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9515735228154864574095625 7136801421116148430571719)
      ·
        refine ⟨10705202131674222645857579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136801421116148430571719 10705202131674222645857579)
        ·
          refine ⟨16057803197511333968786369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10705202131674222645857579 16057803197511333968786369)
          ·
            refine ⟨12043352398133500476589777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16057803197511333968786369 12043352398133500476589777)
            ·
              refine ⟨9032514298600125357442333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12043352398133500476589777 9032514298600125357442333)
              ·
                refine ⟨3387192861975047009040875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9032514298600125357442333 3387192861975047009040875)
                ·
                  refine ⟨5080789292962570513561313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387192861975047009040875 5080789292962570513561313)
                  ·
                    refine ⟨3810591969721927885170985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5080789292962570513561313 3810591969721927885170985)
                    ·
                      refine ⟨2857943977291445913878239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810591969721927885170985 2857943977291445913878239)
                      ·
                        rfl

theorem cell23_5565826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5565826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565826 prefixEnd_5565826 := by exact prefixLift 5565826
  have htrace : WordTrace (prefixWord ++ tailWord_5565826) baseStart_5565826 baseEnd_5565826 := by
    simpa [prefixWord, tailWord_5565826, baseEnd_5565826] using wordTrace_append hprefix tailTrace_5565826
  have hstable : (prefixWord ++ tailWord_5565826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565826).length < 2 ^ (prefixWord ++ tailWord_5565826).sum := by decide
  have hdescent : baseEnd_5565826 < baseStart_5565826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565842 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5565842 : Nat := 118140960795 + 5565842 * 2 ^ 59
def prefixEnd_5565842 : Nat := 4983230072969 + 3 ^ 40 * 5565842 * 2
def baseEnd_5565842 : Nat := 2857952192981917851278165

theorem tailTrace_5565842 : CollatzResearch.WordTrace tailWord_5565842 prefixEnd_5565842 2857952192981917851278165 := by
  unfold tailWord_5565842
  simp only [CollatzResearch.WordTrace]
  refine ⟨50750733775478119744988945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135335290067941652653303853 50750733775478119744988945)
  ·
    refine ⟨38063050331608589808741709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50750733775478119744988945 38063050331608589808741709)
    ·
      refine ⟨14273643874353221178278141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38063050331608589808741709 14273643874353221178278141)
      ·
        refine ⟨5352616452882457941854303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14273643874353221178278141 5352616452882457941854303)
        ·
          refine ⟨8028924679323686912781455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5352616452882457941854303 8028924679323686912781455)
          ·
            refine ⟨12043387018985530369172183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8028924679323686912781455 12043387018985530369172183)
            ·
              refine ⟨18065080528478295553758275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12043387018985530369172183 18065080528478295553758275)
              ·
                refine ⟨27097620792717443330637413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18065080528478295553758275 27097620792717443330637413)
                ·
                  refine ⟨5080803898634520624494515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27097620792717443330637413 5080803898634520624494515)
                  ·
                    refine ⟨7621205847951780936741773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080803898634520624494515 7621205847951780936741773)
                    ·
                      refine ⟨2857952192981917851278165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7621205847951780936741773 2857952192981917851278165)
                      ·
                        rfl

theorem cell23_5565842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5565842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565842 prefixEnd_5565842 := by exact prefixLift 5565842
  have htrace : WordTrace (prefixWord ++ tailWord_5565842) baseStart_5565842 baseEnd_5565842 := by
    simpa [prefixWord, tailWord_5565842, baseEnd_5565842] using wordTrace_append hprefix tailTrace_5565842
  have hstable : (prefixWord ++ tailWord_5565842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565842).length < 2 ^ (prefixWord ++ tailWord_5565842).sum := by decide
  have hdescent : baseEnd_5565842 < baseStart_5565842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5565888 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 5]
def baseStart_5565888 : Nat := 118140960795 + 5565888 * 2 ^ 59
def prefixEnd_5565888 : Nat := 4983230072969 + 3 ^ 40 * 5565888 * 2
def baseEnd_5565888 : Nat := 317552868121336074589217

theorem tailTrace_5565888 : CollatzResearch.WordTrace tailWord_5565888 prefixEnd_5565888 317552868121336074589217 := by
  unfold tailWord_5565888
  simp only [CollatzResearch.WordTrace]
  refine ⟨101502306429872914418065159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135336408573163885890753545 101502306429872914418065159)
  ·
    refine ⟨152253459644809371627097739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101502306429872914418065159 152253459644809371627097739)
    ·
      refine ⟨228380189467214057440646609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152253459644809371627097739 228380189467214057440646609)
      ·
        refine ⟨171285142100410543080484957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228380189467214057440646609 171285142100410543080484957)
        ·
          refine ⟨64231928287653953655181859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171285142100410543080484957 64231928287653953655181859)
          ·
            refine ⟨96347892431480930482772789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64231928287653953655181859 96347892431480930482772789)
            ·
              refine ⟨9032614915451337232759949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96347892431480930482772789 9032614915451337232759949)
              ·
                refine ⟨3387230593294251462284981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9032614915451337232759949 3387230593294251462284981)
                ·
                  refine ⟨317552868121336074589217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387230593294251462284981 317552868121336074589217)
                  ·
                    rfl

theorem cell23_5565888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 5].length) (baseStart_5565888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5565888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5565888 prefixEnd_5565888 := by exact prefixLift 5565888
  have htrace : WordTrace (prefixWord ++ tailWord_5565888) baseStart_5565888 baseEnd_5565888 := by
    simpa [prefixWord, tailWord_5565888, baseEnd_5565888] using wordTrace_append hprefix tailTrace_5565888
  have hstable : (prefixWord ++ tailWord_5565888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5565888).length < 2 ^ (prefixWord ++ tailWord_5565888).sum := by decide
  have hdescent : baseEnd_5565888 < baseStart_5565888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5565888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566001 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_5566001 : Nat := 118140960795 + 5566001 * 2 ^ 59
def prefixEnd_5566001 : Nat := 4983230072969 + 3 ^ 40 * 5566001 * 2
def baseEnd_5566001 : Nat := 2858033836405982729189933

theorem tailTrace_5566001 : CollatzResearch.WordTrace tailWord_5566001 prefixEnd_5566001 2858033836405982729189933 := by
  unfold tailWord_5566001
  simp only [CollatzResearch.WordTrace]
  refine ⟨203008734308336449134993857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135339156205557632756662571 203008734308336449134993857)
  ·
    refine ⟨152256550731252336851245393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203008734308336449134993857 152256550731252336851245393)
    ·
      refine ⟨114192413048439252638434045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152256550731252336851245393 114192413048439252638434045)
      ·
        refine ⟨42822154893164719739412767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114192413048439252638434045 42822154893164719739412767)
        ·
          refine ⟨64233232339747079609119151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42822154893164719739412767 64233232339747079609119151)
          ·
            refine ⟨96349848509620619413678727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64233232339747079609119151 96349848509620619413678727)
            ·
              refine ⟨144524772764430929120518091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96349848509620619413678727 144524772764430929120518091)
              ·
                refine ⟨216787159146646393680777137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144524772764430929120518091 216787159146646393680777137)
                ·
                  refine ⟨162590369359984795260582853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216787159146646393680777137 162590369359984795260582853)
                  ·
                    refine ⟨30485694254997149111359285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162590369359984795260582853 30485694254997149111359285)
                    ·
                      refine ⟨2858033836405982729189933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30485694254997149111359285 2858033836405982729189933)
                      ·
                        rfl

theorem cell23_5566001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_5566001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566001 prefixEnd_5566001 := by exact prefixLift 5566001
  have htrace : WordTrace (prefixWord ++ tailWord_5566001) baseStart_5566001 baseEnd_5566001 := by
    simpa [prefixWord, tailWord_5566001, baseEnd_5566001] using wordTrace_append hprefix tailTrace_5566001
  have hstable : (prefixWord ++ tailWord_5566001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566001).length < 2 ^ (prefixWord ++ tailWord_5566001).sum := by decide
  have hdescent : baseEnd_5566001 < baseStart_5566001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566012 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 6]
def baseStart_5566012 : Nat := 118140960795 + 5566012 * 2 ^ 59
def prefixEnd_5566012 : Nat := 4983230072969 + 3 ^ 40 * 5566012 * 2
def baseEnd_5566012 : Nat := 317559942743686909572487

theorem tailTrace_5566012 : CollatzResearch.WordTrace tailWord_5566012 prefixEnd_5566012 317559942743686909572487 := by
  unfold tailWord_5566012
  simp only [CollatzResearch.WordTrace]
  refine ⟨101504567755648299006822145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135339423674197732009096193 101504567755648299006822145)
  ·
    refine ⟨76128425816736224255116609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101504567755648299006822145 76128425816736224255116609)
    ·
      refine ⟨57096319362552168191337457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76128425816736224255116609 57096319362552168191337457)
      ·
        refine ⟨42822239521914126143503093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57096319362552168191337457 42822239521914126143503093)
        ·
          refine ⟨4014584955179449325953415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42822239521914126143503093 4014584955179449325953415)
          ·
            refine ⟨6021877432769173988930123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014584955179449325953415 6021877432769173988930123)
            ·
              refine ⟨9032816149153760983395185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021877432769173988930123 9032816149153760983395185)
              ·
                refine ⟨6774612111865320737546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9032816149153760983395185 6774612111865320737546389)
                ·
                  refine ⟨317559942743686909572487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6774612111865320737546389 317559942743686909572487)
                  ·
                    rfl

theorem cell23_5566012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_5566012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566012 prefixEnd_5566012 := by exact prefixLift 5566012
  have htrace : WordTrace (prefixWord ++ tailWord_5566012) baseStart_5566012 baseEnd_5566012 := by
    simpa [prefixWord, tailWord_5566012, baseEnd_5566012] using wordTrace_append hprefix tailTrace_5566012
  have hstable : (prefixWord ++ tailWord_5566012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566012).length < 2 ^ (prefixWord ++ tailWord_5566012).sum := by decide
  have hdescent : baseEnd_5566012 < baseStart_5566012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566056 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5566056 : Nat := 118140960795 + 5566056 * 2 ^ 59
def prefixEnd_5566056 : Nat := 4983230072969 + 3 ^ 40 * 5566056 * 2
def baseEnd_5566056 : Nat := 2858062077841980014002181

theorem tailTrace_5566056 : CollatzResearch.WordTrace tailWord_5566056 prefixEnd_5566056 2858062077841980014002181 := by
  unfold tailWord_5566056
  simp only [CollatzResearch.WordTrace]
  refine ⟨101505370161568596764123011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135340493548758129018830681 101505370161568596764123011)
  ·
    refine ⟨152258055242352895146184517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101505370161568596764123011 152258055242352895146184517)
    ·
      refine ⟨28548385357941167839909597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152258055242352895146184517 28548385357941167839909597)
      ·
        refine ⟨10705644509227937939966099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28548385357941167839909597 10705644509227937939966099)
        ·
          refine ⟨16058466763841906909949149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10705644509227937939966099 16058466763841906909949149)
          ·
            refine ⟨6021925036440715091230931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16058466763841906909949149 6021925036440715091230931)
            ·
              refine ⟨9032887554661072636846397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021925036440715091230931 9032887554661072636846397)
              ·
                refine ⟨3387332832997902238817399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9032887554661072636846397 3387332832997902238817399)
                ·
                  refine ⟨5080999249496853358226099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387332832997902238817399 5080999249496853358226099)
                  ·
                    refine ⟨7621498874245280037339149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5080999249496853358226099 7621498874245280037339149)
                    ·
                      refine ⟨2858062077841980014002181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7621498874245280037339149 2858062077841980014002181)
                      ·
                        rfl

theorem cell23_5566056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5566056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566056 prefixEnd_5566056 := by exact prefixLift 5566056
  have htrace : WordTrace (prefixWord ++ tailWord_5566056) baseStart_5566056 baseEnd_5566056 := by
    simpa [prefixWord, tailWord_5566056, baseEnd_5566056] using wordTrace_append hprefix tailTrace_5566056
  have hstable : (prefixWord ++ tailWord_5566056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566056).length < 2 ^ (prefixWord ++ tailWord_5566056).sum := by decide
  have hdescent : baseEnd_5566056 < baseStart_5566056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566152 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_5566152 : Nat := 118140960795 + 5566152 * 2 ^ 59
def prefixEnd_5566152 : Nat := 4983230072969 + 3 ^ 40 * 5566152 * 2
def baseEnd_5566152 : Nat := 2858111371984811638401739

theorem tailTrace_5566152 : CollatzResearch.WordTrace tailWord_5566152 prefixEnd_5566152 2858111371984811638401739 := by
  unfold tailWord_5566152
  simp only [CollatzResearch.WordTrace]
  refine ⟨101507120865394700961870355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135342827820526267949160473 101507120865394700961870355)
  ·
    refine ⟨152260681298092051442805533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101507120865394700961870355 152260681298092051442805533)
    ·
      refine ⟨57097755486784519291052075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152260681298092051442805533 57097755486784519291052075)
      ·
        refine ⟨85646633230176778936578113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57097755486784519291052075 85646633230176778936578113)
        ·
          refine ⟨64234974922632584202433585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85646633230176778936578113 64234974922632584202433585)
          ·
            refine ⟨48176231191974438151825189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64234974922632584202433585 48176231191974438151825189)
            ·
              refine ⟨9033043348495207153467223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48176231191974438151825189 9033043348495207153467223)
              ·
                refine ⟨13549565022742810730200835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9033043348495207153467223 13549565022742810730200835)
                ·
                  refine ⟨20324347534114216095301253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13549565022742810730200835 20324347534114216095301253)
                  ·
                    refine ⟨3810815162646415517868985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20324347534114216095301253 3810815162646415517868985)
                    ·
                      refine ⟨2858111371984811638401739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810815162646415517868985 2858111371984811638401739)
                      ·
                        rfl

theorem cell23_5566152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_5566152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566152 prefixEnd_5566152 := by exact prefixLift 5566152
  have htrace : WordTrace (prefixWord ++ tailWord_5566152) baseStart_5566152 baseEnd_5566152 := by
    simpa [prefixWord, tailWord_5566152, baseEnd_5566152] using wordTrace_append hprefix tailTrace_5566152
  have hstable : (prefixWord ++ tailWord_5566152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566152).length < 2 ^ (prefixWord ++ tailWord_5566152).sum := by decide
  have hdescent : baseEnd_5566152 < baseStart_5566152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566195 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 7, 2]
def baseStart_5566195 : Nat := 118140960795 + 5566195 * 2 ^ 59
def prefixEnd_5566195 : Nat := 4983230072969 + 3 ^ 40 * 5566195 * 2
def baseEnd_5566195 : Nat := 2858133451652954970164041

theorem tailTrace_5566195 : CollatzResearch.WordTrace tailWord_5566195 prefixEnd_5566195 2858133451652954970164041 := by
  unfold tailWord_5566195
  simp only [CollatzResearch.WordTrace]
  refine ⟨203015810069633620267556039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135343873379755746845037359 203015810069633620267556039)
  ·
    refine ⟨304523715104450430401334059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203015810069633620267556039 304523715104450430401334059)
    ·
      refine ⟨456785572656675645602001089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304523715104450430401334059 456785572656675645602001089)
      ·
        refine ⟨342589179492506734201500817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456785572656675645602001089 342589179492506734201500817)
        ·
          refine ⟨256941884619380050651125613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342589179492506734201500817 256941884619380050651125613)
          ·
            refine ⟨96353206732267518994172105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256941884619380050651125613 96353206732267518994172105)
            ·
              refine ⟨72264905049200639245629079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96353206732267518994172105 72264905049200639245629079)
              ·
                refine ⟨108397357573800958868443619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72264905049200639245629079 108397357573800958868443619)
                ·
                  refine ⟨162596036360701438302665429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108397357573800958868443619 162596036360701438302665429)
                  ·
                    refine ⟨3810844602203939960218721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162596036360701438302665429 3810844602203939960218721)
                    ·
                      refine ⟨2858133451652954970164041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3810844602203939960218721 2858133451652954970164041)
                      ·
                        rfl

theorem cell23_5566195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7, 2].length) (baseStart_5566195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566195 prefixEnd_5566195 := by exact prefixLift 5566195
  have htrace : WordTrace (prefixWord ++ tailWord_5566195) baseStart_5566195 baseEnd_5566195 := by
    simpa [prefixWord, tailWord_5566195, baseEnd_5566195] using wordTrace_append hprefix tailTrace_5566195
  have hstable : (prefixWord ++ tailWord_5566195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566195).length < 2 ^ (prefixWord ++ tailWord_5566195).sum := by decide
  have hdescent : baseEnd_5566195 < baseStart_5566195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566225 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_5566225 : Nat := 118140960795 + 5566225 * 2 ^ 59
def prefixEnd_5566225 : Nat := 4983230072969 + 3 ^ 40 * 5566225 * 2
def baseEnd_5566225 : Nat := 2858148856072589852788903

theorem tailTrace_5566225 : CollatzResearch.WordTrace tailWord_5566225 prefixEnd_5566225 2858148856072589852788903 := by
  unfold tailWord_5566225
  simp only [CollatzResearch.WordTrace]
  refine ⟨203016904259524935391148129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135344602839683290260765419 203016904259524935391148129)
  ·
    refine ⟨152262678194643701543361097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203016904259524935391148129 152262678194643701543361097)
    ·
      refine ⟨114197008645982776157520823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152262678194643701543361097 114197008645982776157520823)
      ·
        refine ⟨171295512968974164236281235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114197008645982776157520823 171295512968974164236281235)
        ·
          refine ⟨256943269453461246354421853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171295512968974164236281235 256943269453461246354421853)
          ·
            refine ⟨96353726045047967382908195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256943269453461246354421853 96353726045047967382908195)
            ·
              refine ⟨144530589067571951074362293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96353726045047967382908195 144530589067571951074362293)
              ·
                refine ⟨13549742725084870413221465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144530589067571951074362293 13549742725084870413221465)
                ·
                  refine ⟨10162307043813652809916099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13549742725084870413221465 10162307043813652809916099)
                  ·
                    refine ⟨15243460565720479214874149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10162307043813652809916099 15243460565720479214874149)
                    ·
                      refine ⟨2858148856072589852788903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15243460565720479214874149 2858148856072589852788903)
                      ·
                        rfl

theorem cell23_5566225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_5566225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566225 prefixEnd_5566225 := by exact prefixLift 5566225
  have htrace : WordTrace (prefixWord ++ tailWord_5566225) baseStart_5566225 baseEnd_5566225 := by
    simpa [prefixWord, tailWord_5566225, baseEnd_5566225] using wordTrace_append hprefix tailTrace_5566225
  have hstable : (prefixWord ++ tailWord_5566225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566225).length < 2 ^ (prefixWord ++ tailWord_5566225).sum := by decide
  have hdescent : baseEnd_5566225 < baseStart_5566225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566226 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_5566226 : Nat := 118140960795 + 5566226 * 2 ^ 59
def prefixEnd_5566226 : Nat := 4983230072969 + 3 ^ 40 * 5566226 * 2
def baseEnd_5566226 : Nat := 317572152172582705430711

theorem tailTrace_5566226 : CollatzResearch.WordTrace tailWord_5566226 prefixEnd_5566226 317572152172582705430711 := by
  unfold tailWord_5566226
  simp only [CollatzResearch.WordTrace]
  refine ⟨50754235183130328140483633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135344627155014208374623021 50754235183130328140483633)
  ·
    refine ⟨38065676387347746105362725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50754235183130328140483633 38065676387347746105362725)
    ·
      refine ⟨7137314322627702394755511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38065676387347746105362725 7137314322627702394755511)
      ·
        refine ⟨10705971483941553592133267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7137314322627702394755511 10705971483941553592133267)
        ·
          refine ⟨16058957225912330388199901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10705971483941553592133267 16058957225912330388199901)
          ·
            refine ⟨6022108959717123895574963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16058957225912330388199901 6022108959717123895574963)
            ·
              refine ⟨9033163439575685843362445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022108959717123895574963 9033163439575685843362445)
              ·
                refine ⟨3387436289840882191260917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9033163439575685843362445 3387436289840882191260917)
                ·
                  refine ⟨317572152172582705430711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387436289840882191260917 317572152172582705430711)
                  ·
                    rfl

theorem cell23_5566226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_5566226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566226 prefixEnd_5566226 := by exact prefixLift 5566226
  have htrace : WordTrace (prefixWord ++ tailWord_5566226) baseStart_5566226 baseEnd_5566226 := by
    simpa [prefixWord, tailWord_5566226, baseEnd_5566226] using wordTrace_append hprefix tailTrace_5566226
  have hstable : (prefixWord ++ tailWord_5566226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566226).length < 2 ^ (prefixWord ++ tailWord_5566226).sum := by decide
  have hdescent : baseEnd_5566226 < baseStart_5566226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566242 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_5566242 : Nat := 118140960795 + 5566242 * 2 ^ 59
def prefixEnd_5566242 : Nat := 4983230072969 + 3 ^ 40 * 5566242 * 2
def baseEnd_5566242 : Nat := 2858157585243716286276325

theorem tailTrace_5566242 : CollatzResearch.WordTrace tailWord_5566242 prefixEnd_5566242 2858157585243716286276325 := by
  unfold tailWord_5566242
  simp only [CollatzResearch.WordTrace]
  refine ⟨50754381075115836823629245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135345016200308898196344653 50754381075115836823629245)
  ·
    refine ⟨19032892903168438808860967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50754381075115836823629245 19032892903168438808860967)
    ·
      refine ⟨28549339354752658213291451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19032892903168438808860967 28549339354752658213291451)
      ·
        refine ⟨42824009032128987319937177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28549339354752658213291451 42824009032128987319937177)
        ·
          refine ⟨32118006774096740489952883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42824009032128987319937177 32118006774096740489952883)
          ·
            refine ⟨48177010161145110734929325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32118006774096740489952883 48177010161145110734929325)
            ·
              refine ⟨18066378810429416525598497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48177010161145110734929325 18066378810429416525598497)
              ·
                refine ⟨13549784107822062394198873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18066378810429416525598497 13549784107822062394198873)
                ·
                  refine ⟨10162338080866546795649155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13549784107822062394198873 10162338080866546795649155)
                  ·
                    refine ⟨15243507121299820193473733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10162338080866546795649155 15243507121299820193473733)
                    ·
                      refine ⟨2858157585243716286276325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15243507121299820193473733 2858157585243716286276325)
                      ·
                        rfl

theorem cell23_5566242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_5566242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566242 prefixEnd_5566242 := by exact prefixLift 5566242
  have htrace : WordTrace (prefixWord ++ tailWord_5566242) baseStart_5566242 baseEnd_5566242 := by
    simpa [prefixWord, tailWord_5566242, baseEnd_5566242] using wordTrace_append hprefix tailTrace_5566242
  have hstable : (prefixWord ++ tailWord_5566242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566242).length < 2 ^ (prefixWord ++ tailWord_5566242).sum := by decide
  have hdescent : baseEnd_5566242 < baseStart_5566242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566252 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_5566252 : Nat := 118140960795 + 5566252 * 2 ^ 59
def prefixEnd_5566252 : Nat := 4983230072969 + 3 ^ 40 * 5566252 * 2
def baseEnd_5566252 : Nat := 952720906683420415717093

theorem tailTrace_5566252 : CollatzResearch.WordTrace tailWord_5566252 prefixEnd_5566252 952720906683420415717093 := by
  unfold tailWord_5566252
  simp only [CollatzResearch.WordTrace]
  refine ⟨101508944515213559501190505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135345259353618079334920673 101508944515213559501190505)
  ·
    refine ⟨76131708386410169625892879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101508944515213559501190505 76131708386410169625892879)
    ·
      refine ⟨114197562579615254438839319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76131708386410169625892879 114197562579615254438839319)
      ·
        refine ⟨171296343869422881658258979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114197562579615254438839319 171296343869422881658258979)
        ·
          refine ⟨256944515804134322487388469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171296343869422881658258979 256944515804134322487388469)
          ·
            refine ⟨24088548356637592733192669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256944515804134322487388469 24088548356637592733192669)
            ·
              refine ⟨9033205633739097274947251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24088548356637592733192669 9033205633739097274947251)
              ·
                refine ⟨13549808450608645912420877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9033205633739097274947251 13549808450608645912420877)
                ·
                  refine ⟨5081178168978242217157829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13549808450608645912420877 5081178168978242217157829)
                  ·
                    refine ⟨952720906683420415717093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081178168978242217157829 952720906683420415717093)
                    ·
                      rfl

theorem cell23_5566252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_5566252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566252 prefixEnd_5566252 := by exact prefixLift 5566252
  have htrace : WordTrace (prefixWord ++ tailWord_5566252) baseStart_5566252 baseEnd_5566252 := by
    simpa [prefixWord, tailWord_5566252, baseEnd_5566252] using wordTrace_append hprefix tailTrace_5566252
  have hstable : (prefixWord ++ tailWord_5566252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566252).length < 2 ^ (prefixWord ++ tailWord_5566252).sum := by decide
  have hdescent : baseEnd_5566252 < baseStart_5566252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566343 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_5566343 : Nat := 118140960795 + 5566343 * 2 ^ 59
def prefixEnd_5566343 : Nat := 4983230072969 + 3 ^ 40 * 5566343 * 2
def baseEnd_5566343 : Nat := 2858209446789820391113361

theorem tailTrace_5566343 : CollatzResearch.WordTrace tailWord_5566343 prefixEnd_5566343 2858209446789820391113361 := by
  unfold tailWord_5566343
  simp only [CollatzResearch.WordTrace]
  refine ⟨203021208073097441543943683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135347472048731627695962455 203021208073097441543943683)
  ·
    refine ⟨304531812109646162315915525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203021208073097441543943683 304531812109646162315915525)
    ·
      refine ⟨57099714770558655434234161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304531812109646162315915525 57099714770558655434234161)
      ·
        refine ⟨42824786077918991575675621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57099714770558655434234161 42824786077918991575675621)
        ·
          refine ⟨8029647389609810920439179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42824786077918991575675621 8029647389609810920439179)
          ·
            refine ⟨12044471084414716380658769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029647389609810920439179 12044471084414716380658769)
            ·
              refine ⟨9033353313311037285494077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12044471084414716380658769 9033353313311037285494077)
              ·
                refine ⟨3387507492491638982060279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9033353313311037285494077 3387507492491638982060279)
                ·
                  refine ⟨5081261238737458473090419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387507492491638982060279 5081261238737458473090419)
                  ·
                    refine ⟨7621891858106187709635629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5081261238737458473090419 7621891858106187709635629)
                    ·
                      refine ⟨2858209446789820391113361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7621891858106187709635629 2858209446789820391113361)
                      ·
                        rfl

theorem cell23_5566343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_5566343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566343 prefixEnd_5566343 := by exact prefixLift 5566343
  have htrace : WordTrace (prefixWord ++ tailWord_5566343) baseStart_5566343 baseEnd_5566343 := by
    simpa [prefixWord, tailWord_5566343, baseEnd_5566343] using wordTrace_append hprefix tailTrace_5566343
  have hstable : (prefixWord ++ tailWord_5566343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566343).length < 2 ^ (prefixWord ++ tailWord_5566343).sum := by decide
  have hdescent : baseEnd_5566343 < baseStart_5566343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566359 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 2, 4]
def baseStart_5566359 : Nat := 118140960795 + 5566359 * 2 ^ 59
def prefixEnd_5566359 : Nat := 4983230072969 + 3 ^ 40 * 5566359 * 2
def baseEnd_5566359 : Nat := 952739220826764109504429

theorem tailTrace_5566359 : CollatzResearch.WordTrace tailWord_5566359 prefixEnd_5566359 952739220826764109504429 := by
  unfold tailWord_5566359
  simp only [CollatzResearch.WordTrace]
  refine ⟨203021791641039476276526131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135347861094026317517684087 203021791641039476276526131)
  ·
    refine ⟨304532687461559214414789197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203021791641039476276526131 304532687461559214414789197)
    ·
      refine ⟨114199757798084705405545949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304532687461559214414789197 114199757798084705405545949)
      ·
        refine ⟨42824909174281764527079731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114199757798084705405545949 42824909174281764527079731)
        ·
          refine ⟨64237363761422646790619597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42824909174281764527079731 64237363761422646790619597)
          ·
            refine ⟨24089011410533492546482349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64237363761422646790619597 24089011410533492546482349)
            ·
              refine ⟨9033379278950059704930881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24089011410533492546482349 9033379278950059704930881)
              ·
                refine ⟨6775034459212544778698161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9033379278950059704930881 6775034459212544778698161)
                ·
                  refine ⟨5081275844409408584023621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6775034459212544778698161 5081275844409408584023621)
                  ·
                    refine ⟨952739220826764109504429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081275844409408584023621 952739220826764109504429)
                    ·
                      rfl

theorem cell23_5566359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_5566359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566359 prefixEnd_5566359 := by exact prefixLift 5566359
  have htrace : WordTrace (prefixWord ++ tailWord_5566359) baseStart_5566359 baseEnd_5566359 := by
    simpa [prefixWord, tailWord_5566359, baseEnd_5566359] using wordTrace_append hprefix tailTrace_5566359
  have hstable : (prefixWord ++ tailWord_5566359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566359).length < 2 ^ (prefixWord ++ tailWord_5566359).sum := by decide
  have hdescent : baseEnd_5566359 < baseStart_5566359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566369 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5566369 : Nat := 118140960795 + 5566369 * 2 ^ 59
def prefixEnd_5566369 : Nat := 4983230072969 + 3 ^ 40 * 5566369 * 2
def baseEnd_5566369 : Nat := 2858222797286837289388241

theorem tailTrace_5566369 : CollatzResearch.WordTrace tailWord_5566369 prefixEnd_5566369 2858222797286837289388241 := by
  unfold tailWord_5566369
  simp only [CollatzResearch.WordTrace]
  refine ⟨203022156371003247984390161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135348104247335498656260107 203022156371003247984390161)
  ·
    refine ⟨152266617278252435988292621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203022156371003247984390161 152266617278252435988292621)
    ·
      refine ⟨57099981479344663495609733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152266617278252435988292621 57099981479344663495609733)
      ·
        refine ⟨10706246527377124405426825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57099981479344663495609733 10706246527377124405426825)
        ·
          refine ⟨8029684895532843304070119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10706246527377124405426825 8029684895532843304070119)
          ·
            refine ⟨12044527343299264956105179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029684895532843304070119 12044527343299264956105179)
            ·
              refine ⟨18066791014948897434157769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12044527343299264956105179 18066791014948897434157769)
              ·
                refine ⟨13550093261211673075618327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18066791014948897434157769 13550093261211673075618327)
                ·
                  refine ⟨20325139891817509613427491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13550093261211673075618327 20325139891817509613427491)
                  ·
                    refine ⟨30487709837726264420141237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20325139891817509613427491 30487709837726264420141237)
                    ·
                      refine ⟨2858222797286837289388241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30487709837726264420141237 2858222797286837289388241)
                      ·
                        rfl

theorem cell23_5566369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5566369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566369 prefixEnd_5566369 := by exact prefixLift 5566369
  have htrace : WordTrace (prefixWord ++ tailWord_5566369) baseStart_5566369 baseEnd_5566369 := by
    simpa [prefixWord, tailWord_5566369, baseEnd_5566369] using wordTrace_append hprefix tailTrace_5566369
  have hstable : (prefixWord ++ tailWord_5566369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566369).length < 2 ^ (prefixWord ++ tailWord_5566369).sum := by decide
  have hdescent : baseEnd_5566369 < baseStart_5566369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566389 : List Nat := [1, 3, 3, 2, 1, 4, 2, 7]
def baseStart_5566389 : Nat := 118140960795 + 5566389 * 2 ^ 59
def prefixEnd_5566389 : Nat := 4983230072969 + 3 ^ 40 * 5566389 * 2
def baseEnd_5566389 : Nat := 105860483959256563375487

theorem tailTrace_5566389 : CollatzResearch.WordTrace tailWord_5566389 prefixEnd_5566389 105860483959256563375487 := by
  unfold tailWord_5566389
  simp only [CollatzResearch.WordTrace]
  refine ⟨203022885830930791400118221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135348590553953860933412147 203022885830930791400118221)
  ·
    refine ⟨76133582186599046775044333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203022885830930791400118221 76133582186599046775044333)
    ·
      refine ⟨28550093319974642540641625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76133582186599046775044333 28550093319974642540641625)
      ·
        refine ⟨21412569989980981905481219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28550093319974642540641625 21412569989980981905481219)
        ·
          refine ⟨32118854984971472858221829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21412569989980981905481219 32118854984971472858221829)
          ·
            refine ⟨6022285309682151160916593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32118854984971472858221829 6022285309682151160916593)
            ·
              refine ⟨4516713982261613370687445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6022285309682151160916593 4516713982261613370687445)
              ·
                refine ⟨105860483959256563375487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4516713982261613370687445 105860483959256563375487)
                ·
                  rfl

theorem cell23_5566389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 7].length) (baseStart_5566389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566389 prefixEnd_5566389 := by exact prefixLift 5566389
  have htrace : WordTrace (prefixWord ++ tailWord_5566389) baseStart_5566389 baseEnd_5566389 := by
    simpa [prefixWord, tailWord_5566389, baseEnd_5566389] using wordTrace_append hprefix tailTrace_5566389
  have hstable : (prefixWord ++ tailWord_5566389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566389).length < 2 ^ (prefixWord ++ tailWord_5566389).sum := by decide
  have hdescent : baseEnd_5566389 < baseStart_5566389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566395 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_5566395 : Nat := 118140960795 + 5566395 * 2 ^ 59
def prefixEnd_5566395 : Nat := 4983230072969 + 3 ^ 40 * 5566395 * 2
def baseEnd_5566395 : Nat := 2858236147783854187663121

theorem tailTrace_5566395 : CollatzResearch.WordTrace tailWord_5566395 prefixEnd_5566395 2858236147783854187663121 := by
  unfold tailWord_5566395
  simp only [CollatzResearch.WordTrace]
  refine ⟨203023104668909054424836639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135348736445939369616557759 203023104668909054424836639)
  ·
    refine ⟨304534657003363581637254959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203023104668909054424836639 304534657003363581637254959)
    ·
      refine ⟨456801985505045372455882439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304534657003363581637254959 456801985505045372455882439)
      ·
        refine ⟨685202978257568058683823659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456801985505045372455882439 685202978257568058683823659)
        ·
          refine ⟨1027804467386352088025735489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685202978257568058683823659 1027804467386352088025735489)
          ·
            refine ⟨770853350539764066019301617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027804467386352088025735489 770853350539764066019301617)
            ·
              refine ⟨578140012904823049514476213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770853350539764066019301617 578140012904823049514476213)
              ·
                refine ⟨54200626209827160891982145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 578140012904823049514476213 54200626209827160891982145)
                ·
                  refine ⟨40650469657370370668986609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54200626209827160891982145 40650469657370370668986609)
                  ·
                    refine ⟨30487852243027778001739957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40650469657370370668986609 30487852243027778001739957)
                    ·
                      refine ⟨2858236147783854187663121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30487852243027778001739957 2858236147783854187663121)
                      ·
                        rfl

theorem cell23_5566395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_5566395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566395 prefixEnd_5566395 := by exact prefixLift 5566395
  have htrace : WordTrace (prefixWord ++ tailWord_5566395) baseStart_5566395 baseEnd_5566395 := by
    simpa [prefixWord, tailWord_5566395, baseEnd_5566395] using wordTrace_append hprefix tailTrace_5566395
  have hstable : (prefixWord ++ tailWord_5566395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566395).length < 2 ^ (prefixWord ++ tailWord_5566395).sum := by decide
  have hdescent : baseEnd_5566395 < baseStart_5566395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566442 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_5566442 : Nat := 118140960795 + 5566442 * 2 ^ 59
def prefixEnd_5566442 : Nat := 4983230072969 + 3 ^ 40 * 5566442 * 2
def baseEnd_5566442 : Nat := 2858260281374615503775405

theorem tailTrace_5566442 : CollatzResearch.WordTrace tailWord_5566442 prefixEnd_5566442 2858260281374615503775405 := by
  unfold tailWord_5566442
  simp only [CollatzResearch.WordTrace]
  refine ⟨50756204724934695362949395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135349879266492520967865053 50756204724934695362949395)
  ·
    refine ⟨76134307087402043044424093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50756204724934695362949395 76134307087402043044424093)
    ·
      refine ⟨28550365157775766141659035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76134307087402043044424093 28550365157775766141659035)
      ·
        refine ⟨42825547736663649212488553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28550365157775766141659035 42825547736663649212488553)
        ·
          refine ⟨32119160802497736909366415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42825547736663649212488553 32119160802497736909366415)
          ·
            refine ⟨48178741203746605364049623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32119160802497736909366415 48178741203746605364049623)
            ·
              refine ⟨72268111805619908046074435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48178741203746605364049623 72268111805619908046074435)
              ·
                refine ⟨108402167708429862069111653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72268111805619908046074435 108402167708429862069111653)
                ·
                  refine ⟨20325406445330599137958435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108402167708429862069111653 20325406445330599137958435)
                  ·
                    refine ⟨30488109667995898706937653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20325406445330599137958435 30488109667995898706937653)
                    ·
                      refine ⟨2858260281374615503775405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30488109667995898706937653 2858260281374615503775405)
                      ·
                        rfl

theorem cell23_5566442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_5566442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566442 prefixEnd_5566442 := by exact prefixLift 5566442
  have htrace : WordTrace (prefixWord ++ tailWord_5566442) baseStart_5566442 baseEnd_5566442 := by
    simpa [prefixWord, tailWord_5566442, baseEnd_5566442] using wordTrace_append hprefix tailTrace_5566442
  have hstable : (prefixWord ++ tailWord_5566442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566442).length < 2 ^ (prefixWord ++ tailWord_5566442).sum := by decide
  have hdescent : baseEnd_5566442 < baseStart_5566442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566499 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 2, 5, 2]
def baseStart_5566499 : Nat := 118140960795 + 5566499 * 2 ^ 59
def prefixEnd_5566499 : Nat := 4983230072969 + 3 ^ 40 * 5566499 * 2
def baseEnd_5566499 : Nat := 2858289549771921780762643

theorem tailTrace_5566499 : CollatzResearch.WordTrace tailWord_5566499 prefixEnd_5566499 2858289549771921780762643 := by
  unfold tailWord_5566499
  simp only [CollatzResearch.WordTrace]
  refine ⟨203026897860532280186622551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135351265240354853457748367 203026897860532280186622551)
  ·
    refine ⟨304540346790798420279933827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203026897860532280186622551 304540346790798420279933827)
    ·
      refine ⟨456810520186197630419900741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304540346790798420279933827 456810520186197630419900741)
      ·
        refine ⟨85651972534912055703731389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 456810520186197630419900741 85651972534912055703731389)
        ·
          refine ⟨32119489700592020888899271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85651972534912055703731389 32119489700592020888899271)
          ·
            refine ⟨48179234550888031333348907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32119489700592020888899271 48179234550888031333348907)
            ·
              refine ⟨72268851826332047000023361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48179234550888031333348907 72268851826332047000023361)
              ·
                refine ⟨54201638869749035250017521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72268851826332047000023361 54201638869749035250017521)
                ·
                  refine ⟨40651229152311776437513141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54201638869749035250017521 40651229152311776437513141)
                  ·
                    refine ⟨3811052733029229041016857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40651229152311776437513141 3811052733029229041016857)
                    ·
                      refine ⟨2858289549771921780762643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811052733029229041016857 2858289549771921780762643)
                      ·
                        rfl

theorem cell23_5566499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_5566499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566499 prefixEnd_5566499 := by exact prefixLift 5566499
  have htrace : WordTrace (prefixWord ++ tailWord_5566499) baseStart_5566499 baseEnd_5566499 := by
    simpa [prefixWord, tailWord_5566499, baseEnd_5566499] using wordTrace_append hprefix tailTrace_5566499
  have hstable : (prefixWord ++ tailWord_5566499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566499).length < 2 ^ (prefixWord ++ tailWord_5566499).sum := by decide
  have hdescent : baseEnd_5566499 < baseStart_5566499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566549 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_5566549 : Nat := 118140960795 + 5566549 * 2 ^ 59
def prefixEnd_5566549 : Nat := 4983230072969 + 3 ^ 40 * 5566549 * 2
def baseEnd_5566549 : Nat := 2858315223804646585137413

theorem tailTrace_5566549 : CollatzResearch.WordTrace tailWord_5566549 prefixEnd_5566549 2858315223804646585137413 := by
  unfold tailWord_5566549
  simp only [CollatzResearch.WordTrace]
  refine ⟨203028721510351138725942701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135352481006900759150628467 203028721510351138725942701)
  ·
    refine ⟨76135770566381677022228513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203028721510351138725942701 76135770566381677022228513)
    ·
      refine ⟨57101827924786257766671385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76135770566381677022228513 57101827924786257766671385)
      ·
        refine ⟨42826370943589693325003539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57101827924786257766671385 42826370943589693325003539)
        ·
          refine ⟨64239556415384539987505309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42826370943589693325003539 64239556415384539987505309)
          ·
            refine ⟨24089833655769202495314491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64239556415384539987505309 24089833655769202495314491)
            ·
              refine ⟨36134750483653803742971737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24089833655769202495314491 36134750483653803742971737)
              ·
                refine ⟨27101062862740352807228803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36134750483653803742971737 27101062862740352807228803)
                ·
                  refine ⟨40651594294110529210843205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27101062862740352807228803 40651594294110529210843205)
                  ·
                    refine ⟨7622173930145724227033101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40651594294110529210843205 7622173930145724227033101)
                    ·
                      refine ⟨2858315223804646585137413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7622173930145724227033101 2858315223804646585137413)
                      ·
                        rfl

theorem cell23_5566549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_5566549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566549 prefixEnd_5566549 := by exact prefixLift 5566549
  have htrace : WordTrace (prefixWord ++ tailWord_5566549) baseStart_5566549 baseEnd_5566549 := by
    simpa [prefixWord, tailWord_5566549, baseEnd_5566549] using wordTrace_append hprefix tailTrace_5566549
  have hstable : (prefixWord ++ tailWord_5566549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566549).length < 2 ^ (prefixWord ++ tailWord_5566549).sum := by decide
  have hdescent : baseEnd_5566549 < baseStart_5566549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566556 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5566556 : Nat := 118140960795 + 5566556 * 2 ^ 59
def prefixEnd_5566556 : Nat := 4983230072969 + 3 ^ 40 * 5566556 * 2
def baseEnd_5566556 : Nat := 952772939389742685916627

theorem tailTrace_5566556 : CollatzResearch.WordTrace tailWord_5566556 prefixEnd_5566556 952772939389742685916627 := by
  unfold tailWord_5566556
  simp only [CollatzResearch.WordTrace]
  refine ⟨101514488410662889460723761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135352651214217185947631681 101514488410662889460723761)
  ·
    refine ⟨76135866307997167095542821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101514488410662889460723761 76135866307997167095542821)
    ·
      refine ⟨14275474932749468830414279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76135866307997167095542821 14275474932749468830414279)
      ·
        refine ⟨21413212399124203245621419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14275474932749468830414279 21413212399124203245621419)
        ·
          refine ⟨32119818598686304868432129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21413212399124203245621419 32119818598686304868432129)
          ·
            refine ⟨24089863949014728651324097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32119818598686304868432129 24089863949014728651324097)
            ·
              refine ⟨18067397961761046488493073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24089863949014728651324097 18067397961761046488493073)
              ·
                refine ⟨13550548471320784866369805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18067397961761046488493073 13550548471320784866369805)
                ·
                  refine ⟨5081455676745294324888677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13550548471320784866369805 5081455676745294324888677)
                  ·
                    refine ⟨952772939389742685916627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081455676745294324888677 952772939389742685916627)
                    ·
                      rfl

theorem cell23_5566556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5566556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566556 prefixEnd_5566556 := by exact prefixLift 5566556
  have htrace : WordTrace (prefixWord ++ tailWord_5566556) baseStart_5566556 baseEnd_5566556 := by
    simpa [prefixWord, tailWord_5566556, baseEnd_5566556] using wordTrace_append hprefix tailTrace_5566556
  have hstable : (prefixWord ++ tailWord_5566556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566556).length < 2 ^ (prefixWord ++ tailWord_5566556).sum := by decide
  have hdescent : baseEnd_5566556 < baseStart_5566556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566592 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_5566592 : Nat := 118140960795 + 5566592 * 2 ^ 59
def prefixEnd_5566592 : Nat := 4983230072969 + 3 ^ 40 * 5566592 * 2
def baseEnd_5566592 : Nat := 2858337303472789916899715

theorem tailTrace_5566592 : CollatzResearch.WordTrace tailWord_5566592 prefixEnd_5566592 2858337303472789916899715 := by
  unfold tailWord_5566592
  simp only [CollatzResearch.WordTrace]
  refine ⟨101515144924597678534879015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135353526566130238046505353 101515144924597678534879015)
  ·
    refine ⟨152272717386896517802318523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101515144924597678534879015 152272717386896517802318523)
    ·
      refine ⟨228409076080344776703477785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152272717386896517802318523 228409076080344776703477785)
      ·
        refine ⟨171306807060258582527608339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228409076080344776703477785 171306807060258582527608339)
        ·
          refine ⟨256960210590387873791412509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171306807060258582527608339 256960210590387873791412509)
          ·
            refine ⟨96360078971395452671779691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256960210590387873791412509 96360078971395452671779691)
            ·
              refine ⟨144540118457093179007669537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96360078971395452671779691 144540118457093179007669537)
              ·
                refine ⟨108405088842819884255752153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144540118457093179007669537 108405088842819884255752153)
                ·
                  refine ⟨81303816632114913191814115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108405088842819884255752153 81303816632114913191814115)
                  ·
                    refine ⟨121955724948172369787721173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81303816632114913191814115 121955724948172369787721173)
                    ·
                      refine ⟨2858337303472789916899715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121955724948172369787721173 2858337303472789916899715)
                      ·
                        rfl

theorem cell23_5566592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_5566592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566592 prefixEnd_5566592 := by exact prefixLift 5566592
  have htrace : WordTrace (prefixWord ++ tailWord_5566592) baseStart_5566592 baseEnd_5566592 := by
    simpa [prefixWord, tailWord_5566592, baseEnd_5566592] using wordTrace_append hprefix tailTrace_5566592
  have hstable : (prefixWord ++ tailWord_5566592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566592).length < 2 ^ (prefixWord ++ tailWord_5566592).sum := by decide
  have hdescent : baseEnd_5566592 < baseStart_5566592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566614 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5566614 : Nat := 118140960795 + 5566614 * 2 ^ 59
def prefixEnd_5566614 : Nat := 4983230072969 + 3 ^ 40 * 5566614 * 2
def baseEnd_5566614 : Nat := 2858348600047188830824615

theorem tailTrace_5566614 : CollatzResearch.WordTrace tailWord_5566614 prefixEnd_5566614 2858348600047188830824615 := by
  unfold tailWord_5566614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12689443265944728426691181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135354061503410436551372597 12689443265944728426691181)
  ·
    refine ⟨4758541224729273160009193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12689443265944728426691181 4758541224729273160009193)
    ·
      refine ⟨3568905918546954870006895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4758541224729273160009193 3568905918546954870006895)
      ·
        refine ⟨5353358877820432305010343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3568905918546954870006895 5353358877820432305010343)
        ·
          refine ⟨8030038316730648457515515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5353358877820432305010343 8030038316730648457515515)
          ·
            refine ⟨12045057475095972686273273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8030038316730648457515515 12045057475095972686273273)
            ·
              refine ⟨9033793106321979514704955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12045057475095972686273273 9033793106321979514704955)
              ·
                refine ⟨13550689659482969272057433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9033793106321979514704955 13550689659482969272057433)
                ·
                  refine ⟨10163017244612226954043075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13550689659482969272057433 10163017244612226954043075)
                  ·
                    refine ⟨15244525866918340431064613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10163017244612226954043075 15244525866918340431064613)
                    ·
                      refine ⟨2858348600047188830824615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15244525866918340431064613 2858348600047188830824615)
                      ·
                        rfl

theorem cell23_5566614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5566614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566614 prefixEnd_5566614 := by exact prefixLift 5566614
  have htrace : WordTrace (prefixWord ++ tailWord_5566614) baseStart_5566614 baseEnd_5566614 := by
    simpa [prefixWord, tailWord_5566614, baseEnd_5566614] using wordTrace_append hprefix tailTrace_5566614
  have hstable : (prefixWord ++ tailWord_5566614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566614).length < 2 ^ (prefixWord ++ tailWord_5566614).sum := by decide
  have hdescent : baseEnd_5566614 < baseStart_5566614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566616 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 3, 5]
def baseStart_5566616 : Nat := 118140960795 + 5566616 * 2 ^ 59
def prefixEnd_5566616 : Nat := 4983230072969 + 3 ^ 40 * 5566616 * 2
def baseEnd_5566616 : Nat := 952783209002832607666535

theorem tailTrace_5566616 : CollatzResearch.WordTrace tailWord_5566616 prefixEnd_5566616 952783209002832607666535 := by
  unfold tailWord_5566616
  simp only [CollatzResearch.WordTrace]
  refine ⟨101515582600554204584315851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135354110134072272779087801 101515582600554204584315851)
  ·
    refine ⟨152273373900831306876473777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101515582600554204584315851 152273373900831306876473777)
    ·
      refine ⟨114205030425623480157355333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152273373900831306876473777 114205030425623480157355333)
      ·
        refine ⟨21413443204804402529504125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114205030425623480157355333 21413443204804402529504125)
        ·
          refine ⟨8030041201801650948564047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21413443204804402529504125 8030041201801650948564047)
          ·
            refine ⟨12045061802702476422846071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8030041201801650948564047 12045061802702476422846071)
            ·
              refine ⟨18067592704053714634269107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045061802702476422846071 18067592704053714634269107)
              ·
                refine ⟨27101389056080571951403661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18067592704053714634269107 27101389056080571951403661)
                ·
                  refine ⟨10163020896030214481776373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27101389056080571951403661 10163020896030214481776373)
                  ·
                    refine ⟨952783209002832607666535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10163020896030214481776373 952783209002832607666535)
                    ·
                      rfl

theorem cell23_5566616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_5566616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566616 prefixEnd_5566616 := by exact prefixLift 5566616
  have htrace : WordTrace (prefixWord ++ tailWord_5566616) baseStart_5566616 baseEnd_5566616 := by
    simpa [prefixWord, tailWord_5566616, baseEnd_5566616] using wordTrace_append hprefix tailTrace_5566616
  have hstable : (prefixWord ++ tailWord_5566616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566616).length < 2 ^ (prefixWord ++ tailWord_5566616).sum := by decide
  have hdescent : baseEnd_5566616 < baseStart_5566616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566623 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5566623 : Nat := 118140960795 + 5566623 * 2 ^ 59
def prefixEnd_5566623 : Nat := 4983230072969 + 3 ^ 40 * 5566623 * 2
def baseEnd_5566623 : Nat := 2858353221373079295612073

theorem tailTrace_5566623 : CollatzResearch.WordTrace tailWord_5566623 prefixEnd_5566623 2858353221373079295612073 := by
  unfold tailWord_5566623
  simp only [CollatzResearch.WordTrace]
  refine ⟨203031420512083049364136523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135354280341388699576091015 203031420512083049364136523)
  ·
    refine ⟨304547130768124574046204785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203031420512083049364136523 304547130768124574046204785)
    ·
      refine ⟨228410348076093430534653589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304547130768124574046204785 228410348076093430534653589)
      ·
        refine ⟨10706735066066879556311887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228410348076093430534653589 10706735066066879556311887)
        ·
          refine ⟨16060102599100319334467831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10706735066066879556311887 16060102599100319334467831)
          ·
            refine ⟨24090153898650479001701747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16060102599100319334467831 24090153898650479001701747)
            ·
              refine ⟨36135230847975718502552621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24090153898650479001701747 36135230847975718502552621)
              ·
                refine ⟨13550711567990894438457233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36135230847975718502552621 13550711567990894438457233)
                ·
                  refine ⟨10163033675993170828842925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13550711567990894438457233 10163033675993170828842925)
                  ·
                    refine ⟨3811137628497439060816097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10163033675993170828842925 3811137628497439060816097)
                    ·
                      refine ⟨2858353221373079295612073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811137628497439060816097 2858353221373079295612073)
                      ·
                        rfl

theorem cell23_5566623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5566623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566623 prefixEnd_5566623 := by exact prefixLift 5566623
  have htrace : WordTrace (prefixWord ++ tailWord_5566623) baseStart_5566623 baseEnd_5566623 := by
    simpa [prefixWord, tailWord_5566623, baseEnd_5566623] using wordTrace_append hprefix tailTrace_5566623
  have hstable : (prefixWord ++ tailWord_5566623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566623).length < 2 ^ (prefixWord ++ tailWord_5566623).sum := by decide
  have hdescent : baseEnd_5566623 < baseStart_5566623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566629 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_5566629 : Nat := 118140960795 + 5566629 * 2 ^ 59
def prefixEnd_5566629 : Nat := 4983230072969 + 3 ^ 40 * 5566629 * 2
def baseEnd_5566629 : Nat := 952785434085668757379015

theorem tailTrace_5566629 : CollatzResearch.WordTrace tailWord_5566629 prefixEnd_5566629 952785434085668757379015 := by
  unfold tailWord_5566629
  simp only [CollatzResearch.WordTrace]
  refine ⟨203031639350061312388854941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135354426233374208259236627 203031639350061312388854941)
  ·
    refine ⟨76136864756272992145820603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203031639350061312388854941 76136864756272992145820603)
    ·
      refine ⟨114205297134409488218730905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76136864756272992145820603 114205297134409488218730905)
      ·
        refine ⟨85653972850807116164048179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114205297134409488218730905 85653972850807116164048179)
        ·
          refine ⟨128480959276210674246072269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85653972850807116164048179 128480959276210674246072269)
          ·
            refine ⟨48180359728579002842277101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128480959276210674246072269 48180359728579002842277101)
            ·
              refine ⟨18067634898217126065853913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48180359728579002842277101 18067634898217126065853913)
              ·
                refine ⟨13550726173662844549390435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18067634898217126065853913 13550726173662844549390435)
                ·
                  refine ⟨20326089260494266824085653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13550726173662844549390435 20326089260494266824085653)
                  ·
                    refine ⟨952785434085668757379015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20326089260494266824085653 952785434085668757379015)
                    ·
                      rfl

theorem cell23_5566629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_5566629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566629 prefixEnd_5566629 := by exact prefixLift 5566629
  have htrace : WordTrace (prefixWord ++ tailWord_5566629) baseStart_5566629 baseEnd_5566629 := by
    simpa [prefixWord, tailWord_5566629, baseEnd_5566629] using wordTrace_append hprefix tailTrace_5566629
  have hstable : (prefixWord ++ tailWord_5566629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566629).length < 2 ^ (prefixWord ++ tailWord_5566629).sum := by decide
  have hdescent : baseEnd_5566629 < baseStart_5566629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566647 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 1, 1, 3]
def baseStart_5566647 : Nat := 118140960795 + 5566647 * 2 ^ 59
def prefixEnd_5566647 : Nat := 4983230072969 + 3 ^ 40 * 5566647 * 2
def baseEnd_5566647 : Nat := 2858365544908787201711963

theorem tailTrace_5566647 : CollatzResearch.WordTrace tailWord_5566647 prefixEnd_5566647 2858365544908787201711963 := by
  unfold tailWord_5566647
  simp only [CollatzResearch.WordTrace]
  refine ⟨203032295863996101463010195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135354863909330734308673463 203032295863996101463010195)
  ·
    refine ⟨304548443795994152194515293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203032295863996101463010195 304548443795994152194515293)
    ·
      refine ⟨114205666423497807072943235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304548443795994152194515293 114205666423497807072943235)
      ·
        refine ⟨171308499635246710609414853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114205666423497807072943235 171308499635246710609414853)
        ·
          refine ⟨32120343681608758239265285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171308499635246710609414853 32120343681608758239265285)
          ·
            refine ⟨6022564440301642169862241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32120343681608758239265285 6022564440301642169862241)
            ·
              refine ⟨4516923330226231627396681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6022564440301642169862241 4516923330226231627396681)
              ·
                refine ⟨3387692497669673720547511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4516923330226231627396681 3387692497669673720547511)
                ·
                  refine ⟨5081538746504510580821267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387692497669673720547511 5081538746504510580821267)
                  ·
                    refine ⟨7622308119756765871231901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5081538746504510580821267 7622308119756765871231901)
                    ·
                      refine ⟨2858365544908787201711963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7622308119756765871231901 2858365544908787201711963)
                      ·
                        rfl

theorem cell23_5566647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_5566647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566647 prefixEnd_5566647 := by exact prefixLift 5566647
  have htrace : WordTrace (prefixWord ++ tailWord_5566647) baseStart_5566647 baseEnd_5566647 := by
    simpa [prefixWord, tailWord_5566647, baseEnd_5566647] using wordTrace_append hprefix tailTrace_5566647
  have hstable : (prefixWord ++ tailWord_5566647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566647).length < 2 ^ (prefixWord ++ tailWord_5566647).sum := by decide
  have hdescent : baseEnd_5566647 < baseStart_5566647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566649 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5566649 : Nat := 118140960795 + 5566649 * 2 ^ 59
def prefixEnd_5566649 : Nat := 4983230072969 + 3 ^ 40 * 5566649 * 2
def baseEnd_5566649 : Nat := 2858366571870096193886953

theorem tailTrace_5566649 : CollatzResearch.WordTrace tailWord_5566649 prefixEnd_5566649 2858366571870096193886953 := by
  unfold tailWord_5566649
  simp only [CollatzResearch.WordTrace]
  refine ⟨203032368809988855804583001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135354912539992570536388667 203032368809988855804583001)
  ·
    refine ⟨152274276607491641853437251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203032368809988855804583001 152274276607491641853437251)
    ·
      refine ⟨228411414911237462780155877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152274276607491641853437251 228411414911237462780155877)
      ·
        refine ⟨42827140295857024271279227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228411414911237462780155877 42827140295857024271279227)
        ·
          refine ⟨64240710443785536406918841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42827140295857024271279227 64240710443785536406918841)
          ·
            refine ⟨48180532832839152305189131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64240710443785536406918841 48180532832839152305189131)
            ·
              refine ⟨72270799249258728457783697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48180532832839152305189131 72270799249258728457783697)
              ·
                refine ⟨54203099436944046343337773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72270799249258728457783697 54203099436944046343337773)
                ·
                  refine ⟨20326162288854017378751665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54203099436944046343337773 20326162288854017378751665)
                  ·
                    refine ⟨15244621716640513034063749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20326162288854017378751665 15244621716640513034063749)
                    ·
                      refine ⟨2858366571870096193886953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15244621716640513034063749 2858366571870096193886953)
                      ·
                        rfl

theorem cell23_5566649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5566649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566649 prefixEnd_5566649 := by exact prefixLift 5566649
  have htrace : WordTrace (prefixWord ++ tailWord_5566649) baseStart_5566649 baseEnd_5566649 := by
    simpa [prefixWord, tailWord_5566649, baseEnd_5566649] using wordTrace_append hprefix tailTrace_5566649
  have hstable : (prefixWord ++ tailWord_5566649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566649).length < 2 ^ (prefixWord ++ tailWord_5566649).sum := by decide
  have hdescent : baseEnd_5566649 < baseStart_5566649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566653 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_5566653 : Nat := 118140960795 + 5566653 * 2 ^ 59
def prefixEnd_5566653 : Nat := 4983230072969 + 3 ^ 40 * 5566653 * 2
def baseEnd_5566653 : Nat := 2858368625792714178236935

theorem tailTrace_5566653 : CollatzResearch.WordTrace tailWord_5566653 prefixEnd_5566653 2858368625792714178236935 := by
  unfold tailWord_5566653
  simp only [CollatzResearch.WordTrace]
  refine ⟨203032514701974364487728613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135355009801316242991819075 203032514701974364487728613)
  ·
    refine ⟨38068596506620193341449115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203032514701974364487728613 38068596506620193341449115)
    ·
      refine ⟨57102894759930290012173673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38068596506620193341449115 57102894759930290012173673)
      ·
        refine ⟨42827171069947717509130255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57102894759930290012173673 42827171069947717509130255)
        ·
          refine ⟨64240756604921576263695383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42827171069947717509130255 64240756604921576263695383)
          ·
            refine ⟨96361134907382364395543075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64240756604921576263695383 96361134907382364395543075)
            ·
              refine ⟨144541702361073546593314613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96361134907382364395543075 144541702361073546593314613)
              ·
                refine ⟨13550784596350644993123245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144541702361073546593314613 13550784596350644993123245)
                ·
                  refine ⟨5081544223631491872421217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13550784596350644993123245 5081544223631491872421217)
                  ·
                    refine ⟨3811158167723618904315913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5081544223631491872421217 3811158167723618904315913)
                    ·
                      refine ⟨2858368625792714178236935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811158167723618904315913 2858368625792714178236935)
                      ·
                        rfl

theorem cell23_5566653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_5566653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566653 prefixEnd_5566653 := by exact prefixLift 5566653
  have htrace : WordTrace (prefixWord ++ tailWord_5566653) baseStart_5566653 baseEnd_5566653 := by
    simpa [prefixWord, tailWord_5566653, baseEnd_5566653] using wordTrace_append hprefix tailTrace_5566653
  have hstable : (prefixWord ++ tailWord_5566653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566653).length < 2 ^ (prefixWord ++ tailWord_5566653).sum := by decide
  have hdescent : baseEnd_5566653 < baseStart_5566653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566656 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_5566656 : Nat := 118140960795 + 5566656 * 2 ^ 59
def prefixEnd_5566656 : Nat := 4983230072969 + 3 ^ 40 * 5566656 * 2
def baseEnd_5566656 : Nat := 2858370166234677666499421

theorem tailTrace_5566656 : CollatzResearch.WordTrace tailWord_5566656 prefixEnd_5566656 2858370166234677666499421 := by
  unfold tailWord_5566656
  simp only [CollatzResearch.WordTrace]
  refine ⟨101516312060481748000043911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135355082747308997333391881 101516312060481748000043911)
  ·
    refine ⟨152274468090722622000065867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101516312060481748000043911 152274468090722622000065867)
    ·
      refine ⟨228411702136083933000098801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152274468090722622000065867 228411702136083933000098801)
      ·
        refine ⟨171308776602062949750074101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228411702136083933000098801 171308776602062949750074101)
        ·
          refine ⟨16060197806443401539069447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171308776602062949750074101 16060197806443401539069447)
          ·
            refine ⟨24090296709665102308604171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16060197806443401539069447 24090296709665102308604171)
            ·
              refine ⟨36135445064497653462906257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24090296709665102308604171 36135445064497653462906257)
              ·
                refine ⟨27101583798373240097179693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36135445064497653462906257 27101583798373240097179693)
                ·
                  refine ⟨10163093924389965036442385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27101583798373240097179693 10163093924389965036442385)
                  ·
                    refine ⟨7622320443292473777331789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10163093924389965036442385 7622320443292473777331789)
                    ·
                      refine ⟨2858370166234677666499421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7622320443292473777331789 2858370166234677666499421)
                      ·
                        rfl

theorem cell23_5566656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_5566656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566656 prefixEnd_5566656 := by exact prefixLift 5566656
  have htrace : WordTrace (prefixWord ++ tailWord_5566656) baseStart_5566656 baseEnd_5566656 := by
    simpa [prefixWord, tailWord_5566656, baseEnd_5566656] using wordTrace_append hprefix tailTrace_5566656
  have hstable : (prefixWord ++ tailWord_5566656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566656).length < 2 ^ (prefixWord ++ tailWord_5566656).sum := by decide
  have hdescent : baseEnd_5566656 < baseStart_5566656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566666 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_5566666 : Nat := 118140960795 + 5566666 * 2 ^ 59
def prefixEnd_5566666 : Nat := 4983230072969 + 3 ^ 40 * 5566666 * 2
def baseEnd_5566666 : Nat := 2858375301041222627374375

theorem tailTrace_5566666 : CollatzResearch.WordTrace tailWord_5566666 prefixEnd_5566666 2858375301041222627374375 := by
  unfold tailWord_5566666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50758247212731816926987963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135355325900618178471967901 50758247212731816926987963)
  ·
    refine ⟨76137370819097725390481945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50758247212731816926987963 76137370819097725390481945)
    ·
      refine ⟨57103028114323294042861459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76137370819097725390481945 57103028114323294042861459)
      ·
        refine ⟨85654542171484941064292189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57103028114323294042861459 85654542171484941064292189)
        ·
          refine ⟨32120453314306852899109571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85654542171484941064292189 32120453314306852899109571)
          ·
            refine ⟨48180679971460279348664357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32120453314306852899109571 48180679971460279348664357)
            ·
              refine ⟨9033877494648802377874567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48180679971460279348664357 9033877494648802377874567)
              ·
                refine ⟨13550816241973203566811851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9033877494648802377874567 13550816241973203566811851)
                ·
                  refine ⟨20326224362959805350217777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13550816241973203566811851 20326224362959805350217777)
                  ·
                    refine ⟨15244668272219854012663333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20326224362959805350217777 15244668272219854012663333)
                    ·
                      refine ⟨2858375301041222627374375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15244668272219854012663333 2858375301041222627374375)
                      ·
                        rfl

theorem cell23_5566666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_5566666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566666 prefixEnd_5566666 := by exact prefixLift 5566666
  have htrace : WordTrace (prefixWord ++ tailWord_5566666) baseStart_5566666 baseEnd_5566666 := by
    simpa [prefixWord, tailWord_5566666, baseEnd_5566666] using wordTrace_append hprefix tailTrace_5566666
  have hstable : (prefixWord ++ tailWord_5566666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566666).length < 2 ^ (prefixWord ++ tailWord_5566666).sum := by decide
  have hdescent : baseEnd_5566666 < baseStart_5566666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566670 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_5566670 : Nat := 118140960795 + 5566670 * 2 ^ 59
def prefixEnd_5566670 : Nat := 4983230072969 + 3 ^ 40 * 5566670 * 2
def baseEnd_5566670 : Nat := 2858377354963840611724357

theorem tailTrace_5566670 : CollatzResearch.WordTrace tailWord_5566670 prefixEnd_5566670 2858377354963840611724357 := by
  unfold tailWord_5566670
  simp only [CollatzResearch.WordTrace]
  refine ⟨25379141842864097048887183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135355423161941850927398309 25379141842864097048887183)
  ·
    refine ⟨38068712764296145573330775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25379141842864097048887183 38068712764296145573330775)
    ·
      refine ⟨57103069146444218359996163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38068712764296145573330775 57103069146444218359996163)
      ·
        refine ⟨85654603719666327539994245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57103069146444218359996163 85654603719666327539994245)
        ·
          refine ⟨16060238197437436413748921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85654603719666327539994245 16060238197437436413748921)
          ·
            refine ⟨12045178648078077310311691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16060238197437436413748921 12045178648078077310311691)
            ·
              refine ⟨18067767972117115965467537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045178648078077310311691 18067767972117115965467537)
              ·
                refine ⟨13550825979087836974100653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18067767972117115965467537 13550825979087836974100653)
                ·
                  refine ⟨5081559742157938865287745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13550825979087836974100653 5081559742157938865287745)
                  ·
                    refine ⟨3811169806618454148965809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5081559742157938865287745 3811169806618454148965809)
                    ·
                      refine ⟨2858377354963840611724357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811169806618454148965809 2858377354963840611724357)
                      ·
                        rfl

theorem cell23_5566670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_5566670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566670 prefixEnd_5566670 := by exact prefixLift 5566670
  have htrace : WordTrace (prefixWord ++ tailWord_5566670) baseStart_5566670 baseEnd_5566670 := by
    simpa [prefixWord, tailWord_5566670, baseEnd_5566670] using wordTrace_append hprefix tailTrace_5566670
  have hstable : (prefixWord ++ tailWord_5566670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566670).length < 2 ^ (prefixWord ++ tailWord_5566670).sum := by decide
  have hdescent : baseEnd_5566670 < baseStart_5566670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566684 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_5566684 : Nat := 118140960795 + 5566684 * 2 ^ 59
def prefixEnd_5566684 : Nat := 4983230072969 + 3 ^ 40 * 5566684 * 2
def baseEnd_5566684 : Nat := 952794847897667852316431

theorem tailTrace_5566684 : CollatzResearch.WordTrace tailWord_5566684 prefixEnd_5566684 952794847897667852316431 := by
  unfold tailWord_5566684
  simp only [CollatzResearch.WordTrace]
  refine ⟨101516822682431028391053553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135355763576574704521404737 101516822682431028391053553)
  ·
    refine ⟨76137617011823271293290165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101516822682431028391053553 76137617011823271293290165)
    ·
      refine ⟨7137901594858431683745953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76137617011823271293290165 7137901594858431683745953)
      ·
        refine ⟨5353426196143823762809465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7137901594858431683745953 5353426196143823762809465)
        ·
          refine ⟨4015069647107867822107099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5353426196143823762809465 4015069647107867822107099)
          ·
            refine ⟨6022604470661801733160649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015069647107867822107099 6022604470661801733160649)
            ·
              refine ⟨4516953352996351299870487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6022604470661801733160649 4516953352996351299870487)
              ·
                refine ⟨6775430029494526949805731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4516953352996351299870487 6775430029494526949805731)
                ·
                  refine ⟨10163145044241790424708597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6775430029494526949805731 10163145044241790424708597)
                  ·
                    refine ⟨952794847897667852316431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10163145044241790424708597 952794847897667852316431)
                    ·
                      rfl

theorem cell23_5566684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_5566684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566684 prefixEnd_5566684 := by exact prefixLift 5566684
  have htrace : WordTrace (prefixWord ++ tailWord_5566684) baseStart_5566684 baseEnd_5566684 := by
    simpa [prefixWord, tailWord_5566684, baseEnd_5566684] using wordTrace_append hprefix tailTrace_5566684
  have hstable : (prefixWord ++ tailWord_5566684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566684).length < 2 ^ (prefixWord ++ tailWord_5566684).sum := by decide
  have hdescent : baseEnd_5566684 < baseStart_5566684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566703 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 3]
def baseStart_5566703 : Nat := 118140960795 + 5566703 * 2 ^ 59
def prefixEnd_5566703 : Nat := 4983230072969 + 3 ^ 40 * 5566703 * 2
def baseEnd_5566703 : Nat := 2858394299825438982611705

theorem tailTrace_5566703 : CollatzResearch.WordTrace tailWord_5566703 prefixEnd_5566703 2858394299825438982611705 := by
  unfold tailWord_5566703
  simp only [CollatzResearch.WordTrace]
  refine ⟨203034338351793223027048763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135356225567862148684699175 203034338351793223027048763)
  ·
    refine ⟨304551507527689834540573145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203034338351793223027048763 304551507527689834540573145)
    ·
      refine ⟨228413630645767375905429859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304551507527689834540573145 228413630645767375905429859)
      ·
        refine ⟨342620445968651063858144789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228413630645767375905429859 342620445968651063858144789)
        ·
          refine ⟨16060333404780518618350537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 342620445968651063858144789 16060333404780518618350537)
          ·
            refine ⟨12045250053585388963762903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16060333404780518618350537 12045250053585388963762903)
            ·
              refine ⟨18067875080378083445644355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045250053585388963762903 18067875080378083445644355)
              ·
                refine ⟨27101812620567125168466533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18067875080378083445644355 27101812620567125168466533)
                ·
                  refine ⟨5081589866356335969087475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27101812620567125168466533 5081589866356335969087475)
                  ·
                    refine ⟨7622384799534503953631213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5081589866356335969087475 7622384799534503953631213)
                    ·
                      refine ⟨2858394299825438982611705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7622384799534503953631213 2858394299825438982611705)
                      ·
                        rfl

theorem cell23_5566703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_5566703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566703 prefixEnd_5566703 := by exact prefixLift 5566703
  have htrace : WordTrace (prefixWord ++ tailWord_5566703) baseStart_5566703 baseEnd_5566703 := by
    simpa [prefixWord, tailWord_5566703, baseEnd_5566703] using wordTrace_append hprefix tailTrace_5566703
  have hstable : (prefixWord ++ tailWord_5566703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566703).length < 2 ^ (prefixWord ++ tailWord_5566703).sum := by decide
  have hdescent : baseEnd_5566703 < baseStart_5566703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566719 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 2, 6]
def baseStart_5566719 : Nat := 118140960795 + 5566719 * 2 ^ 59
def prefixEnd_5566719 : Nat := 4983230072969 + 3 ^ 40 * 5566719 * 2
def baseEnd_5566719 : Nat := 952800838505303640003877

theorem tailTrace_5566719 : CollatzResearch.WordTrace tailWord_5566719 prefixEnd_5566719 952800838505303640003877 := by
  unfold tailWord_5566719
  simp only [CollatzResearch.WordTrace]
  refine ⟨203034921919735257759631211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135356614613156838506420807 203034921919735257759631211)
  ·
    refine ⟨304552382879602886639446817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203034921919735257759631211 304552382879602886639446817)
    ·
      refine ⟨228414287159702164979585113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304552382879602886639446817 228414287159702164979585113)
      ·
        refine ⟨171310715369776623734688835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228414287159702164979585113 171310715369776623734688835)
        ·
          refine ⟨256966073054664935602033253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171310715369776623734688835 256966073054664935602033253)
          ·
            refine ⟨48181138697749675425381235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256966073054664935602033253 48181138697749675425381235)
            ·
              refine ⟨72271708046624513138071853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48181138697749675425381235 72271708046624513138071853)
              ·
                refine ⟨27101890517484192426776945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72271708046624513138071853 27101890517484192426776945)
                ·
                  refine ⟨20326417888113144320082709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27101890517484192426776945 20326417888113144320082709)
                  ·
                    refine ⟨952800838505303640003877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20326417888113144320082709 952800838505303640003877)
                    ·
                      rfl

theorem cell23_5566719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_5566719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566719 prefixEnd_5566719 := by exact prefixLift 5566719
  have htrace : WordTrace (prefixWord ++ tailWord_5566719) baseStart_5566719 baseEnd_5566719 := by
    simpa [prefixWord, tailWord_5566719, baseEnd_5566719] using wordTrace_append hprefix tailTrace_5566719
  have hstable : (prefixWord ++ tailWord_5566719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566719).length < 2 ^ (prefixWord ++ tailWord_5566719).sum := by decide
  have hdescent : baseEnd_5566719 < baseStart_5566719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566739 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4]
def baseStart_5566739 : Nat := 118140960795 + 5566739 * 2 ^ 59
def prefixEnd_5566739 : Nat := 4983230072969 + 3 ^ 40 * 5566739 * 2
def baseEnd_5566739 : Nat := 2858412785129000841761539

theorem tailTrace_5566739 : CollatzResearch.WordTrace tailWord_5566739 prefixEnd_5566739 2858412785129000841761539 := by
  unfold tailWord_5566739
  simp only [CollatzResearch.WordTrace]
  refine ⟨203035651379662801175359271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135357100919775200783572847 203035651379662801175359271)
  ·
    refine ⟨304553477069494201763038907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203035651379662801175359271 304553477069494201763038907)
    ·
      refine ⟨456830215604241302644558361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304553477069494201763038907 456830215604241302644558361)
      ·
        refine ⟨342622661703180976983418771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456830215604241302644558361 342622661703180976983418771)
        ·
          refine ⟨513933992554771465475128157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342622661703180976983418771 513933992554771465475128157)
          ·
            refine ⟨192725247208039299553173059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513933992554771465475128157 192725247208039299553173059)
            ·
              refine ⟨289087870812058949329759589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192725247208039299553173059 289087870812058949329759589)
              ·
                refine ⟨54203975777261052999329923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289087870812058949329759589 54203975777261052999329923)
                ·
                  refine ⟨81305963665891579498994885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54203975777261052999329923 81305963665891579498994885)
                  ·
                    refine ⟨15244868187354671156061541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81305963665891579498994885 15244868187354671156061541)
                    ·
                      refine ⟨2858412785129000841761539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15244868187354671156061541 2858412785129000841761539)
                      ·
                        rfl

theorem cell23_5566739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_5566739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566739 prefixEnd_5566739 := by exact prefixLift 5566739
  have htrace : WordTrace (prefixWord ++ tailWord_5566739) baseStart_5566739 baseEnd_5566739 := by
    simpa [prefixWord, tailWord_5566739, baseEnd_5566739] using wordTrace_append hprefix tailTrace_5566739
  have hstable : (prefixWord ++ tailWord_5566739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566739).length < 2 ^ (prefixWord ++ tailWord_5566739).sum := by decide
  have hdescent : baseEnd_5566739 < baseStart_5566739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566776 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_5566776 : Nat := 118140960795 + 5566776 * 2 ^ 59
def prefixEnd_5566776 : Nat := 4983230072969 + 3 ^ 40 * 5566776 * 2
def baseEnd_5566776 : Nat := 2858431783913217196998869

theorem tailTrace_5566776 : CollatzResearch.WordTrace tailWord_5566776 prefixEnd_5566776 2858431783913217196998869 := by
  unfold tailWord_5566776
  simp only [CollatzResearch.WordTrace]
  refine ⟨101518500440264378247228091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135358000587019170996304121 101518500440264378247228091)
  ·
    refine ⟨152277750660396567370842137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101518500440264378247228091 152277750660396567370842137)
    ·
      refine ⟨114208312995297425528131603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152277750660396567370842137 114208312995297425528131603)
      ·
        refine ⟨171312469492946138292197405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114208312995297425528131603 171312469492946138292197405)
        ·
          refine ⟨64242176059854801859574027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171312469492946138292197405 64242176059854801859574027)
          ·
            refine ⟨96363264089782202789361041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64242176059854801859574027 96363264089782202789361041)
            ·
              refine ⟨72272448067336652092020781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96363264089782202789361041 72272448067336652092020781)
              ·
                refine ⟨27102168025251244534507793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72272448067336652092020781 27102168025251244534507793)
                ·
                  refine ⟨20326626018938433400880845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27102168025251244534507793 20326626018938433400880845)
                  ·
                    refine ⟨7622484757101912525330317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20326626018938433400880845 7622484757101912525330317)
                    ·
                      refine ⟨2858431783913217196998869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7622484757101912525330317 2858431783913217196998869)
                      ·
                        rfl

theorem cell23_5566776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_5566776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566776 prefixEnd_5566776 := by exact prefixLift 5566776
  have htrace : WordTrace (prefixWord ++ tailWord_5566776) baseStart_5566776 baseEnd_5566776 := by
    simpa [prefixWord, tailWord_5566776, baseEnd_5566776] using wordTrace_append hprefix tailTrace_5566776
  have hstable : (prefixWord ++ tailWord_5566776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566776).length < 2 ^ (prefixWord ++ tailWord_5566776).sum := by decide
  have hdescent : baseEnd_5566776 < baseStart_5566776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566777 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5566777 : Nat := 118140960795 + 5566777 * 2 ^ 59
def prefixEnd_5566777 : Nat := 4983230072969 + 3 ^ 40 * 5566777 * 2
def baseEnd_5566777 : Nat := 2858432297393871693086365

theorem tailTrace_5566777 : CollatzResearch.WordTrace tailWord_5566777 prefixEnd_5566777 2858432297393871693086365 := by
  unfold tailWord_5566777
  simp only [CollatzResearch.WordTrace]
  refine ⟨203037037353525133665242585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135358024902350089110161723 203037037353525133665242585)
  ·
    refine ⟨152277778015143850248931939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203037037353525133665242585 152277778015143850248931939)
    ·
      refine ⟨228416667022715775373397909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152277778015143850248931939 228416667022715775373397909)
      ·
        refine ⟨10707031266689801970628027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228416667022715775373397909 10707031266689801970628027)
        ·
          refine ⟨16060546900034702955942041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10707031266689801970628027 16060546900034702955942041)
          ·
            refine ⟨12045410175026027216956531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16060546900034702955942041 12045410175026027216956531)
            ·
              refine ⟨18068115262539040825434797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045410175026027216956531 18068115262539040825434797)
              ·
                refine ⟨6775543223452140309538049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18068115262539040825434797 6775543223452140309538049)
                ·
                  refine ⟨5081657417589105232153537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6775543223452140309538049 5081657417589105232153537)
                  ·
                    refine ⟨3811243063191828924115153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5081657417589105232153537 3811243063191828924115153)
                    ·
                      refine ⟨2858432297393871693086365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811243063191828924115153 2858432297393871693086365)
                      ·
                        rfl

theorem cell23_5566777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5566777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566777 prefixEnd_5566777 := by exact prefixLift 5566777
  have htrace : WordTrace (prefixWord ++ tailWord_5566777) baseStart_5566777 baseEnd_5566777 := by
    simpa [prefixWord, tailWord_5566777, baseEnd_5566777] using wordTrace_append hprefix tailTrace_5566777
  have hstable : (prefixWord ++ tailWord_5566777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566777).length < 2 ^ (prefixWord ++ tailWord_5566777).sum := by decide
  have hdescent : baseEnd_5566777 < baseStart_5566777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566843 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 3, 4]
def baseStart_5566843 : Nat := 118140960795 + 5566843 * 2 ^ 59
def prefixEnd_5566843 : Nat := 4983230072969 + 3 ^ 40 * 5566843 * 2
def baseEnd_5566843 : Nat := 952822062372356144953687

theorem tailTrace_5566843 : CollatzResearch.WordTrace tailWord_5566843 prefixEnd_5566843 952822062372356144953687 := by
  unfold tailWord_5566843
  simp only [CollatzResearch.WordTrace]
  refine ⟨203039444571286026937145183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135359629714190684624763455 203039444571286026937145183)
  ·
    refine ⟨304559166856929040405717775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203039444571286026937145183 304559166856929040405717775)
    ·
      refine ⟨456838750285393560608576663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304559166856929040405717775 456838750285393560608576663)
      ·
        refine ⟨685258125428090340912864995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456838750285393560608576663 685258125428090340912864995)
        ·
          refine ⟨1027887188142135511369297493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685258125428090340912864995 1027887188142135511369297493)
          ·
            refine ⟨12045552986040650523858955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1027887188142135511369297493 12045552986040650523858955)
            ·
              refine ⟨18068329479060975785788433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045552986040650523858955 18068329479060975785788433)
              ·
                refine ⟨13551247109295731839341325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18068329479060975785788433 13551247109295731839341325)
                ·
                  refine ⟨5081717665985899439752997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13551247109295731839341325 5081717665985899439752997)
                  ·
                    refine ⟨952822062372356144953687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081717665985899439752997 952822062372356144953687)
                    ·
                      rfl

theorem cell23_5566843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 4].length) (baseStart_5566843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566843 prefixEnd_5566843 := by exact prefixLift 5566843
  have htrace : WordTrace (prefixWord ++ tailWord_5566843) baseStart_5566843 baseEnd_5566843 := by
    simpa [prefixWord, tailWord_5566843, baseEnd_5566843] using wordTrace_append hprefix tailTrace_5566843
  have hstable : (prefixWord ++ tailWord_5566843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566843).length < 2 ^ (prefixWord ++ tailWord_5566843).sum := by decide
  have hdescent : baseEnd_5566843 < baseStart_5566843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566856 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 8]
def baseStart_5566856 : Nat := 118140960795 + 5566856 * 2 ^ 59
def prefixEnd_5566856 : Nat := 4983230072969 + 3 ^ 40 * 5566856 * 2
def baseEnd_5566856 : Nat := 317608095818397431555389

theorem tailTrace_5566856 : CollatzResearch.WordTrace tailWord_5566856 prefixEnd_5566856 317608095818397431555389 := by
  unfold tailWord_5566856
  simp only [CollatzResearch.WordTrace]
  refine ⟨101519959360119465078684211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135359945813492620104912281 101519959360119465078684211)
  ·
    refine ⟨152279939040179197618026317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101519959360119465078684211 152279939040179197618026317)
    ·
      refine ⟨57104977140067199106759869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152279939040179197618026317 57104977140067199106759869)
      ·
        refine ⟨21414366427525199665034951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57104977140067199106759869 21414366427525199665034951)
        ·
          refine ⟨32121549641287799497552427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21414366427525199665034951 32121549641287799497552427)
          ·
            refine ⟨48182324461931699246328641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32121549641287799497552427 48182324461931699246328641)
            ·
              refine ⟨36136743346448774434746481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48182324461931699246328641 36136743346448774434746481)
              ·
                refine ⟨27102557509836580826059861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36136743346448774434746481 27102557509836580826059861)
                ·
                  refine ⟨317608095818397431555389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27102557509836580826059861 317608095818397431555389)
                  ·
                    rfl

theorem cell23_5566856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_5566856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566856 prefixEnd_5566856 := by exact prefixLift 5566856
  have htrace : WordTrace (prefixWord ++ tailWord_5566856) baseStart_5566856 baseEnd_5566856 := by
    simpa [prefixWord, tailWord_5566856, baseEnd_5566856] using wordTrace_append hprefix tailTrace_5566856
  have hstable : (prefixWord ++ tailWord_5566856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566856).length < 2 ^ (prefixWord ++ tailWord_5566856).sum := by decide
  have hdescent : baseEnd_5566856 < baseStart_5566856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566860 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_5566860 : Nat := 118140960795 + 5566860 * 2 ^ 59
def prefixEnd_5566860 : Nat := 4983230072969 + 3 ^ 40 * 5566860 * 2
def baseEnd_5566860 : Nat := 952824972096064956116161

theorem tailTrace_5566860 : CollatzResearch.WordTrace tailWord_5566860 prefixEnd_5566860 952824972096064956116161 := by
  unfold tailWord_5566860
  simp only [CollatzResearch.WordTrace]
  refine ⟨101520032306112219420257017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135360043074816292560342689 101520032306112219420257017)
  ·
    refine ⟨76140024229584164565192763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101520032306112219420257017 76140024229584164565192763)
    ·
      refine ⟨114210036344376246847789145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76140024229584164565192763 114210036344376246847789145)
      ·
        refine ⟨85657527258282185135841859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114210036344376246847789145 85657527258282185135841859)
        ·
          refine ⟨128486290887423277703762789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85657527258282185135841859 128486290887423277703762789)
          ·
            refine ⟨24091179541391864569455523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128486290887423277703762789 24091179541391864569455523)
            ·
              refine ⟨36136769312087796854183285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24091179541391864569455523 36136769312087796854183285)
              ·
                refine ⟨3387822123008230955079683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36136769312087796854183285 3387822123008230955079683)
                ·
                  refine ⟨5081733184512346432619525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387822123008230955079683 5081733184512346432619525)
                  ·
                    refine ⟨952824972096064956116161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081733184512346432619525 952824972096064956116161)
                    ·
                      rfl

theorem cell23_5566860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_5566860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566860 prefixEnd_5566860 := by exact prefixLift 5566860
  have htrace : WordTrace (prefixWord ++ tailWord_5566860) baseStart_5566860 baseEnd_5566860 := by
    simpa [prefixWord, tailWord_5566860, baseEnd_5566860] using wordTrace_append hprefix tailTrace_5566860
  have hstable : (prefixWord ++ tailWord_5566860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566860).length < 2 ^ (prefixWord ++ tailWord_5566860).sum := by decide
  have hdescent : baseEnd_5566860 < baseStart_5566860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566903 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 1, 5]
def baseStart_5566903 : Nat := 118140960795 + 5566903 * 2 ^ 59
def prefixEnd_5566903 : Nat := 4983230072969 + 3 ^ 40 * 5566903 * 2
def baseEnd_5566903 : Nat := 952832331985446066703595

theorem tailTrace_5566903 : CollatzResearch.WordTrace tailWord_5566903 prefixEnd_5566903 952832331985446066703595 := by
  unfold tailWord_5566903
  simp only [CollatzResearch.WordTrace]
  refine ⟨203041632951068657184329363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135361088634045771456219575 203041632951068657184329363)
  ·
    refine ⟨304562449426602985776494045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203041632951068657184329363 304562449426602985776494045)
    ·
      refine ⟨114210918534976119666185267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304562449426602985776494045 114210918534976119666185267)
      ·
        refine ⟨171316377802464179499277901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114210918534976119666185267 171316377802464179499277901)
        ·
          refine ⟨64243641675924067312229213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171316377802464179499277901 64243641675924067312229213)
          ·
            refine ⟨24091365628471525242085955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64243641675924067312229213 24091365628471525242085955)
            ·
              refine ⟨36137048442707287863128933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24091365628471525242085955 36137048442707287863128933)
              ·
                refine ⟨6775696583007616474336675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36137048442707287863128933 6775696583007616474336675)
                ·
                  refine ⟨10163544874511424711505013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6775696583007616474336675 10163544874511424711505013)
                  ·
                    refine ⟨952832331985446066703595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10163544874511424711505013 952832331985446066703595)
                    ·
                      rfl

theorem cell23_5566903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_5566903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566903 prefixEnd_5566903 := by exact prefixLift 5566903
  have htrace : WordTrace (prefixWord ++ tailWord_5566903) baseStart_5566903 baseEnd_5566903 := by
    simpa [prefixWord, tailWord_5566903, baseEnd_5566903] using wordTrace_append hprefix tailTrace_5566903
  have hstable : (prefixWord ++ tailWord_5566903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566903).length < 2 ^ (prefixWord ++ tailWord_5566903).sum := by decide
  have hdescent : baseEnd_5566903 < baseStart_5566903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566906 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_5566906 : Nat := 118140960795 + 5566906 * 2 ^ 59
def prefixEnd_5566906 : Nat := 4983230072969 + 3 ^ 40 * 5566906 * 2
def baseEnd_5566906 : Nat := 2858498536398301688373271

theorem tailTrace_5566906 : CollatzResearch.WordTrace tailWord_5566906 prefixEnd_5566906 2858498536398301688373271 := by
  unfold tailWord_5566906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50760435592514447174172143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135361161580038525797792381 50760435592514447174172143)
  ·
    refine ⟨76140653388771670761258215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50760435592514447174172143 76140653388771670761258215)
    ·
      refine ⟨114210980083157506141887323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76140653388771670761258215 114210980083157506141887323)
      ·
        refine ⟨171316470124736259212830985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114210980083157506141887323 171316470124736259212830985)
        ·
          refine ⟨128487352593552194409623239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171316470124736259212830985 128487352593552194409623239)
          ·
            refine ⟨192731028890328291614434859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128487352593552194409623239 192731028890328291614434859)
            ·
              refine ⟨289096543335492437421652289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192731028890328291614434859 289096543335492437421652289)
              ·
                refine ⟨216822407501619328066239217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289096543335492437421652289 216822407501619328066239217)
                ·
                  refine ⟨162616805626214496049679413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216822407501619328066239217 162616805626214496049679413)
                  ·
                    refine ⟨15245325527457609004657445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162616805626214496049679413 15245325527457609004657445)
                    ·
                      refine ⟨2858498536398301688373271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15245325527457609004657445 2858498536398301688373271)
                      ·
                        rfl

theorem cell23_5566906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_5566906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566906 prefixEnd_5566906 := by exact prefixLift 5566906
  have htrace : WordTrace (prefixWord ++ tailWord_5566906) baseStart_5566906 baseEnd_5566906 := by
    simpa [prefixWord, tailWord_5566906, baseEnd_5566906] using wordTrace_append hprefix tailTrace_5566906
  have hstable : (prefixWord ++ tailWord_5566906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566906).length < 2 ^ (prefixWord ++ tailWord_5566906).sum := by decide
  have hdescent : baseEnd_5566906 < baseStart_5566906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566910 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_5566910 : Nat := 118140960795 + 5566910 * 2 ^ 59
def prefixEnd_5566910 : Nat := 4983230072969 + 3 ^ 40 * 5566910 * 2
def baseEnd_5566910 : Nat := 2858500590320919672723253

theorem tailTrace_5566910 : CollatzResearch.WordTrace tailWord_5566910 prefixEnd_5566910 2858500590320919672723253 := by
  unfold tailWord_5566910
  simp only [CollatzResearch.WordTrace]
  refine ⟨25380236032755412172479273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135361258841362198253222789 25380236032755412172479273)
  ·
    refine ⟨19035177024566559129359455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25380236032755412172479273 19035177024566559129359455)
    ·
      refine ⟨28552765536849838694039183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19035177024566559129359455 28552765536849838694039183)
      ·
        refine ⟨42829148305274758041058775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28552765536849838694039183 42829148305274758041058775)
        ·
          refine ⟨64243722457912137061588163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42829148305274758041058775 64243722457912137061588163)
          ·
            refine ⟨96365583686868205592382245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64243722457912137061588163 96365583686868205592382245)
            ·
              refine ⟨18068546941287788548571671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96365583686868205592382245 18068546941287788548571671)
              ·
                refine ⟨27102820411931682822857507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18068546941287788548571671 27102820411931682822857507)
                ·
                  refine ⟨40654230617897524234286261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27102820411931682822857507 40654230617897524234286261)
                  ·
                    refine ⟨3811334120427892896964337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40654230617897524234286261 3811334120427892896964337)
                    ·
                      refine ⟨2858500590320919672723253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811334120427892896964337 2858500590320919672723253)
                      ·
                        rfl

theorem cell23_5566910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_5566910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566910 prefixEnd_5566910 := by exact prefixLift 5566910
  have htrace : WordTrace (prefixWord ++ tailWord_5566910) baseStart_5566910 baseEnd_5566910 := by
    simpa [prefixWord, tailWord_5566910, baseEnd_5566910] using wordTrace_append hprefix tailTrace_5566910
  have hstable : (prefixWord ++ tailWord_5566910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566910).length < 2 ^ (prefixWord ++ tailWord_5566910).sum := by decide
  have hdescent : baseEnd_5566910 < baseStart_5566910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566943 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_5566943 : Nat := 118140960795 + 5566943 * 2 ^ 59
def prefixEnd_5566943 : Nat := 4983230072969 + 3 ^ 40 * 5566943 * 2
def baseEnd_5566943 : Nat := 2858517535182518043610601

theorem tailTrace_5566943 : CollatzResearch.WordTrace tailWord_5566943 prefixEnd_5566943 2858517535182518043610601 := by
  unfold tailWord_5566943
  simp only [CollatzResearch.WordTrace]
  refine ⟨203043091870923744015785483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135362061247282496010523655 203043091870923744015785483)
  ·
    refine ⟨304564637806385616023678225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203043091870923744015785483 304564637806385616023678225)
    ·
      refine ⟨228423478354789212017758669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304564637806385616023678225 228423478354789212017758669)
      ·
        refine ⟨85658804383045954506659501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228423478354789212017758669 85658804383045954506659501)
        ·
          refine ⟨32122051643642232939997313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85658804383045954506659501 32122051643642232939997313)
          ·
            refine ⟨24091538732731674704997985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32122051643642232939997313 24091538732731674704997985)
            ·
              refine ⟨18068654049548756028748489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24091538732731674704997985 18068654049548756028748489)
              ·
                refine ⟨13551490537161567021561367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18068654049548756028748489 13551490537161567021561367)
                ·
                  refine ⟨20327235805742350532342051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13551490537161567021561367 20327235805742350532342051)
                  ·
                    refine ⟨30490853708613525798513077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20327235805742350532342051 30490853708613525798513077)
                    ·
                      refine ⟨2858517535182518043610601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30490853708613525798513077 2858517535182518043610601)
                      ·
                        rfl

theorem cell23_5566943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_5566943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566943 prefixEnd_5566943 := by exact prefixLift 5566943
  have htrace : WordTrace (prefixWord ++ tailWord_5566943) baseStart_5566943 baseEnd_5566943 := by
    simpa [prefixWord, tailWord_5566943, baseEnd_5566943] using wordTrace_append hprefix tailTrace_5566943
  have hstable : (prefixWord ++ tailWord_5566943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566943).length < 2 ^ (prefixWord ++ tailWord_5566943).sum := by decide
  have hdescent : baseEnd_5566943 < baseStart_5566943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566957 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5566957 : Nat := 118140960795 + 5566957 * 2 ^ 59
def prefixEnd_5566957 : Nat := 4983230072969 + 3 ^ 40 * 5566957 * 2
def baseEnd_5566957 : Nat := 2858524723911680988835537

theorem tailTrace_5566957 : CollatzResearch.WordTrace tailWord_5566957 prefixEnd_5566957 2858524723911680988835537 := by
  unfold tailWord_5566957
  simp only [CollatzResearch.WordTrace]
  refine ⟨203043602492873024406795125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135362401661915349604530083 203043602492873024406795125)
  ·
    refine ⟨19035337733706846038137043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203043602492873024406795125 19035337733706846038137043)
    ·
      refine ⟨28553006600560269057205565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19035337733706846038137043 28553006600560269057205565)
      ·
        refine ⟨10707377475210100896452087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28553006600560269057205565 10707377475210100896452087)
        ·
          refine ⟨16061066212815151344678131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10707377475210100896452087 16061066212815151344678131)
          ·
            refine ⟨24091599319222727017017197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16061066212815151344678131 24091599319222727017017197)
            ·
              refine ⟨9034349744708522631381449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24091599319222727017017197 9034349744708522631381449)
              ·
                refine ⟨6775762308531391973536087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9034349744708522631381449 6775762308531391973536087)
                ·
                  refine ⟨10163643462797087960304131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6775762308531391973536087 10163643462797087960304131)
                  ·
                    refine ⟨15245465194195631940456197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10163643462797087960304131 15245465194195631940456197)
                    ·
                      refine ⟨2858524723911680988835537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15245465194195631940456197 2858524723911680988835537)
                      ·
                        rfl

theorem cell23_5566957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5566957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566957 prefixEnd_5566957 := by exact prefixLift 5566957
  have htrace : WordTrace (prefixWord ++ tailWord_5566957) baseStart_5566957 baseEnd_5566957 := by
    simpa [prefixWord, tailWord_5566957, baseEnd_5566957] using wordTrace_append hprefix tailTrace_5566957
  have hstable : (prefixWord ++ tailWord_5566957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566957).length < 2 ^ (prefixWord ++ tailWord_5566957).sum := by decide
  have hdescent : baseEnd_5566957 < baseStart_5566957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5566976 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_5566976 : Nat := 118140960795 + 5566976 * 2 ^ 59
def prefixEnd_5566976 : Nat := 4983230072969 + 3 ^ 40 * 5566976 * 2
def baseEnd_5566976 : Nat := 952844826681372138165983

theorem tailTrace_5566976 : CollatzResearch.WordTrace tailWord_5566976 prefixEnd_5566976 952844826681372138165983 := by
  unfold tailWord_5566976
  simp only [CollatzResearch.WordTrace]
  refine ⟨101522147739902095325868391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135362863653202793767824521 101522147739902095325868391)
  ·
    refine ⟨152283221609853142988802587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101522147739902095325868391 152283221609853142988802587)
    ·
      refine ⟨228424832414779714483203881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152283221609853142988802587 228424832414779714483203881)
      ·
        refine ⟨171318624311084785862402911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228424832414779714483203881 171318624311084785862402911)
        ·
          refine ⟨256977936466627178793604367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171318624311084785862402911 256977936466627178793604367)
          ·
            refine ⟨385466904699940768190406551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256977936466627178793604367 385466904699940768190406551)
            ·
              refine ⟨578200357049911152285609827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385466904699940768190406551 578200357049911152285609827)
              ·
                refine ⟨867300535574866728428414741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578200357049911152285609827 867300535574866728428414741)
                ·
                  refine ⟨40654712605071877895081941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 867300535574866728428414741 40654712605071877895081941)
                  ·
                    refine ⟨952844826681372138165983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40654712605071877895081941 952844826681372138165983)
                    ·
                      rfl

theorem cell23_5566976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_5566976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5566976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5566976 prefixEnd_5566976 := by exact prefixLift 5566976
  have htrace : WordTrace (prefixWord ++ tailWord_5566976) baseStart_5566976 baseEnd_5566976 := by
    simpa [prefixWord, tailWord_5566976, baseEnd_5566976] using wordTrace_append hprefix tailTrace_5566976
  have hstable : (prefixWord ++ tailWord_5566976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5566976).length < 2 ^ (prefixWord ++ tailWord_5566976).sum := by decide
  have hdescent : baseEnd_5566976 < baseStart_5566976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5566976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567028 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5567028 : Nat := 118140960795 + 5567028 * 2 ^ 59
def prefixEnd_5567028 : Nat := 4983230072969 + 3 ^ 40 * 5567028 * 2
def baseEnd_5567028 : Nat := 2858561181038150211047711

theorem tailTrace_5567028 : CollatzResearch.WordTrace tailWord_5567028 prefixEnd_5567028 2858561181038150211047711 := by
  unfold tailWord_5567028
  simp only [CollatzResearch.WordTrace]
  refine ⟨101523096037807901766314869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135364128050410535688419825 101523096037807901766314869)
  ·
    refine ⟨9517790253544490790592019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101523096037807901766314869 9517790253544490790592019)
    ·
      refine ⟨14276685380316736185888029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9517790253544490790592019 14276685380316736185888029)
      ·
        refine ⟨5353757017618776069708011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14276685380316736185888029 5353757017618776069708011)
        ·
          refine ⟨8030635526428164104562017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5353757017618776069708011 8030635526428164104562017)
          ·
            refine ⟨6022976644821123078421513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8030635526428164104562017 6022976644821123078421513)
            ·
              refine ⟨4517232483615842308816135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6022976644821123078421513 4517232483615842308816135)
              ·
                refine ⟨6775848725423763463224203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517232483615842308816135 6775848725423763463224203)
                ·
                  refine ⟨10163773088135645194836305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6775848725423763463224203 10163773088135645194836305)
                  ·
                    refine ⟨7622829816101733896127229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10163773088135645194836305 7622829816101733896127229)
                    ·
                      refine ⟨2858561181038150211047711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7622829816101733896127229 2858561181038150211047711)
                      ·
                        rfl

theorem cell23_5567028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5567028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567028 prefixEnd_5567028 := by exact prefixLift 5567028
  have htrace : WordTrace (prefixWord ++ tailWord_5567028) baseStart_5567028 baseEnd_5567028 := by
    simpa [prefixWord, tailWord_5567028, baseEnd_5567028] using wordTrace_append hprefix tailTrace_5567028
  have hstable : (prefixWord ++ tailWord_5567028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567028).length < 2 ^ (prefixWord ++ tailWord_5567028).sum := by decide
  have hdescent : baseEnd_5567028 < baseStart_5567028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567033 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5567033 : Nat := 118140960795 + 5567033 * 2 ^ 59
def prefixEnd_5567033 : Nat := 4983230072969 + 3 ^ 40 * 5567033 * 2
def baseEnd_5567033 : Nat := 2858563748441422691485187

theorem tailTrace_5567033 : CollatzResearch.WordTrace tailWord_5567033 prefixEnd_5567033 2858563748441422691485187 := by
  unfold tailWord_5567033
  simp only [CollatzResearch.WordTrace]
  refine ⟨203046374440597689386561753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135364249627065126257707835 203046374440597689386561753)
  ·
    refine ⟨152284780830448267039921315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203046374440597689386561753 152284780830448267039921315)
    ·
      refine ⟨228427171245672400559881973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152284780830448267039921315 228427171245672400559881973)
      ·
        refine ⟨21415047304281787552488935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228427171245672400559881973 21415047304281787552488935)
        ·
          refine ⟨32122570956422681328733403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21415047304281787552488935 32122570956422681328733403)
          ·
            refine ⟨48183856434634021993100105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32122570956422681328733403 48183856434634021993100105)
            ·
              refine ⟨36137892325975516494825079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48183856434634021993100105 36137892325975516494825079)
              ·
                refine ⟨54206838488963274742237619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36137892325975516494825079 54206838488963274742237619)
                ·
                  refine ⟨81310257733444912113356429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54206838488963274742237619 81310257733444912113356429)
                  ·
                    refine ⟨30491346650041842042508661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81310257733444912113356429 30491346650041842042508661)
                    ·
                      refine ⟨2858563748441422691485187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30491346650041842042508661 2858563748441422691485187)
                      ·
                        rfl

theorem cell23_5567033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5567033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567033 prefixEnd_5567033 := by exact prefixLift 5567033
  have htrace : WordTrace (prefixWord ++ tailWord_5567033) baseStart_5567033 baseEnd_5567033 := by
    simpa [prefixWord, tailWord_5567033, baseEnd_5567033] using wordTrace_append hprefix tailTrace_5567033
  have hstable : (prefixWord ++ tailWord_5567033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567033).length < 2 ^ (prefixWord ++ tailWord_5567033).sum := by decide
  have hdescent : baseEnd_5567033 < baseStart_5567033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567034 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2]
def baseStart_5567034 : Nat := 118140960795 + 5567034 * 2 ^ 59
def prefixEnd_5567034 : Nat := 4983230072969 + 3 ^ 40 * 5567034 * 2
def baseEnd_5567034 : Nat := 2858564261922077187572683

theorem tailTrace_5567034 : CollatzResearch.WordTrace tailWord_5567034 prefixEnd_5567034 2858564261922077187572683 := by
  unfold tailWord_5567034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50761602728398516639337039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135364273942396044371565437 50761602728398516639337039)
  ·
    refine ⟨76142404092597774959005559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50761602728398516639337039 76142404092597774959005559)
    ·
      refine ⟨114213606138896662438508339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76142404092597774959005559 114213606138896662438508339)
      ·
        refine ⟨171320409208344993657762509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114213606138896662438508339 171320409208344993657762509)
        ·
          refine ⟨64245153453129372621660941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171320409208344993657762509 64245153453129372621660941)
          ·
            refine ⟨24091932544923514733122853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64245153453129372621660941 24091932544923514733122853)
            ·
              refine ⟨4517237352173159012460535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24091932544923514733122853 4517237352173159012460535)
              ·
                refine ⟨6775856028259738518690803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517237352173159012460535 6775856028259738518690803)
                ·
                  refine ⟨10163784042389607778036205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6775856028259738518690803 10163784042389607778036205)
                  ·
                    refine ⟨3811419015896102916763577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10163784042389607778036205 3811419015896102916763577)
                    ·
                      refine ⟨2858564261922077187572683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811419015896102916763577 2858564261922077187572683)
                      ·
                        rfl

theorem cell23_5567034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_5567034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567034 prefixEnd_5567034 := by exact prefixLift 5567034
  have htrace : WordTrace (prefixWord ++ tailWord_5567034) baseStart_5567034 baseEnd_5567034 := by
    simpa [prefixWord, tailWord_5567034, baseEnd_5567034] using wordTrace_append hprefix tailTrace_5567034
  have hstable : (prefixWord ++ tailWord_5567034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567034).length < 2 ^ (prefixWord ++ tailWord_5567034).sum := by decide
  have hdescent : baseEnd_5567034 < baseStart_5567034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567060 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_5567060 : Nat := 118140960795 + 5567060 * 2 ^ 59
def prefixEnd_5567060 : Nat := 4983230072969 + 3 ^ 40 * 5567060 * 2
def baseEnd_5567060 : Nat := 2858577612419094085847563

theorem tailTrace_5567060 : CollatzResearch.WordTrace tailWord_5567060 prefixEnd_5567060 2858577612419094085847563 := by
  unfold tailWord_5567060
  simp only [CollatzResearch.WordTrace]
  refine ⟨101523679605749936498897317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135364906140999915331863089 101523679605749936498897317)
  ·
    refine ⟨19035689926078113093543247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101523679605749936498897317 19035689926078113093543247)
    ·
      refine ⟨28553534889117169640314871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19035689926078113093543247 28553534889117169640314871)
      ·
        refine ⟨42830302333675754460472307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28553534889117169640314871 42830302333675754460472307)
        ·
          refine ⟨64245453500513631690708461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42830302333675754460472307 64245453500513631690708461)
          ·
            refine ⟨24092045062692611884015673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64245453500513631690708461 24092045062692611884015673)
            ·
              refine ⟨18069033797019458913011755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24092045062692611884015673 18069033797019458913011755)
              ·
                refine ⟨27103550695529188369517633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18069033797019458913011755 27103550695529188369517633)
                ·
                  refine ⟨20327663021646891277138225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27103550695529188369517633 20327663021646891277138225)
                  ·
                    refine ⟨15245747266235168457853669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20327663021646891277138225 15245747266235168457853669)
                    ·
                      refine ⟨2858577612419094085847563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15245747266235168457853669 2858577612419094085847563)
                      ·
                        rfl

theorem cell23_5567060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_5567060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567060 prefixEnd_5567060 := by exact prefixLift 5567060
  have htrace : WordTrace (prefixWord ++ tailWord_5567060) baseStart_5567060 baseEnd_5567060 := by
    simpa [prefixWord, tailWord_5567060, baseEnd_5567060] using wordTrace_append hprefix tailTrace_5567060
  have hstable : (prefixWord ++ tailWord_5567060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567060).length < 2 ^ (prefixWord ++ tailWord_5567060).sum := by decide
  have hdescent : baseEnd_5567060 < baseStart_5567060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567103 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_5567103 : Nat := 118140960795 + 5567103 * 2 ^ 59
def prefixEnd_5567103 : Nat := 4983230072969 + 3 ^ 40 * 5567103 * 2
def baseEnd_5567103 : Nat := 2858599692087237417609865

theorem tailTrace_5567103 : CollatzResearch.WordTrace tailWord_5567103 prefixEnd_5567103 2858599692087237417609865 := by
  unfold tailWord_5567103
  simp only [CollatzResearch.WordTrace]
  refine ⟨203048927550344091341609963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135365951700229394227739975 203048927550344091341609963)
  ·
    refine ⟨304573391325516137012414945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203048927550344091341609963 304573391325516137012414945)
    ·
      refine ⟨228430043494137102759311209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304573391325516137012414945 228430043494137102759311209)
      ·
        refine ⟨171322532620602827069483407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228430043494137102759311209 171322532620602827069483407)
        ·
          refine ⟨256983798930904240604225111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171322532620602827069483407 256983798930904240604225111)
          ·
            refine ⟨385475698396356360906337667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256983798930904240604225111 385475698396356360906337667)
            ·
              refine ⟨578213547594534541359506501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385475698396356360906337667 578213547594534541359506501)
              ·
                refine ⟨108415040173975226504907469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578213547594534541359506501 108415040173975226504907469)
                ·
                  refine ⟨40655640065240709939340301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108415040173975226504907469 40655640065240709939340301)
                  ·
                    refine ⟨15245865024465266227252613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40655640065240709939340301 15245865024465266227252613)
                    ·
                      refine ⟨2858599692087237417609865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15245865024465266227252613 2858599692087237417609865)
                      ·
                        rfl

theorem cell23_5567103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_5567103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567103 prefixEnd_5567103 := by exact prefixLift 5567103
  have htrace : WordTrace (prefixWord ++ tailWord_5567103) baseStart_5567103 baseEnd_5567103 := by
    simpa [prefixWord, tailWord_5567103, baseEnd_5567103] using wordTrace_append hprefix tailTrace_5567103
  have hstable : (prefixWord ++ tailWord_5567103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567103).length < 2 ^ (prefixWord ++ tailWord_5567103).sum := by decide
  have hdescent : baseEnd_5567103 < baseStart_5567103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567164 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_5567164 : Nat := 118140960795 + 5567164 * 2 ^ 59
def prefixEnd_5567164 : Nat := 4983230072969 + 3 ^ 40 * 5567164 * 2
def baseEnd_5567164 : Nat := 952877004802387226315695

theorem tailTrace_5567164 : CollatzResearch.WordTrace tailWord_5567164 prefixEnd_5567164 952877004802387226315695 := by
  unfold tailWord_5567164
  simp only [CollatzResearch.WordTrace]
  refine ⟨101525576201561549379790273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135367434935415399173053697 101525576201561549379790273)
  ·
    refine ⟨76144182151171162034842705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101525576201561549379790273 76144182151171162034842705)
    ·
      refine ⟨57108136613378371526132029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76144182151171162034842705 57108136613378371526132029)
      ·
        refine ⟨21415551230016889322299511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57108136613378371526132029 21415551230016889322299511)
        ·
          refine ⟨32123326845025333983449267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21415551230016889322299511 32123326845025333983449267)
          ·
            refine ⟨48184990267538000975173901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32123326845025333983449267 48184990267538000975173901)
            ·
              refine ⟨18069371350326750365690213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48184990267538000975173901 18069371350326750365690213)
              ·
                refine ⟨3388007128186265693566915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18069371350326750365690213 3388007128186265693566915)
                ·
                  refine ⟨5082010692279398540350373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388007128186265693566915 5082010692279398540350373)
                  ·
                    refine ⟨952877004802387226315695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082010692279398540350373 952877004802387226315695)
                    ·
                      rfl

theorem cell23_5567164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_5567164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567164 prefixEnd_5567164 := by exact prefixLift 5567164
  have htrace : WordTrace (prefixWord ++ tailWord_5567164) baseStart_5567164 baseEnd_5567164 := by
    simpa [prefixWord, tailWord_5567164, baseEnd_5567164] using wordTrace_append hprefix tailTrace_5567164
  have hstable : (prefixWord ++ tailWord_5567164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567164).length < 2 ^ (prefixWord ++ tailWord_5567164).sum := by decide
  have hdescent : baseEnd_5567164 < baseStart_5567164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567173 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_5567173 : Nat := 118140960795 + 5567173 * 2 ^ 59
def prefixEnd_5567173 : Nat := 4983230072969 + 3 ^ 40 * 5567173 * 2
def baseEnd_5567173 : Nat := 952878545244350714578181

theorem tailTrace_5567173 : CollatzResearch.WordTrace tailWord_5567173 prefixEnd_5567173 952878545244350714578181 := by
  unfold tailWord_5567173
  simp only [CollatzResearch.WordTrace]
  refine ⟨203051480660090493296658173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135367653773393662197772115 203051480660090493296658173)
  ·
    refine ⟨76144305247533934986246815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203051480660090493296658173 76144305247533934986246815)
    ·
      refine ⟨114216457871300902479370223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76144305247533934986246815 114216457871300902479370223)
      ·
        refine ⟨171324686806951353719055335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114216457871300902479370223 171324686806951353719055335)
        ·
          refine ⟨256987030210427030578583003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171324686806951353719055335 256987030210427030578583003)
          ·
            refine ⟨385480545315640545867874505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256987030210427030578583003 385480545315640545867874505)
            ·
              refine ⟨289110408986730409400905879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385480545315640545867874505 289110408986730409400905879)
              ·
                refine ⟨433665613480095614101358819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289110408986730409400905879 433665613480095614101358819)
                ·
                  refine ⟨650498420220143421152038229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433665613480095614101358819 650498420220143421152038229)
                  ·
                    refine ⟨952878545244350714578181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 650498420220143421152038229 952878545244350714578181)
                    ·
                      rfl

theorem cell23_5567173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_5567173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567173 prefixEnd_5567173 := by exact prefixLift 5567173
  have htrace : WordTrace (prefixWord ++ tailWord_5567173) baseStart_5567173 baseEnd_5567173 := by
    simpa [prefixWord, tailWord_5567173, baseEnd_5567173] using wordTrace_append hprefix tailTrace_5567173
  have hstable : (prefixWord ++ tailWord_5567173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567173).length < 2 ^ (prefixWord ++ tailWord_5567173).sum := by decide
  have hdescent : baseEnd_5567173 < baseStart_5567173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567181 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5567181 : Nat := 118140960795 + 5567181 * 2 ^ 59
def prefixEnd_5567181 : Nat := 4983230072969 + 3 ^ 40 * 5567181 * 2
def baseEnd_5567181 : Nat := 952879914526096037478169

theorem tailTrace_5567181 : CollatzResearch.WordTrace tailWord_5567181 prefixEnd_5567181 952879914526096037478169 := by
  unfold tailWord_5567181
  simp only [CollatzResearch.WordTrace]
  refine ⟨203051772444061510662949397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135367848296041007108632931 203051772444061510662949397)
  ·
    refine ⟨9518051833315383312325753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203051772444061510662949397 9518051833315383312325753)
    ·
      refine ⟨7138538874986537484244315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9518051833315383312325753 7138538874986537484244315)
      ·
        refine ⟨10707808312479806226366473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7138538874986537484244315 10707808312479806226366473)
        ·
          refine ⟨8030856234359854669774855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10707808312479806226366473 8030856234359854669774855)
          ·
            refine ⟨12046284351539782004662283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8030856234359854669774855 12046284351539782004662283)
            ·
              refine ⟨18069426527309673006993425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12046284351539782004662283 18069426527309673006993425)
              ·
                refine ⟨13552069895482254755245069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18069426527309673006993425 13552069895482254755245069)
                ·
                  refine ⟨5082026210805845533216901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13552069895482254755245069 5082026210805845533216901)
                  ·
                    refine ⟨952879914526096037478169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082026210805845533216901 952879914526096037478169)
                    ·
                      rfl

theorem cell23_5567181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5567181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567181 prefixEnd_5567181 := by exact prefixLift 5567181
  have htrace : WordTrace (prefixWord ++ tailWord_5567181) baseStart_5567181 baseEnd_5567181 := by
    simpa [prefixWord, tailWord_5567181, baseEnd_5567181] using wordTrace_append hprefix tailTrace_5567181
  have hstable : (prefixWord ++ tailWord_5567181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567181).length < 2 ^ (prefixWord ++ tailWord_5567181).sum := by decide
  have hdescent : baseEnd_5567181 < baseStart_5567181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567237 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_5567237 : Nat := 118140960795 + 5567237 * 2 ^ 59
def prefixEnd_5567237 : Nat := 4983230072969 + 3 ^ 40 * 5567237 * 2
def baseEnd_5567237 : Nat := 952889499498313297778083

theorem tailTrace_5567237 : CollatzResearch.WordTrace tailWord_5567237 prefixEnd_5567237 952889499498313297778083 := by
  unfold tailWord_5567237
  simp only [CollatzResearch.WordTrace]
  refine ⟨203053814931858632226987965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135369209954572421484658643 203053814931858632226987965)
  ·
    refine ⟨76145180599446987085120487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203053814931858632226987965 76145180599446987085120487)
    ·
      refine ⟨114217770899170480627680731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76145180599446987085120487 114217770899170480627680731)
      ·
        refine ⟨171326656348755720941521097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114217770899170480627680731 171326656348755720941521097)
        ·
          refine ⟨128494992261566790706140823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171326656348755720941521097 128494992261566790706140823)
          ·
            refine ⟨192742488392350186059211235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128494992261566790706140823 192742488392350186059211235)
            ·
              refine ⟨289113732588525279088816853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192742488392350186059211235 289113732588525279088816853)
              ·
                refine ⟨6776103107543561228644145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 289113732588525279088816853 6776103107543561228644145)
                ·
                  refine ⟨5082077330657670921483109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6776103107543561228644145 5082077330657670921483109)
                  ·
                    refine ⟨952889499498313297778083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082077330657670921483109 952889499498313297778083)
                    ·
                      rfl

theorem cell23_5567237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_5567237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567237 prefixEnd_5567237 := by exact prefixLift 5567237
  have htrace : WordTrace (prefixWord ++ tailWord_5567237) baseStart_5567237 baseEnd_5567237 := by
    simpa [prefixWord, tailWord_5567237, baseEnd_5567237] using wordTrace_append hprefix tailTrace_5567237
  have hstable : (prefixWord ++ tailWord_5567237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567237).length < 2 ^ (prefixWord ++ tailWord_5567237).sum := by decide
  have hdescent : baseEnd_5567237 < baseStart_5567237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567255 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 1, 1, 3]
def baseStart_5567255 : Nat := 118140960795 + 5567255 * 2 ^ 59
def prefixEnd_5567255 : Nat := 4983230072969 + 3 ^ 40 * 5567255 * 2
def baseEnd_5567255 : Nat := 2858677741146720822909167

theorem tailTrace_5567255 : CollatzResearch.WordTrace tailWord_5567255 prefixEnd_5567255 2858677741146720822909167 := by
  unfold tailWord_5567255
  simp only [CollatzResearch.WordTrace]
  refine ⟨203054471445793421301143219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135369647630528947534095479 203054471445793421301143219)
  ·
    refine ⟨304581707168690131951714829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203054471445793421301143219 304581707168690131951714829)
    ·
      refine ⟨114218140188258799481893061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304581707168690131951714829 114218140188258799481893061)
      ·
        refine ⟨21415901285298524902854949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114218140188258799481893061 21415901285298524902854949)
        ·
          refine ⟨4015481490993473419285303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21415901285298524902854949 4015481490993473419285303)
          ·
            refine ⟨6023222236490210128927955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015481490993473419285303 6023222236490210128927955)
            ·
              refine ⟨9034833354735315193391933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023222236490210128927955 9034833354735315193391933)
              ·
                refine ⟨3388062508025743197521975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9034833354735315193391933 3388062508025743197521975)
                ·
                  refine ⟨5082093762038614796282963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388062508025743197521975 5082093762038614796282963)
                  ·
                    refine ⟨7623140643057922194424445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5082093762038614796282963 7623140643057922194424445)
                    ·
                      refine ⟨2858677741146720822909167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623140643057922194424445 2858677741146720822909167)
                      ·
                        rfl

theorem cell23_5567255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_5567255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567255 prefixEnd_5567255 := by exact prefixLift 5567255
  have htrace : WordTrace (prefixWord ++ tailWord_5567255) baseStart_5567255 baseEnd_5567255 := by
    simpa [prefixWord, tailWord_5567255, baseEnd_5567255] using wordTrace_append hprefix tailTrace_5567255
  have hstable : (prefixWord ++ tailWord_5567255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567255).length < 2 ^ (prefixWord ++ tailWord_5567255).sum := by decide
  have hdescent : baseEnd_5567255 < baseStart_5567255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567264 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3]
def baseStart_5567264 : Nat := 118140960795 + 5567264 * 2 ^ 59
def prefixEnd_5567264 : Nat := 4983230072969 + 3 ^ 40 * 5567264 * 2
def baseEnd_5567264 : Nat := 2858682362472611287696625

theorem tailTrace_5567264 : CollatzResearch.WordTrace tailWord_5567264 prefixEnd_5567264 2858682362472611287696625 := by
  unfold tailWord_5567264
  simp only [CollatzResearch.WordTrace]
  refine ⟨101527399851380407919110423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135369866468507210558813897 101527399851380407919110423)
  ·
    refine ⟨152291099777070611878665635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101527399851380407919110423 152291099777070611878665635)
    ·
      refine ⟨228436649665605917817998453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152291099777070611878665635 228436649665605917817998453)
      ·
        refine ⟨21415935906150554795437355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228436649665605917817998453 21415935906150554795437355)
        ·
          refine ⟨32123903859225832193156033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21415935906150554795437355 32123903859225832193156033)
          ·
            refine ⟨24092927894419374144867025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32123903859225832193156033 24092927894419374144867025)
            ·
              refine ⟨18069695920814530608650269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24092927894419374144867025 18069695920814530608650269)
              ·
                refine ⟨6776135970305448978243851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18069695920814530608650269 6776135970305448978243851)
                ·
                  refine ⟨10164203955458173467365777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776135970305448978243851 10164203955458173467365777)
                  ·
                    refine ⟨7623152966593630100524333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10164203955458173467365777 7623152966593630100524333)
                    ·
                      refine ⟨2858682362472611287696625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623152966593630100524333 2858682362472611287696625)
                      ·
                        rfl

theorem cell23_5567264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_5567264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567264 prefixEnd_5567264 := by exact prefixLift 5567264
  have htrace : WordTrace (prefixWord ++ tailWord_5567264) baseStart_5567264 baseEnd_5567264 := by
    simpa [prefixWord, tailWord_5567264, baseEnd_5567264] using wordTrace_append hprefix tailTrace_5567264
  have hstable : (prefixWord ++ tailWord_5567264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567264).length < 2 ^ (prefixWord ++ tailWord_5567264).sum := by decide
  have hdescent : baseEnd_5567264 < baseStart_5567264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567278 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5567278 : Nat := 118140960795 + 5567278 * 2 ^ 59
def prefixEnd_5567278 : Nat := 4983230072969 + 3 ^ 40 * 5567278 * 2
def baseEnd_5567278 : Nat := 2858689551201774232921561

theorem tailTrace_5567278 : CollatzResearch.WordTrace tailWord_5567278 prefixEnd_5567278 2858689551201774232921561 := by
  unfold tailWord_5567278
  simp only [CollatzResearch.WordTrace]
  refine ⟨25381913790588762028653811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135370206883140064152820325 25381913790588762028653811)
  ·
    refine ⟨38072870685883143042980717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25381913790588762028653811 38072870685883143042980717)
    ·
      refine ⟨14277326507206178641117769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38072870685883143042980717 14277326507206178641117769)
      ·
        refine ⟨10707994880404633980838327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14277326507206178641117769 10707994880404633980838327)
        ·
          refine ⟨16061992320606950971257491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10707994880404633980838327 16061992320606950971257491)
          ·
            refine ⟨24092988480910426456886237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16061992320606950971257491 24092988480910426456886237)
            ·
              refine ⟨9034870680341409921332339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24092988480910426456886237 9034870680341409921332339)
              ·
                refine ⟨13552306020512114881998509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9034870680341409921332339 13552306020512114881998509)
                ·
                  refine ⟨5082114757692043080749441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13552306020512114881998509 5082114757692043080749441)
                  ·
                    refine ⟨3811586068269032310562081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5082114757692043080749441 3811586068269032310562081)
                    ·
                      refine ⟨2858689551201774232921561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811586068269032310562081 2858689551201774232921561)
                      ·
                        rfl

theorem cell23_5567278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5567278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567278 prefixEnd_5567278 := by exact prefixLift 5567278
  have htrace : WordTrace (prefixWord ++ tailWord_5567278) baseStart_5567278 baseEnd_5567278 := by
    simpa [prefixWord, tailWord_5567278, baseEnd_5567278] using wordTrace_append hprefix tailTrace_5567278
  have hstable : (prefixWord ++ tailWord_5567278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567278).length < 2 ^ (prefixWord ++ tailWord_5567278).sum := by decide
  have hdescent : baseEnd_5567278 < baseStart_5567278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567284 : List Nat := [2, 5, 1, 1, 3, 1, 2, 8]
def baseStart_5567284 : Nat := 118140960795 + 5567284 * 2 ^ 59
def prefixEnd_5567284 : Nat := 4983230072969 + 3 ^ 40 * 5567284 * 2
def baseEnd_5567284 : Nat := 105877504892063007757279

theorem tailTrace_5567284 : CollatzResearch.WordTrace tailWord_5567284 prefixEnd_5567284 105877504892063007757279 := by
  unfold tailWord_5567284
  simp only [CollatzResearch.WordTrace]
  refine ⟨101527764581344179626974453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135370352775125572835965937 101527764581344179626974453)
  ·
    refine ⟨9518227929501016840028855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101527764581344179626974453 9518227929501016840028855)
    ·
      refine ⟨14277341894251525260043283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9518227929501016840028855 14277341894251525260043283)
      ·
        refine ⟨21416012841377287890064925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14277341894251525260043283 21416012841377287890064925)
        ·
          refine ⟨8031004815516482958774347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21416012841377287890064925 8031004815516482958774347)
          ·
            refine ⟨12046507223274724438161521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8031004815516482958774347 12046507223274724438161521)
            ·
              refine ⟨9034880417456043328621141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12046507223274724438161521 9034880417456043328621141)
              ·
                refine ⟨105877504892063007757279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9034880417456043328621141 105877504892063007757279)
                ·
                  rfl

theorem cell23_5567284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 8].length) (baseStart_5567284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567284 prefixEnd_5567284 := by exact prefixLift 5567284
  have htrace : WordTrace (prefixWord ++ tailWord_5567284) baseStart_5567284 baseEnd_5567284 := by
    simpa [prefixWord, tailWord_5567284, baseEnd_5567284] using wordTrace_append hprefix tailTrace_5567284
  have hstable : (prefixWord ++ tailWord_5567284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567284).length < 2 ^ (prefixWord ++ tailWord_5567284).sum := by decide
  have hdescent : baseEnd_5567284 < baseStart_5567284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567304 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_5567304 : Nat := 118140960795 + 5567304 * 2 ^ 59
def prefixEnd_5567304 : Nat := 4983230072969 + 3 ^ 40 * 5567304 * 2
def baseEnd_5567304 : Nat := 2858702901698791131196441

theorem tailTrace_5567304 : CollatzResearch.WordTrace tailWord_5567304 prefixEnd_5567304 2858702901698791131196441 := by
  unfold tailWord_5567304
  simp only [CollatzResearch.WordTrace]
  refine ⟨101528129311307951334838483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135370839081743935113117977 101528129311307951334838483)
  ·
    refine ⟨152292193966961927002257725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101528129311307951334838483 152292193966961927002257725)
    ·
      refine ⟨57109572737610722625846647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152292193966961927002257725 57109572737610722625846647)
      ·
        refine ⟨85664359106416083938769971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57109572737610722625846647 85664359106416083938769971)
        ·
          refine ⟨128496538659624125908154957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85664359106416083938769971 128496538659624125908154957)
          ·
            refine ⟨48186201997359047215558109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128496538659624125908154957 48186201997359047215558109)
            ·
              refine ⟨18069825749009642705834291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48186201997359047215558109 18069825749009642705834291)
              ·
                refine ⟨27104738623514464058751437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18069825749009642705834291 27104738623514464058751437)
                ·
                  refine ⟨10164276983817924022031789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27104738623514464058751437 10164276983817924022031789)
                  ·
                    refine ⟨3811603868931721508261921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10164276983817924022031789 3811603868931721508261921)
                    ·
                      refine ⟨2858702901698791131196441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811603868931721508261921 2858702901698791131196441)
                      ·
                        rfl

theorem cell23_5567304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_5567304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567304 prefixEnd_5567304 := by exact prefixLift 5567304
  have htrace : WordTrace (prefixWord ++ tailWord_5567304) baseStart_5567304 baseEnd_5567304 := by
    simpa [prefixWord, tailWord_5567304, baseEnd_5567304] using wordTrace_append hprefix tailTrace_5567304
  have hstable : (prefixWord ++ tailWord_5567304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567304).length < 2 ^ (prefixWord ++ tailWord_5567304).sum := by decide
  have hdescent : baseEnd_5567304 < baseStart_5567304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567407 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_5567407 : Nat := 118140960795 + 5567407 * 2 ^ 59
def prefixEnd_5567407 : Nat := 4983230072969 + 3 ^ 40 * 5567407 * 2
def baseEnd_5567407 : Nat := 2858755790206204228208467

theorem tailTrace_5567407 : CollatzResearch.WordTrace tailWord_5567407 prefixEnd_5567407 2858755790206204228208467 := by
  unfold tailWord_5567407
  simp only [CollatzResearch.WordTrace]
  refine ⟨203060015341242751260676475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135373343560828500840450983 203060015341242751260676475)
  ·
    refine ⟨304590023011864126891014713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203060015341242751260676475 304590023011864126891014713)
    ·
      refine ⟨228442517258898095168261035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304590023011864126891014713 228442517258898095168261035)
      ·
        refine ⟨342663775888347142752391553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228442517258898095168261035 342663775888347142752391553)
        ·
          refine ⟨256997831916260357064293665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342663775888347142752391553 256997831916260357064293665)
          ·
            refine ⟨192748373937195267798220249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256997831916260357064293665 192748373937195267798220249)
            ·
              refine ⟨144561280452896450848665187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192748373937195267798220249 144561280452896450848665187)
              ·
                refine ⟨216841920679344676272997781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144561280452896450848665187 216841920679344676272997781)
                ·
                  refine ⟨10164465031844281700296771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216841920679344676272997781 10164465031844281700296771)
                  ·
                    refine ⟨15246697547766422550445157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10164465031844281700296771 15246697547766422550445157)
                    ·
                      refine ⟨2858755790206204228208467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15246697547766422550445157 2858755790206204228208467)
                      ·
                        rfl

theorem cell23_5567407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_5567407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567407 prefixEnd_5567407 := by exact prefixLift 5567407
  have htrace : WordTrace (prefixWord ++ tailWord_5567407) baseStart_5567407 baseEnd_5567407 := by
    simpa [prefixWord, tailWord_5567407, baseEnd_5567407] using wordTrace_append hprefix tailTrace_5567407
  have hstable : (prefixWord ++ tailWord_5567407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567407).length < 2 ^ (prefixWord ++ tailWord_5567407).sum := by decide
  have hdescent : baseEnd_5567407 < baseStart_5567407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567478 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5567478 : Nat := 118140960795 + 5567478 * 2 ^ 59
def prefixEnd_5567478 : Nat := 4983230072969 + 3 ^ 40 * 5567478 * 2
def baseEnd_5567478 : Nat := 2858792247332673450420641

theorem tailTrace_5567478 : CollatzResearch.WordTrace tailWord_5567478 prefixEnd_5567478 2858792247332673450420641 := by
  unfold tailWord_5567478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12691412807749095649156943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135375069949323686924340725 12691412807749095649156943)
  ·
    refine ⟨19037119211623643473735415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12691412807749095649156943 19037119211623643473735415)
    ·
      refine ⟨28555678817435465210603123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19037119211623643473735415 28555678817435465210603123)
      ·
        refine ⟨42833518226153197815904685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28555678817435465210603123 42833518226153197815904685)
        ·
          refine ⟨16062569334807449180964257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42833518226153197815904685 16062569334807449180964257)
          ·
            refine ⟨12046927001105586885723193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16062569334807449180964257 12046927001105586885723193)
            ·
              refine ⟨9035195250829190164292395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12046927001105586885723193 9035195250829190164292395)
              ·
                refine ⟨13552792876243785246438593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9035195250829190164292395 13552792876243785246438593)
                ·
                  refine ⟨10164594657182838934828945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13552792876243785246438593 10164594657182838934828945)
                  ·
                    refine ⟨7623445992887129201121709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10164594657182838934828945 7623445992887129201121709)
                    ·
                      refine ⟨2858792247332673450420641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623445992887129201121709 2858792247332673450420641)
                      ·
                        rfl

theorem cell23_5567478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5567478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567478 prefixEnd_5567478 := by exact prefixLift 5567478
  have htrace : WordTrace (prefixWord ++ tailWord_5567478) baseStart_5567478 baseEnd_5567478 := by
    simpa [prefixWord, tailWord_5567478, baseEnd_5567478] using wordTrace_append hprefix tailTrace_5567478
  have hstable : (prefixWord ++ tailWord_5567478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567478).length < 2 ^ (prefixWord ++ tailWord_5567478).sum := by decide
  have hdescent : baseEnd_5567478 < baseStart_5567478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567507 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 5, 6]
def baseStart_5567507 : Nat := 118140960795 + 5567507 * 2 ^ 59
def prefixEnd_5567507 : Nat := 4983230072969 + 3 ^ 40 * 5567507 * 2
def baseEnd_5567507 : Nat := 952935712757217945652669

theorem tailTrace_5567507 : CollatzResearch.WordTrace tailWord_5567507 prefixEnd_5567507 952935712757217945652669 := by
  unfold tailWord_5567507
  simp only [CollatzResearch.WordTrace]
  refine ⟨203063662640880468339316775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135375775093920312226211183 203063662640880468339316775)
  ·
    refine ⟨304595493961320702508975163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203063662640880468339316775 304595493961320702508975163)
    ·
      refine ⟨456893240941981053763462745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304595493961320702508975163 456893240941981053763462745)
      ·
        refine ⟨342669930706485790322597059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456893240941981053763462745 342669930706485790322597059)
        ·
          refine ⟨514004896059728685483895589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342669930706485790322597059 514004896059728685483895589)
          ·
            refine ⟨96375918011199128528230423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 514004896059728685483895589 96375918011199128528230423)
            ·
              refine ⟨144563877016798692792345635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96375918011199128528230423 144563877016798692792345635)
              ·
                refine ⟨216845815525198039188518453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144563877016798692792345635 216845815525198039188518453)
                ·
                  refine ⟨20329295205487316173923605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216845815525198039188518453 20329295205487316173923605)
                  ·
                    refine ⟨952935712757217945652669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20329295205487316173923605 952935712757217945652669)
                    ·
                      rfl

theorem cell23_5567507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 6].length) (baseStart_5567507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567507 prefixEnd_5567507 := by exact prefixLift 5567507
  have htrace : WordTrace (prefixWord ++ tailWord_5567507) baseStart_5567507 baseEnd_5567507 := by
    simpa [prefixWord, tailWord_5567507, baseEnd_5567507] using wordTrace_append hprefix tailTrace_5567507
  have hstable : (prefixWord ++ tailWord_5567507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567507).length < 2 ^ (prefixWord ++ tailWord_5567507).sum := by decide
  have hdescent : baseEnd_5567507 < baseStart_5567507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567514 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_5567514 : Nat := 118140960795 + 5567514 * 2 ^ 59
def prefixEnd_5567514 : Nat := 4983230072969 + 3 ^ 40 * 5567514 * 2
def baseEnd_5567514 : Nat := 2858810732636235309570475

theorem tailTrace_5567514 : CollatzResearch.WordTrace tailWord_5567514 prefixEnd_5567514 2858810732636235309570475 := by
  unfold tailWord_5567514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50765979487963777133705399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135375945301236739023214397 50765979487963777133705399)
  ·
    refine ⟨76148969231945665700558099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50765979487963777133705399 76148969231945665700558099)
    ·
      refine ⟨114223453847918498550837149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76148969231945665700558099 114223453847918498550837149)
      ·
        refine ⟨42833795192969436956563931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114223453847918498550837149 42833795192969436956563931)
        ·
          refine ⟨64250692789454155434845897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42833795192969436956563931 64250692789454155434845897)
          ·
            refine ⟨48188019592090616576134423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64250692789454155434845897 48188019592090616576134423)
            ·
              refine ⟨72282029388135924864201635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48188019592090616576134423 72282029388135924864201635)
              ·
                refine ⟨108423044082203887296302453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72282029388135924864201635 108423044082203887296302453)
                ·
                  refine ⟨10164660382706614434028355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108423044082203887296302453 10164660382706614434028355)
                  ·
                    refine ⟨15246990574059921651042533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10164660382706614434028355 15246990574059921651042533)
                    ·
                      refine ⟨2858810732636235309570475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15246990574059921651042533 2858810732636235309570475)
                      ·
                        rfl

theorem cell23_5567514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_5567514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567514 prefixEnd_5567514 := by exact prefixLift 5567514
  have htrace : WordTrace (prefixWord ++ tailWord_5567514) baseStart_5567514 baseEnd_5567514 := by
    simpa [prefixWord, tailWord_5567514, baseEnd_5567514] using wordTrace_append hprefix tailTrace_5567514
  have hstable : (prefixWord ++ tailWord_5567514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567514).length < 2 ^ (prefixWord ++ tailWord_5567514).sum := by decide
  have hdescent : baseEnd_5567514 < baseStart_5567514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567542 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_5567542 : Nat := 118140960795 + 5567542 * 2 ^ 59
def prefixEnd_5567542 : Nat := 4983230072969 + 3 ^ 40 * 5567542 * 2
def baseEnd_5567542 : Nat := 2858825110094561200020347

theorem tailTrace_5567542 : CollatzResearch.WordTrace tailWord_5567542 prefixEnd_5567542 2858825110094561200020347 := by
  unfold tailWord_5567542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12691558699734604332302555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135376626130502446211227253 12691558699734604332302555)
  ·
    refine ⟨19037338049601906498453833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12691558699734604332302555 19037338049601906498453833)
    ·
      refine ⟨14278003537201429873840375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19037338049601906498453833 14278003537201429873840375)
      ·
        refine ⟨21417005305802144810760563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14278003537201429873840375 21417005305802144810760563)
        ·
          refine ⟨32125507958703217216140845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21417005305802144810760563 32125507958703217216140845)
          ·
            refine ⟨12047065484513706456052817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32125507958703217216140845 12047065484513706456052817)
            ·
              refine ⟨9035299113385279842039613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12047065484513706456052817 9035299113385279842039613)
              ·
                refine ⟨3388237167519479940764855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9035299113385279842039613 3388237167519479940764855)
                ·
                  refine ⟨5082355751279219911147283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388237167519479940764855 5082355751279219911147283)
                  ·
                    refine ⟨7623533626918829866720925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5082355751279219911147283 7623533626918829866720925)
                    ·
                      refine ⟨2858825110094561200020347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623533626918829866720925 2858825110094561200020347)
                      ·
                        rfl

theorem cell23_5567542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_5567542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567542 prefixEnd_5567542 := by exact prefixLift 5567542
  have htrace : WordTrace (prefixWord ++ tailWord_5567542) baseStart_5567542 baseEnd_5567542 := by
    simpa [prefixWord, tailWord_5567542, baseEnd_5567542] using wordTrace_append hprefix tailTrace_5567542
  have hstable : (prefixWord ++ tailWord_5567542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567542).length < 2 ^ (prefixWord ++ tailWord_5567542).sum := by decide
  have hdescent : baseEnd_5567542 < baseStart_5567542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567548 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_5567548 : Nat := 118140960795 + 5567548 * 2 ^ 59
def prefixEnd_5567548 : Nat := 4983230072969 + 3 ^ 40 * 5567548 * 2
def baseEnd_5567548 : Nat := 2858828190978488176545319

theorem tailTrace_5567548 : CollatzResearch.WordTrace tailWord_5567548 prefixEnd_5567548 2858828190978488176545319 := by
  unfold tailWord_5567548
  simp only [CollatzResearch.WordTrace]
  refine ⟨101532579016865966170779649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135376772022487954894372865 101532579016865966170779649)
  ·
    refine ⟨76149434262649474628084737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101532579016865966170779649 76149434262649474628084737)
    ·
      refine ⟨57112075696987105971063553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76149434262649474628084737 57112075696987105971063553)
      ·
        refine ⟨42834056772740329478297665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57112075696987105971063553 42834056772740329478297665)
        ·
          refine ⟨32125542579555247108723249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42834056772740329478297665 32125542579555247108723249)
          ·
            refine ⟨24094156934666435331542437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32125542579555247108723249 24094156934666435331542437)
            ·
              refine ⟨4517654425249956624664207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24094156934666435331542437 4517654425249956624664207)
              ·
                refine ⟨6776481637874934936996311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517654425249956624664207 6776481637874934936996311)
                ·
                  refine ⟨10164722456812402405494467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776481637874934936996311 10164722456812402405494467)
                  ·
                    refine ⟨15247083685218603608241701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10164722456812402405494467 15247083685218603608241701)
                    ·
                      refine ⟨2858828190978488176545319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15247083685218603608241701 2858828190978488176545319)
                      ·
                        rfl

theorem cell23_5567548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_5567548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567548 prefixEnd_5567548 := by exact prefixLift 5567548
  have htrace : WordTrace (prefixWord ++ tailWord_5567548) baseStart_5567548 baseEnd_5567548 := by
    simpa [prefixWord, tailWord_5567548, baseEnd_5567548] using wordTrace_append hprefix tailTrace_5567548
  have hstable : (prefixWord ++ tailWord_5567548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567548).length < 2 ^ (prefixWord ++ tailWord_5567548).sum := by decide
  have hdescent : baseEnd_5567548 < baseStart_5567548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567565 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_5567565 : Nat := 118140960795 + 5567565 * 2 ^ 59
def prefixEnd_5567565 : Nat := 4983230072969 + 3 ^ 40 * 5567565 * 2
def baseEnd_5567565 : Nat := 2858836920149614610032741

theorem tailTrace_5567565 : CollatzResearch.WordTrace tailWord_5567565 prefixEnd_5567565 2858836920149614610032741 := by
  unfold tailWord_5567565
  simp only [CollatzResearch.WordTrace]
  refine ⟨203065778074670344244928149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135377185383113562829952099 203065778074670344244928149)
  ·
    refine ⟨9518708347250172386481007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203065778074670344244928149 9518708347250172386481007)
    ·
      refine ⟨14278062520875258579721511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9518708347250172386481007 14278062520875258579721511)
      ·
        refine ⟨21417093781312887869582267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14278062520875258579721511 21417093781312887869582267)
        ·
          refine ⟨32125640671969331804373401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21417093781312887869582267 32125640671969331804373401)
          ·
            refine ⟨24094230503976998853280051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32125640671969331804373401 24094230503976998853280051)
            ·
              refine ⟨36141345755965498279920077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24094230503976998853280051 36141345755965498279920077)
              ·
                refine ⟨13553004658487061854970029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36141345755965498279920077 13553004658487061854970029)
                ·
                  refine ⟨5082376746932648195613761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13553004658487061854970029 5082376746932648195613761)
                  ·
                    refine ⟨3811782560199486146710321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5082376746932648195613761 3811782560199486146710321)
                    ·
                      refine ⟨2858836920149614610032741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811782560199486146710321 2858836920149614610032741)
                      ·
                        rfl

theorem cell23_5567565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_5567565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567565 prefixEnd_5567565 := by exact prefixLift 5567565
  have htrace : WordTrace (prefixWord ++ tailWord_5567565) baseStart_5567565 baseEnd_5567565 := by
    simpa [prefixWord, tailWord_5567565, baseEnd_5567565] using wordTrace_append hprefix tailTrace_5567565
  have hstable : (prefixWord ++ tailWord_5567565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567565).length < 2 ^ (prefixWord ++ tailWord_5567565).sum := by decide
  have hdescent : baseEnd_5567565 < baseStart_5567565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567582 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_5567582 : Nat := 118140960795 + 5567582 * 2 ^ 59
def prefixEnd_5567582 : Nat := 4983230072969 + 3 ^ 40 * 5567582 * 2
def baseEnd_5567582 : Nat := 2858845649320741043520163

theorem tailTrace_5567582 : CollatzResearch.WordTrace tailWord_5567582 prefixEnd_5567582 2858845649320741043520163 := by
  unfold tailWord_5567582
  simp only [CollatzResearch.WordTrace]
  refine ⟨25383299764451094518537125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135377598743739170765531333 25383299764451094518537125)
  ·
    refine ⟨4759368705834580222225711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25383299764451094518537125 4759368705834580222225711)
    ·
      refine ⟨7139053058751870333338567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4759368705834580222225711 7139053058751870333338567)
      ·
        refine ⟨10708579588127805500007851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139053058751870333338567 10708579588127805500007851)
        ·
          refine ⟨16062869382191708250011777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708579588127805500007851 16062869382191708250011777)
          ·
            refine ⟨12047152036643781187508833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16062869382191708250011777 12047152036643781187508833)
            ·
              refine ⟨9035364027482835890631625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12047152036643781187508833 9035364027482835890631625)
              ·
                refine ⟨6776523020612126917973719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035364027482835890631625 6776523020612126917973719)
                ·
                  refine ⟨10164784530918190376960579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776523020612126917973719 10164784530918190376960579)
                  ·
                    refine ⟨15247176796377285565440869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10164784530918190376960579 15247176796377285565440869)
                    ·
                      refine ⟨2858845649320741043520163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15247176796377285565440869 2858845649320741043520163)
                      ·
                        rfl

theorem cell23_5567582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_5567582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567582 prefixEnd_5567582 := by exact prefixLift 5567582
  have htrace : WordTrace (prefixWord ++ tailWord_5567582) baseStart_5567582 baseEnd_5567582 := by
    simpa [prefixWord, tailWord_5567582, baseEnd_5567582] using wordTrace_append hprefix tailTrace_5567582
  have hstable : (prefixWord ++ tailWord_5567582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567582).length < 2 ^ (prefixWord ++ tailWord_5567582).sum := by decide
  have hdescent : baseEnd_5567582 < baseStart_5567582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567598 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5567598 : Nat := 118140960795 + 5567598 * 2 ^ 59
def prefixEnd_5567598 : Nat := 4983230072969 + 3 ^ 40 * 5567598 * 2
def baseEnd_5567598 : Nat := 2858853865011212980920089

theorem tailTrace_5567598 : CollatzResearch.WordTrace tailWord_5567598 prefixEnd_5567598 2858853865011212980920089 := by
  unfold tailWord_5567598
  simp only [CollatzResearch.WordTrace]
  refine ⟨25383372710443848860109931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135377987789033860587252965 25383372710443848860109931)
  ·
    refine ⟨38075059065665773290164897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25383372710443848860109931 38075059065665773290164897)
    ·
      refine ⟨28556294299249329967623673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38075059065665773290164897 28556294299249329967623673)
      ·
        refine ⟨21417220724436997475717755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28556294299249329967623673 21417220724436997475717755)
        ·
          refine ⟨32125831086655496213576633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21417220724436997475717755 32125831086655496213576633)
          ·
            refine ⟨24094373314991622160182475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32125831086655496213576633 24094373314991622160182475)
            ·
              refine ⟨36141559972487433240273713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24094373314991622160182475 36141559972487433240273713)
              ·
                refine ⟨27106169979365574930205285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36141559972487433240273713 27106169979365574930205285)
                ·
                  refine ⟨5082406871131045299413491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27106169979365574930205285 5082406871131045299413491)
                  ·
                    refine ⟨7623610306696567949120237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5082406871131045299413491 7623610306696567949120237)
                    ·
                      refine ⟨2858853865011212980920089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623610306696567949120237 2858853865011212980920089)
                      ·
                        rfl

theorem cell23_5567598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5567598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567598 prefixEnd_5567598 := by exact prefixLift 5567598
  have htrace : WordTrace (prefixWord ++ tailWord_5567598) baseStart_5567598 baseEnd_5567598 := by
    simpa [prefixWord, tailWord_5567598, baseEnd_5567598] using wordTrace_append hprefix tailTrace_5567598
  have hstable : (prefixWord ++ tailWord_5567598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567598).length < 2 ^ (prefixWord ++ tailWord_5567598).sum := by decide
  have hdescent : baseEnd_5567598 < baseStart_5567598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567608 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 1, 3, 2]
def baseStart_5567608 : Nat := 118140960795 + 5567608 * 2 ^ 59
def prefixEnd_5567608 : Nat := 4983230072969 + 3 ^ 40 * 5567608 * 2
def baseEnd_5567608 : Nat := 2858858999817757941795043

theorem tailTrace_5567608 : CollatzResearch.WordTrace tailWord_5567608 prefixEnd_5567608 2858858999817757941795043 := by
  unfold tailWord_5567608
  simp only [CollatzResearch.WordTrace]
  refine ⟨101533673206757281294371739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135378230942343041725828985 101533673206757281294371739)
  ·
    refine ⟨152300509810135921941557609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101533673206757281294371739 152300509810135921941557609)
    ·
      refine ⟨114225382357601941456168207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152300509810135921941557609 114225382357601941456168207)
      ·
        refine ⟨171338073536402912184252311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114225382357601941456168207 171338073536402912184252311)
        ·
          refine ⟨257007110304604368276378467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171338073536402912184252311 257007110304604368276378467)
          ·
            refine ⟨385510665456906552414567701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257007110304604368276378467 385510665456906552414567701)
            ·
              refine ⟨18070812443292494644432861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 385510665456906552414567701 18070812443292494644432861)
              ·
                refine ⟨6776554666234685491662323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18070812443292494644432861 6776554666234685491662323)
                ·
                  refine ⟨10164831999352028237493485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776554666234685491662323 10164831999352028237493485)
                  ·
                    refine ⟨3811811999757010589060057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10164831999352028237493485 3811811999757010589060057)
                    ·
                      refine ⟨2858858999817757941795043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811811999757010589060057 2858858999817757941795043)
                      ·
                        rfl

theorem cell23_5567608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_5567608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567608 prefixEnd_5567608 := by exact prefixLift 5567608
  have htrace : WordTrace (prefixWord ++ tailWord_5567608) baseStart_5567608 baseEnd_5567608 := by
    simpa [prefixWord, tailWord_5567608, baseEnd_5567608] using wordTrace_append hprefix tailTrace_5567608
  have hstable : (prefixWord ++ tailWord_5567608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567608).length < 2 ^ (prefixWord ++ tailWord_5567608).sum := by decide
  have hdescent : baseEnd_5567608 < baseStart_5567608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567642 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5567642 : Nat := 118140960795 + 5567642 * 2 ^ 59
def prefixEnd_5567642 : Nat := 4983230072969 + 3 ^ 40 * 5567642 * 2
def baseEnd_5567642 : Nat := 2858876458160010808769887

theorem tailTrace_5567642 : CollatzResearch.WordTrace tailWord_5567642 prefixEnd_5567642 2858876458160010808769887 := by
  unfold tailWord_5567642
  simp only [CollatzResearch.WordTrace]
  refine ⟨50767146623847846598870295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135379057663594257596987453 50767146623847846598870295)
  ·
    refine ⟨76150719935771769898305443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50767146623847846598870295 76150719935771769898305443)
    ·
      refine ⟨114226079903657654847458165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76150719935771769898305443 114226079903657654847458165)
      ·
        refine ⟨10708694990967905141949203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114226079903657654847458165 10708694990967905141949203)
        ·
          refine ⟨16063042486451857712923805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708694990967905141949203 16063042486451857712923805)
          ·
            refine ⟨6023640932419446642346427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16063042486451857712923805 6023640932419446642346427)
            ·
              refine ⟨9035461398629169963519641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023640932419446642346427 9035461398629169963519641)
              ·
                refine ⟨6776596048971877472639731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035461398629169963519641 6776596048971877472639731)
                ·
                  refine ⟨10164894073457816208959597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776596048971877472639731 10164894073457816208959597)
                  ·
                    refine ⟨3811835277546681078359849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10164894073457816208959597 3811835277546681078359849)
                    ·
                      refine ⟨2858876458160010808769887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811835277546681078359849 2858876458160010808769887)
                      ·
                        rfl

theorem cell23_5567642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5567642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567642 prefixEnd_5567642 := by exact prefixLift 5567642
  have htrace : WordTrace (prefixWord ++ tailWord_5567642) baseStart_5567642 baseEnd_5567642 := by
    simpa [prefixWord, tailWord_5567642, baseEnd_5567642] using wordTrace_append hprefix tailTrace_5567642
  have hstable : (prefixWord ++ tailWord_5567642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567642).length < 2 ^ (prefixWord ++ tailWord_5567642).sum := by decide
  have hdescent : baseEnd_5567642 < baseStart_5567642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567655 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5567655 : Nat := 118140960795 + 5567655 * 2 ^ 59
def prefixEnd_5567655 : Nat := 4983230072969 + 3 ^ 40 * 5567655 * 2
def baseEnd_5567655 : Nat := 2858883133408519257907327

theorem tailTrace_5567655 : CollatzResearch.WordTrace tailWord_5567655 prefixEnd_5567655 2858883133408519257907327 := by
  unfold tailWord_5567655
  simp only [CollatzResearch.WordTrace]
  refine ⟨203069060644344289615704419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135379373762896193077136279 203069060644344289615704419)
  ·
    refine ⟨304603590966516434423556629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203069060644344289615704419 304603590966516434423556629)
    ·
      refine ⟨14278293326555457863604217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 304603590966516434423556629 14278293326555457863604217)
      ·
        refine ⟨10708719994916593397703163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14278293326555457863604217 10708719994916593397703163)
        ·
          refine ⟨16063079992374890096554745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708719994916593397703163 16063079992374890096554745)
          ·
            refine ⟨12047309994281167572416059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16063079992374890096554745 12047309994281167572416059)
            ·
              refine ⟨18070964991421751358624089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12047309994281167572416059 18070964991421751358624089)
              ·
                refine ⟨13553223743566313518968067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18070964991421751358624089 13553223743566313518968067)
                ·
                  refine ⟨20329835615349470278452101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13553223743566313518968067 20329835615349470278452101)
                  ·
                    refine ⟨3811844177878025677209769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20329835615349470278452101 3811844177878025677209769)
                    ·
                      refine ⟨2858883133408519257907327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811844177878025677209769 2858883133408519257907327)
                      ·
                        rfl

theorem cell23_5567655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5567655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567655 prefixEnd_5567655 := by exact prefixLift 5567655
  have htrace : WordTrace (prefixWord ++ tailWord_5567655) baseStart_5567655 baseEnd_5567655 := by
    simpa [prefixWord, tailWord_5567655, baseEnd_5567655] using wordTrace_append hprefix tailTrace_5567655
  have hstable : (prefixWord ++ tailWord_5567655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567655).length < 2 ^ (prefixWord ++ tailWord_5567655).sum := by decide
  have hdescent : baseEnd_5567655 < baseStart_5567655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567658 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5567658 : Nat := 118140960795 + 5567658 * 2 ^ 59
def prefixEnd_5567658 : Nat := 4983230072969 + 3 ^ 40 * 5567658 * 2
def baseEnd_5567658 : Nat := 2858884673850482746169813

theorem tailTrace_5567658 : CollatzResearch.WordTrace tailWord_5567658 prefixEnd_5567658 2858884673850482746169813 := by
  unfold tailWord_5567658
  simp only [CollatzResearch.WordTrace]
  refine ⟨50767292515833355282015907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135379446708888947418709085 50767292515833355282015907)
  ·
    refine ⟨76150938773750032923023861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50767292515833355282015907 76150938773750032923023861)
    ·
      refine ⟨7139150510039065586533487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76150938773750032923023861 7139150510039065586533487)
      ·
        refine ⟨10708725765058598379800231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139150510039065586533487 10708725765058598379800231)
        ·
          refine ⟨16063088647587897569700347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708725765058598379800231 16063088647587897569700347)
          ·
            refine ⟨24094632971381846354550521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16063088647587897569700347 24094632971381846354550521)
            ·
              refine ⟨18070974728536384765912891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24094632971381846354550521 18070974728536384765912891)
              ·
                refine ⟨27106462092804577148869337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18070974728536384765912891 27106462092804577148869337)
                ·
                  refine ⟨20329846569603432861652003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27106462092804577148869337 20329846569603432861652003)
                  ·
                    refine ⟨30494769854405149292478005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20329846569603432861652003 30494769854405149292478005)
                    ·
                      refine ⟨2858884673850482746169813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30494769854405149292478005 2858884673850482746169813)
                      ·
                        rfl

theorem cell23_5567658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5567658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567658 prefixEnd_5567658 := by exact prefixLift 5567658
  have htrace : WordTrace (prefixWord ++ tailWord_5567658) baseStart_5567658 baseEnd_5567658 := by
    simpa [prefixWord, tailWord_5567658, baseEnd_5567658] using wordTrace_append hprefix tailTrace_5567658
  have hstable : (prefixWord ++ tailWord_5567658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567658).length < 2 ^ (prefixWord ++ tailWord_5567658).sum := by decide
  have hdescent : baseEnd_5567658 < baseStart_5567658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567671 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_5567671 : Nat := 118140960795 + 5567671 * 2 ^ 59
def prefixEnd_5567671 : Nat := 4983230072969 + 3 ^ 40 * 5567671 * 2
def baseEnd_5567671 : Nat := 2858891349098991195307253

theorem tailTrace_5567671 : CollatzResearch.WordTrace tailWord_5567671 prefixEnd_5567671 2858891349098991195307253 := by
  unfold tailWord_5567671
  simp only [CollatzResearch.WordTrace]
  refine ⟨203069644212286324348286867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135379762808190882898857911 203069644212286324348286867)
  ·
    refine ⟨304604466318429486522430301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203069644212286324348286867 304604466318429486522430301)
    ·
      refine ⟨114226674869411057445911363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304604466318429486522430301 114226674869411057445911363)
      ·
        refine ⟨171340012304116586168867045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114226674869411057445911363 171340012304116586168867045)
        ·
          refine ⟨32126252307021859906662571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171340012304116586168867045 32126252307021859906662571)
          ·
            refine ⟨48189378460532789859993857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32126252307021859906662571 48189378460532789859993857)
            ·
              refine ⟨36142033845399592394995393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48189378460532789859993857 36142033845399592394995393)
              ·
                refine ⟨27106525384049694296246545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36142033845399592394995393 27106525384049694296246545)
                ·
                  refine ⟨20329894038037270722184909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27106525384049694296246545 20329894038037270722184909)
                  ·
                    refine ⟨7623710264263976520819341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20329894038037270722184909 7623710264263976520819341)
                    ·
                      refine ⟨2858891349098991195307253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623710264263976520819341 2858891349098991195307253)
                      ·
                        rfl

theorem cell23_5567671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_5567671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567671 prefixEnd_5567671 := by exact prefixLift 5567671
  have htrace : WordTrace (prefixWord ++ tailWord_5567671) baseStart_5567671 baseEnd_5567671 := by
    simpa [prefixWord, tailWord_5567671, baseEnd_5567671] using wordTrace_append hprefix tailTrace_5567671
  have hstable : (prefixWord ++ tailWord_5567671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567671).length < 2 ^ (prefixWord ++ tailWord_5567671).sum := by decide
  have hdescent : baseEnd_5567671 < baseStart_5567671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567674 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_5567674 : Nat := 118140960795 + 5567674 * 2 ^ 59
def prefixEnd_5567674 : Nat := 4983230072969 + 3 ^ 40 * 5567674 * 2
def baseEnd_5567674 : Nat := 952964296513651561189913

theorem tailTrace_5567674 : CollatzResearch.WordTrace tailWord_5567674 prefixEnd_5567674 952964296513651561189913 := by
  unfold tailWord_5567674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50767438407818863965161519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135379835754183637240430717 50767438407818863965161519)
  ·
    refine ⟨76151157611728295947742279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50767438407818863965161519 76151157611728295947742279)
    ·
      refine ⟨114226736417592443921613419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76151157611728295947742279 114226736417592443921613419)
      ·
        refine ⟨171340104626388665882420129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114226736417592443921613419 171340104626388665882420129)
        ·
          refine ⟨128505078469791499411815097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171340104626388665882420129 128505078469791499411815097)
          ·
            refine ⟨96378808852343624558861323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128505078469791499411815097 96378808852343624558861323)
            ·
              refine ⟨144568213278515436838291985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96378808852343624558861323 144568213278515436838291985)
              ·
                refine ⟨108426159958886577628718989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144568213278515436838291985 108426159958886577628718989)
                ·
                  refine ⟨40659809984582466610769621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108426159958886577628718989 40659809984582466610769621)
                  ·
                    refine ⟨952964296513651561189913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40659809984582466610769621 952964296513651561189913)
                    ·
                      rfl

theorem cell23_5567674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_5567674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567674 prefixEnd_5567674 := by exact prefixLift 5567674
  have htrace : WordTrace (prefixWord ++ tailWord_5567674) baseStart_5567674 baseEnd_5567674 := by
    simpa [prefixWord, tailWord_5567674, baseEnd_5567674] using wordTrace_append hprefix tailTrace_5567674
  have hstable : (prefixWord ++ tailWord_5567674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567674).length < 2 ^ (prefixWord ++ tailWord_5567674).sum := by decide
  have hdescent : baseEnd_5567674 < baseStart_5567674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567698 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5567698 : Nat := 118140960795 + 5567698 * 2 ^ 59
def prefixEnd_5567698 : Nat := 4983230072969 + 3 ^ 40 * 5567698 * 2
def baseEnd_5567698 : Nat := 2858905213076662589669629

theorem tailTrace_5567698 : CollatzResearch.WordTrace tailWord_5567698 prefixEnd_5567698 2858905213076662589669629 := by
  unfold tailWord_5567698
  simp only [CollatzResearch.WordTrace]
  refine ⟨50767657245797126989879937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135380419322125671973013165 50767657245797126989879937)
  ·
    refine ⟨38075742934347845242409953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50767657245797126989879937 38075742934347845242409953)
    ·
      refine ⟨28556807200760883931807465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38075742934347845242409953 28556807200760883931807465)
      ·
        refine ⟨21417605400570662948855599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28556807200760883931807465 21417605400570662948855599)
        ·
          refine ⟨32126408100855994423283399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21417605400570662948855599 32126408100855994423283399)
          ·
            refine ⟨48189612151283991634925099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32126408100855994423283399 48189612151283991634925099)
            ·
              refine ⟨72284418226925987452387649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48189612151283991634925099 72284418226925987452387649)
              ·
                refine ⟨54213313670194490589290737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72284418226925987452387649 54213313670194490589290737)
                ·
                  refine ⟨40659985252645867941968053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54213313670194490589290737 40659985252645867941968053)
                  ·
                    refine ⟨3811873617435550119559505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40659985252645867941968053 3811873617435550119559505)
                    ·
                      refine ⟨2858905213076662589669629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811873617435550119559505 2858905213076662589669629)
                      ·
                        rfl

theorem cell23_5567698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5567698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567698 prefixEnd_5567698 := by exact prefixLift 5567698
  have htrace : WordTrace (prefixWord ++ tailWord_5567698) baseStart_5567698 baseEnd_5567698 := by
    simpa [prefixWord, tailWord_5567698, baseEnd_5567698] using wordTrace_append hprefix tailTrace_5567698
  have hstable : (prefixWord ++ tailWord_5567698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567698).length < 2 ^ (prefixWord ++ tailWord_5567698).sum := by decide
  have hdescent : baseEnd_5567698 < baseStart_5567698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567738 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_5567738 : Nat := 118140960795 + 5567738 * 2 ^ 59
def prefixEnd_5567738 : Nat := 4983230072969 + 3 ^ 40 * 5567738 * 2
def baseEnd_5567738 : Nat := 952975250767614144389815

theorem tailTrace_5567738 : CollatzResearch.WordTrace tailWord_5567738 prefixEnd_5567738 952975250767614144389815 := by
  unfold tailWord_5567738
  simp only [CollatzResearch.WordTrace]
  refine ⟨50768021975760898697743967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135381391935362396527317245 50768021975760898697743967)
  ·
    refine ⟨76152032963641348046615951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50768021975760898697743967 76152032963641348046615951)
    ·
      refine ⟨114228049445462022069923927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76152032963641348046615951 114228049445462022069923927)
      ·
        refine ⟨171342074168193033104885891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114228049445462022069923927 171342074168193033104885891)
        ·
          refine ⟨257013111252289549657328837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171342074168193033104885891 257013111252289549657328837)
          ·
            refine ⟨48189958359804290560749157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257013111252289549657328837 48189958359804290560749157)
            ·
              refine ⟨9035617192463304480140467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48189958359804290560749157 9035617192463304480140467)
              ·
                refine ⟨13553425788694956720210701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9035617192463304480140467 13553425788694956720210701)
                ·
                  refine ⟨5082534670760608770079013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13553425788694956720210701 5082534670760608770079013)
                  ·
                    refine ⟨952975250767614144389815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082534670760608770079013 952975250767614144389815)
                    ·
                      rfl

theorem cell23_5567738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_5567738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567738 prefixEnd_5567738 := by exact prefixLift 5567738
  have htrace : WordTrace (prefixWord ++ tailWord_5567738) baseStart_5567738 baseEnd_5567738 := by
    simpa [prefixWord, tailWord_5567738, baseEnd_5567738] using wordTrace_append hprefix tailTrace_5567738
  have hstable : (prefixWord ++ tailWord_5567738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567738).length < 2 ^ (prefixWord ++ tailWord_5567738).sum := by decide
  have hdescent : baseEnd_5567738 < baseStart_5567738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567748 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5567748 : Nat := 118140960795 + 5567748 * 2 ^ 59
def prefixEnd_5567748 : Nat := 4983230072969 + 3 ^ 40 * 5567748 * 2
def baseEnd_5567748 : Nat := 2858930887109387394044399

theorem tailTrace_5567748 : CollatzResearch.WordTrace tailWord_5567748 prefixEnd_5567748 2858930887109387394044399 := by
  unfold tailWord_5567748
  simp only [CollatzResearch.WordTrace]
  refine ⟨101536226316503683249419949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135381635088671577665893265 101536226316503683249419949)
  ·
    refine ⟨38076084868688881218532481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101536226316503683249419949 38076084868688881218532481)
    ·
      refine ⟨28557063651516660913899361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38076084868688881218532481 28557063651516660913899361)
      ·
        refine ⟨21417797738637495685424521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28557063651516660913899361 21417797738637495685424521)
        ·
          refine ⟨16063348303978121764068391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21417797738637495685424521 16063348303978121764068391)
          ·
            refine ⟨24095022455967182646102587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16063348303978121764068391 24095022455967182646102587)
            ·
              refine ⟨36142533683950773969153881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24095022455967182646102587 36142533683950773969153881)
              ·
                refine ⟨27106900262963080476865411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36142533683950773969153881 27106900262963080476865411)
                ·
                  refine ⟨40660350394444620715298117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27106900262963080476865411 40660350394444620715298117)
                  ·
                    refine ⟨7623815698958366384118397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40660350394444620715298117 7623815698958366384118397)
                    ·
                      refine ⟨2858930887109387394044399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623815698958366384118397 2858930887109387394044399)
                      ·
                        rfl

theorem cell23_5567748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5567748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567748 prefixEnd_5567748 := by exact prefixLift 5567748
  have htrace : WordTrace (prefixWord ++ tailWord_5567748) baseStart_5567748 baseEnd_5567748 := by
    simpa [prefixWord, tailWord_5567748, baseEnd_5567748] using wordTrace_append hprefix tailTrace_5567748
  have hstable : (prefixWord ++ tailWord_5567748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567748).length < 2 ^ (prefixWord ++ tailWord_5567748).sum := by decide
  have hdescent : baseEnd_5567748 < baseStart_5567748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567761 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_5567761 : Nat := 118140960795 + 5567761 * 2 ^ 59
def prefixEnd_5567761 : Nat := 4983230072969 + 3 ^ 40 * 5567761 * 2
def baseEnd_5567761 : Nat := 2858937562357895843181839

theorem tailTrace_5567761 : CollatzResearch.WordTrace tailWord_5567761 prefixEnd_5567761 2858937562357895843181839 := by
  unfold tailWord_5567761
  simp only [CollatzResearch.WordTrace]
  refine ⟨203072926781960269719063137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135381951187973513146042091 203072926781960269719063137)
  ·
    refine ⟨152304695086470202289297353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203072926781960269719063137 152304695086470202289297353)
    ·
      refine ⟨114228521314852651716973015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152304695086470202289297353 114228521314852651716973015)
      ·
        refine ⟨171342781972278977575459523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114228521314852651716973015 171342781972278977575459523)
        ·
          refine ⟨257014172958418466363189285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171342781972278977575459523 257014172958418466363189285)
          ·
            refine ⟨48190157429703462443097991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257014172958418466363189285 48190157429703462443097991)
            ·
              refine ⟨72285236144555193664646987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48190157429703462443097991 72285236144555193664646987)
              ·
                refine ⟨108427854216832790496970481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72285236144555193664646987 108427854216832790496970481)
                ·
                  refine ⟨81320890662624592872727861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108427854216832790496970481 81320890662624592872727861)
                  ·
                    refine ⟨7623833499621055581818237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81320890662624592872727861 7623833499621055581818237)
                    ·
                      refine ⟨2858937562357895843181839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623833499621055581818237 2858937562357895843181839)
                      ·
                        rfl

theorem cell23_5567761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_5567761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567761 prefixEnd_5567761 := by exact prefixLift 5567761
  have htrace : WordTrace (prefixWord ++ tailWord_5567761) baseStart_5567761 baseEnd_5567761 := by
    simpa [prefixWord, tailWord_5567761, baseEnd_5567761] using wordTrace_append hprefix tailTrace_5567761
  have hstable : (prefixWord ++ tailWord_5567761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567761).length < 2 ^ (prefixWord ++ tailWord_5567761).sum := by decide
  have hdescent : baseEnd_5567761 < baseStart_5567761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567795 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 3]
def baseStart_5567795 : Nat := 118140960795 + 5567795 * 2 ^ 59
def prefixEnd_5567795 : Nat := 4983230072969 + 3 ^ 40 * 5567795 * 2
def baseEnd_5567795 : Nat := 2858955020700148710156683

theorem tailTrace_5567795 : CollatzResearch.WordTrace tailWord_5567795 prefixEnd_5567795 2858955020700148710156683 := by
  unfold tailWord_5567795
  simp only [CollatzResearch.WordTrace]
  refine ⟨203074166863837093525800839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135382777909224729017200559 203074166863837093525800839)
  ·
    refine ⟨304611250295755640288701259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203074166863837093525800839 304611250295755640288701259)
    ·
      refine ⟨456916875443633460433051889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304611250295755640288701259 456916875443633460433051889)
      ·
        refine ⟨342687656582725095324788917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456916875443633460433051889 342687656582725095324788917)
        ·
          refine ⟨32126967804630477686698961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 342687656582725095324788917 32126967804630477686698961)
          ·
            refine ⟨24095225853472858265024221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32126967804630477686698961 24095225853472858265024221)
            ·
              refine ⟨9035709695052321849384083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24095225853472858265024221 9035709695052321849384083)
              ·
                refine ⟨13553564542578482774076125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9035709695052321849384083 13553564542578482774076125)
                ·
                  refine ⟨5082586703466931040278547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13553564542578482774076125 5082586703466931040278547)
                  ·
                    refine ⟨7623880055200396560417821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5082586703466931040278547 7623880055200396560417821)
                    ·
                      refine ⟨2858955020700148710156683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7623880055200396560417821 2858955020700148710156683)
                      ·
                        rfl

theorem cell23_5567795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_5567795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567795 prefixEnd_5567795 := by exact prefixLift 5567795
  have htrace : WordTrace (prefixWord ++ tailWord_5567795) baseStart_5567795 baseEnd_5567795 := by
    simpa [prefixWord, tailWord_5567795, baseEnd_5567795] using wordTrace_append hprefix tailTrace_5567795
  have hstable : (prefixWord ++ tailWord_5567795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567795).length < 2 ^ (prefixWord ++ tailWord_5567795).sum := by decide
  have hdescent : baseEnd_5567795 < baseStart_5567795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567811 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 1, 6]
def baseStart_5567811 : Nat := 118140960795 + 5567811 * 2 ^ 59
def prefixEnd_5567811 : Nat := 4983230072969 + 3 ^ 40 * 5567811 * 2
def baseEnd_5567811 : Nat := 952987745463540215852203

theorem tailTrace_5567811 : CollatzResearch.WordTrace tailWord_5567811 prefixEnd_5567811 952987745463540215852203 := by
  unfold tailWord_5567811
  simp only [CollatzResearch.WordTrace]
  refine ⟨203074750431779128258383287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135383166954519418838922191 203074750431779128258383287)
  ·
    refine ⟨304612125647668692387574931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203074750431779128258383287 304612125647668692387574931)
    ·
      refine ⟨456918188471503038581362397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304612125647668692387574931 456918188471503038581362397)
      ·
        refine ⟨171344320676813639468010899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456918188471503038581362397 171344320676813639468010899)
        ·
          refine ⟨257016481015220459202016349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171344320676813639468010899 257016481015220459202016349)
          ·
            refine ⟨96381180380707672200756131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257016481015220459202016349 96381180380707672200756131)
            ·
              refine ⟨144571770571061508301134197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96381180380707672200756131 144571770571061508301134197)
              ·
                refine ⟨13553603491037016403231331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144571770571061508301134197 13553603491037016403231331)
                ·
                  refine ⟨20330405236555524604846997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13553603491037016403231331 20330405236555524604846997)
                  ·
                    refine ⟨952987745463540215852203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20330405236555524604846997 952987745463540215852203)
                    ·
                      rfl

theorem cell23_5567811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 6].length) (baseStart_5567811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567811 prefixEnd_5567811 := by exact prefixLift 5567811
  have htrace : WordTrace (prefixWord ++ tailWord_5567811) baseStart_5567811 baseEnd_5567811 := by
    simpa [prefixWord, tailWord_5567811, baseEnd_5567811] using wordTrace_append hprefix tailTrace_5567811
  have hstable : (prefixWord ++ tailWord_5567811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567811).length < 2 ^ (prefixWord ++ tailWord_5567811).sum := by decide
  have hdescent : baseEnd_5567811 < baseStart_5567811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567815 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 1, 5]
def baseStart_5567815 : Nat := 118140960795 + 5567815 * 2 ^ 59
def prefixEnd_5567815 : Nat := 4983230072969 + 3 ^ 40 * 5567815 * 2
def baseEnd_5567815 : Nat := 952988430104412877302197

theorem tailTrace_5567815 : CollatzResearch.WordTrace tailWord_5567815 prefixEnd_5567815 952988430104412877302197 := by
  unfold tailWord_5567815
  simp only [CollatzResearch.WordTrace]
  refine ⟨203074896323764636941528899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135383264215843091294352599 203074896323764636941528899)
  ·
    refine ⟨304612344485646955412293349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203074896323764636941528899 304612344485646955412293349)
    ·
      refine ⟨57114814591058804139805003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304612344485646955412293349 57114814591058804139805003)
      ·
        refine ⟨85672221886588206209707505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57114814591058804139805003 85672221886588206209707505)
        ·
          refine ⟨64254166414941154657280629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85672221886588206209707505 64254166414941154657280629)
          ·
            refine ⟨6023828101400733249120059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64254166414941154657280629 6023828101400733249120059)
            ·
              refine ⟨9035742152101099873680089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023828101400733249120059 9035742152101099873680089)
              ·
                refine ⟨6776806614075824905260067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035742152101099873680089 6776806614075824905260067)
                ·
                  refine ⟨10165209921113737357890101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776806614075824905260067 10165209921113737357890101)
                  ·
                    refine ⟨952988430104412877302197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10165209921113737357890101 952988430104412877302197)
                    ·
                      rfl

theorem cell23_5567815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_5567815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567815 prefixEnd_5567815 := by exact prefixLift 5567815
  have htrace : WordTrace (prefixWord ++ tailWord_5567815) baseStart_5567815 baseEnd_5567815 := by
    simpa [prefixWord, tailWord_5567815, baseEnd_5567815] using wordTrace_append hprefix tailTrace_5567815
  have hstable : (prefixWord ++ tailWord_5567815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567815).length < 2 ^ (prefixWord ++ tailWord_5567815).sum := by decide
  have hdescent : baseEnd_5567815 < baseStart_5567815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567818 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_5567818 : Nat := 118140960795 + 5567818 * 2 ^ 59
def prefixEnd_5567818 : Nat := 4983230072969 + 3 ^ 40 * 5567818 * 2
def baseEnd_5567818 : Nat := 2858966830755202120169077

theorem tailTrace_5567818 : CollatzResearch.WordTrace tailWord_5567818 prefixEnd_5567818 2858966830755202120169077 := by
  unfold tailWord_5567818
  simp only [CollatzResearch.WordTrace]
  refine ⟨50768751435688442113472027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135383337161835845635925405 50768751435688442113472027)
  ·
    refine ⟨76153127153532663170208041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50768751435688442113472027 76153127153532663170208041)
    ·
      refine ⟨57114845365149497377656031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76153127153532663170208041 57114845365149497377656031)
      ·
        refine ⟨85672268047724246066484047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57114845365149497377656031 85672268047724246066484047)
        ·
          refine ⟨128508402071586369099726071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85672268047724246066484047 128508402071586369099726071)
          ·
            refine ⟨192762603107379553649589107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128508402071586369099726071 192762603107379553649589107)
            ·
              refine ⟨289143904661069330474383661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192762603107379553649589107 289143904661069330474383661)
              ·
                refine ⟨108428964247900998927893873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289143904661069330474383661 108428964247900998927893873)
                ·
                  refine ⟨81321723185925749195920405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108428964247900998927893873 81321723185925749195920405)
                  ·
                    refine ⟨3811955774340269493558769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81321723185925749195920405 3811955774340269493558769)
                    ·
                      refine ⟨2858966830755202120169077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3811955774340269493558769 2858966830755202120169077)
                      ·
                        rfl

theorem cell23_5567818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_5567818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567818 prefixEnd_5567818 := by exact prefixLift 5567818
  have htrace : WordTrace (prefixWord ++ tailWord_5567818) baseStart_5567818 baseEnd_5567818 := by
    simpa [prefixWord, tailWord_5567818, baseEnd_5567818] using wordTrace_append hprefix tailTrace_5567818
  have hstable : (prefixWord ++ tailWord_5567818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567818).length < 2 ^ (prefixWord ++ tailWord_5567818).sum := by decide
  have hdescent : baseEnd_5567818 < baseStart_5567818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567828 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_5567828 : Nat := 118140960795 + 5567828 * 2 ^ 59
def prefixEnd_5567828 : Nat := 4983230072969 + 3 ^ 40 * 5567828 * 2
def baseEnd_5567828 : Nat := 952990655187249027014677

theorem tailTrace_5567828 : CollatzResearch.WordTrace tailWord_5567828 prefixEnd_5567828 952990655187249027014677 := by
  unfold tailWord_5567828
  simp only [CollatzResearch.WordTrace]
  refine ⟨101537685236358770080876069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135383580315145026774501425 101537685236358770080876069)
  ·
    refine ⟨19038315981817269390164263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101537685236358770080876069 19038315981817269390164263)
    ·
      refine ⟨28557473972725904085246395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19038315981817269390164263 28557473972725904085246395)
      ·
        refine ⟨42836210959088856127869593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28557473972725904085246395 42836210959088856127869593)
        ·
          refine ⟨32127158219316642095902195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42836210959088856127869593 32127158219316642095902195)
          ·
            refine ⟨48190737328974963143853293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32127158219316642095902195 48190737328974963143853293)
            ·
              refine ⟨18071526498365611178944985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48190737328974963143853293 18071526498365611178944985)
              ·
                refine ⟨13553644873774208384208739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18071526498365611178944985 13553644873774208384208739)
                ·
                  refine ⟨20330467310661312576313109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13553644873774208384208739 20330467310661312576313109)
                  ·
                    refine ⟨952990655187249027014677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20330467310661312576313109 952990655187249027014677)
                    ·
                      rfl

theorem cell23_5567828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_5567828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567828 prefixEnd_5567828 := by exact prefixLift 5567828
  have htrace : WordTrace (prefixWord ++ tailWord_5567828) baseStart_5567828 baseEnd_5567828 := by
    simpa [prefixWord, tailWord_5567828, baseEnd_5567828] using wordTrace_append hprefix tailTrace_5567828
  have hstable : (prefixWord ++ tailWord_5567828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567828).length < 2 ^ (prefixWord ++ tailWord_5567828).sum := by decide
  have hdescent : baseEnd_5567828 < baseStart_5567828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567845 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_5567845 : Nat := 118140960795 + 5567845 * 2 ^ 59
def prefixEnd_5567845 : Nat := 4983230072969 + 3 ^ 40 * 5567845 * 2
def baseEnd_5567845 : Nat := 952993564910957838177151

theorem tailTrace_5567845 : CollatzResearch.WordTrace tailWord_5567845 prefixEnd_5567845 952993564910957838177151 := by
  unfold tailWord_5567845
  simp only [CollatzResearch.WordTrace]
  refine ⟨203075990513655952065120989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135383993675770634710080659 203075990513655952065120989)
  ·
    refine ⟨76153496442620982024420371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203075990513655952065120989 76153496442620982024420371)
    ·
      refine ⟨114230244663931473036630557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76153496442620982024420371 114230244663931473036630557)
      ·
        refine ⟨42836341748974302388736459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114230244663931473036630557 42836341748974302388736459)
        ·
          refine ⟨64254512623461453583104689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42836341748974302388736459 64254512623461453583104689)
          ·
            refine ⟨48190884467596090187328517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64254512623461453583104689 48190884467596090187328517)
            ·
              refine ⟨9035790837674266910124097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48190884467596090187328517 9035790837674266910124097)
              ·
                refine ⟨6776843128255700182593073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035790837674266910124097 6776843128255700182593073)
                ·
                  refine ⟨5082632346191775136944805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6776843128255700182593073 5082632346191775136944805)
                  ·
                    refine ⟨952993564910957838177151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082632346191775136944805 952993564910957838177151)
                    ·
                      rfl

theorem cell23_5567845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_5567845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567845 prefixEnd_5567845 := by exact prefixLift 5567845
  have htrace : WordTrace (prefixWord ++ tailWord_5567845) baseStart_5567845 baseEnd_5567845 := by
    simpa [prefixWord, tailWord_5567845, baseEnd_5567845] using wordTrace_append hprefix tailTrace_5567845
  have hstable : (prefixWord ++ tailWord_5567845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567845).length < 2 ^ (prefixWord ++ tailWord_5567845).sum := by decide
  have hdescent : baseEnd_5567845 < baseStart_5567845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567886 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5567886 : Nat := 118140960795 + 5567886 * 2 ^ 59
def prefixEnd_5567886 : Nat := 4983230072969 + 3 ^ 40 * 5567886 * 2
def baseEnd_5567886 : Nat := 2859001747439707854118765

theorem tailTrace_5567886 : CollatzResearch.WordTrace tailWord_5567886 prefixEnd_5567886 2859001747439707854118765 := by
  unfold tailWord_5567886
  simp only [CollatzResearch.WordTrace]
  refine ⟨25384685738313427008420439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135384990604338277378242341 25384685738313427008420439)
  ·
    refine ⟨38077028607470140512630659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25384685738313427008420439 38077028607470140512630659)
    ·
      refine ⟨57115542911205210768945989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38077028607470140512630659 57115542911205210768945989)
      ·
        refine ⟨10709164295850977019177373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57115542911205210768945989 10709164295850977019177373)
        ·
          refine ⟨4015936610944116382191515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10709164295850977019177373 4015936610944116382191515)
          ·
            refine ⟨6023904916416174573287273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015936610944116382191515 6023904916416174573287273)
            ·
              refine ⟨4517928687312130929965455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6023904916416174573287273 4517928687312130929965455)
              ·
                refine ⟨6776893030968196394948183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517928687312130929965455 6776893030968196394948183)
                ·
                  refine ⟨10165339546452294592422275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776893030968196394948183 10165339546452294592422275)
                  ·
                    refine ⟨15248009319678441888633413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10165339546452294592422275 15248009319678441888633413)
                    ·
                      refine ⟨2859001747439707854118765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15248009319678441888633413 2859001747439707854118765)
                      ·
                        rfl

theorem cell23_5567886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5567886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567886 prefixEnd_5567886 := by exact prefixLift 5567886
  have htrace : WordTrace (prefixWord ++ tailWord_5567886) baseStart_5567886 baseEnd_5567886 := by
    simpa [prefixWord, tailWord_5567886, baseEnd_5567886] using wordTrace_append hprefix tailTrace_5567886
  have hstable : (prefixWord ++ tailWord_5567886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567886).length < 2 ^ (prefixWord ++ tailWord_5567886).sum := by decide
  have hdescent : baseEnd_5567886 < baseStart_5567886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567928 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_5567928 : Nat := 118140960795 + 5567928 * 2 ^ 59
def prefixEnd_5567928 : Nat := 4983230072969 + 3 ^ 40 * 5567928 * 2
def baseEnd_5567928 : Nat := 2859023313627196689793571

theorem tailTrace_5567928 : CollatzResearch.WordTrace tailWord_5567928 prefixEnd_5567928 2859023313627196689793571 := by
  unfold tailWord_5567928
  simp only [CollatzResearch.WordTrace]
  refine ⟨101539508886177628620196219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135386011848236838160261625 101539508886177628620196219)
  ·
    refine ⟨152309263329266442930294329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101539508886177628620196219 152309263329266442930294329)
    ·
      refine ⟨114231947496949832197720747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152309263329266442930294329 114231947496949832197720747)
      ·
        refine ⟨171347921245424748296581121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114231947496949832197720747 171347921245424748296581121)
        ·
          refine ⟨128510940934068561222435841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171347921245424748296581121 128510940934068561222435841)
          ·
            refine ⟨96383205700551420916826881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128510940934068561222435841 96383205700551420916826881)
            ·
              refine ⟨72287404275413565687620161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96383205700551420916826881 72287404275413565687620161)
              ·
                refine ⟨54215553206560174265715121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72287404275413565687620161 54215553206560174265715121)
                ·
                  refine ⟨40661664904920130699286341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54215553206560174265715121 40661664904920130699286341)
                  ·
                    refine ⟨7624062169672524506116189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40661664904920130699286341 7624062169672524506116189)
                    ·
                      refine ⟨2859023313627196689793571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7624062169672524506116189 2859023313627196689793571)
                      ·
                        rfl

theorem cell23_5567928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_5567928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567928 prefixEnd_5567928 := by exact prefixLift 5567928
  have htrace : WordTrace (prefixWord ++ tailWord_5567928) baseStart_5567928 baseEnd_5567928 := by
    simpa [prefixWord, tailWord_5567928, baseEnd_5567928] using wordTrace_append hprefix tailTrace_5567928
  have hstable : (prefixWord ++ tailWord_5567928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567928).length < 2 ^ (prefixWord ++ tailWord_5567928).sum := by decide
  have hdescent : baseEnd_5567928 < baseStart_5567928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567929 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 1, 3, 2]
def baseStart_5567929 : Nat := 118140960795 + 5567929 * 2 ^ 59
def prefixEnd_5567929 : Nat := 4983230072969 + 3 ^ 40 * 5567929 * 2
def baseEnd_5567929 : Nat := 2859023827107851185881067

theorem tailTrace_5567929 : CollatzResearch.WordTrace tailWord_5567929 prefixEnd_5567929 2859023827107851185881067 := by
  unfold tailWord_5567929
  simp only [CollatzResearch.WordTrace]
  refine ⟨203079054245351634411178841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135386036163567756274119227 203079054245351634411178841)
  ·
    refine ⟨152309290684013725808384131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203079054245351634411178841 152309290684013725808384131)
    ·
      refine ⟨228463936026020588712576197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152309290684013725808384131 228463936026020588712576197)
      ·
        refine ⟨42836988004878860383608037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228463936026020588712576197 42836988004878860383608037)
        ·
          refine ⟨8031935250914786321926507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42836988004878860383608037 8031935250914786321926507)
          ·
            refine ⟨12047902876372179482889761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8031935250914786321926507 12047902876372179482889761)
            ·
              refine ⟨9035927157279134612167321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12047902876372179482889761 9035927157279134612167321)
              ·
                refine ⟨6776945367959350959125491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035927157279134612167321 6776945367959350959125491)
                ·
                  refine ⟨10165418051939026438688237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776945367959350959125491 10165418051939026438688237)
                  ·
                    refine ⟨3812031769477134914508089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10165418051939026438688237 3812031769477134914508089)
                    ·
                      refine ⟨2859023827107851185881067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812031769477134914508089 2859023827107851185881067)
                      ·
                        rfl

theorem cell23_5567929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_5567929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567929 prefixEnd_5567929 := by exact prefixLift 5567929
  have htrace : WordTrace (prefixWord ++ tailWord_5567929) baseStart_5567929 baseEnd_5567929 := by
    simpa [prefixWord, tailWord_5567929, baseEnd_5567929] using wordTrace_append hprefix tailTrace_5567929
  have hstable : (prefixWord ++ tailWord_5567929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567929).length < 2 ^ (prefixWord ++ tailWord_5567929).sum := by decide
  have hdescent : baseEnd_5567929 < baseStart_5567929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5567965 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 7]
def baseStart_5567965 : Nat := 118140960795 + 5567965 * 2 ^ 59
def prefixEnd_5567965 : Nat := 4983230072969 + 3 ^ 40 * 5567965 * 2
def baseEnd_5567965 : Nat := 317671368045712560558989

theorem tailTrace_5567965 : CollatzResearch.WordTrace tailWord_5567965 prefixEnd_5567965 317671368045712560558989 := by
  unfold tailWord_5567965
  simp only [CollatzResearch.WordTrace]
  refine ⟨203080367273221212559489349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135386911515480808372992899 203080367273221212559489349)
  ·
    refine ⟨38077568863728977354904253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203080367273221212559489349 38077568863728977354904253)
    ·
      refine ⟨14279088323898366508089095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38077568863728977354904253 14279088323898366508089095)
      ·
        refine ⟨21418632485847549762133643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14279088323898366508089095 21418632485847549762133643)
        ·
          refine ⟨32127948728771324643200465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21418632485847549762133643 32127948728771324643200465)
          ·
            refine ⟨24095961546578493482400349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32127948728771324643200465 24095961546578493482400349)
            ·
              refine ⟨9035985579966935055900131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24095961546578493482400349 9035985579966935055900131)
              ·
                refine ⟨13553978369950402583850197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9035985579966935055900131 13553978369950402583850197)
                ·
                  refine ⟨317671368045712560558989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13553978369950402583850197 317671368045712560558989)
                  ·
                    rfl

theorem cell23_5567965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_5567965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5567965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5567965 prefixEnd_5567965 := by exact prefixLift 5567965
  have htrace : WordTrace (prefixWord ++ tailWord_5567965) baseStart_5567965 baseEnd_5567965 := by
    simpa [prefixWord, tailWord_5567965, baseEnd_5567965] using wordTrace_append hprefix tailTrace_5567965
  have hstable : (prefixWord ++ tailWord_5567965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5567965).length < 2 ^ (prefixWord ++ tailWord_5567965).sum := by decide
  have hdescent : baseEnd_5567965 < baseStart_5567965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5567965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568032 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5568032 : Nat := 118140960795 + 5568032 * 2 ^ 59
def prefixEnd_5568032 : Nat := 4983230072969 + 3 ^ 40 * 5568032 * 2
def baseEnd_5568032 : Nat := 2859076715615264282893093

theorem tailTrace_5568032 : CollatzResearch.WordTrace tailWord_5568032 prefixEnd_5568032 2859076715615264282893093 := by
  unfold tailWord_5568032
  simp only [CollatzResearch.WordTrace]
  refine ⟨101541405481989241501089175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135388540642652322001452233 101541405481989241501089175)
  ·
    refine ⟨152312108222983862251633763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101541405481989241501089175 152312108222983862251633763)
    ·
      refine ⟨228468162334475793377450645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152312108222983862251633763 228468162334475793377450645)
      ·
        refine ⟨10709445109428552814567999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228468162334475793377450645 10709445109428552814567999)
        ·
          refine ⟨16064167664142829221851999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10709445109428552814567999 16064167664142829221851999)
          ·
            refine ⟨24096251496214243832777999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16064167664142829221851999 24096251496214243832777999)
            ·
              refine ⟨36144377244321365749166999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24096251496214243832777999 36144377244321365749166999)
              ·
                refine ⟨54216565866482048623750499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36144377244321365749166999 54216565866482048623750499)
                ·
                  refine ⟨81324848799723072935625749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54216565866482048623750499 81324848799723072935625749)
                  ·
                    refine ⟨3812102287487019043857457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81324848799723072935625749 3812102287487019043857457)
                    ·
                      refine ⟨2859076715615264282893093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812102287487019043857457 2859076715615264282893093)
                      ·
                        rfl

theorem cell23_5568032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5568032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568032 prefixEnd_5568032 := by exact prefixLift 5568032
  have htrace : WordTrace (prefixWord ++ tailWord_5568032) baseStart_5568032 baseEnd_5568032 := by
    simpa [prefixWord, tailWord_5568032, baseEnd_5568032] using wordTrace_append hprefix tailTrace_5568032
  have hstable : (prefixWord ++ tailWord_5568032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568032).length < 2 ^ (prefixWord ++ tailWord_5568032).sum := by decide
  have hdescent : baseEnd_5568032 < baseStart_5568032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568042 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_5568042 : Nat := 118140960795 + 5568042 * 2 ^ 59
def prefixEnd_5568042 : Nat := 4983230072969 + 3 ^ 40 * 5568042 * 2
def baseEnd_5568042 : Nat := 953027283473936414589349

theorem tailTrace_5568042 : CollatzResearch.WordTrace tailWord_5568042 prefixEnd_5568042 953027283473936414589349 := by
  unfold tailWord_5568042
  simp only [CollatzResearch.WordTrace]
  refine ⟨50770793923485563677510595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135388783795961503140028253 50770793923485563677510595)
  ·
    refine ⟨76156190885228345516265893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50770793923485563677510595 76156190885228345516265893)
    ·
      refine ⟨14279285790980314784299855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76156190885228345516265893 14279285790980314784299855)
      ·
        refine ⟨21418928686470472176449783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14279285790980314784299855 21418928686470472176449783)
        ·
          refine ⟨32128393029705708264674675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21418928686470472176449783 32128393029705708264674675)
          ·
            refine ⟨48192589544558562397012013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32128393029705708264674675 48192589544558562397012013)
            ·
              refine ⟨18072221079209460898879505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48192589544558562397012013 18072221079209460898879505)
              ·
                refine ⟨13554165809407095674159629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18072221079209460898879505 13554165809407095674159629)
                ·
                  refine ⟨5082812178527660877809861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13554165809407095674159629 5082812178527660877809861)
                  ·
                    refine ⟨953027283473936414589349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5082812178527660877809861 953027283473936414589349)
                    ·
                      rfl

theorem cell23_5568042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_5568042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568042 prefixEnd_5568042 := by exact prefixLift 5568042
  have htrace : WordTrace (prefixWord ++ tailWord_5568042) baseStart_5568042 baseEnd_5568042 := by
    simpa [prefixWord, tailWord_5568042, baseEnd_5568042] using wordTrace_append hprefix tailTrace_5568042
  have hstable : (prefixWord ++ tailWord_5568042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568042).length < 2 ^ (prefixWord ++ tailWord_5568042).sum := by decide
  have hdescent : baseEnd_5568042 < baseStart_5568042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568105 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_5568105 : Nat := 118140960795 + 5568105 * 2 ^ 59
def prefixEnd_5568105 : Nat := 4983230072969 + 3 ^ 40 * 5568105 * 2
def baseEnd_5568105 : Nat := 2859114199703042497280257

theorem tailTrace_5568105 : CollatzResearch.WordTrace tailWord_5568105 prefixEnd_5568105 2859114199703042497280257 := by
  unfold tailWord_5568105
  simp only [CollatzResearch.WordTrace]
  refine ⟨203085473492714016469585769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135390315661809344313057179 203085473492714016469585769)
  ·
    refine ⟨152314105119535512352189327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203085473492714016469585769 152314105119535512352189327)
    ·
      refine ⟨228471157679303268528283991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152314105119535512352189327 228471157679303268528283991)
      ·
        refine ⟨342706736518954902792425987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228471157679303268528283991 342706736518954902792425987)
        ·
          refine ⟨514060104778432354188638981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342706736518954902792425987 514060104778432354188638981)
          ·
            refine ⟨96386269645956066410369809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 514060104778432354188638981 96386269645956066410369809)
            ·
              refine ⟨72289702234467049807777357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96386269645956066410369809 72289702234467049807777357)
              ·
                refine ⟨27108638337925143677916509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72289702234467049807777357 27108638337925143677916509)
                ·
                  refine ⟨10165739376721928879218691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27108638337925143677916509 10165739376721928879218691)
                  ·
                    refine ⟨15248609065082893318828037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10165739376721928879218691 15248609065082893318828037)
                    ·
                      refine ⟨2859114199703042497280257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15248609065082893318828037 2859114199703042497280257)
                      ·
                        rfl

theorem cell23_5568105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_5568105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568105 prefixEnd_5568105 := by exact prefixLift 5568105
  have htrace : WordTrace (prefixWord ++ tailWord_5568105) baseStart_5568105 baseEnd_5568105 := by
    simpa [prefixWord, tailWord_5568105, baseEnd_5568105] using wordTrace_append hprefix tailTrace_5568105
  have hstable : (prefixWord ++ tailWord_5568105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568105).length < 2 ^ (prefixWord ++ tailWord_5568105).sum := by decide
  have hdescent : baseEnd_5568105 < baseStart_5568105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568135 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5568135 : Nat := 118140960795 + 5568135 * 2 ^ 59
def prefixEnd_5568135 : Nat := 4983230072969 + 3 ^ 40 * 5568135 * 2
def baseEnd_5568135 : Nat := 2859129604122677379905119

theorem tailTrace_5568135 : CollatzResearch.WordTrace tailWord_5568135 prefixEnd_5568135 2859129604122677379905119 := by
  unfold tailWord_5568135
  simp only [CollatzResearch.WordTrace]
  refine ⟨203086567682605331593177859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135391045121736887728785239 203086567682605331593177859)
  ·
    refine ⟨304629851523907997389766789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203086567682605331593177859 304629851523907997389766789)
    ·
      refine ⟨57118097160732749510581273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304629851523907997389766789 57118097160732749510581273)
      ·
        refine ⟨42838572870549562132935955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57118097160732749510581273 42838572870549562132935955)
        ·
          refine ⟨64257859305824343199403933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42838572870549562132935955 64257859305824343199403933)
          ·
            refine ⟨24096697239684128699776475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64257859305824343199403933 24096697239684128699776475)
            ·
              refine ⟨36145045859526193049664713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24096697239684128699776475 36145045859526193049664713)
              ·
                refine ⟨27108784394644644787248535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36145045859526193049664713 27108784394644644787248535)
                ·
                  refine ⟨40663176591966967180872803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27108784394644644787248535 40663176591966967180872803)
                  ·
                    refine ⟨60994764887950450771309205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40663176591966967180872803 60994764887950450771309205)
                    ·
                      refine ⟨2859129604122677379905119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60994764887950450771309205 2859129604122677379905119)
                      ·
                        rfl

theorem cell23_5568135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5568135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568135 prefixEnd_5568135 := by exact prefixLift 5568135
  have htrace : WordTrace (prefixWord ++ tailWord_5568135) baseStart_5568135 baseEnd_5568135 := by
    simpa [prefixWord, tailWord_5568135, baseEnd_5568135] using wordTrace_append hprefix tailTrace_5568135
  have hstable : (prefixWord ++ tailWord_5568135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568135).length < 2 ^ (prefixWord ++ tailWord_5568135).sum := by decide
  have hdescent : baseEnd_5568135 < baseStart_5568135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568142 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5568142 : Nat := 118140960795 + 5568142 * 2 ^ 59
def prefixEnd_5568142 : Nat := 4983230072969 + 3 ^ 40 * 5568142 * 2
def baseEnd_5568142 : Nat := 2859133198487258852517587

theorem tailTrace_5568142 : CollatzResearch.WordTrace tailWord_5568142 prefixEnd_5568142 2859133198487258852517587 := by
  unfold tailWord_5568142
  simp only [CollatzResearch.WordTrace]
  refine ⟨25385852874197496473585335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135391215329053314525788453 25385852874197496473585335)
  ·
    refine ⟨38078779311296244710378003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25385852874197496473585335 38078779311296244710378003)
    ·
      refine ⟨57118168966944367065567005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38078779311296244710378003 57118168966944367065567005)
      ·
        refine ⟨21419313362604137649587627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57118168966944367065567005 21419313362604137649587627)
        ·
          refine ⟨32128970043906206474381441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21419313362604137649587627 32128970043906206474381441)
          ·
            refine ⟨24096727532929654855786081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32128970043906206474381441 24096727532929654855786081)
            ·
              refine ⟨18072545649697241141839561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24096727532929654855786081 18072545649697241141839561)
              ·
                refine ⟨13554409237272930856379671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18072545649697241141839561 13554409237272930856379671)
                ·
                  refine ⟨20331613855909396284569507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13554409237272930856379671 20331613855909396284569507)
                  ·
                    refine ⟨30497420783864094426854261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20331613855909396284569507 30497420783864094426854261)
                    ·
                      refine ⟨2859133198487258852517587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30497420783864094426854261 2859133198487258852517587)
                      ·
                        rfl

theorem cell23_5568142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5568142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568142 prefixEnd_5568142 := by exact prefixLift 5568142
  have htrace : WordTrace (prefixWord ++ tailWord_5568142) baseStart_5568142 baseEnd_5568142 := by
    simpa [prefixWord, tailWord_5568142, baseEnd_5568142] using wordTrace_append hprefix tailTrace_5568142
  have hstable : (prefixWord ++ tailWord_5568142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568142).length < 2 ^ (prefixWord ++ tailWord_5568142).sum := by decide
  have hdescent : baseEnd_5568142 < baseStart_5568142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568156 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_5568156 : Nat := 118140960795 + 5568156 * 2 ^ 59
def prefixEnd_5568156 : Nat := 4983230072969 + 3 ^ 40 * 5568156 * 2
def baseEnd_5568156 : Nat := 2859140387216421797742523

theorem tailTrace_5568156 : CollatzResearch.WordTrace tailWord_5568156 prefixEnd_5568156 2859140387216421797742523 := by
  unfold tailWord_5568156
  simp only [CollatzResearch.WordTrace]
  refine ⟨101543666807764626089846161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135391555743686168119794881 101543666807764626089846161)
  ·
    refine ⟨76157750105823469567384621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101543666807764626089846161 76157750105823469567384621)
    ·
      refine ⟨28559156289683801087769233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76157750105823469567384621 28559156289683801087769233)
      ·
        refine ⟨21419367217262850815826925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28559156289683801087769233 21419367217262850815826925)
        ·
          refine ⟨8032262706473569055935097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21419367217262850815826925 8032262706473569055935097)
          ·
            refine ⟨6024197029855176791951323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8032262706473569055935097 6024197029855176791951323)
            ·
              refine ⟨9036295544782765187926985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024197029855176791951323 9036295544782765187926985)
              ·
                refine ⟨6777221658587073890945239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9036295544782765187926985 6777221658587073890945239)
                ·
                  refine ⟨10165832487880610836417859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6777221658587073890945239 10165832487880610836417859)
                  ·
                    refine ⟨15248748731820916254626789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10165832487880610836417859 15248748731820916254626789)
                    ·
                      refine ⟨2859140387216421797742523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15248748731820916254626789 2859140387216421797742523)
                      ·
                        rfl

theorem cell23_5568156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_5568156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568156 prefixEnd_5568156 := by exact prefixLift 5568156
  have htrace : WordTrace (prefixWord ++ tailWord_5568156) baseStart_5568156 baseEnd_5568156 := by
    simpa [prefixWord, tailWord_5568156, baseEnd_5568156] using wordTrace_append hprefix tailTrace_5568156
  have hstable : (prefixWord ++ tailWord_5568156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568156).length < 2 ^ (prefixWord ++ tailWord_5568156).sum := by decide
  have hdescent : baseEnd_5568156 < baseStart_5568156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568173 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_5568173 : Nat := 118140960795 + 5568173 * 2 ^ 59
def prefixEnd_5568173 : Nat := 4983230072969 + 3 ^ 40 * 5568173 * 2
def baseEnd_5568173 : Nat := 2859149116387548231229945

theorem tailTrace_5568173 : CollatzResearch.WordTrace tailWord_5568173 prefixEnd_5568173 2859149116387548231229945 := by
  unfold tailWord_5568173
  simp only [CollatzResearch.WordTrace]
  refine ⟨203087953656467664083061173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135391969104311776055374115 203087953656467664083061173)
  ·
    refine ⟨19039495655293843507786985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203087953656467664083061173 19039495655293843507786985)
    ·
      refine ⟨14279621741470382630840239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19039495655293843507786985 14279621741470382630840239)
      ·
        refine ⟨21419432612205573946260359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14279621741470382630840239 21419432612205573946260359)
        ·
          refine ⟨32129148918308360919390539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21419432612205573946260359 32129148918308360919390539)
          ·
            refine ⟨48193723377462541379085809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32129148918308360919390539 48193723377462541379085809)
            ·
              refine ⟨36145292533096906034314357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48193723377462541379085809 36145292533096906034314357)
              ·
                refine ⟨3388621174977834940716971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36145292533096906034314357 3388621174977834940716971)
                ·
                  refine ⟨5082931762466752411075457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388621174977834940716971 5082931762466752411075457)
                  ·
                    refine ⟨3812198821850064308306593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5082931762466752411075457 3812198821850064308306593)
                    ·
                      refine ⟨2859149116387548231229945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812198821850064308306593 2859149116387548231229945)
                      ·
                        rfl

theorem cell23_5568173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_5568173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568173 prefixEnd_5568173 := by exact prefixLift 5568173
  have htrace : WordTrace (prefixWord ++ tailWord_5568173) baseStart_5568173 baseEnd_5568173 := by
    simpa [prefixWord, tailWord_5568173, baseEnd_5568173] using wordTrace_append hprefix tailTrace_5568173
  have hstable : (prefixWord ++ tailWord_5568173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568173).length < 2 ^ (prefixWord ++ tailWord_5568173).sum := by decide
  have hdescent : baseEnd_5568173 < baseStart_5568173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568185 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5568185 : Nat := 118140960795 + 5568185 * 2 ^ 59
def prefixEnd_5568185 : Nat := 4983230072969 + 3 ^ 40 * 5568185 * 2
def baseEnd_5568185 : Nat := 2859155278155402184279889

theorem tailTrace_5568185 : CollatzResearch.WordTrace tailWord_5568185 prefixEnd_5568185 2859155278155402184279889 := by
  unfold tailWord_5568185
  simp only [CollatzResearch.WordTrace]
  refine ⟨203088391332424190132498009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135392260888282793421665339 203088391332424190132498009)
  ·
    refine ⟨152316293499318142599373507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203088391332424190132498009 152316293499318142599373507)
    ·
      refine ⟨228474440248977213899060261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152316293499318142599373507 228474440248977213899060261)
      ·
        refine ⟨42838957546683227606073799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228474440248977213899060261 42838957546683227606073799)
        ·
          refine ⟨64258436320024841409110699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42838957546683227606073799 64258436320024841409110699)
          ·
            refine ⟨96387654480037262113666049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64258436320024841409110699 96387654480037262113666049)
            ·
              refine ⟨72290740860027946585249537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96387654480037262113666049 72290740860027946585249537)
              ·
                refine ⟨54218055645020959938937153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72290740860027946585249537 54218055645020959938937153)
                ·
                  refine ⟨40663541733765719954202865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54218055645020959938937153 40663541733765719954202865)
                  ·
                    refine ⟨30497656300324289965652149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40663541733765719954202865 30497656300324289965652149)
                    ·
                      refine ⟨2859155278155402184279889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30497656300324289965652149 2859155278155402184279889)
                      ·
                        rfl

theorem cell23_5568185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5568185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568185 prefixEnd_5568185 := by exact prefixLift 5568185
  have htrace : WordTrace (prefixWord ++ tailWord_5568185) baseStart_5568185 baseEnd_5568185 := by
    simpa [prefixWord, tailWord_5568185, baseEnd_5568185] using wordTrace_append hprefix tailTrace_5568185
  have hstable : (prefixWord ++ tailWord_5568185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568185).length < 2 ^ (prefixWord ++ tailWord_5568185).sum := by decide
  have hdescent : baseEnd_5568185 < baseStart_5568185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568190 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_5568190 : Nat := 118140960795 + 5568190 * 2 ^ 59
def prefixEnd_5568190 : Nat := 4983230072969 + 3 ^ 40 * 5568190 * 2
def baseEnd_5568190 : Nat := 2859157845558674664717367

theorem tailTrace_5568190 : CollatzResearch.WordTrace tailWord_5568190 prefixEnd_5568190 2859157845558674664717367 := by
  unfold tailWord_5568190
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386071712175759498303753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135392382464937383990953349 25386071712175759498303753)
  ·
    refine ⟨19039553784131819623727815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25386071712175759498303753 19039553784131819623727815)
    ·
      refine ⟨28559330676197729435591723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19039553784131819623727815 28559330676197729435591723)
      ·
        refine ⟨42838996014296594153387585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28559330676197729435591723 42838996014296594153387585)
        ·
          refine ⟨32129247010722445615040689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42838996014296594153387585 32129247010722445615040689)
          ·
            refine ⟨24096935258041834211280517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32129247010722445615040689 24096935258041834211280517)
            ·
              refine ⟨4518175360882843914615097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24096935258041834211280517 4518175360882843914615097)
              ·
                refine ⟨3388631520662132935961323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4518175360882843914615097 3388631520662132935961323)
                ·
                  refine ⟨5082947280993199403941985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388631520662132935961323 5082947280993199403941985)
                  ·
                    refine ⟨3812210460744899552956489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5082947280993199403941985 3812210460744899552956489)
                    ·
                      refine ⟨2859157845558674664717367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812210460744899552956489 2859157845558674664717367)
                      ·
                        rfl

theorem cell23_5568190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_5568190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568190 prefixEnd_5568190 := by exact prefixLift 5568190
  have htrace : WordTrace (prefixWord ++ tailWord_5568190) baseStart_5568190 baseEnd_5568190 := by
    simpa [prefixWord, tailWord_5568190, baseEnd_5568190] using wordTrace_append hprefix tailTrace_5568190
  have hstable : (prefixWord ++ tailWord_5568190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568190).length < 2 ^ (prefixWord ++ tailWord_5568190).sum := by decide
  have hdescent : baseEnd_5568190 < baseStart_5568190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568229 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5568229 : Nat := 118140960795 + 5568229 * 2 ^ 59
def prefixEnd_5568229 : Nat := 4983230072969 + 3 ^ 40 * 5568229 * 2
def baseEnd_5568229 : Nat := 2859177871304200012129687

theorem tailTrace_5568229 : CollatzResearch.WordTrace tailWord_5568229 prefixEnd_5568229 2859177871304200012129687 := by
  unfold tailWord_5568229
  simp only [CollatzResearch.WordTrace]
  refine ⟨203089996144264785647099741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135393330762843190431399827 203089996144264785647099741)
  ·
    refine ⟨76158748554099294617662403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203089996144264785647099741 76158748554099294617662403)
    ·
      refine ⟨114238122831148941926493605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76158748554099294617662403 114238122831148941926493605)
      ·
        refine ⟨21419648030840426611217551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114238122831148941926493605 21419648030840426611217551)
        ·
          refine ⟨32129472046260639916826327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21419648030840426611217551 32129472046260639916826327)
          ·
            refine ⟨48194208069390959875239491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32129472046260639916826327 48194208069390959875239491)
            ·
              refine ⟨72291312104086439812859237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48194208069390959875239491 72291312104086439812859237)
              ·
                refine ⟨13554621019516207464911107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72291312104086439812859237 13554621019516207464911107)
                ·
                  refine ⟨20331931529274311197366661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13554621019516207464911107 20331931529274311197366661)
                  ·
                    refine ⟨3812237161738933349506249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20331931529274311197366661 3812237161738933349506249)
                    ·
                      refine ⟨2859177871304200012129687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812237161738933349506249 2859177871304200012129687)
                      ·
                        rfl

theorem cell23_5568229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5568229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568229 prefixEnd_5568229 := by exact prefixLift 5568229
  have htrace : WordTrace (prefixWord ++ tailWord_5568229) baseStart_5568229 baseEnd_5568229 := by
    simpa [prefixWord, tailWord_5568229, baseEnd_5568229] using wordTrace_append hprefix tailTrace_5568229
  have hstable : (prefixWord ++ tailWord_5568229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568229).length < 2 ^ (prefixWord ++ tailWord_5568229).sum := by decide
  have hdescent : baseEnd_5568229 < baseStart_5568229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568242 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5568242 : Nat := 118140960795 + 5568242 * 2 ^ 59
def prefixEnd_5568242 : Nat := 4983230072969 + 3 ^ 40 * 5568242 * 2
def baseEnd_5568242 : Nat := 2859184546552708461267127

theorem tailTrace_5568242 : CollatzResearch.WordTrace tailWord_5568242 prefixEnd_5568242 2859184546552708461267127 := by
  unfold tailWord_5568242
  simp only [CollatzResearch.WordTrace]
  refine ⟨50772617573304422216830745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135393646862145125911548653 50772617573304422216830745)
  ·
    refine ⟨38079463179978316662623059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50772617573304422216830745 38079463179978316662623059)
    ·
      refine ⟨57119194769967474993934589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38079463179978316662623059 57119194769967474993934589)
      ·
        refine ⟨21419698038737803122725471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57119194769967474993934589 21419698038737803122725471)
        ·
          refine ⟨32129547058106704684088207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21419698038737803122725471 32129547058106704684088207)
          ·
            refine ⟨48194320587160057026132311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32129547058106704684088207 48194320587160057026132311)
            ·
              refine ⟨72291480880740085539198467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48194320587160057026132311 72291480880740085539198467)
              ·
                refine ⟨108437221321110128308797701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72291480880740085539198467 108437221321110128308797701)
                ·
                  refine ⟨20331978997708149057899569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108437221321110128308797701 20331978997708149057899569)
                  ·
                    refine ⟨15248984248281111793424677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20331978997708149057899569 15248984248281111793424677)
                    ·
                      refine ⟨2859184546552708461267127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15248984248281111793424677 2859184546552708461267127)
                      ·
                        rfl

theorem cell23_5568242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5568242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568242 prefixEnd_5568242 := by exact prefixLift 5568242
  have htrace : WordTrace (prefixWord ++ tailWord_5568242) baseStart_5568242 baseEnd_5568242 := by
    simpa [prefixWord, tailWord_5568242, baseEnd_5568242] using wordTrace_append hprefix tailTrace_5568242
  have hstable : (prefixWord ++ tailWord_5568242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568242).length < 2 ^ (prefixWord ++ tailWord_5568242).sum := by decide
  have hdescent : baseEnd_5568242 < baseStart_5568242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568252 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 7]
def baseStart_5568252 : Nat := 118140960795 + 5568252 * 2 ^ 59
def prefixEnd_5568252 : Nat := 4983230072969 + 3 ^ 40 * 5568252 * 2
def baseEnd_5568252 : Nat := 317687742373250380238009

theorem tailTrace_5568252 : CollatzResearch.WordTrace tailWord_5568252 prefixEnd_5568252 317687742373250380238009 := by
  unfold tailWord_5568252
  simp only [CollatzResearch.WordTrace]
  refine ⟨101545417511590730287593505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135393890015454307050124673 101545417511590730287593505)
  ·
    refine ⟨76159063133693047715695129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101545417511590730287593505 76159063133693047715695129)
    ·
      refine ⟨57119297350269785786771347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76159063133693047715695129 57119297350269785786771347)
      ·
        refine ⟨85678946025404678680157021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57119297350269785786771347 85678946025404678680157021)
        ·
          refine ⟨32129604759526754505058883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85678946025404678680157021 32129604759526754505058883)
          ·
            refine ⟨48194407139290131757588325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32129604759526754505058883 48194407139290131757588325)
            ·
              refine ⟨9036451338616899704547811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48194407139290131757588325 9036451338616899704547811)
              ·
                refine ⟨13554677007925349556821717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9036451338616899704547811 13554677007925349556821717)
                ·
                  refine ⟨317687742373250380238009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13554677007925349556821717 317687742373250380238009)
                  ·
                    rfl

theorem cell23_5568252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_5568252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568252 prefixEnd_5568252 := by exact prefixLift 5568252
  have htrace : WordTrace (prefixWord ++ tailWord_5568252) baseStart_5568252 baseEnd_5568252 := by
    simpa [prefixWord, tailWord_5568252, baseEnd_5568252] using wordTrace_append hprefix tailTrace_5568252
  have hstable : (prefixWord ++ tailWord_5568252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568252).length < 2 ^ (prefixWord ++ tailWord_5568252).sum := by decide
  have hdescent : baseEnd_5568252 < baseStart_5568252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568263 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5568263 : Nat := 118140960795 + 5568263 * 2 ^ 59
def prefixEnd_5568263 : Nat := 4983230072969 + 3 ^ 40 * 5568263 * 2
def baseEnd_5568263 : Nat := 2859195329646452879104531

theorem tailTrace_5568263 : CollatzResearch.WordTrace tailWord_5568263 prefixEnd_5568263 2859195329646452879104531 := by
  unfold tailWord_5568263
  simp only [CollatzResearch.WordTrace]
  refine ⟨203091236226141609453837443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135394157484094406302558295 203091236226141609453837443)
  ·
    refine ⟨304636854339212414180756165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203091236226141609453837443 304636854339212414180756165)
    ·
      refine ⟨57119410188602327658891781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304636854339212414180756165 57119410188602327658891781)
      ·
        refine ⟨10709889410362936436042209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57119410188602327658891781 10709889410362936436042209)
        ·
          refine ⟨8032417057772202327031657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10709889410362936436042209 8032417057772202327031657)
          ·
            refine ⟨6024312793329151745273743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8032417057772202327031657 6024312793329151745273743)
            ·
              refine ⟨9036469189993727617910615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024312793329151745273743 9036469189993727617910615)
              ·
                refine ⟨13554703784990591426865923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9036469189993727617910615 13554703784990591426865923)
                ·
                  refine ⟨20332055677485887140298885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13554703784990591426865923 20332055677485887140298885)
                  ·
                    refine ⟨3812260439528603838806041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20332055677485887140298885 3812260439528603838806041)
                    ·
                      refine ⟨2859195329646452879104531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812260439528603838806041 2859195329646452879104531)
                      ·
                        rfl

theorem cell23_5568263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5568263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568263 prefixEnd_5568263 := by exact prefixLift 5568263
  have htrace : WordTrace (prefixWord ++ tailWord_5568263) baseStart_5568263 baseEnd_5568263 := by
    simpa [prefixWord, tailWord_5568263, baseEnd_5568263] using wordTrace_append hprefix tailTrace_5568263
  have hstable : (prefixWord ++ tailWord_5568263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568263).length < 2 ^ (prefixWord ++ tailWord_5568263).sum := by decide
  have hdescent : baseEnd_5568263 < baseStart_5568263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568275 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_5568275 : Nat := 118140960795 + 5568275 * 2 ^ 59
def prefixEnd_5568275 : Nat := 4983230072969 + 3 ^ 40 * 5568275 * 2
def baseEnd_5568275 : Nat := 2859201491414306832154475

theorem tailTrace_5568275 : CollatzResearch.WordTrace tailWord_5568275 prefixEnd_5568275 2859201491414306832154475 := by
  unfold tailWord_5568275
  simp only [CollatzResearch.WordTrace]
  refine ⟨203091673902098135503274279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135394449268065423668849519 203091673902098135503274279)
  ·
    refine ⟨304637510853147203254911419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203091673902098135503274279 304637510853147203254911419)
    ·
      refine ⟨456956266279720804882367129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304637510853147203254911419 456956266279720804882367129)
      ·
        refine ⟨342717199709790603661775347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456956266279720804882367129 342717199709790603661775347)
        ·
          refine ⟨514075799564685905492663021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342717199709790603661775347 514075799564685905492663021)
          ·
            refine ⟨192778424836757214559748633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514075799564685905492663021 192778424836757214559748633)
            ·
              refine ⟨144583818627567910919811475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192778424836757214559748633 144583818627567910919811475)
              ·
                refine ⟨216875727941351866379717213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144583818627567910919811475 216875727941351866379717213)
                ·
                  refine ⟨81328397978006949892393955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216875727941351866379717213 81328397978006949892393955)
                  ·
                    refine ⟨121992596967010424838590933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81328397978006949892393955 121992596967010424838590933)
                    ·
                      refine ⟨2859201491414306832154475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121992596967010424838590933 2859201491414306832154475)
                      ·
                        rfl

theorem cell23_5568275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_5568275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568275 prefixEnd_5568275 := by exact prefixLift 5568275
  have htrace : WordTrace (prefixWord ++ tailWord_5568275) baseStart_5568275 baseEnd_5568275 := by
    simpa [prefixWord, tailWord_5568275, baseEnd_5568275] using wordTrace_append hprefix tailTrace_5568275
  have hstable : (prefixWord ++ tailWord_5568275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568275).length < 2 ^ (prefixWord ++ tailWord_5568275).sum := by decide
  have hdescent : baseEnd_5568275 < baseStart_5568275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568282 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_5568282 : Nat := 118140960795 + 5568282 * 2 ^ 59
def prefixEnd_5568282 : Nat := 4983230072969 + 3 ^ 40 * 5568282 * 2
def baseEnd_5568282 : Nat := 953068361926296101588981

theorem tailTrace_5568282 : CollatzResearch.WordTrace tailWord_5568282 prefixEnd_5568282 953068361926296101588981 := by
  unfold tailWord_5568282
  simp only [CollatzResearch.WordTrace]
  refine ⟨50772982303268193924694775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135394619475381850465852733 50772982303268193924694775)
  ·
    refine ⟨76159473454902290887042163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50772982303268193924694775 76159473454902290887042163)
    ·
      refine ⟨114239210182353436330563245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76159473454902290887042163 114239210182353436330563245)
      ·
        refine ⟨42839703818382538623961217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114239210182353436330563245 42839703818382538623961217)
        ·
          refine ⟨32129777863786903967970913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42839703818382538623961217 32129777863786903967970913)
          ·
            refine ⟨24097333397840177975978185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32129777863786903967970913 24097333397840177975978185)
            ·
              refine ⟨18073000048380133481983639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24097333397840177975978185 18073000048380133481983639)
              ·
                refine ⟨27109500072570200222975459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18073000048380133481983639 27109500072570200222975459)
                ·
                  refine ⟨40664250108855300334463189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27109500072570200222975459 40664250108855300334463189)
                  ·
                    refine ⟨953068361926296101588981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40664250108855300334463189 953068361926296101588981)
                    ·
                      rfl

theorem cell23_5568282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_5568282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568282 prefixEnd_5568282 := by exact prefixLift 5568282
  have htrace : WordTrace (prefixWord ++ tailWord_5568282) baseStart_5568282 baseEnd_5568282 := by
    simpa [prefixWord, tailWord_5568282, baseEnd_5568282] using wordTrace_append hprefix tailTrace_5568282
  have hstable : (prefixWord ++ tailWord_5568282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568282).length < 2 ^ (prefixWord ++ tailWord_5568282).sum := by decide
  have hdescent : baseEnd_5568282 < baseStart_5568282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568309 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_5568309 : Nat := 118140960795 + 5568309 * 2 ^ 59
def prefixEnd_5568309 : Nat := 4983230072969 + 3 ^ 40 * 5568309 * 2
def baseEnd_5568309 : Nat := 2859218949756559699129319

theorem tailTrace_5568309 : CollatzResearch.WordTrace tailWord_5568309 prefixEnd_5568309 2859218949756559699129319 := by
  unfold tailWord_5568309
  simp only [CollatzResearch.WordTrace]
  refine ⟨203092913983974959310011981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135395275989316639540007987 203092913983974959310011981)
  ·
    refine ⟨76159842743990609741254493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203092913983974959310011981 76159842743990609741254493)
    ·
      refine ⟨28559941028996478652970435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76159842743990609741254493 28559941028996478652970435)
      ·
        refine ⟨42839911543494717979455653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28559941028996478652970435 42839911543494717979455653)
        ·
          refine ⟨8032483414405259621147935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42839911543494717979455653 8032483414405259621147935)
          ·
            refine ⟨12048725121607889431721903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8032483414405259621147935 12048725121607889431721903)
            ·
              refine ⟨18073087682411834147582855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12048725121607889431721903 18073087682411834147582855)
              ·
                refine ⟨27109631523617751221374283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18073087682411834147582855 27109631523617751221374283)
                ·
                  refine ⟨40664447285426626832061425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27109631523617751221374283 40664447285426626832061425)
                  ·
                    refine ⟨30498335464069970124046069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40664447285426626832061425 30498335464069970124046069)
                    ·
                      refine ⟨2859218949756559699129319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30498335464069970124046069 2859218949756559699129319)
                      ·
                        rfl

theorem cell23_5568309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_5568309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568309 prefixEnd_5568309 := by exact prefixLift 5568309
  have htrace : WordTrace (prefixWord ++ tailWord_5568309) baseStart_5568309 baseEnd_5568309 := by
    simpa [prefixWord, tailWord_5568309, baseEnd_5568309] using wordTrace_append hprefix tailTrace_5568309
  have hstable : (prefixWord ++ tailWord_5568309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568309).length < 2 ^ (prefixWord ++ tailWord_5568309).sum := by decide
  have hdescent : baseEnd_5568309 < baseStart_5568309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568346 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_5568346 : Nat := 118140960795 + 5568346 * 2 ^ 59
def prefixEnd_5568346 : Nat := 4983230072969 + 3 ^ 40 * 5568346 * 2
def baseEnd_5568346 : Nat := 953079316180258684788883

theorem tailTrace_5568346 : CollatzResearch.WordTrace tailWord_5568346 prefixEnd_5568346 953079316180258684788883 := by
  unfold tailWord_5568346
  simp only [CollatzResearch.WordTrace]
  refine ⟨50773565871210228657277223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135396175656560609752739261 50773565871210228657277223)
  ·
    refine ⟨76160348806815342985915835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50773565871210228657277223 76160348806815342985915835)
    ·
      refine ⟨114240523210223014478873753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76160348806815342985915835 114240523210223014478873753)
      ·
        refine ⟨85680392407667260859155315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114240523210223014478873753 85680392407667260859155315)
        ·
          refine ⟨128520588611500891288732973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85680392407667260859155315 128520588611500891288732973)
          ·
            refine ⟨48195220729312834233274865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128520588611500891288732973 48195220729312834233274865)
            ·
              refine ⟨36146415546984625674956149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48195220729312834233274865 36146415546984625674956149)
              ·
                refine ⟨3388726457529808657027139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36146415546984625674956149 3388726457529808657027139)
                ·
                  refine ⟨5083089686294712985540709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388726457529808657027139 5083089686294712985540709)
                  ·
                    refine ⟨953079316180258684788883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5083089686294712985540709 953079316180258684788883)
                    ·
                      rfl

theorem cell23_5568346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_5568346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568346 prefixEnd_5568346 := by exact prefixLift 5568346
  have htrace : WordTrace (prefixWord ++ tailWord_5568346) baseStart_5568346 baseEnd_5568346 := by
    simpa [prefixWord, tailWord_5568346, baseEnd_5568346] using wordTrace_append hprefix tailTrace_5568346
  have hstable : (prefixWord ++ tailWord_5568346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568346).length < 2 ^ (prefixWord ++ tailWord_5568346).sum := by decide
  have hdescent : baseEnd_5568346 < baseStart_5568346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568359 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 6]
def baseStart_5568359 : Nat := 118140960795 + 5568359 * 2 ^ 59
def prefixEnd_5568359 : Nat := 4983230072969 + 3 ^ 40 * 5568359 * 2
def baseEnd_5568359 : Nat := 317693847087698278167121

theorem tailTrace_5568359 : CollatzResearch.WordTrace tailWord_5568359 prefixEnd_5568359 317693847087698278167121 := by
  unfold tailWord_5568359
  simp only [CollatzResearch.WordTrace]
  refine ⟨203094737633793817849332131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135396491755862545232888087 203094737633793817849332131)
  ·
    refine ⟨304642106450690726773998197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203094737633793817849332131 304642106450690726773998197)
    ·
      refine ⟨28560197479752255635062331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 304642106450690726773998197 28560197479752255635062331)
      ·
        refine ⟨42840296219628383452593497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28560197479752255635062331 42840296219628383452593497)
        ·
          refine ⟨32130222164721287589445123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42840296219628383452593497 32130222164721287589445123)
          ·
            refine ⟨48195333247081931384167685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32130222164721287589445123 48195333247081931384167685)
            ·
              refine ⟨9036624983827862134531441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48195333247081931384167685 9036624983827862134531441)
              ·
                refine ⟨6777468737870896600898581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9036624983827862134531441 6777468737870896600898581)
                ·
                  refine ⟨317693847087698278167121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6777468737870896600898581 317693847087698278167121)
                  ·
                    rfl

theorem cell23_5568359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 6].length) (baseStart_5568359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568359 prefixEnd_5568359 := by exact prefixLift 5568359
  have htrace : WordTrace (prefixWord ++ tailWord_5568359) baseStart_5568359 baseEnd_5568359 := by
    simpa [prefixWord, tailWord_5568359, baseEnd_5568359] using wordTrace_append hprefix tailTrace_5568359
  have hstable : (prefixWord ++ tailWord_5568359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568359).length < 2 ^ (prefixWord ++ tailWord_5568359).sum := by decide
  have hdescent : baseEnd_5568359 < baseStart_5568359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568379 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 1, 5, 2]
def baseStart_5568379 : Nat := 118140960795 + 5568379 * 2 ^ 59
def prefixEnd_5568379 : Nat := 4983230072969 + 3 ^ 40 * 5568379 * 2
def baseEnd_5568379 : Nat := 2859254893402374425253997

theorem tailTrace_5568379 : CollatzResearch.WordTrace tailWord_5568379 prefixEnd_5568379 2859254893402374425253997 := by
  unfold tailWord_5568379
  simp only [CollatzResearch.WordTrace]
  refine ⟨203095467093721361265060191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135396978062480907510040127 203095467093721361265060191)
  ·
    refine ⟨304643200640582041897590287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203095467093721361265060191 304643200640582041897590287)
    ·
      refine ⟨456964800960873062846385431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304643200640582041897590287 456964800960873062846385431)
      ·
        refine ⟨685447201441309594269578147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456964800960873062846385431 685447201441309594269578147)
        ·
          refine ⟨1028170802161964391404367221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685447201441309594269578147 1028170802161964391404367221)
          ·
            refine ⟨96391012702684161694159427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1028170802161964391404367221 96391012702684161694159427)
            ·
              refine ⟨144586519054026242541239141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96391012702684161694159427 144586519054026242541239141)
              ·
                refine ⟨27109972322629920476482339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144586519054026242541239141 27109972322629920476482339)
                ·
                  refine ⟨40664958483944880714723509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27109972322629920476482339 40664958483944880714723509)
                  ·
                    refine ⟨3812339857869832567005329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40664958483944880714723509 3812339857869832567005329)
                    ·
                      refine ⟨2859254893402374425253997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812339857869832567005329 2859254893402374425253997)
                      ·
                        rfl

theorem cell23_5568379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5, 2].length) (baseStart_5568379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568379 prefixEnd_5568379 := by exact prefixLift 5568379
  have htrace : WordTrace (prefixWord ++ tailWord_5568379) baseStart_5568379 baseEnd_5568379 := by
    simpa [prefixWord, tailWord_5568379, baseEnd_5568379] using wordTrace_append hprefix tailTrace_5568379
  have hstable : (prefixWord ++ tailWord_5568379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568379).length < 2 ^ (prefixWord ++ tailWord_5568379).sum := by decide
  have hdescent : baseEnd_5568379 < baseStart_5568379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568389 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_5568389 : Nat := 118140960795 + 5568389 * 2 ^ 59
def prefixEnd_5568389 : Nat := 4983230072969 + 3 ^ 40 * 5568389 * 2
def baseEnd_5568389 : Nat := 953086676069639795376317

theorem tailTrace_5568389 : CollatzResearch.WordTrace tailWord_5568389 prefixEnd_5568389 953086676069639795376317 := by
  unfold tailWord_5568389
  simp only [CollatzResearch.WordTrace]
  refine ⟨203095831823685132972924221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135397221215790088648616147 203095831823685132972924221)
  ·
    refine ⟨76160936933881924864846583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203095831823685132972924221 76160936933881924864846583)
    ·
      refine ⟨114241405400822887297269875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76160936933881924864846583 114241405400822887297269875)
      ·
        refine ⟨171362108101234330945904813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114241405400822887297269875 171362108101234330945904813)
        ·
          refine ⟨64260790537962874104714305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171362108101234330945904813 64260790537962874104714305)
          ·
            refine ⟨48195592903472155578535729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64260790537962874104714305 48195592903472155578535729)
            ·
              refine ⟨36146694677604116683901797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48195592903472155578535729 36146694677604116683901797)
              ·
                refine ⟨6777505252050771878231587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36146694677604116683901797 6777505252050771878231587)
                ·
                  refine ⟨10166257878076157817347381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6777505252050771878231587 10166257878076157817347381)
                  ·
                    refine ⟨953086676069639795376317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10166257878076157817347381 953086676069639795376317)
                    ·
                      rfl

theorem cell23_5568389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_5568389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568389 prefixEnd_5568389 := by exact prefixLift 5568389
  have htrace : WordTrace (prefixWord ++ tailWord_5568389) baseStart_5568389 baseEnd_5568389 := by
    simpa [prefixWord, tailWord_5568389, baseEnd_5568389] using wordTrace_append hprefix tailTrace_5568389
  have hstable : (prefixWord ++ tailWord_5568389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568389).length < 2 ^ (prefixWord ++ tailWord_5568389).sum := by decide
  have hdescent : baseEnd_5568389 < baseStart_5568389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568459 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 3]
def baseStart_5568459 : Nat := 118140960795 + 5568459 * 2 ^ 59
def prefixEnd_5568459 : Nat := 4983230072969 + 3 ^ 40 * 5568459 * 2
def baseEnd_5568459 : Nat := 2859295971854734112253629

theorem tailTrace_5568459 : CollatzResearch.WordTrace tailWord_5568459 prefixEnd_5568459 2859295971854734112253629 := by
  unfold tailWord_5568459
  simp only [CollatzResearch.WordTrace]
  refine ⟨203098384933431534927972431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135398923288954356618648287 203098384933431534927972431)
  ·
    refine ⟨304647577400147302391958647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203098384933431534927972431 304647577400147302391958647)
    ·
      refine ⟨456971366100220953587937971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304647577400147302391958647 456971366100220953587937971)
      ·
        refine ⟨685457049150331430381906957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456971366100220953587937971 685457049150331430381906957)
        ·
          refine ⟨257046393431374286393215109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 685457049150331430381906957 257046393431374286393215109)
          ·
            refine ⟨48196198768382678698727833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257046393431374286393215109 48196198768382678698727833)
            ·
              refine ⟨36147149076287009024045875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48196198768382678698727833 36147149076287009024045875)
              ·
                refine ⟨54220723614430513536068813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36147149076287009024045875 54220723614430513536068813)
                ·
                  refine ⟨20332771355411442576025805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54220723614430513536068813 20332771355411442576025805)
                  ·
                    refine ⟨7624789258279290966009677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20332771355411442576025805 7624789258279290966009677)
                    ·
                      refine ⟨2859295971854734112253629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7624789258279290966009677 2859295971854734112253629)
                      ·
                        rfl

theorem cell23_5568459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 3].length) (baseStart_5568459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568459 prefixEnd_5568459 := by exact prefixLift 5568459
  have htrace : WordTrace (prefixWord ++ tailWord_5568459) baseStart_5568459 baseEnd_5568459 := by
    simpa [prefixWord, tailWord_5568459, baseEnd_5568459] using wordTrace_append hprefix tailTrace_5568459
  have hstable : (prefixWord ++ tailWord_5568459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568459).length < 2 ^ (prefixWord ++ tailWord_5568459).sum := by decide
  have hdescent : baseEnd_5568459 < baseStart_5568459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568466 : List Nat := [3, 2, 2, 3, 2, 2, 9]
def baseStart_5568466 : Nat := 118140960795 + 5568466 * 2 ^ 59
def prefixEnd_5568466 : Nat := 4983230072969 + 3 ^ 40 * 5568466 * 2
def baseEnd_5568466 : Nat := 35299994644682908455137

theorem tailTrace_5568466 : CollatzResearch.WordTrace tailWord_5568466 prefixEnd_5568466 35299994644682908455137 := by
  unfold tailWord_5568466
  simp only [CollatzResearch.WordTrace]
  refine ⟨50774660061101543780869313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135399093496270783415651501 50774660061101543780869313)
  ·
    refine ⟨38080995045826157835651985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50774660061101543780869313 38080995045826157835651985)
    ·
      refine ⟨28560746284369618376738989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38080995045826157835651985 28560746284369618376738989)
      ·
        refine ⟨10710279856638606891277121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28560746284369618376738989 10710279856638606891277121)
        ·
          refine ⟨8032709892478955168457841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10710279856638606891277121 8032709892478955168457841)
          ·
            refine ⟨6024532419359216376343381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8032709892478955168457841 6024532419359216376343381)
            ·
              refine ⟨35299994644682908455137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6024532419359216376343381 35299994644682908455137)
              ·
                rfl

theorem cell23_5568466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 9].length) (baseStart_5568466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568466 prefixEnd_5568466 := by exact prefixLift 5568466
  have htrace : WordTrace (prefixWord ++ tailWord_5568466) baseStart_5568466 baseEnd_5568466 := by
    simpa [prefixWord, tailWord_5568466, baseEnd_5568466] using wordTrace_append hprefix tailTrace_5568466
  have hstable : (prefixWord ++ tailWord_5568466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568466).length < 2 ^ (prefixWord ++ tailWord_5568466).sum := by decide
  have hdescent : baseEnd_5568466 < baseStart_5568466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568477 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_5568477 : Nat := 118140960795 + 5568477 * 2 ^ 59
def prefixEnd_5568477 : Nat := 4983230072969 + 3 ^ 40 * 5568477 * 2
def baseEnd_5568477 : Nat := 2859305214506515041828547

theorem tailTrace_5568477 : CollatzResearch.WordTrace tailWord_5568477 prefixEnd_5568477 2859305214506515041828547 := by
  unfold tailWord_5568477
  simp only [CollatzResearch.WordTrace]
  refine ⟨203099041447366324002127685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135399360964910882668085123 203099041447366324002127685)
  ·
    refine ⟨38081070271381185750398941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203099041447366324002127685 38081070271381185750398941)
    ·
      refine ⟨14280401351767944656399603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38081070271381185750398941 14280401351767944656399603)
      ·
        refine ⟨21420602027651916984599405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14280401351767944656399603 21420602027651916984599405)
        ·
          refine ⟨8032725760369468869224777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21420602027651916984599405 8032725760369468869224777)
          ·
            refine ⟨6024544320277101651918583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8032725760369468869224777 6024544320277101651918583)
            ·
              refine ⟨9036816480415652477877875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024544320277101651918583 9036816480415652477877875)
              ·
                refine ⟨13555224720623478716816813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9036816480415652477877875 13555224720623478716816813)
                ·
                  refine ⟨5083209270233804518806305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13555224720623478716816813 5083209270233804518806305)
                  ·
                    refine ⟨3812406952675353389104729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5083209270233804518806305 3812406952675353389104729)
                    ·
                      refine ⟨2859305214506515041828547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812406952675353389104729 2859305214506515041828547)
                      ·
                        rfl

theorem cell23_5568477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_5568477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568477 prefixEnd_5568477 := by exact prefixLift 5568477
  have htrace : WordTrace (prefixWord ++ tailWord_5568477) baseStart_5568477 baseEnd_5568477 := by
    simpa [prefixWord, tailWord_5568477, baseEnd_5568477] using wordTrace_append hprefix tailTrace_5568477
  have hstable : (prefixWord ++ tailWord_5568477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568477).length < 2 ^ (prefixWord ++ tailWord_5568477).sum := by decide
  have hdescent : baseEnd_5568477 < baseStart_5568477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568487 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 2, 4]
def baseStart_5568487 : Nat := 118140960795 + 5568487 * 2 ^ 59
def prefixEnd_5568487 : Nat := 4983230072969 + 3 ^ 40 * 5568487 * 2
def baseEnd_5568487 : Nat := 953103449771020000901167

theorem tailTrace_5568487 : CollatzResearch.WordTrace tailWord_5568487 prefixEnd_5568487 953103449771020000901167 := by
  unfold tailWord_5568487
  simp only [CollatzResearch.WordTrace]
  refine ⟨203099406177330095709991715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135399604118220063806661143 203099406177330095709991715)
  ·
    refine ⟨304649109265995143564987573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203099406177330095709991715 304649109265995143564987573)
    ·
      refine ⟨28560853993687044709217585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 304649109265995143564987573 28560853993687044709217585)
      ·
        refine ⟨21420640495265283531913189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28560853993687044709217585 21420640495265283531913189)
        ·
          refine ⟨4016370092862240662233723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21420640495265283531913189 4016370092862240662233723)
          ·
            refine ⟨6024555139293360993350585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016370092862240662233723 6024555139293360993350585)
            ·
              refine ⟨4518416354470020745012939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6024555139293360993350585 4518416354470020745012939)
              ·
                refine ⟨6777624531705031117519409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518416354470020745012939 6777624531705031117519409)
                ·
                  refine ⟨5083218398778773338139557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6777624531705031117519409 5083218398778773338139557)
                  ·
                    refine ⟨953103449771020000901167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5083218398778773338139557 953103449771020000901167)
                    ·
                      rfl

theorem cell23_5568487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_5568487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568487 prefixEnd_5568487 := by exact prefixLift 5568487
  have htrace : WordTrace (prefixWord ++ tailWord_5568487) baseStart_5568487 baseEnd_5568487 := by
    simpa [prefixWord, tailWord_5568487, baseEnd_5568487] using wordTrace_append hprefix tailTrace_5568487
  have hstable : (prefixWord ++ tailWord_5568487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568487).length < 2 ^ (prefixWord ++ tailWord_5568487).sum := by decide
  have hdescent : baseEnd_5568487 < baseStart_5568487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568520 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_5568520 : Nat := 118140960795 + 5568520 * 2 ^ 59
def prefixEnd_5568520 : Nat := 4983230072969 + 3 ^ 40 * 5568520 * 2
def baseEnd_5568520 : Nat := 2859327294174658373590849

theorem tailTrace_5568520 : CollatzResearch.WordTrace tailWord_5568520 prefixEnd_5568520 2859327294174658373590849 := by
  unfold tailWord_5568520
  simp only [CollatzResearch.WordTrace]
  refine ⟨101550304893105271172971507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135400406524140361563962009 101550304893105271172971507)
  ·
    refine ⟨152325457339657906759457261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101550304893105271172971507 152325457339657906759457261)
    ·
      refine ⟨57122046502371715034796473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152325457339657906759457261 57122046502371715034796473)
      ·
        refine ⟨42841534876778786276097355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57122046502371715034796473 42841534876778786276097355)
        ·
          refine ⟨64262302315168179414146033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42841534876778786276097355 64262302315168179414146033)
          ·
            refine ⟨48196726736376134560609525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64262302315168179414146033 48196726736376134560609525)
            ·
              refine ⟨4518443131535262615057143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48196726736376134560609525 4518443131535262615057143)
              ·
                refine ⟨6777664697302893922585715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518443131535262615057143 6777664697302893922585715)
                ·
                  refine ⟨10166497045954340883878573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6777664697302893922585715 10166497045954340883878573)
                  ·
                    refine ⟨3812436392232877831454465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10166497045954340883878573 3812436392232877831454465)
                    ·
                      refine ⟨2859327294174658373590849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812436392232877831454465 2859327294174658373590849)
                      ·
                        rfl

theorem cell23_5568520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_5568520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568520 prefixEnd_5568520 := by exact prefixLift 5568520
  have htrace : WordTrace (prefixWord ++ tailWord_5568520) baseStart_5568520 baseEnd_5568520 := by
    simpa [prefixWord, tailWord_5568520, baseEnd_5568520] using wordTrace_append hprefix tailTrace_5568520
  have hstable : (prefixWord ++ tailWord_5568520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568520).length < 2 ^ (prefixWord ++ tailWord_5568520).sum := by decide
  have hdescent : baseEnd_5568520 < baseStart_5568520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568546 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_5568546 : Nat := 118140960795 + 5568546 * 2 ^ 59
def prefixEnd_5568546 : Nat := 4983230072969 + 3 ^ 40 * 5568546 * 2
def baseEnd_5568546 : Nat := 2859340644671675271865729

theorem tailTrace_5568546 : CollatzResearch.WordTrace tailWord_5568546 prefixEnd_5568546 2859340644671675271865729 := by
  unfold tailWord_5568546
  simp only [CollatzResearch.WordTrace]
  refine ⟨50775389521029087196597373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135401038722744232524259661 50775389521029087196597373)
  ·
    refine ⟨19040771070385907698724015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50775389521029087196597373 19040771070385907698724015)
    ·
      refine ⟨28561156605578861548086023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19040771070385907698724015 28561156605578861548086023)
      ·
        refine ⟨42841734908368292322129035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28561156605578861548086023 42841734908368292322129035)
        ·
          refine ⟨64262602362552438483193553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42841734908368292322129035 64262602362552438483193553)
          ·
            refine ⟨48196951771914328862395165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64262602362552438483193553 48196951771914328862395165)
            ·
              refine ⟨18073856914467873323398187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48196951771914328862395165 18073856914467873323398187)
              ·
                refine ⟨27110785371701809985097281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18073856914467873323398187 27110785371701809985097281)
                ·
                  refine ⟨20333089028776357488822961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27110785371701809985097281 20333089028776357488822961)
                  ·
                    refine ⟨15249816771582268116617221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20333089028776357488822961 15249816771582268116617221)
                    ·
                      refine ⟨2859340644671675271865729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15249816771582268116617221 2859340644671675271865729)
                      ·
                        rfl

theorem cell23_5568546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_5568546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568546 prefixEnd_5568546 := by exact prefixLift 5568546
  have htrace : WordTrace (prefixWord ++ tailWord_5568546) baseStart_5568546 baseEnd_5568546 := by
    simpa [prefixWord, tailWord_5568546, baseEnd_5568546] using wordTrace_append hprefix tailTrace_5568546
  have hstable : (prefixWord ++ tailWord_5568546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568546).length < 2 ^ (prefixWord ++ tailWord_5568546).sum := by decide
  have hdescent : baseEnd_5568546 < baseStart_5568546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568573 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 5]
def baseStart_5568573 : Nat := 118140960795 + 5568573 * 2 ^ 59
def prefixEnd_5568573 : Nat := 4983230072969 + 3 ^ 40 * 5568573 * 2
def baseEnd_5568573 : Nat := 317706056516594074025345

theorem tailTrace_5568573 : CollatzResearch.WordTrace tailWord_5568573 prefixEnd_5568573 317706056516594074025345 := by
  unfold tailWord_5568573
  simp only [CollatzResearch.WordTrace]
  refine ⟨203102542855018532397622373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135401695236679021598414915 203102542855018532397622373)
  ·
    refine ⟨38081726785315974824554195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203102542855018532397622373 38081726785315974824554195)
    ·
      refine ⟨57122590177973962236831293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38081726785315974824554195 57122590177973962236831293)
      ·
        refine ⟨21420971316740235838811735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57122590177973962236831293 21420971316740235838811735)
        ·
          refine ⟨32131456975110353758217603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21420971316740235838811735 32131456975110353758217603)
          ·
            refine ⟨48197185462665530637326405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32131456975110353758217603 48197185462665530637326405)
            ·
              refine ⟨9036972274249786994498701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48197185462665530637326405 9036972274249786994498701)
              ·
                refine ⟨3388864602843670122937013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9036972274249786994498701 3388864602843670122937013)
                ·
                  refine ⟨317706056516594074025345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3388864602843670122937013 317706056516594074025345)
                  ·
                    rfl

theorem cell23_5568573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_5568573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568573 prefixEnd_5568573 := by exact prefixLift 5568573
  have htrace : WordTrace (prefixWord ++ tailWord_5568573) baseStart_5568573 baseEnd_5568573 := by
    simpa [prefixWord, tailWord_5568573, baseEnd_5568573] using wordTrace_append hprefix tailTrace_5568573
  have hstable : (prefixWord ++ tailWord_5568573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568573).length < 2 ^ (prefixWord ++ tailWord_5568573).sum := by decide
  have hdescent : baseEnd_5568573 < baseStart_5568573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568579 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5]
def baseStart_5568579 : Nat := 118140960795 + 5568579 * 2 ^ 59
def prefixEnd_5568579 : Nat := 4983230072969 + 3 ^ 40 * 5568579 * 2
def baseEnd_5568579 : Nat := 2859357589533273642753077

theorem tailTrace_5568579 : CollatzResearch.WordTrace tailWord_5568579 prefixEnd_5568579 2859357589533273642753077 := by
  unfold tailWord_5568579
  simp only [CollatzResearch.WordTrace]
  refine ⟨203102761692996795422340791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135401841128664530281560527 203102761692996795422340791)
  ·
    refine ⟨304654142539495193133511187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203102761692996795422340791 304654142539495193133511187)
    ·
      refine ⟨456981213809242789700266781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304654142539495193133511187 456981213809242789700266781)
      ·
        refine ⟨171367955178466046137600043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456981213809242789700266781 171367955178466046137600043)
        ·
          refine ⟨257051932767699069206400065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171367955178466046137600043 257051932767699069206400065)
          ·
            refine ⟨192788949575774301904800049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257051932767699069206400065 192788949575774301904800049)
            ·
              refine ⟨144591712181830726428600037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192788949575774301904800049 144591712181830726428600037)
              ·
                refine ⟨27110946034093261205362507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144591712181830726428600037 27110946034093261205362507)
                ·
                  refine ⟨40666419051139891808043761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27110946034093261205362507 40666419051139891808043761)
                  ·
                    refine ⟨30499814288354918856032821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40666419051139891808043761 30499814288354918856032821)
                    ·
                      refine ⟨2859357589533273642753077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30499814288354918856032821 2859357589533273642753077)
                      ·
                        rfl

theorem cell23_5568579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_5568579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568579 prefixEnd_5568579 := by exact prefixLift 5568579
  have htrace : WordTrace (prefixWord ++ tailWord_5568579) baseStart_5568579 baseEnd_5568579 := by
    simpa [prefixWord, tailWord_5568579, baseEnd_5568579] using wordTrace_append hprefix tailTrace_5568579
  have hstable : (prefixWord ++ tailWord_5568579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568579).length < 2 ^ (prefixWord ++ tailWord_5568579).sum := by decide
  have hdescent : baseEnd_5568579 < baseStart_5568579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568643 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 3]
def baseStart_5568643 : Nat := 118140960795 + 5568643 * 2 ^ 59
def prefixEnd_5568643 : Nat := 4983230072969 + 3 ^ 40 * 5568643 * 2
def baseEnd_5568643 : Nat := 2859390452295161392352783

theorem tailTrace_5568643 : CollatzResearch.WordTrace tailWord_5568643 prefixEnd_5568643 2859390452295161392352783 := by
  unfold tailWord_5568643
  simp only [CollatzResearch.WordTrace]
  refine ⟨203105095964764934352670583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135403397309843289568447055 203105095964764934352670583)
  ·
    refine ⟨304657643947147401529005875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203105095964764934352670583 304657643947147401529005875)
    ·
      refine ⟨456986465920721102293508813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304657643947147401529005875 456986465920721102293508813)
      ·
        refine ⟨171369924720270413360065805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456986465920721102293508813 171369924720270413360065805)
        ·
          refine ⟨64263721770101405010024677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171369924720270413360065805 64263721770101405010024677)
          ·
            refine ⟨12049447831894013439379627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64263721770101405010024677 12049447831894013439379627)
            ·
              refine ⟨18074171747841020159069441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12049447831894013439379627 18074171747841020159069441)
              ·
                refine ⟨13555628810880765119302081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18074171747841020159069441 13555628810880765119302081)
                ·
                  refine ⟨10166721608160573839476561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13555628810880765119302081 10166721608160573839476561)
                  ·
                    refine ⟨7625041206120430379607421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10166721608160573839476561 7625041206120430379607421)
                    ·
                      refine ⟨2859390452295161392352783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7625041206120430379607421 2859390452295161392352783)
                      ·
                        rfl

theorem cell23_5568643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_5568643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568643 prefixEnd_5568643 := by exact prefixLift 5568643
  have htrace : WordTrace (prefixWord ++ tailWord_5568643) baseStart_5568643 baseEnd_5568643 := by
    simpa [prefixWord, tailWord_5568643, baseEnd_5568643] using wordTrace_append hprefix tailTrace_5568643
  have hstable : (prefixWord ++ tailWord_5568643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568643).length < 2 ^ (prefixWord ++ tailWord_5568643).sum := by decide
  have hdescent : baseEnd_5568643 < baseStart_5568643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568650 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_5568650 : Nat := 118140960795 + 5568650 * 2 ^ 59
def prefixEnd_5568650 : Nat := 4983230072969 + 3 ^ 40 * 5568650 * 2
def baseEnd_5568650 : Nat := 953131348886580954988417

theorem tailTrace_5568650 : CollatzResearch.WordTrace tailWord_5568650 prefixEnd_5568650 953131348886580954988417 := by
  unfold tailWord_5568650
  simp only [CollatzResearch.WordTrace]
  refine ⟨50776337818934893637043851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135403567517159716365450269 50776337818934893637043851)
  ·
    refine ⟨76164506728402340455565777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50776337818934893637043851 76164506728402340455565777)
    ·
      refine ⟨57123380046301755341674333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76164506728402340455565777 57123380046301755341674333)
      ·
        refine ⟨21421267517363158253127875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57123380046301755341674333 21421267517363158253127875)
        ·
          refine ⟨32131901276044737379691813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21421267517363158253127875 32131901276044737379691813)
          ·
            refine ⟨6024731489258388258692215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32131901276044737379691813 6024731489258388258692215)
            ·
              refine ⟨9037097233887582388038323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024731489258388258692215 9037097233887582388038323)
              ·
                refine ⟨13555645850831373582057485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9037097233887582388038323 13555645850831373582057485)
                ·
                  refine ⟨5083367194061765093271557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13555645850831373582057485 5083367194061765093271557)
                  ·
                    refine ⟨953131348886580954988417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5083367194061765093271557 953131348886580954988417)
                    ·
                      rfl

theorem cell23_5568650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_5568650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568650 prefixEnd_5568650 := by exact prefixLift 5568650
  have htrace : WordTrace (prefixWord ++ tailWord_5568650) baseStart_5568650 baseEnd_5568650 := by
    simpa [prefixWord, tailWord_5568650, baseEnd_5568650] using wordTrace_append hprefix tailTrace_5568650
  have hstable : (prefixWord ++ tailWord_5568650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568650).length < 2 ^ (prefixWord ++ tailWord_5568650).sum := by decide
  have hdescent : baseEnd_5568650 < baseStart_5568650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568659 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 9]
def baseStart_5568659 : Nat := 118140960795 + 5568659 * 2 ^ 59
def prefixEnd_5568659 : Nat := 4983230072969 + 3 ^ 40 * 5568659 * 2
def baseEnd_5568659 : Nat := 953132889328544443250903

theorem tailTrace_5568659 : CollatzResearch.WordTrace tailWord_5568659 prefixEnd_5568659 953132889328544443250903 := by
  unfold tailWord_5568659
  simp only [CollatzResearch.WordTrace]
  refine ⟨203105679532706969085253031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135403786355137979390168687 203105679532706969085253031)
  ·
    refine ⟨304658519299060453627879547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203105679532706969085253031 304658519299060453627879547)
    ·
      refine ⟨456987778948590680441819321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304658519299060453627879547 456987778948590680441819321)
      ·
        refine ⟨342740834211443010331364491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456987778948590680441819321 342740834211443010331364491)
        ·
          refine ⟨514111251317164515497046737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342740834211443010331364491 514111251317164515497046737)
          ·
            refine ⟨385583438487873386622785053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514111251317164515497046737 385583438487873386622785053)
            ·
              refine ⟨144593789432952519983544395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385583438487873386622785053 144593789432952519983544395)
              ·
                refine ⟨216890684149428779975316593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144593789432952519983544395 216890684149428779975316593)
                ·
                  refine ⟨162668013112071584981487445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216890684149428779975316593 162668013112071584981487445)
                  ·
                    refine ⟨953132889328544443250903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162668013112071584981487445 953132889328544443250903)
                    ·
                      rfl

theorem cell23_5568659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_5568659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568659 prefixEnd_5568659 := by exact prefixLift 5568659
  have htrace : WordTrace (prefixWord ++ tailWord_5568659) baseStart_5568659 baseEnd_5568659 := by
    simpa [prefixWord, tailWord_5568659, baseEnd_5568659] using wordTrace_append hprefix tailTrace_5568659
  have hstable : (prefixWord ++ tailWord_5568659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568659).length < 2 ^ (prefixWord ++ tailWord_5568659).sum := by decide
  have hdescent : baseEnd_5568659 < baseStart_5568659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568663 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 6]
def baseStart_5568663 : Nat := 118140960795 + 5568663 * 2 ^ 59
def prefixEnd_5568663 : Nat := 4983230072969 + 3 ^ 40 * 5568663 * 2
def baseEnd_5568663 : Nat := 317711191323139034900299

theorem tailTrace_5568663 : CollatzResearch.WordTrace tailWord_5568663 prefixEnd_5568663 317711191323139034900299 := by
  unfold tailWord_5568663
  simp only [CollatzResearch.WordTrace]
  refine ⟨203105825424692477768398643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135403883616461651845599095 203105825424692477768398643)
  ·
    refine ⟨304658738137038716652597965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203105825424692477768398643 304658738137038716652597965)
    ·
      refine ⟨114247026801389518744724237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304658738137038716652597965 114247026801389518744724237)
      ·
        refine ⟨42842635050521069529271589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114247026801389518744724237 42842635050521069529271589)
        ·
          refine ⟨8032994071972700536738423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42842635050521069529271589 8032994071972700536738423)
          ·
            refine ⟨12049491107959050805107635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8032994071972700536738423 12049491107959050805107635)
            ·
              refine ⟨18074236661938576207661453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12049491107959050805107635 18074236661938576207661453)
              ·
                refine ⟨6777838748226966077873045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18074236661938576207661453 6777838748226966077873045)
                ·
                  refine ⟨317711191323139034900299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6777838748226966077873045 317711191323139034900299)
                  ·
                    rfl

theorem cell23_5568663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 6].length) (baseStart_5568663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568663 prefixEnd_5568663 := by exact prefixLift 5568663
  have htrace : WordTrace (prefixWord ++ tailWord_5568663) baseStart_5568663 baseEnd_5568663 := by
    simpa [prefixWord, tailWord_5568663, baseEnd_5568663] using wordTrace_append hprefix tailTrace_5568663
  have hstable : (prefixWord ++ tailWord_5568663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568663).length < 2 ^ (prefixWord ++ tailWord_5568663).sum := by decide
  have hdescent : baseEnd_5568663 < baseStart_5568663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568730 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2]
def baseStart_5568730 : Nat := 118140960795 + 5568730 * 2 ^ 59
def prefixEnd_5568730 : Nat := 4983230072969 + 3 ^ 40 * 5568730 * 2
def baseEnd_5568730 : Nat := 2859435125112102551964883

theorem tailTrace_5568730 : CollatzResearch.WordTrace tailWord_5568730 prefixEnd_5568730 2859435125112102551964883 := by
  unfold tailWord_5568730
  simp only [CollatzResearch.WordTrace]
  refine ⟨50777067278862437052771911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135405512743633165474058429 50777067278862437052771911)
  ·
    refine ⟨76165600918293655579157867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50777067278862437052771911 76165600918293655579157867)
    ·
      refine ⟨114248401377440483368736801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76165600918293655579157867 114248401377440483368736801)
      ·
        refine ⟨85686301033080362526552601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114248401377440483368736801 85686301033080362526552601)
        ·
          refine ⟨64264725774810271894914451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85686301033080362526552601 64264725774810271894914451)
          ·
            refine ⟨96397088662215407842371677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64264725774810271894914451 96397088662215407842371677)
            ·
              refine ⟨36148908248330777940889379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96397088662215407842371677 36148908248330777940889379)
              ·
                refine ⟨54223362372496166911334069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36148908248330777940889379 54223362372496166911334069)
                ·
                  refine ⟨5083440222421515647937569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54223362372496166911334069 5083440222421515647937569)
                  ·
                    refine ⟨3812580166816136735953177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5083440222421515647937569 3812580166816136735953177)
                    ·
                      refine ⟨2859435125112102551964883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812580166816136735953177 2859435125112102551964883)
                      ·
                        rfl

theorem cell23_5568730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_5568730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568730 prefixEnd_5568730 := by exact prefixLift 5568730
  have htrace : WordTrace (prefixWord ++ tailWord_5568730) baseStart_5568730 baseEnd_5568730 := by
    simpa [prefixWord, tailWord_5568730, baseEnd_5568730] using wordTrace_append hprefix tailTrace_5568730
  have hstable : (prefixWord ++ tailWord_5568730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568730).length < 2 ^ (prefixWord ++ tailWord_5568730).sum := by decide
  have hdescent : baseEnd_5568730 < baseStart_5568730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568764 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_5568764 : Nat := 118140960795 + 5568764 * 2 ^ 59
def prefixEnd_5568764 : Nat := 4983230072969 + 3 ^ 40 * 5568764 * 2
def baseEnd_5568764 : Nat := 2859452583454355418939727

theorem tailTrace_5568764 : CollatzResearch.WordTrace tailWord_5568764 prefixEnd_5568764 2859452583454355418939727 := by
  unfold tailWord_5568764
  simp only [CollatzResearch.WordTrace]
  refine ⟨101554754598663286008912673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135406339464884381345216897 101554754598663286008912673)
  ·
    refine ⟨76166065948997464506684505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101554754598663286008912673 76166065948997464506684505)
    ·
      refine ⟨57124549461748098380013379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76166065948997464506684505 57124549461748098380013379)
      ·
        refine ⟨85686824192622147570020069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57124549461748098380013379 85686824192622147570020069)
        ·
          refine ⟨16066279536116652669378763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85686824192622147570020069 16066279536116652669378763)
          ·
            refine ⟨24099419304174979004068145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16066279536116652669378763 24099419304174979004068145)
            ·
              refine ⟨18074564478131234253051109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24099419304174979004068145 18074564478131234253051109)
              ·
                refine ⟨3388980839649606422447083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18074564478131234253051109 3388980839649606422447083)
                ·
                  refine ⟨5083471259474409633670625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388980839649606422447083 5083471259474409633670625)
                  ·
                    refine ⟨3812603444605807225252969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5083471259474409633670625 3812603444605807225252969)
                    ·
                      refine ⟨2859452583454355418939727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812603444605807225252969 2859452583454355418939727)
                      ·
                        rfl

theorem cell23_5568764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_5568764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568764 prefixEnd_5568764 := by exact prefixLift 5568764
  have htrace : WordTrace (prefixWord ++ tailWord_5568764) baseStart_5568764 baseEnd_5568764 := by
    simpa [prefixWord, tailWord_5568764, baseEnd_5568764] using wordTrace_append hprefix tailTrace_5568764
  have hstable : (prefixWord ++ tailWord_5568764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568764).length < 2 ^ (prefixWord ++ tailWord_5568764).sum := by decide
  have hdescent : baseEnd_5568764 < baseStart_5568764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568773 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 7, 2]
def baseStart_5568773 : Nat := 118140960795 + 5568773 * 2 ^ 59
def prefixEnd_5568773 : Nat := 4983230072969 + 3 ^ 40 * 5568773 * 2
def baseEnd_5568773 : Nat := 2859457204780245883727185

theorem tailTrace_5568773 : CollatzResearch.WordTrace tailWord_5568773 prefixEnd_5568773 2859457204780245883727185 := by
  unfold tailWord_5568773
  simp only [CollatzResearch.WordTrace]
  refine ⟨203109837454293966554902973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135406558302862644369935315 203109837454293966554902973)
  ·
    refine ⟨76166189045360237458088615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203109837454293966554902973 76166189045360237458088615)
    ·
      refine ⟨114249283568040356187132923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76166189045360237458088615 114249283568040356187132923)
      ·
        refine ⟨171373925352060534280699385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114249283568040356187132923 171373925352060534280699385)
        ·
          refine ⟨128530444014045400710524539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171373925352060534280699385 128530444014045400710524539)
          ·
            refine ⟨192795666021068101065786809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128530444014045400710524539 192795666021068101065786809)
            ·
              refine ⟨144596749515801075799340107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192795666021068101065786809 144596749515801075799340107)
              ·
                refine ⟨216895124273701613699010161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144596749515801075799340107 216895124273701613699010161)
                ·
                  refine ⟨162671343205276210274257621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216895124273701613699010161 162671343205276210274257621)
                  ·
                    refine ⟨3812609606373661178302913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162671343205276210274257621 3812609606373661178302913)
                    ·
                      refine ⟨2859457204780245883727185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812609606373661178302913 2859457204780245883727185)
                      ·
                        rfl

theorem cell23_5568773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_5568773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568773 prefixEnd_5568773 := by exact prefixLift 5568773
  have htrace : WordTrace (prefixWord ++ tailWord_5568773) baseStart_5568773 baseEnd_5568773 := by
    simpa [prefixWord, tailWord_5568773, baseEnd_5568773] using wordTrace_append hprefix tailTrace_5568773
  have hstable : (prefixWord ++ tailWord_5568773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568773).length < 2 ^ (prefixWord ++ tailWord_5568773).sum := by decide
  have hdescent : baseEnd_5568773 < baseStart_5568773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568798 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5568798 : Nat := 118140960795 + 5568798 * 2 ^ 59
def prefixEnd_5568798 : Nat := 4983230072969 + 3 ^ 40 * 5568798 * 2
def baseEnd_5568798 : Nat := 2859470041796608285914571

theorem tailTrace_5568798 : CollatzResearch.WordTrace tailWord_5568798 prefixEnd_5568798 2859470041796608285914571 := by
  unfold tailWord_5568798
  simp only [CollatzResearch.WordTrace]
  refine ⟨25388843659900424478070381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135407166186135597216375365 25388843659900424478070381)
  ·
    refine ⟨9520816372462659179276393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25388843659900424478070381 9520816372462659179276393)
    ·
      refine ⟨7140612279346994384457295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9520816372462659179276393 7140612279346994384457295)
      ·
        refine ⟨10710918419020491576685943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7140612279346994384457295 10710918419020491576685943)
        ·
          refine ⟨16066377628530737365028915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710918419020491576685943 16066377628530737365028915)
          ·
            refine ⟨24099566442796106047543373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16066377628530737365028915 24099566442796106047543373)
            ·
              refine ⟨9037337416048539767828765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24099566442796106047543373 9037337416048539767828765)
              ·
                refine ⟨3389001531018202412935787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9037337416048539767828765 3389001531018202412935787)
                ·
                  refine ⟨5083502296527303619403681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389001531018202412935787 5083502296527303619403681)
                  ·
                    refine ⟨3812626722395477714552761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5083502296527303619403681 3812626722395477714552761)
                    ·
                      refine ⟨2859470041796608285914571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812626722395477714552761 2859470041796608285914571)
                      ·
                        rfl

theorem cell23_5568798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5568798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568798 prefixEnd_5568798 := by exact prefixLift 5568798
  have htrace : WordTrace (prefixWord ++ tailWord_5568798) baseStart_5568798 baseEnd_5568798 := by
    simpa [prefixWord, tailWord_5568798, baseEnd_5568798] using wordTrace_append hprefix tailTrace_5568798
  have hstable : (prefixWord ++ tailWord_5568798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568798).length < 2 ^ (prefixWord ++ tailWord_5568798).sum := by decide
  have hdescent : baseEnd_5568798 < baseStart_5568798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568816 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_5568816 : Nat := 118140960795 + 5568816 * 2 ^ 59
def prefixEnd_5568816 : Nat := 4983230072969 + 3 ^ 40 * 5568816 * 2
def baseEnd_5568816 : Nat := 2859479284448389215489487

theorem tailTrace_5568816 : CollatzResearch.WordTrace tailWord_5568816 prefixEnd_5568816 2859479284448389215489487 := by
  unfold tailWord_5568816
  simp only [CollatzResearch.WordTrace]
  refine ⟨101555702896569092449359151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135407603862092123265812201 101555702896569092449359151)
  ·
    refine ⟨152333554344853638674038727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101555702896569092449359151 152333554344853638674038727)
    ·
      refine ⟨228500331517280458011058091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152333554344853638674038727 228500331517280458011058091)
      ·
        refine ⟨342750497275920687016587137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228500331517280458011058091 342750497275920687016587137)
        ·
          refine ⟨257062872956940515262440353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342750497275920687016587137 257062872956940515262440353)
          ·
            refine ⟨192797154717705386446830265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257062872956940515262440353 192797154717705386446830265)
            ·
              refine ⟨144597866038279039835122699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192797154717705386446830265 144597866038279039835122699)
              ·
                refine ⟨216896799057418559752684049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144597866038279039835122699 216896799057418559752684049)
                ·
                  refine ⟨162672599293063919814513037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216896799057418559752684049 162672599293063919814513037)
                  ·
                    refine ⟨61002224734898969930442389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162672599293063919814513037 61002224734898969930442389)
                    ·
                      refine ⟨2859479284448389215489487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61002224734898969930442389 2859479284448389215489487)
                      ·
                        rfl

theorem cell23_5568816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_5568816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568816 prefixEnd_5568816 := by exact prefixLift 5568816
  have htrace : WordTrace (prefixWord ++ tailWord_5568816) baseStart_5568816 baseEnd_5568816 := by
    simpa [prefixWord, tailWord_5568816, baseEnd_5568816] using wordTrace_append hprefix tailTrace_5568816
  have hstable : (prefixWord ++ tailWord_5568816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568816).length < 2 ^ (prefixWord ++ tailWord_5568816).sum := by decide
  have hdescent : baseEnd_5568816 < baseStart_5568816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568873 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_5568873 : Nat := 118140960795 + 5568873 * 2 ^ 59
def prefixEnd_5568873 : Nat := 4983230072969 + 3 ^ 40 * 5568873 * 2
def baseEnd_5568873 : Nat := 953169517615231830825575

theorem tailTrace_5568873 : CollatzResearch.WordTrace tailWord_5568873 prefixEnd_5568873 953169517615231830825575 := by
  unfold tailWord_5568873
  simp only [CollatzResearch.WordTrace]
  refine ⟨203113484753931683633543273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135408989835954455755695515 203113484753931683633543273)
  ·
    refine ⟨152335113565448762725157455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203113484753931683633543273 152335113565448762725157455)
    ·
      refine ⟨228502670348173144087736183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152335113565448762725157455 228502670348173144087736183)
      ·
        refine ⟨342754005522259716131604275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228502670348173144087736183 342754005522259716131604275)
        ·
          refine ⟨514131008283389574197406413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342754005522259716131604275 514131008283389574197406413)
          ·
            refine ⟨192799128106271090324027405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514131008283389574197406413 192799128106271090324027405)
            ·
              refine ⟨72299673039851658871510277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192799128106271090324027405 72299673039851658871510277)
              ·
                refine ⟨13556188694972186038408177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72299673039851658871510277 13556188694972186038408177)
                ·
                  refine ⟨10167141521229139528806133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13556188694972186038408177 10167141521229139528806133)
                  ·
                    refine ⟨953169517615231830825575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10167141521229139528806133 953169517615231830825575)
                    ·
                      rfl

theorem cell23_5568873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_5568873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568873 prefixEnd_5568873 := by exact prefixLift 5568873
  have htrace : WordTrace (prefixWord ++ tailWord_5568873) baseStart_5568873 baseEnd_5568873 := by
    simpa [prefixWord, tailWord_5568873, baseEnd_5568873] using wordTrace_append hprefix tailTrace_5568873
  have hstable : (prefixWord ++ tailWord_5568873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568873).length < 2 ^ (prefixWord ++ tailWord_5568873).sum := by decide
  have hdescent : baseEnd_5568873 < baseStart_5568873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568880 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 2, 5, 2]
def baseStart_5568880 : Nat := 118140960795 + 5568880 * 2 ^ 59
def prefixEnd_5568880 : Nat := 4983230072969 + 3 ^ 40 * 5568880 * 2
def baseEnd_5568880 : Nat := 2859512147210276965089193

theorem tailTrace_5568880 : CollatzResearch.WordTrace tailWord_5568880 prefixEnd_5568880 2859512147210276965089193 := by
  unfold tailWord_5568880
  simp only [CollatzResearch.WordTrace]
  refine ⟨101556870032453161914524047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135409160043270882552698729 101556870032453161914524047)
  ·
    refine ⟨152335305048679742871786071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101556870032453161914524047 152335305048679742871786071)
    ·
      refine ⟨228502957573019614307679107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152335305048679742871786071 228502957573019614307679107)
      ·
        refine ⟨342754436359529421461518661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228502957573019614307679107 342754436359529421461518661)
        ·
          refine ⟨64266456817411766524034749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342754436359529421461518661 64266456817411766524034749)
          ·
            refine ⟨24099921306529412446513031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64266456817411766524034749 24099921306529412446513031)
            ·
              refine ⟨36149881959794118669769547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24099921306529412446513031 36149881959794118669769547)
              ·
                refine ⟨54224822939691178004654321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36149881959794118669769547 54224822939691178004654321)
                ·
                  refine ⟨40668617204768383503490741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54224822939691178004654321 40668617204768383503490741)
                  ·
                    refine ⟨3812682862947035953452257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40668617204768383503490741 3812682862947035953452257)
                    ·
                      refine ⟨2859512147210276965089193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812682862947035953452257 2859512147210276965089193)
                      ·
                        rfl

theorem cell23_5568880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 5, 2].length) (baseStart_5568880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568880 prefixEnd_5568880 := by exact prefixLift 5568880
  have htrace : WordTrace (prefixWord ++ tailWord_5568880) baseStart_5568880 baseEnd_5568880 := by
    simpa [prefixWord, tailWord_5568880, baseEnd_5568880] using wordTrace_append hprefix tailTrace_5568880
  have hstable : (prefixWord ++ tailWord_5568880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568880).length < 2 ^ (prefixWord ++ tailWord_5568880).sum := by decide
  have hdescent : baseEnd_5568880 < baseStart_5568880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5568933 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 8]
def baseStart_5568933 : Nat := 118140960795 + 5568933 * 2 ^ 59
def prefixEnd_5568933 : Nat := 4983230072969 + 3 ^ 40 * 5568933 * 2
def baseEnd_5568933 : Nat := 317726595742773917525161

theorem tailTrace_5568933 : CollatzResearch.WordTrace tailWord_5568933 prefixEnd_5568933 317726595742773917525161 := by
  unfold tailWord_5568933
  simp only [CollatzResearch.WordTrace]
  refine ⟨203115673133714313880727453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135410448755809542587151635 203115673133714313880727453)
  ·
    refine ⟨76168377425142867705272795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203115673133714313880727453 76168377425142867705272795)
    ·
      refine ⟨114252566137714301557909193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76168377425142867705272795 114252566137714301557909193)
      ·
        refine ⟨85689424603285726168431895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114252566137714301557909193 85689424603285726168431895)
        ·
          refine ⟨128534136904928589252647843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85689424603285726168431895 128534136904928589252647843)
          ·
            refine ⟨192801205357392883878971765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128534136904928589252647843 192801205357392883878971765)
            ·
              refine ⟨18075113002255582863653603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192801205357392883878971765 18075113002255582863653603)
              ·
                refine ⟨27112669503383374295480405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18075113002255582863653603 27112669503383374295480405)
                ·
                  refine ⟨317726595742773917525161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27112669503383374295480405 317726595742773917525161)
                  ·
                    rfl

theorem cell23_5568933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_5568933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5568933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5568933 prefixEnd_5568933 := by exact prefixLift 5568933
  have htrace : WordTrace (prefixWord ++ tailWord_5568933) baseStart_5568933 baseEnd_5568933 := by
    simpa [prefixWord, tailWord_5568933, baseEnd_5568933] using wordTrace_append hprefix tailTrace_5568933
  have hstable : (prefixWord ++ tailWord_5568933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5568933).length < 2 ^ (prefixWord ++ tailWord_5568933).sum := by decide
  have hdescent : baseEnd_5568933 < baseStart_5568933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5568933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569017 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 4]
def baseStart_5569017 : Nat := 118140960795 + 5569017 * 2 ^ 59
def prefixEnd_5569017 : Nat := 4983230072969 + 3 ^ 40 * 5569017 * 2
def baseEnd_5569017 : Nat := 2859582494059942929076063

theorem tailTrace_5569017 : CollatzResearch.WordTrace tailWord_5569017 prefixEnd_5569017 2859582494059942929076063 := by
  unfold tailWord_5569017
  simp only [CollatzResearch.WordTrace]
  refine ⟨203118736865409996226785305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135412491243606664151190203 203118736865409996226785305)
  ·
    refine ⟨152339052649057497170088979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203118736865409996226785305 152339052649057497170088979)
    ·
      refine ⟨228508578973586245755133469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152339052649057497170088979 228508578973586245755133469)
      ·
        refine ⟨85690717115094842158175051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228508578973586245755133469 85690717115094842158175051)
        ·
          refine ⟨128536075672642263237262577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85690717115094842158175051 128536075672642263237262577)
          ·
            refine ⟨96402056754481697427946933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128536075672642263237262577 96402056754481697427946933)
            ·
              refine ⟨9037692820732659133870025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96402056754481697427946933 9037692820732659133870025)
              ·
                refine ⟨6778269615549494350402519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9037692820732659133870025 6778269615549494350402519)
                ·
                  refine ⟨10167404423324241525603779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6778269615549494350402519 10167404423324241525603779)
                  ·
                    refine ⟨15251106634986362288405669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10167404423324241525603779 15251106634986362288405669)
                    ·
                      refine ⟨2859582494059942929076063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15251106634986362288405669 2859582494059942929076063)
                      ·
                        rfl

theorem cell23_5569017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_5569017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569017 prefixEnd_5569017 := by exact prefixLift 5569017
  have htrace : WordTrace (prefixWord ++ tailWord_5569017) baseStart_5569017 baseEnd_5569017 := by
    simpa [prefixWord, tailWord_5569017, baseEnd_5569017] using wordTrace_append hprefix tailTrace_5569017
  have hstable : (prefixWord ++ tailWord_5569017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569017).length < 2 ^ (prefixWord ++ tailWord_5569017).sum := by decide
  have hdescent : baseEnd_5569017 < baseStart_5569017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569023 : List Nat := [1, 1, 2, 2, 1, 2, 3, 11]
def baseStart_5569023 : Nat := 118140960795 + 5569023 * 2 ^ 59
def prefixEnd_5569023 : Nat := 4983230072969 + 3 ^ 40 * 5569023 * 2
def baseEnd_5569023 : Nat := 105910576849772959466705

theorem tailTrace_5569023 : CollatzResearch.WordTrace tailWord_5569023 prefixEnd_5569023 105910576849772959466705 := by
  unfold tailWord_5569023
  simp only [CollatzResearch.WordTrace]
  refine ⟨203118955703388259251503723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135412637135592172834335815 203118955703388259251503723)
  ·
    refine ⟨304678433555082388877255585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203118955703388259251503723 304678433555082388877255585)
    ·
      refine ⟨228508825166311791657941689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304678433555082388877255585 228508825166311791657941689)
      ·
        refine ⟨171381618874733843743456267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228508825166311791657941689 171381618874733843743456267)
        ·
          refine ⟨257072428312100765615184401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171381618874733843743456267 257072428312100765615184401)
          ·
            refine ⟨192804321234075574211388301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257072428312100765615184401 192804321234075574211388301)
            ·
              refine ⟨72301620462778340329270613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192804321234075574211388301 72301620462778340329270613)
              ·
                refine ⟨105910576849772959466705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 72301620462778340329270613 105910576849772959466705)
                ·
                  rfl

theorem cell23_5569023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 11].length) (baseStart_5569023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569023 prefixEnd_5569023 := by exact prefixLift 5569023
  have htrace : WordTrace (prefixWord ++ tailWord_5569023) baseStart_5569023 baseEnd_5569023 := by
    simpa [prefixWord, tailWord_5569023, baseEnd_5569023] using wordTrace_append hprefix tailTrace_5569023
  have hstable : (prefixWord ++ tailWord_5569023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569023).length < 2 ^ (prefixWord ++ tailWord_5569023).sum := by decide
  have hdescent : baseEnd_5569023 < baseStart_5569023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569034 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_5569034 : Nat := 118140960795 + 5569034 * 2 ^ 59
def prefixEnd_5569034 : Nat := 4983230072969 + 3 ^ 40 * 5569034 * 2
def baseEnd_5569034 : Nat := 2859591223231069362563485

theorem tailTrace_5569034 : CollatzResearch.WordTrace tailWord_5569034 prefixEnd_5569034 2859591223231069362563485 := by
  unfold tailWord_5569034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50779839226587102032538539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135412904604232272086769437 50779839226587102032538539)
  ·
    refine ⟨76169758839880653048807809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50779839226587102032538539 76169758839880653048807809)
    ·
      refine ⟨57127319129910489786605857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76169758839880653048807809 57127319129910489786605857)
      ·
        refine ⟨42845489347432867339954393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57127319129910489786605857 42845489347432867339954393)
        ·
          refine ⟨32134117010574650504965795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42845489347432867339954393 32134117010574650504965795)
          ·
            refine ⟨48201175515861975757448693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32134117010574650504965795 48201175515861975757448693)
            ·
              refine ⟨4518860204612060227260815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48201175515861975757448693 4518860204612060227260815)
              ·
                refine ⟨6778290306918090340891223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518860204612060227260815 6778290306918090340891223)
                ·
                  refine ⟨10167435460377135511336835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6778290306918090340891223 10167435460377135511336835)
                  ·
                    refine ⟨15251153190565703267005253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10167435460377135511336835 15251153190565703267005253)
                    ·
                      refine ⟨2859591223231069362563485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15251153190565703267005253 2859591223231069362563485)
                      ·
                        rfl

theorem cell23_5569034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_5569034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569034 prefixEnd_5569034 := by exact prefixLift 5569034
  have htrace : WordTrace (prefixWord ++ tailWord_5569034) baseStart_5569034 baseEnd_5569034 := by
    simpa [prefixWord, tailWord_5569034, baseEnd_5569034] using wordTrace_append hprefix tailTrace_5569034
  have hstable : (prefixWord ++ tailWord_5569034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569034).length < 2 ^ (prefixWord ++ tailWord_5569034).sum := by decide
  have hdescent : baseEnd_5569034 < baseStart_5569034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569064 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5569064 : Nat := 118140960795 + 5569064 * 2 ^ 59
def prefixEnd_5569064 : Nat := 4983230072969 + 3 ^ 40 * 5569064 * 2
def baseEnd_5569064 : Nat := 2859606627650704245188347

theorem tailTrace_5569064 : CollatzResearch.WordTrace tailWord_5569064 prefixEnd_5569064 2859606627650704245188347 := by
  unfold tailWord_5569064
  simp only [CollatzResearch.WordTrace]
  refine ⟨101560225548119861626873123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135413634064159815502497497 101560225548119861626873123)
  ·
    refine ⟨152340338322179792440309685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101560225548119861626873123 152340338322179792440309685)
    ·
      refine ⟨14281906717704355541279033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152340338322179792440309685 14281906717704355541279033)
      ·
        refine ⟨10711430038278266655959275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14281906717704355541279033 10711430038278266655959275)
        ·
          refine ⟨16067145057417399983938913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10711430038278266655959275 16067145057417399983938913)
          ·
            refine ⟨12050358793063049987954185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16067145057417399983938913 12050358793063049987954185)
            ·
              refine ⟨9037769094797287490965639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12050358793063049987954185 9037769094797287490965639)
              ·
                refine ⟨13556653642195931236448459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9037769094797287490965639 13556653642195931236448459)
                ·
                  refine ⟨20334980463293896854672689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13556653642195931236448459 20334980463293896854672689)
                  ·
                    refine ⟨15251235347470422641004517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20334980463293896854672689 15251235347470422641004517)
                    ·
                      refine ⟨2859606627650704245188347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15251235347470422641004517 2859606627650704245188347)
                      ·
                        rfl

theorem cell23_5569064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5569064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569064 prefixEnd_5569064 := by exact prefixLift 5569064
  have htrace : WordTrace (prefixWord ++ tailWord_5569064) baseStart_5569064 baseEnd_5569064 := by
    simpa [prefixWord, tailWord_5569064, baseEnd_5569064] using wordTrace_append hprefix tailTrace_5569064
  have hstable : (prefixWord ++ tailWord_5569064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569064).length < 2 ^ (prefixWord ++ tailWord_5569064).sum := by decide
  have hdescent : baseEnd_5569064 < baseStart_5569064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569080 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_5569080 : Nat := 118140960795 + 5569080 * 2 ^ 59
def prefixEnd_5569080 : Nat := 4983230072969 + 3 ^ 40 * 5569080 * 2
def baseEnd_5569080 : Nat := 2859614843341176182588273

theorem tailTrace_5569080 : CollatzResearch.WordTrace tailWord_5569080 prefixEnd_5569080 2859614843341176182588273 := by
  unfold tailWord_5569080
  simp only [CollatzResearch.WordTrace]
  refine ⟨101560517332090878993164347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135414023109454505324219129 101560517332090878993164347)
  ·
    refine ⟨152340775998136318489746521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101560517332090878993164347 152340775998136318489746521)
    ·
      refine ⟨114255581998602238867309891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152340775998136318489746521 114255581998602238867309891)
      ·
        refine ⟨171383372997903358300964837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114255581998602238867309891 171383372997903358300964837)
        ·
          refine ⟨32134382437106879681430907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171383372997903358300964837 32134382437106879681430907)
          ·
            refine ⟨48201573655660319522146361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32134382437106879681430907 48201573655660319522146361)
            ·
              refine ⟨36151180241745239641609771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48201573655660319522146361 36151180241745239641609771)
              ·
                refine ⟨54226770362617859462414657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36151180241745239641609771 54226770362617859462414657)
                ·
                  refine ⟨40670077771963394596810993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54226770362617859462414657 40670077771963394596810993)
                  ·
                    refine ⟨30502558328972545947608245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40670077771963394596810993 30502558328972545947608245)
                    ·
                      refine ⟨2859614843341176182588273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30502558328972545947608245 2859614843341176182588273)
                      ·
                        rfl

theorem cell23_5569080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_5569080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569080 prefixEnd_5569080 := by exact prefixLift 5569080
  have htrace : WordTrace (prefixWord ++ tailWord_5569080) baseStart_5569080 baseEnd_5569080 := by
    simpa [prefixWord, tailWord_5569080, baseEnd_5569080] using wordTrace_append hprefix tailTrace_5569080
  have hstable : (prefixWord ++ tailWord_5569080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569080).length < 2 ^ (prefixWord ++ tailWord_5569080).sum := by decide
  have hdescent : baseEnd_5569080 < baseStart_5569080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569100 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_5569100 : Nat := 118140960795 + 5569100 * 2 ^ 59
def prefixEnd_5569100 : Nat := 4983230072969 + 3 ^ 40 * 5569100 * 2
def baseEnd_5569100 : Nat := 953208370984755368112727

theorem tailTrace_5569100 : CollatzResearch.WordTrace tailWord_5569100 prefixEnd_5569100 953208370984755368112727 := by
  unfold tailWord_5569100
  simp only [CollatzResearch.WordTrace]
  refine ⟨101560882062054650701028377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135414509416072867601371169 101560882062054650701028377)
  ·
    refine ⟨76170661546540988025771283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101560882062054650701028377 76170661546540988025771283)
    ·
      refine ⟨114255992319811482038656925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76170661546540988025771283 114255992319811482038656925)
      ·
        refine ⟨42845997119929305764496347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114255992319811482038656925 42845997119929305764496347)
        ·
          refine ⟨64268995679893958646744521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42845997119929305764496347 64268995679893958646744521)
          ·
            refine ⟨48201746759920468985058391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64268995679893958646744521 48201746759920468985058391)
            ·
              refine ⟨72302620139880703477587587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48201746759920468985058391 72302620139880703477587587)
              ·
                refine ⟨108453930209821055216381381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72302620139880703477587587 108453930209821055216381381)
                ·
                  refine ⟨20335111914341447853071509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108453930209821055216381381 20335111914341447853071509)
                  ·
                    refine ⟨953208370984755368112727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20335111914341447853071509 953208370984755368112727)
                    ·
                      rfl

theorem cell23_5569100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_5569100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569100 prefixEnd_5569100 := by exact prefixLift 5569100
  have htrace : WordTrace (prefixWord ++ tailWord_5569100) baseStart_5569100 baseEnd_5569100 := by
    simpa [prefixWord, tailWord_5569100, baseEnd_5569100] using wordTrace_append hprefix tailTrace_5569100
  have hstable : (prefixWord ++ tailWord_5569100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569100).length < 2 ^ (prefixWord ++ tailWord_5569100).sum := by decide
  have hdescent : baseEnd_5569100 < baseStart_5569100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569101 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_5569101 : Nat := 118140960795 + 5569101 * 2 ^ 59
def prefixEnd_5569101 : Nat := 4983230072969 + 3 ^ 40 * 5569101 * 2
def baseEnd_5569101 : Nat := 2859625626434920600425677

theorem tailTrace_5569101 : CollatzResearch.WordTrace tailWord_5569101 prefixEnd_5569101 2859625626434920600425677 := by
  unfold tailWord_5569101
  simp only [CollatzResearch.WordTrace]
  refine ⟨203121800597105678572843157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135414533731403785715228771 203121800597105678572843157)
  ·
    refine ⟨9521334402989328683102023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203121800597105678572843157 9521334402989328683102023)
    ·
      refine ⟨14282001604483993024653035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9521334402989328683102023 14282001604483993024653035)
      ·
        refine ⟨21423002406725989536979553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14282001604483993024653035 21423002406725989536979553)
        ·
          refine ⟨16067251805044492152734665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21423002406725989536979553 16067251805044492152734665)
          ·
            refine ⟨12050438853783369114550999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16067251805044492152734665 12050438853783369114550999)
            ·
              refine ⟨18075658280675053671826499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12050438853783369114550999 18075658280675053671826499)
              ·
                refine ⟨27113487421012580507739749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18075658280675053671826499 27113487421012580507739749)
                ·
                  refine ⟨5083778891439858845201203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27113487421012580507739749 5083778891439858845201203)
                  ·
                    refine ⟨7625668337159788267801805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5083778891439858845201203 7625668337159788267801805)
                    ·
                      refine ⟨2859625626434920600425677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7625668337159788267801805 2859625626434920600425677)
                      ·
                        rfl

theorem cell23_5569101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_5569101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569101 prefixEnd_5569101 := by exact prefixLift 5569101
  have htrace : WordTrace (prefixWord ++ tailWord_5569101) baseStart_5569101 baseEnd_5569101 := by
    simpa [prefixWord, tailWord_5569101, baseEnd_5569101] using wordTrace_append hprefix tailTrace_5569101
  have hstable : (prefixWord ++ tailWord_5569101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569101).length < 2 ^ (prefixWord ++ tailWord_5569101).sum := by decide
  have hdescent : baseEnd_5569101 < baseStart_5569101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569128 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5569128 : Nat := 118140960795 + 5569128 * 2 ^ 59
def prefixEnd_5569128 : Nat := 4983230072969 + 3 ^ 40 * 5569128 * 2
def baseEnd_5569128 : Nat := 2859639490412591994788053

theorem tailTrace_5569128 : CollatzResearch.WordTrace tailWord_5569128 prefixEnd_5569128 2859639490412591994788053 := by
  unfold tailWord_5569128
  simp only [CollatzResearch.WordTrace]
  refine ⟨101561392684003931092038019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135415190245338574789384025 101561392684003931092038019)
  ·
    refine ⟨152342089026005896638057029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101561392684003931092038019 152342089026005896638057029)
    ·
      refine ⟨28564141692376105619635693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152342089026005896638057029 28564141692376105619635693)
      ·
        refine ⟨10711553134641039607363385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28564141692376105619635693 10711553134641039607363385)
        ·
          refine ⟨8033664850980779705522539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10711553134641039607363385 8033664850980779705522539)
          ·
            refine ⟨12050497276471169558283809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8033664850980779705522539 12050497276471169558283809)
            ·
              refine ⟨9037872957353377168712857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12050497276471169558283809 9037872957353377168712857)
              ·
                refine ⟨6778404718015032876534643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9037872957353377168712857 6778404718015032876534643)
                ·
                  refine ⟨10167607077022549314801965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6778404718015032876534643 10167607077022549314801965)
                  ·
                    refine ⟨3812852653883455993050737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10167607077022549314801965 3812852653883455993050737)
                    ·
                      refine ⟨2859639490412591994788053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812852653883455993050737 2859639490412591994788053)
                      ·
                        rfl

theorem cell23_5569128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5569128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569128 prefixEnd_5569128 := by exact prefixLift 5569128
  have htrace : WordTrace (prefixWord ++ tailWord_5569128) baseStart_5569128 baseEnd_5569128 := by
    simpa [prefixWord, tailWord_5569128, baseEnd_5569128] using wordTrace_append hprefix tailTrace_5569128
  have hstable : (prefixWord ++ tailWord_5569128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569128).length < 2 ^ (prefixWord ++ tailWord_5569128).sum := by decide
  have hdescent : baseEnd_5569128 < baseStart_5569128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569147 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 5]
def baseStart_5569147 : Nat := 118140960795 + 5569147 * 2 ^ 59
def prefixEnd_5569147 : Nat := 4983230072969 + 3 ^ 40 * 5569147 * 2
def baseEnd_5569147 : Nat := 317738805171669713383385

theorem tailTrace_5569147 : CollatzResearch.WordTrace tailWord_5569147 prefixEnd_5569147 317738805171669713383385 := by
  unfold tailWord_5569147
  simp only [CollatzResearch.WordTrace]
  refine ⟨203123478354939028429017695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135415652236626018952678463 203123478354939028429017695)
  ·
    refine ⟨304685217532408542643526543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203123478354939028429017695 304685217532408542643526543)
    ·
      refine ⟨457027826298612813965289815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304685217532408542643526543 457027826298612813965289815)
      ·
        refine ⟨685541739447919220947934723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457027826298612813965289815 685541739447919220947934723)
        ·
          refine ⟨1028312609171878831421902085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685541739447919220947934723 1028312609171878831421902085)
          ·
            refine ⟨192808614219727280891606641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1028312609171878831421902085 192808614219727280891606641)
            ·
              refine ⟨144606460664795460668704981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192808614219727280891606641 144606460664795460668704981)
              ·
                refine ⟨3389213921831143609422773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144606460664795460668704981 3389213921831143609422773)
                ·
                  refine ⟨317738805171669713383385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3389213921831143609422773 317738805171669713383385)
                  ·
                    rfl

theorem cell23_5569147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 5].length) (baseStart_5569147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569147 prefixEnd_5569147 := by exact prefixLift 5569147
  have htrace : WordTrace (prefixWord ++ tailWord_5569147) baseStart_5569147 baseEnd_5569147 := by
    simpa [prefixWord, tailWord_5569147, baseEnd_5569147] using wordTrace_append hprefix tailTrace_5569147
  have hstable : (prefixWord ++ tailWord_5569147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569147).length < 2 ^ (prefixWord ++ tailWord_5569147).sum := by decide
  have hdescent : baseEnd_5569147 < baseStart_5569147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569167 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 7, 2]
def baseStart_5569167 : Nat := 118140960795 + 5569167 * 2 ^ 59
def prefixEnd_5569167 : Nat := 4983230072969 + 3 ^ 40 * 5569167 * 2
def baseEnd_5569167 : Nat := 2859659516158117342200373

theorem tailTrace_5569167 : CollatzResearch.WordTrace tailWord_5569167 prefixEnd_5569167 2859659516158117342200373 := by
  unfold tailWord_5569167
  simp only [CollatzResearch.WordTrace]
  refine ⟨203124207814866571844745755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135416138543244381229830503 203124207814866571844745755)
  ·
    refine ⟨304686311722299857767118633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203124207814866571844745755 304686311722299857767118633)
    ·
      refine ⟨228514733791724893325338975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304686311722299857767118633 228514733791724893325338975)
      ·
        refine ⟨342772100687587339988008463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228514733791724893325338975 342772100687587339988008463)
        ·
          refine ⟨514158151031381009982012695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342772100687587339988008463 514158151031381009982012695)
          ·
            refine ⟨771237226547071514973019043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514158151031381009982012695 771237226547071514973019043)
            ·
              refine ⟨1156855839820607272459528565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771237226547071514973019043 1156855839820607272459528565)
              ·
                refine ⟨108455234983181931793080803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1156855839820607272459528565 108455234983181931793080803)
                ·
                  refine ⟨162682852474772897689621205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108455234983181931793080803 162682852474772897689621205)
                  ·
                    refine ⟨3812879354877489789600497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162682852474772897689621205 3812879354877489789600497)
                    ·
                      refine ⟨2859659516158117342200373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812879354877489789600497 2859659516158117342200373)
                      ·
                        rfl

theorem cell23_5569167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7, 2].length) (baseStart_5569167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569167 prefixEnd_5569167 := by exact prefixLift 5569167
  have htrace : WordTrace (prefixWord ++ tailWord_5569167) baseStart_5569167 baseEnd_5569167 := by
    simpa [prefixWord, tailWord_5569167, baseEnd_5569167] using wordTrace_append hprefix tailTrace_5569167
  have hstable : (prefixWord ++ tailWord_5569167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569167).length < 2 ^ (prefixWord ++ tailWord_5569167).sum := by decide
  have hdescent : baseEnd_5569167 < baseStart_5569167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569214 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5569214 : Nat := 118140960795 + 5569214 * 2 ^ 59
def prefixEnd_5569214 : Nat := 4983230072969 + 3 ^ 40 * 5569214 * 2
def baseEnd_5569214 : Nat := 2859683649748878658312657

theorem tailTrace_5569214 : CollatzResearch.WordTrace tailWord_5569214 prefixEnd_5569214 2859683649748878658312657 := by
  unfold tailWord_5569214
  simp only [CollatzResearch.WordTrace]
  refine ⟨25390740255712037358963337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135417281363797532581137797 25390740255712037358963337)
  ·
    refine ⟨19043055191784028019222503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25390740255712037358963337 19043055191784028019222503)
    ·
      refine ⟨28564582787676042028833755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19043055191784028019222503 28564582787676042028833755)
      ·
        refine ⟨42846874181514063043250633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28564582787676042028833755 42846874181514063043250633)
        ·
          refine ⟨32135155636135547282437975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42846874181514063043250633 32135155636135547282437975)
          ·
            refine ⟨48202733454203320923656963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32135155636135547282437975 48202733454203320923656963)
            ·
              refine ⟨72304100181304981385485445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48202733454203320923656963 72304100181304981385485445)
              ·
                refine ⟨13557018783994684009778521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72304100181304981385485445 13557018783994684009778521)
                ·
                  refine ⟨10167764087996013007333891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13557018783994684009778521 10167764087996013007333891)
                  ·
                    refine ⟨15251646131994019511000837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10167764087996013007333891 15251646131994019511000837)
                    ·
                      refine ⟨2859683649748878658312657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15251646131994019511000837 2859683649748878658312657)
                      ·
                        rfl

theorem cell23_5569214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5569214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569214 prefixEnd_5569214 := by exact prefixLift 5569214
  have htrace : WordTrace (prefixWord ++ tailWord_5569214) baseStart_5569214 baseEnd_5569214 := by
    simpa [prefixWord, tailWord_5569214, baseEnd_5569214] using wordTrace_append hprefix tailTrace_5569214
  have hstable : (prefixWord ++ tailWord_5569214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569214).length < 2 ^ (prefixWord ++ tailWord_5569214).sum := by decide
  have hdescent : baseEnd_5569214 < baseStart_5569214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569251 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5569251 : Nat := 118140960795 + 5569251 * 2 ^ 59
def prefixEnd_5569251 : Nat := 4983230072969 + 3 ^ 40 * 5569251 * 2
def baseEnd_5569251 : Nat := 2859702648533095013549987

theorem tailTrace_5569251 : CollatzResearch.WordTrace tailWord_5569251 prefixEnd_5569251 2859702648533095013549987 := by
  unfold tailWord_5569251
  simp only [CollatzResearch.WordTrace]
  refine ⟨203127271546562254190803607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135418181031041502793869071 203127271546562254190803607)
  ·
    refine ⟨304690907319843381286205411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203127271546562254190803607 304690907319843381286205411)
    ·
      refine ⟨457036360979765071929308117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304690907319843381286205411 457036360979765071929308117)
      ·
        refine ⟨10711789710463243873343159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 457036360979765071929308117 10711789710463243873343159)
        ·
          refine ⟨16067684565694865810014739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10711789710463243873343159 16067684565694865810014739)
          ·
            refine ⟨24101526848542298715022109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16067684565694865810014739 24101526848542298715022109)
            ·
              refine ⟨9038072568203362018133291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24101526848542298715022109 9038072568203362018133291)
              ·
                refine ⟨13557108852305043027199937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9038072568203362018133291 13557108852305043027199937)
                ·
                  refine ⟨10167831639228782270399953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13557108852305043027199937 10167831639228782270399953)
                  ·
                    refine ⟨7625873729421586702799965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10167831639228782270399953 7625873729421586702799965)
                    ·
                      refine ⟨2859702648533095013549987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7625873729421586702799965 2859702648533095013549987)
                      ·
                        rfl

theorem cell23_5569251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5569251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569251 prefixEnd_5569251 := by exact prefixLift 5569251
  have htrace : WordTrace (prefixWord ++ tailWord_5569251) baseStart_5569251 baseEnd_5569251 := by
    simpa [prefixWord, tailWord_5569251, baseEnd_5569251] using wordTrace_append hprefix tailTrace_5569251
  have hstable : (prefixWord ++ tailWord_5569251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569251).length < 2 ^ (prefixWord ++ tailWord_5569251).sum := by decide
  have hdescent : baseEnd_5569251 < baseStart_5569251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569264 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3]
def baseStart_5569264 : Nat := 118140960795 + 5569264 * 2 ^ 59
def prefixEnd_5569264 : Nat := 4983230072969 + 3 ^ 40 * 5569264 * 2
def baseEnd_5569264 : Nat := 2859709323781603462687427

theorem tailTrace_5569264 : CollatzResearch.WordTrace tailWord_5569264 prefixEnd_5569264 2859709323781603462687427 := by
  unfold tailWord_5569264
  simp only [CollatzResearch.WordTrace]
  refine ⟨101563872847757578705513423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135418497130343438274017897 101563872847757578705513423)
  ·
    refine ⟨152345809271636368058270135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101563872847757578705513423 152345809271636368058270135)
    ·
      refine ⟨228518713907454552087405203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152345809271636368058270135 228518713907454552087405203)
      ·
        refine ⟨342778070861181828131107805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228518713907454552087405203 342778070861181828131107805)
        ·
          refine ⟨128541776572943185549165427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342778070861181828131107805 128541776572943185549165427)
          ·
            refine ⟨192812664859414778323748141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128541776572943185549165427 192812664859414778323748141)
            ·
              refine ⟨72304749322280541871405553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192812664859414778323748141 72304749322280541871405553)
              ·
                refine ⟨54228561991710406403554165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72304749322280541871405553 54228561991710406403554165)
                ·
                  refine ⟨5083927686722850600333203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54228561991710406403554165 5083927686722850600333203)
                  ·
                    refine ⟨7625891530084275900499805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5083927686722850600333203 7625891530084275900499805)
                    ·
                      refine ⟨2859709323781603462687427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7625891530084275900499805 2859709323781603462687427)
                      ·
                        rfl

theorem cell23_5569264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_5569264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569264 prefixEnd_5569264 := by exact prefixLift 5569264
  have htrace : WordTrace (prefixWord ++ tailWord_5569264) baseStart_5569264 baseEnd_5569264 := by
    simpa [prefixWord, tailWord_5569264, baseEnd_5569264] using wordTrace_append hprefix tailTrace_5569264
  have hstable : (prefixWord ++ tailWord_5569264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569264).length < 2 ^ (prefixWord ++ tailWord_5569264).sum := by decide
  have hdescent : baseEnd_5569264 < baseStart_5569264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569304 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 8, 2]
def baseStart_5569304 : Nat := 118140960795 + 5569304 * 2 ^ 59
def prefixEnd_5569304 : Nat := 4983230072969 + 3 ^ 40 * 5569304 * 2
def baseEnd_5569304 : Nat := 2859729863007783306187243

theorem tailTrace_5569304 : CollatzResearch.WordTrace tailWord_5569304 prefixEnd_5569304 2859729863007783306187243 := by
  unfold tailWord_5569304
  simp only [CollatzResearch.WordTrace]
  refine ⟨101564602307685122121241483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135419469743580162828321977 101564602307685122121241483)
  ·
    refine ⟨152346903461527683181862225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101564602307685122121241483 152346903461527683181862225)
    ·
      refine ⟨114260177596145762386396669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152346903461527683181862225 114260177596145762386396669)
      ·
        refine ⟨42847566598554660894898751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114260177596145762386396669 42847566598554660894898751)
        ·
          refine ⟨64271349897831991342348127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42847566598554660894898751 64271349897831991342348127)
          ·
            refine ⟨96407024846747987013522191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64271349897831991342348127 96407024846747987013522191)
            ·
              refine ⟨144610537270121980520283287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96407024846747987013522191 144610537270121980520283287)
              ·
                refine ⟨216915805905182970780424931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144610537270121980520283287 216915805905182970780424931)
                ·
                  refine ⟨325373708857774456170637397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216915805905182970780424931 325373708857774456170637397)
                  ·
                    refine ⟨3812973150677044408249657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 325373708857774456170637397 3812973150677044408249657)
                    ·
                      refine ⟨2859729863007783306187243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3812973150677044408249657 2859729863007783306187243)
                      ·
                        rfl

theorem cell23_5569304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_5569304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569304 prefixEnd_5569304 := by exact prefixLift 5569304
  have htrace : WordTrace (prefixWord ++ tailWord_5569304) baseStart_5569304 baseEnd_5569304 := by
    simpa [prefixWord, tailWord_5569304, baseEnd_5569304] using wordTrace_append hprefix tailTrace_5569304
  have hstable : (prefixWord ++ tailWord_5569304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569304).length < 2 ^ (prefixWord ++ tailWord_5569304).sum := by decide
  have hdescent : baseEnd_5569304 < baseStart_5569304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569324 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_5569324 : Nat := 118140960795 + 5569324 * 2 ^ 59
def prefixEnd_5569324 : Nat := 4983230072969 + 3 ^ 40 * 5569324 * 2
def baseEnd_5569324 : Nat := 2859740132620873227937151

theorem tailTrace_5569324 : CollatzResearch.WordTrace tailWord_5569324 prefixEnd_5569324 2859740132620873227937151 := by
  unfold tailWord_5569324
  simp only [CollatzResearch.WordTrace]
  refine ⟨101564967037648893829105513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135419956050198525105474017 101564967037648893829105513)
  ·
    refine ⟨76173725278236670371829135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101564967037648893829105513 76173725278236670371829135)
    ·
      refine ⟨114260587917355005557743703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76173725278236670371829135 114260587917355005557743703)
      ·
        refine ⟨171390881876032508336615555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114260587917355005557743703 171390881876032508336615555)
        ·
          refine ⟨257086322814048762504923333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171390881876032508336615555 257086322814048762504923333)
          ·
            refine ⟨48203685527634142969673125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257086322814048762504923333 48203685527634142969673125)
            ·
              refine ⟨9038191036431401806813711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48203685527634142969673125 9038191036431401806813711)
              ·
                refine ⟨13557286554647102710220567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9038191036431401806813711 13557286554647102710220567)
                ·
                  refine ⟨20335929831970654065330851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13557286554647102710220567 20335929831970654065330851)
                  ·
                    refine ⟨30503894747955981097996277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20335929831970654065330851 30503894747955981097996277)
                    ·
                      refine ⟨2859740132620873227937151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30503894747955981097996277 2859740132620873227937151)
                      ·
                        rfl

theorem cell23_5569324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_5569324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569324 prefixEnd_5569324 := by exact prefixLift 5569324
  have htrace : WordTrace (prefixWord ++ tailWord_5569324) baseStart_5569324 baseEnd_5569324 := by
    simpa [prefixWord, tailWord_5569324, baseEnd_5569324] using wordTrace_append hprefix tailTrace_5569324
  have hstable : (prefixWord ++ tailWord_5569324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569324).length < 2 ^ (prefixWord ++ tailWord_5569324).sum := by decide
  have hdescent : baseEnd_5569324 < baseStart_5569324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569332 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_5569332 : Nat := 118140960795 + 5569332 * 2 ^ 59
def prefixEnd_5569332 : Nat := 4983230072969 + 3 ^ 40 * 5569332 * 2
def baseEnd_5569332 : Nat := 2859744240466109196637115

theorem tailTrace_5569332 : CollatzResearch.WordTrace tailWord_5569332 prefixEnd_5569332 2859744240466109196637115 := by
  unfold tailWord_5569332
  simp only [CollatzResearch.WordTrace]
  refine ⟨101565112929634402512251125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135420150572845870016334833 101565112929634402512251125)
  ·
    refine ⟨9521729337153225235523543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101565112929634402512251125 9521729337153225235523543)
    ·
      refine ⟨14282594005729837853285315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9521729337153225235523543 14282594005729837853285315)
      ·
        refine ⟨21423891008594756779927973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14282594005729837853285315 21423891008594756779927973)
        ·
          refine ⟨4016979564111516896236495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21423891008594756779927973 4016979564111516896236495)
          ·
            refine ⟨6025469346167275344354743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016979564111516896236495 6025469346167275344354743)
            ·
              refine ⟨9038204019250913016532115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6025469346167275344354743 9038204019250913016532115)
              ·
                refine ⟨13557306028876369524798173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9038204019250913016532115 13557306028876369524798173)
                ·
                  refine ⟨5083989760828638571799315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13557306028876369524798173 5083989760828638571799315)
                  ·
                    refine ⟨7625984641242957857698973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5083989760828638571799315 7625984641242957857698973)
                    ·
                      refine ⟨2859744240466109196637115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7625984641242957857698973 2859744240466109196637115)
                      ·
                        rfl

theorem cell23_5569332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_5569332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569332 prefixEnd_5569332 := by exact prefixLift 5569332
  have htrace : WordTrace (prefixWord ++ tailWord_5569332) baseStart_5569332 baseEnd_5569332 := by
    simpa [prefixWord, tailWord_5569332, baseEnd_5569332] using wordTrace_append hprefix tailTrace_5569332
  have hstable : (prefixWord ++ tailWord_5569332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569332).length < 2 ^ (prefixWord ++ tailWord_5569332).sum := by decide
  have hdescent : baseEnd_5569332 < baseStart_5569332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569347 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_5569347 : Nat := 118140960795 + 5569347 * 2 ^ 59
def prefixEnd_5569347 : Nat := 4983230072969 + 3 ^ 40 * 5569347 * 2
def baseEnd_5569347 : Nat := 2859751942675926637949545

theorem tailTrace_5569347 : CollatzResearch.WordTrace tailWord_5569347 prefixEnd_5569347 2859751942675926637949545 := by
  unfold tailWord_5569347
  simp only [CollatzResearch.WordTrace]
  refine ⟨203130772954214462586298295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135420515302809641724198863 203130772954214462586298295)
  ·
    refine ⟨304696159431321693879447443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203130772954214462586298295 304696159431321693879447443)
    ·
      refine ⟨457044239146982540819171165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304696159431321693879447443 457044239146982540819171165)
      ·
        refine ⟨171391589680118452807189187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457044239146982540819171165 171391589680118452807189187)
        ·
          refine ⟨257087384520177679210783781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171391589680118452807189187 257087384520177679210783781)
          ·
            refine ⟨48203884597533314852021959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257087384520177679210783781 48203884597533314852021959)
            ·
              refine ⟨72305826896299972278032939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48203884597533314852021959 72305826896299972278032939)
              ·
                refine ⟨108458740344449958417049409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72305826896299972278032939 108458740344449958417049409)
                ·
                  refine ⟨81344055258337468812787057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108458740344449958417049409 81344055258337468812787057)
                  ·
                    refine ⟨61008041443753101609590293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81344055258337468812787057 61008041443753101609590293)
                    ·
                      refine ⟨2859751942675926637949545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61008041443753101609590293 2859751942675926637949545)
                      ·
                        rfl

theorem cell23_5569347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_5569347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569347 prefixEnd_5569347 := by exact prefixLift 5569347
  have htrace : WordTrace (prefixWord ++ tailWord_5569347) baseStart_5569347 baseEnd_5569347 := by
    simpa [prefixWord, tailWord_5569347, baseEnd_5569347] using wordTrace_append hprefix tailTrace_5569347
  have hstable : (prefixWord ++ tailWord_5569347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569347).length < 2 ^ (prefixWord ++ tailWord_5569347).sum := by decide
  have hdescent : baseEnd_5569347 < baseStart_5569347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569388 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_5569388 : Nat := 118140960795 + 5569388 * 2 ^ 59
def prefixEnd_5569388 : Nat := 4983230072969 + 3 ^ 40 * 5569388 * 2
def baseEnd_5569388 : Nat := 2859772995382760977536857

theorem tailTrace_5569388 : CollatzResearch.WordTrace tailWord_5569388 prefixEnd_5569388 2859772995382760977536857 := by
  unfold tailWord_5569388
  simp only [CollatzResearch.WordTrace]
  refine ⟨101566134173532963294270409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135421512231377284392360545 101566134173532963294270409)
  ·
    refine ⟨76174600630149722470702807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101566134173532963294270409 76174600630149722470702807)
    ·
      refine ⟨114261900945224583706054211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76174600630149722470702807 114261900945224583706054211)
      ·
        refine ⟨171392851417836875559081317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114261900945224583706054211 171392851417836875559081317)
        ·
          refine ⟨32136159640844414167327747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171392851417836875559081317 32136159640844414167327747)
          ·
            refine ⟨48204239461266621250991621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32136159640844414167327747 48204239461266621250991621)
            ·
              refine ⟨9038294898987491484560929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48204239461266621250991621 9038294898987491484560929)
              ·
                refine ⟨6778721174240618613420697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9038294898987491484560929 6778721174240618613420697)
                ·
                  refine ⟨5084040880680463960065523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6778721174240618613420697 5084040880680463960065523)
                  ·
                    refine ⟨7626061321020695940098285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5084040880680463960065523 7626061321020695940098285)
                    ·
                      refine ⟨2859772995382760977536857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626061321020695940098285 2859772995382760977536857)
                      ·
                        rfl

theorem cell23_5569388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_5569388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569388 prefixEnd_5569388 := by exact prefixLift 5569388
  have htrace : WordTrace (prefixWord ++ tailWord_5569388) baseStart_5569388 baseEnd_5569388 := by
    simpa [prefixWord, tailWord_5569388, baseEnd_5569388] using wordTrace_append hprefix tailTrace_5569388
  have hstable : (prefixWord ++ tailWord_5569388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569388).length < 2 ^ (prefixWord ++ tailWord_5569388).sum := by decide
  have hdescent : baseEnd_5569388 < baseStart_5569388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569394 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5569394 : Nat := 118140960795 + 5569394 * 2 ^ 59
def prefixEnd_5569394 : Nat := 4983230072969 + 3 ^ 40 * 5569394 * 2
def baseEnd_5569394 : Nat := 2859776076266687954061829

theorem tailTrace_5569394 : CollatzResearch.WordTrace tailWord_5569394 prefixEnd_5569394 2859776076266687954061829 := by
  unfold tailWord_5569394
  simp only [CollatzResearch.WordTrace]
  refine ⟨50783121796261047403314809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135421658123362793075506157 50783121796261047403314809)
  ·
    refine ⟨38087341347195785552486107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50783121796261047403314809 38087341347195785552486107)
    ·
      refine ⟨57131012020793678328729161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38087341347195785552486107 57131012020793678328729161)
      ·
        refine ⟨42848259015595258746546871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57131012020793678328729161 42848259015595258746546871)
        ·
          refine ⟨64272388523392888119820307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42848259015595258746546871 64272388523392888119820307)
          ·
            refine ⟨96408582785089332179730461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64272388523392888119820307 96408582785089332179730461)
            ·
              refine ⟨36153218544408499567398923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96408582785089332179730461 36153218544408499567398923)
              ·
                refine ⟨54229827816612749351098385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36153218544408499567398923 54229827816612749351098385)
                ·
                  refine ⟨40672370862459562013323789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54229827816612749351098385 40672370862459562013323789)
                  ·
                    refine ⟨15252139073422335754996421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40672370862459562013323789 15252139073422335754996421)
                    ·
                      refine ⟨2859776076266687954061829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15252139073422335754996421 2859776076266687954061829)
                      ·
                        rfl

theorem cell23_5569394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5569394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569394 prefixEnd_5569394 := by exact prefixLift 5569394
  have htrace : WordTrace (prefixWord ++ tailWord_5569394) baseStart_5569394 baseEnd_5569394 := by
    simpa [prefixWord, tailWord_5569394, baseEnd_5569394] using wordTrace_append hprefix tailTrace_5569394
  have hstable : (prefixWord ++ tailWord_5569394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569394).length < 2 ^ (prefixWord ++ tailWord_5569394).sum := by decide
  have hdescent : baseEnd_5569394 < baseStart_5569394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569428 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5569428 : Nat := 118140960795 + 5569428 * 2 ^ 59
def prefixEnd_5569428 : Nat := 4983230072969 + 3 ^ 40 * 5569428 * 2
def baseEnd_5569428 : Nat := 2859793534608940821036673

theorem tailTrace_5569428 : CollatzResearch.WordTrace tailWord_5569428 prefixEnd_5569428 2859793534608940821036673 := by
  unfold tailWord_5569428
  simp only [CollatzResearch.WordTrace]
  refine ⟨101566863633460506709998469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135422484844614008946664625 101566863633460506709998469)
  ·
    refine ⟨19043786931273845008124713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101566863633460506709998469 19043786931273845008124713)
    ·
      refine ⟨14282840198455383756093535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19043786931273845008124713 14282840198455383756093535)
      ·
        refine ⟨21424260297683075634140303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14282840198455383756093535 21424260297683075634140303)
        ·
          refine ⟨32136390446524613451210455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21424260297683075634140303 32136390446524613451210455)
          ·
            refine ⟨48204585669786920176815683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32136390446524613451210455 48204585669786920176815683)
            ·
              refine ⟨72306878504680380265223525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48204585669786920176815683 72306878504680380265223525)
              ·
                refine ⟨13557539719627571299729411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72306878504680380265223525 13557539719627571299729411)
                ·
                  refine ⟨20336309579441356949594117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13557539719627571299729411 20336309579441356949594117)
                  ·
                    refine ⟨3813058046145254428048897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20336309579441356949594117 3813058046145254428048897)
                    ·
                      refine ⟨2859793534608940821036673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813058046145254428048897 2859793534608940821036673)
                      ·
                        rfl

theorem cell23_5569428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5569428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569428 prefixEnd_5569428 := by exact prefixLift 5569428
  have htrace : WordTrace (prefixWord ++ tailWord_5569428) baseStart_5569428 baseEnd_5569428 := by
    simpa [prefixWord, tailWord_5569428, baseEnd_5569428] using wordTrace_append hprefix tailTrace_5569428
  have hstable : (prefixWord ++ tailWord_5569428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569428).length < 2 ^ (prefixWord ++ tailWord_5569428).sum := by decide
  have hdescent : baseEnd_5569428 < baseStart_5569428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569441 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5569441 : Nat := 118140960795 + 5569441 * 2 ^ 59
def prefixEnd_5569441 : Nat := 4983230072969 + 3 ^ 40 * 5569441 * 2
def baseEnd_5569441 : Nat := 2859800209857449270174113

theorem tailTrace_5569441 : CollatzResearch.WordTrace tailWord_5569441 prefixEnd_5569441 2859800209857449270174113 := by
  unfold tailWord_5569441
  simp only [CollatzResearch.WordTrace]
  refine ⟨203134201415873916640220177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135422800943915944426813451 203134201415873916640220177)
  ·
    refine ⟨152350651061905437480165133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203134201415873916640220177 152350651061905437480165133)
    ·
      refine ⟨57131494148214539055061925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152350651061905437480165133 57131494148214539055061925)
      ·
        refine ⟨10712155152790226072824111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57131494148214539055061925 10712155152790226072824111)
        ·
          refine ⟨16068232729185339109236167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10712155152790226072824111 16068232729185339109236167)
          ·
            refine ⟨24102349093778008663854251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16068232729185339109236167 24102349093778008663854251)
            ·
              refine ⟨36153523640667012995781377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24102349093778008663854251 36153523640667012995781377)
              ·
                refine ⟨27115142730500259746836033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36153523640667012995781377 27115142730500259746836033)
                ·
                  refine ⟨20336357047875194810127025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27115142730500259746836033 20336357047875194810127025)
                  ·
                    refine ⟨15252267785906396107595269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20336357047875194810127025 15252267785906396107595269)
                    ·
                      refine ⟨2859800209857449270174113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15252267785906396107595269 2859800209857449270174113)
                      ·
                        rfl

theorem cell23_5569441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5569441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569441 prefixEnd_5569441 := by exact prefixLift 5569441
  have htrace : WordTrace (prefixWord ++ tailWord_5569441) baseStart_5569441 baseEnd_5569441 := by
    simpa [prefixWord, tailWord_5569441, baseEnd_5569441] using wordTrace_append hprefix tailTrace_5569441
  have hstable : (prefixWord ++ tailWord_5569441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569441).length < 2 ^ (prefixWord ++ tailWord_5569441).sum := by decide
  have hdescent : baseEnd_5569441 < baseStart_5569441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569461 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_5569461 : Nat := 118140960795 + 5569461 * 2 ^ 59
def prefixEnd_5569461 : Nat := 4983230072969 + 3 ^ 40 * 5569461 * 2
def baseEnd_5569461 : Nat := 2859810479470539191924021

theorem tailTrace_5569461 : CollatzResearch.WordTrace tailWord_5569461 prefixEnd_5569461 2859810479470539191924021 := by
  unfold tailWord_5569461
  simp only [CollatzResearch.WordTrace]
  refine ⟨203134930875801460055948237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135423287250534306703965491 203134930875801460055948237)
  ·
    refine ⟨76175599078425547520980589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203134930875801460055948237 76175599078425547520980589)
    ·
      refine ⟨28565849654409580320367721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76175599078425547520980589 28565849654409580320367721)
      ·
        refine ⟨21424387240807185240275791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28565849654409580320367721 21424387240807185240275791)
        ·
          refine ⟨32136580861210777860413687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21424387240807185240275791 32136580861210777860413687)
          ·
            refine ⟨48204871291816166790620531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32136580861210777860413687 48204871291816166790620531)
            ·
              refine ⟨72307306937724250185930797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48204871291816166790620531 72307306937724250185930797)
              ·
                refine ⟨27115240101646593819724049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72307306937724250185930797 27115240101646593819724049)
                ·
                  refine ⟨20336430076234945364793037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27115240101646593819724049 20336430076234945364793037)
                  ·
                    refine ⟨7626161278588104511797389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20336430076234945364793037 7626161278588104511797389)
                    ·
                      refine ⟨2859810479470539191924021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626161278588104511797389 2859810479470539191924021)
                      ·
                        rfl

theorem cell23_5569461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_5569461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569461 prefixEnd_5569461 := by exact prefixLift 5569461
  have htrace : WordTrace (prefixWord ++ tailWord_5569461) baseStart_5569461 baseEnd_5569461 := by
    simpa [prefixWord, tailWord_5569461, baseEnd_5569461] using wordTrace_append hprefix tailTrace_5569461
  have hstable : (prefixWord ++ tailWord_5569461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569461).length < 2 ^ (prefixWord ++ tailWord_5569461).sum := by decide
  have hdescent : baseEnd_5569461 < baseStart_5569461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569464 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_5569464 : Nat := 118140960795 + 5569464 * 2 ^ 59
def prefixEnd_5569464 : Nat := 4983230072969 + 3 ^ 40 * 5569464 * 2
def baseEnd_5569464 : Nat := 953270673304167560062169

theorem tailTrace_5569464 : CollatzResearch.WordTrace tailWord_5569464 prefixEnd_5569464 953270673304167560062169 := by
  unfold tailWord_5569464
  simp only [CollatzResearch.WordTrace]
  refine ⟨101567520147395295784153723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135423360196527061045538297 101567520147395295784153723)
  ·
    refine ⟨152351280221092943676230585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101567520147395295784153723 152351280221092943676230585)
    ·
      refine ⟨114263460165819707757172939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152351280221092943676230585 114263460165819707757172939)
      ·
        refine ⟨171395190248729561635759409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114263460165819707757172939 171395190248729561635759409)
        ·
          refine ⟨128546392686547171226819557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171395190248729561635759409 128546392686547171226819557)
          ·
            refine ⟨24102448628727594605028667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128546392686547171226819557 24102448628727594605028667)
            ·
              refine ⟨36153672943091391907543001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24102448628727594605028667 36153672943091391907543001)
              ·
                refine ⟨27115254707318543930657251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36153672943091391907543001 27115254707318543930657251)
                ·
                  refine ⟨40672882060977815895985877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27115254707318543930657251 40672882060977815895985877)
                  ·
                    refine ⟨953270673304167560062169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40672882060977815895985877 953270673304167560062169)
                    ·
                      rfl

theorem cell23_5569464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_5569464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569464 prefixEnd_5569464 := by exact prefixLift 5569464
  have htrace : WordTrace (prefixWord ++ tailWord_5569464) baseStart_5569464 baseEnd_5569464 := by
    simpa [prefixWord, tailWord_5569464, baseEnd_5569464] using wordTrace_append hprefix tailTrace_5569464
  have hstable : (prefixWord ++ tailWord_5569464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569464).length < 2 ^ (prefixWord ++ tailWord_5569464).sum := by decide
  have hdescent : baseEnd_5569464 < baseStart_5569464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569571 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 3, 5]
def baseStart_5569571 : Nat := 118140960795 + 5569571 * 2 ^ 59
def prefixEnd_5569571 : Nat := 4983230072969 + 3 ^ 40 * 5569571 * 2
def baseEnd_5569571 : Nat := 953288987447511253849505

theorem tailTrace_5569571 : CollatzResearch.WordTrace tailWord_5569571 prefixEnd_5569571 953288987447511253849505 := by
  unfold tailWord_5569571
  simp only [CollatzResearch.WordTrace]
  refine ⟨203138942905402948842452567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135425961936935299228301711 203138942905402948842452567)
  ·
    refine ⟨304708414358104423263678851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203138942905402948842452567 304708414358104423263678851)
    ·
      refine ⟨457062621537156634895518277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304708414358104423263678851 457062621537156634895518277)
      ·
        refine ⟨85699241538216869042909677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 457062621537156634895518277 85699241538216869042909677)
        ·
          refine ⟨32137215576831325891091129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85699241538216869042909677 32137215576831325891091129)
          ·
            refine ⟨24102911682623494418318347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32137215576831325891091129 24102911682623494418318347)
            ·
              refine ⟨36154367523935241627477521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24102911682623494418318347 36154367523935241627477521)
              ·
                refine ⟨27115775642951431220608141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36154367523935241627477521 27115775642951431220608141)
                ·
                  refine ⟨10168415866106786707728053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27115775642951431220608141 10168415866106786707728053)
                  ·
                    refine ⟨953288987447511253849505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10168415866106786707728053 953288987447511253849505)
                    ·
                      rfl

theorem cell23_5569571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 5].length) (baseStart_5569571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569571 prefixEnd_5569571 := by exact prefixLift 5569571
  have htrace : WordTrace (prefixWord ++ tailWord_5569571) baseStart_5569571 baseEnd_5569571 := by
    simpa [prefixWord, tailWord_5569571, baseEnd_5569571] using wordTrace_append hprefix tailTrace_5569571
  have hstable : (prefixWord ++ tailWord_5569571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569571).length < 2 ^ (prefixWord ++ tailWord_5569571).sum := by decide
  have hdescent : baseEnd_5569571 < baseStart_5569571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569608 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_5569608 : Nat := 118140960795 + 5569608 * 2 ^ 59
def prefixEnd_5569608 : Nat := 4983230072969 + 3 ^ 40 * 5569608 * 2
def baseEnd_5569608 : Nat := 2859885961126750116785845

theorem tailTrace_5569608 : CollatzResearch.WordTrace tailWord_5569608 prefixEnd_5569608 2859885961126750116785845 := by
  unfold tailWord_5569608
  simp only [CollatzResearch.WordTrace]
  refine ⟨101570146203134452080774739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135426861604179269441032985 101570146203134452080774739)
  ·
    refine ⟨152355219304701678121162109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101570146203134452080774739 152355219304701678121162109)
    ·
      refine ⟨57133207239263129295435791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152355219304701678121162109 57133207239263129295435791)
      ·
        refine ⟨85699810858894693943153687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57133207239263129295435791 85699810858894693943153687)
        ·
          refine ⟨128549716288342040914730531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85699810858894693943153687 128549716288342040914730531)
          ·
            refine ⟨192824574432513061372095797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128549716288342040914730531 192824574432513061372095797)
            ·
              refine ⟨18077303853048099503633981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192824574432513061372095797 18077303853048099503633981)
              ·
                refine ⟨6778988944893037313862743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18077303853048099503633981 6778988944893037313862743)
                ·
                  refine ⟨10168483417339555970794115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6778988944893037313862743 10168483417339555970794115)
                  ·
                    refine ⟨15252725126009333956191173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10168483417339555970794115 15252725126009333956191173)
                    ·
                      refine ⟨2859885961126750116785845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15252725126009333956191173 2859885961126750116785845)
                      ·
                        rfl

theorem cell23_5569608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_5569608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569608 prefixEnd_5569608 := by exact prefixLift 5569608
  have htrace : WordTrace (prefixWord ++ tailWord_5569608) baseStart_5569608 baseEnd_5569608 := by
    simpa [prefixWord, tailWord_5569608, baseEnd_5569608] using wordTrace_append hprefix tailTrace_5569608
  have hstable : (prefixWord ++ tailWord_5569608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569608).length < 2 ^ (prefixWord ++ tailWord_5569608).sum := by decide
  have hdescent : baseEnd_5569608 < baseStart_5569608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569621 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_5569621 : Nat := 118140960795 + 5569621 * 2 ^ 59
def prefixEnd_5569621 : Nat := 4983230072969 + 3 ^ 40 * 5569621 * 2
def baseEnd_5569621 : Nat := 2859892636375258565923285

theorem tailTrace_5569621 : CollatzResearch.WordTrace tailWord_5569621 prefixEnd_5569621 2859892636375258565923285 := by
  unfold tailWord_5569621
  simp only [CollatzResearch.WordTrace]
  refine ⟨203140766555221807381772717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135427177703481204921181811 203140766555221807381772717)
  ·
    refine ⟨76177787458208177768164769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203140766555221807381772717 76177787458208177768164769)
    ·
      refine ⟨57133340593656133326123577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76177787458208177768164769 57133340593656133326123577)
      ·
        refine ⟨42850005445242099994592683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57133340593656133326123577 42850005445242099994592683)
        ·
          refine ⟨64275008167863149991889025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42850005445242099994592683 64275008167863149991889025)
          ·
            refine ⟨48206256125897362493916769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64275008167863149991889025 48206256125897362493916769)
            ·
              refine ⟨36154692094423021870437577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48206256125897362493916769 36154692094423021870437577)
              ·
                refine ⟨27116019070817266402828183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36154692094423021870437577 27116019070817266402828183)
                ·
                  refine ⟨40674028606225899604242275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27116019070817266402828183 40674028606225899604242275)
                  ·
                    refine ⟨61011042909338849406363413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40674028606225899604242275 61011042909338849406363413)
                    ·
                      refine ⟨2859892636375258565923285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61011042909338849406363413 2859892636375258565923285)
                      ·
                        rfl

theorem cell23_5569621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_5569621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569621 prefixEnd_5569621 := by exact prefixLift 5569621
  have htrace : WordTrace (prefixWord ++ tailWord_5569621) baseStart_5569621 baseEnd_5569621 := by
    simpa [prefixWord, tailWord_5569621, baseEnd_5569621] using wordTrace_append hprefix tailTrace_5569621
  have hstable : (prefixWord ++ tailWord_5569621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569621).length < 2 ^ (prefixWord ++ tailWord_5569621).sum := by decide
  have hdescent : baseEnd_5569621 < baseStart_5569621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569628 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5569628 : Nat := 118140960795 + 5569628 * 2 ^ 59
def prefixEnd_5569628 : Nat := 4983230072969 + 3 ^ 40 * 5569628 * 2
def baseEnd_5569628 : Nat := 2859896230739840038535753

theorem tailTrace_5569628 : CollatzResearch.WordTrace tailWord_5569628 prefixEnd_5569628 2859896230739840038535753 := by
  unfold tailWord_5569628
  simp only [CollatzResearch.WordTrace]
  refine ⟨101570510933098223788638769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135427347910797631718185025 101570510933098223788638769)
  ·
    refine ⟨76177883199823667841479077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101570510933098223788638769 76177883199823667841479077)
    ·
      refine ⟨14283353099966937720277327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76177883199823667841479077 14283353099966937720277327)
      ·
        refine ⟨21425029649950406580415991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14283353099966937720277327 21425029649950406580415991)
        ·
          refine ⟨32137544474925609870623987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21425029649950406580415991 32137544474925609870623987)
          ·
            refine ⟨48206316712388414805935981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32137544474925609870623987 48206316712388414805935981)
            ·
              refine ⟨18077368767145655552225993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48206316712388414805935981 18077368767145655552225993)
              ·
                refine ⟨13558026575359241664169495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18077368767145655552225993 13558026575359241664169495)
                ·
                  refine ⟨20337039863038862496254243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13558026575359241664169495 20337039863038862496254243)
                  ·
                    refine ⟨30505559794558293744381365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20337039863038862496254243 30505559794558293744381365)
                    ·
                      refine ⟨2859896230739840038535753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30505559794558293744381365 2859896230739840038535753)
                      ·
                        rfl

theorem cell23_5569628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5569628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569628 prefixEnd_5569628 := by exact prefixLift 5569628
  have htrace : WordTrace (prefixWord ++ tailWord_5569628) baseStart_5569628 baseEnd_5569628 := by
    simpa [prefixWord, tailWord_5569628, baseEnd_5569628] using wordTrace_append hprefix tailTrace_5569628
  have hstable : (prefixWord ++ tailWord_5569628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569628).length < 2 ^ (prefixWord ++ tailWord_5569628).sum := by decide
  have hdescent : baseEnd_5569628 < baseStart_5569628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569642 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_5569642 : Nat := 118140960795 + 5569642 * 2 ^ 59
def prefixEnd_5569642 : Nat := 4983230072969 + 3 ^ 40 * 5569642 * 2
def baseEnd_5569642 : Nat := 2859903419469002983760689

theorem tailTrace_5569642 : CollatzResearch.WordTrace tailWord_5569642 prefixEnd_5569642 2859903419469002983760689 := by
  unfold tailWord_5569642
  simp only [CollatzResearch.WordTrace]
  refine ⟨50785383122036431992071795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135427688325430485312191453 50785383122036431992071795)
  ·
    refine ⟨76178074683054647988107693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50785383122036431992071795 76178074683054647988107693)
    ·
      refine ⟨28566778006145492995540385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76178074683054647988107693 28566778006145492995540385)
      ·
        refine ⟨21425083504609119746655289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28566778006145492995540385 21425083504609119746655289)
        ·
          refine ⟨16068812628456839809991467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21425083504609119746655289 16068812628456839809991467)
          ·
            refine ⟨24103218942685259714987201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16068812628456839809991467 24103218942685259714987201)
            ·
              refine ⟨18077414207013944786240401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24103218942685259714987201 18077414207013944786240401)
              ·
                refine ⟨13558060655260458589680301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18077414207013944786240401 13558060655260458589680301)
                ·
                  refine ⟨5084272745722671971130113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13558060655260458589680301 5084272745722671971130113)
                  ·
                    refine ⟨3813204559292003978347585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5084272745722671971130113 3813204559292003978347585)
                    ·
                      refine ⟨2859903419469002983760689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3813204559292003978347585 2859903419469002983760689)
                      ·
                        rfl

theorem cell23_5569642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_5569642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569642 prefixEnd_5569642 := by exact prefixLift 5569642
  have htrace : WordTrace (prefixWord ++ tailWord_5569642) baseStart_5569642 baseEnd_5569642 := by
    simpa [prefixWord, tailWord_5569642, baseEnd_5569642] using wordTrace_append hprefix tailTrace_5569642
  have hstable : (prefixWord ++ tailWord_5569642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569642).length < 2 ^ (prefixWord ++ tailWord_5569642).sum := by decide
  have hdescent : baseEnd_5569642 < baseStart_5569642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569645 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_5569645 : Nat := 118140960795 + 5569645 * 2 ^ 59
def prefixEnd_5569645 : Nat := 4983230072969 + 3 ^ 40 * 5569645 * 2
def baseEnd_5569645 : Nat := 2859904959910966472023175

theorem tailTrace_5569645 : CollatzResearch.WordTrace tailWord_5569645 prefixEnd_5569645 2859904959910966472023175 := by
  unfold tailWord_5569645
  simp only [CollatzResearch.WordTrace]
  refine ⟨203141641907134859480646389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135427761271423239653764259 203141641907134859480646389)
  ·
    refine ⟨19044528928793893076310599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203141641907134859480646389 19044528928793893076310599)
    ·
      refine ⟨28566793393190839614465899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19044528928793893076310599 28566793393190839614465899)
      ·
        refine ⟨42850190089786259421698849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28566793393190839614465899 42850190089786259421698849)
        ·
          refine ⟨32137642567339694566274137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42850190089786259421698849 32137642567339694566274137)
          ·
            refine ⟨24103231925504770924705603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32137642567339694566274137 24103231925504770924705603)
            ·
              refine ⟨36154847888257156387058405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24103231925504770924705603 36154847888257156387058405)
              ·
                refine ⟨6779033979048216822573451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36154847888257156387058405 6779033979048216822573451)
                ·
                  refine ⟨10168550968572325233860177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6779033979048216822573451 10168550968572325233860177)
                  ·
                    refine ⟨7626413226429243925395133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10168550968572325233860177 7626413226429243925395133)
                    ·
                      refine ⟨2859904959910966472023175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626413226429243925395133 2859904959910966472023175)
                      ·
                        rfl

theorem cell23_5569645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_5569645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569645 prefixEnd_5569645 := by exact prefixLift 5569645
  have htrace : WordTrace (prefixWord ++ tailWord_5569645) baseStart_5569645 baseEnd_5569645 := by
    simpa [prefixWord, tailWord_5569645, baseEnd_5569645] using wordTrace_append hprefix tailTrace_5569645
  have hstable : (prefixWord ++ tailWord_5569645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569645).length < 2 ^ (prefixWord ++ tailWord_5569645).sum := by decide
  have hdescent : baseEnd_5569645 < baseStart_5569645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569653 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5569653 : Nat := 118140960795 + 5569653 * 2 ^ 59
def prefixEnd_5569653 : Nat := 4983230072969 + 3 ^ 40 * 5569653 * 2
def baseEnd_5569653 : Nat := 2859909067756202440723139

theorem tailTrace_5569653 : CollatzResearch.WordTrace tailWord_5569653 prefixEnd_5569653 2859909067756202440723139 := by
  unfold tailWord_5569653
  simp only [CollatzResearch.WordTrace]
  refine ⟨203141933691105876846937613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135427955794070584564625075 203141933691105876846937613)
  ·
    refine ⟨76178225134164703817601605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203141933691105876846937613 76178225134164703817601605)
    ·
      refine ⟨14283417212655881965800301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76178225134164703817601605 14283417212655881965800301)
      ·
        refine ⟨5356281454745955737175113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14283417212655881965800301 5356281454745955737175113)
        ·
          refine ⟨4017211091059466802881335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5356281454745955737175113 4017211091059466802881335)
          ·
            refine ⟨6025816636589200204322003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017211091059466802881335 6025816636589200204322003)
            ·
              refine ⟨9038724954883800306483005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6025816636589200204322003 9038724954883800306483005)
              ·
                refine ⟨3389521858081425114931127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9038724954883800306483005 3389521858081425114931127)
                ·
                  refine ⟨5084282787122137672396691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389521858081425114931127 5084282787122137672396691)
                  ·
                    refine ⟨7626424180683206508595037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5084282787122137672396691 7626424180683206508595037)
                    ·
                      refine ⟨2859909067756202440723139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7626424180683206508595037 2859909067756202440723139)
                      ·
                        rfl

theorem cell23_5569653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5569653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569653 prefixEnd_5569653 := by exact prefixLift 5569653
  have htrace : WordTrace (prefixWord ++ tailWord_5569653) baseStart_5569653 baseEnd_5569653 := by
    simpa [prefixWord, tailWord_5569653, baseEnd_5569653] using wordTrace_append hprefix tailTrace_5569653
  have hstable : (prefixWord ++ tailWord_5569653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569653).length < 2 ^ (prefixWord ++ tailWord_5569653).sum := by decide
  have hdescent : baseEnd_5569653 < baseStart_5569653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5569671 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5569671 : Nat := 118140960795 + 5569671 * 2 ^ 59
def prefixEnd_5569671 : Nat := 4983230072969 + 3 ^ 40 * 5569671 * 2
def baseEnd_5569671 : Nat := 2859918310407983370298055

theorem tailTrace_5569671 : CollatzResearch.WordTrace tailWord_5569671 prefixEnd_5569671 2859918310407983370298055 := by
  unfold tailWord_5569671
  simp only [CollatzResearch.WordTrace]
  refine ⟨203142590205040665921092867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135428393470027110614061911 203142590205040665921092867)
  ·
    refine ⟨304713885307560998881639301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203142590205040665921092867 304713885307560998881639301)
    ·
      refine ⟨57133853495167687290307369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304713885307560998881639301 57133853495167687290307369)
      ·
        refine ⟨42850390121375765467730527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57133853495167687290307369 42850390121375765467730527)
        ·
          refine ⟨64275585182063648201595791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42850390121375765467730527 64275585182063648201595791)
          ·
            refine ⟨96413377773095472302393687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64275585182063648201595791 96413377773095472302393687)
            ·
              refine ⟨144620066659643208453590531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96413377773095472302393687 144620066659643208453590531)
              ·
                refine ⟨216930099989464812680385797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144620066659643208453590531 216930099989464812680385797)
                ·
                  refine ⟨40674393748024652377572337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216930099989464812680385797 40674393748024652377572337)
                  ·
                    refine ⟨30505795311018489283179253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40674393748024652377572337 30505795311018489283179253)
                    ·
                      refine ⟨2859918310407983370298055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30505795311018489283179253 2859918310407983370298055)
                      ·
                        rfl

theorem cell23_5569671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5569671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5569671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5569671 prefixEnd_5569671 := by exact prefixLift 5569671
  have htrace : WordTrace (prefixWord ++ tailWord_5569671) baseStart_5569671 baseEnd_5569671 := by
    simpa [prefixWord, tailWord_5569671, baseEnd_5569671] using wordTrace_append hprefix tailTrace_5569671
  have hstable : (prefixWord ++ tailWord_5569671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5569671).length < 2 ^ (prefixWord ++ tailWord_5569671).sum := by decide
  have hdescent : baseEnd_5569671 < baseStart_5569671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5569671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
