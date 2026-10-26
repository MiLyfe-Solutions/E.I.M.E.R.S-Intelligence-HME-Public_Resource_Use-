import V185TrunkScan20Chunk036

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_225930 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_225930 : Nat := 118140960795 + 225930 * 2 ^ 59
def prefixEnd_225930 : Nat := 4983230072969 + 3 ^ 40 * 225930 * 2
def baseEnd_225930 : Nat := 103120608240361139143087

theorem tailTrace_225930 : CollatzResearch.WordTrace tailWord_225930 prefixEnd_225930 103120608240361139143087 := by
  unfold tailWord_225930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060086017875417654284811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5493562714334447078092829 2060086017875417654284811)
  ·
    refine ⟨3090129026813126481427217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060086017875417654284811 3090129026813126481427217)
    ·
      refine ⟨2317596770109844861070413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3090129026813126481427217 2317596770109844861070413)
      ·
        refine ⟨869098788791191822901405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2317596770109844861070413 869098788791191822901405)
        ·
          refine ⟨325912045796696933588027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 869098788791191822901405 325912045796696933588027)
          ·
            refine ⟨488868068695045400382041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325912045796696933588027 488868068695045400382041)
            ·
              refine ⟨366651051521284050286531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488868068695045400382041 366651051521284050286531)
              ·
                refine ⟨549976577281926075429797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366651051521284050286531 549976577281926075429797)
                ·
                  refine ⟨103120608240361139143087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549976577281926075429797 103120608240361139143087)
                  ·
                    rfl

theorem cell20_225930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_225930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225930 prefixEnd_225930 := by exact prefixLift 225930
  have htrace : WordTrace (prefixWord ++ tailWord_225930) baseStart_225930 baseEnd_225930 := by
    simpa [prefixWord, tailWord_225930, baseEnd_225930] using wordTrace_append hprefix tailTrace_225930
  have hstable : (prefixWord ++ tailWord_225930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225930).length < 2 ^ (prefixWord ++ tailWord_225930).sum := by decide
  have hdescent : baseEnd_225930 < baseStart_225930 := by decide
  rcases family_descends (prefixWord ++ tailWord_225930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225940 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_225940 : Nat := 118140960795 + 225940 * 2 ^ 59
def prefixEnd_225940 : Nat := 4983230072969 + 3 ^ 40 * 225940 * 2
def baseEnd_225940 : Nat := 103125172512845548809713

theorem tailTrace_225940 : CollatzResearch.WordTrace tailWord_225940 prefixEnd_225940 103125172512845548809713 := by
  unfold tailWord_225940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4120354400732721162501637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5493805867643628216668849 4120354400732721162501637)
  ·
    refine ⟨772566450137385217969057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4120354400732721162501637 772566450137385217969057)
    ·
      refine ⟨579424837603038913476793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 772566450137385217969057 579424837603038913476793)
      ·
        refine ⟨434568628202279185107595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579424837603038913476793 434568628202279185107595)
        ·
          refine ⟨651852942303418777661393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434568628202279185107595 651852942303418777661393)
          ·
            refine ⟨488889706727564083246045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651852942303418777661393 488889706727564083246045)
            ·
              refine ⟨183333640022836531217267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488889706727564083246045 183333640022836531217267)
              ·
                refine ⟨275000460034254796825901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183333640022836531217267 275000460034254796825901)
                ·
                  refine ⟨103125172512845548809713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275000460034254796825901 103125172512845548809713)
                  ·
                    rfl

theorem cell20_225940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_225940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225940 prefixEnd_225940 := by exact prefixLift 225940
  have htrace : WordTrace (prefixWord ++ tailWord_225940) baseStart_225940 baseEnd_225940 := by
    simpa [prefixWord, tailWord_225940, baseEnd_225940] using wordTrace_append hprefix tailTrace_225940
  have hstable : (prefixWord ++ tailWord_225940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225940).length < 2 ^ (prefixWord ++ tailWord_225940).sum := by decide
  have hdescent : baseEnd_225940 < baseStart_225940 := by decide
  rcases family_descends (prefixWord ++ tailWord_225940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225975 : List Nat := [1, 1, 3, 1, 7, 1, 6]
def baseStart_225975 : Nat := 118140960795 + 225975 * 2 ^ 59
def prefixEnd_225975 : Nat := 4983230072969 + 3 ^ 40 * 225975 * 2
def baseEnd_225975 : Nat := 11460127496282331404767

theorem tailTrace_225975 : CollatzResearch.WordTrace tailWord_225975 prefixEnd_225975 11460127496282331404767 := by
  unfold tailWord_225975
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241985356338643302527379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5494656904225762201684919 8241985356338643302527379)
  ·
    refine ⟨12362978034507964953791069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241985356338643302527379 12362978034507964953791069)
    ·
      refine ⟨4636116762940486857671651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12362978034507964953791069 4636116762940486857671651)
      ·
        refine ⟨6954175144410730286507477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636116762940486857671651 6954175144410730286507477)
        ·
          refine ⟨162988479947126491090019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6954175144410730286507477 162988479947126491090019)
          ·
            refine ⟨244482719920689736635029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162988479947126491090019 244482719920689736635029)
            ·
              refine ⟨11460127496282331404767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244482719920689736635029 11460127496282331404767)
              ·
                rfl

theorem cell20_225975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 6].length) (baseStart_225975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225975 prefixEnd_225975 := by exact prefixLift 225975
  have htrace : WordTrace (prefixWord ++ tailWord_225975) baseStart_225975 baseEnd_225975 := by
    simpa [prefixWord, tailWord_225975, baseEnd_225975] using wordTrace_append hprefix tailTrace_225975
  have hstable : (prefixWord ++ tailWord_225975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225975).length < 2 ^ (prefixWord ++ tailWord_225975).sum := by decide
  have hdescent : baseEnd_225975 < baseStart_225975 := by decide
  rcases family_descends (prefixWord ++ tailWord_225975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225982 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_225982 : Nat := 118140960795 + 225982 * 2 ^ 59
def prefixEnd_225982 : Nat := 4983230072969 + 3 ^ 40 * 225982 * 2
def baseEnd_225982 : Nat := 103144342457280069409541

theorem tailTrace_225982 : CollatzResearch.WordTrace tailWord_225982 prefixEnd_225982 103144342457280069409541 := by
  unfold tailWord_225982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030280083414160437254025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5494827111542188998688133 1030280083414160437254025)
  ·
    refine ⟨772710062560620327940519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1030280083414160437254025 772710062560620327940519)
    ·
      refine ⟨1159065093840930491910779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 772710062560620327940519 1159065093840930491910779)
      ·
        refine ⟨1738597640761395737866169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159065093840930491910779 1738597640761395737866169)
        ·
          refine ⟨1303948230571046803399627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1738597640761395737866169 1303948230571046803399627)
          ·
            refine ⟨1955922345856570205099441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303948230571046803399627 1955922345856570205099441)
            ·
              refine ⟨1466941759392427653824581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955922345856570205099441 1466941759392427653824581)
              ·
                refine ⟨275051579886080185092109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1466941759392427653824581 275051579886080185092109)
                ·
                  refine ⟨103144342457280069409541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275051579886080185092109 103144342457280069409541)
                  ·
                    rfl

theorem cell20_225982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_225982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225982 prefixEnd_225982 := by exact prefixLift 225982
  have htrace : WordTrace (prefixWord ++ tailWord_225982) baseStart_225982 baseEnd_225982 := by
    simpa [prefixWord, tailWord_225982, baseEnd_225982] using wordTrace_append hprefix tailTrace_225982
  have hstable : (prefixWord ++ tailWord_225982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225982).length < 2 ^ (prefixWord ++ tailWord_225982).sum := by decide
  have hdescent : baseEnd_225982 < baseStart_225982 := by decide
  rcases family_descends (prefixWord ++ tailWord_225982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225996 : List Nat := [2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_225996 : Nat := 118140960795 + 225996 * 2 ^ 59
def prefixEnd_225996 : Nat := 4983230072969 + 3 ^ 40 * 225996 * 2
def baseEnd_225996 : Nat := 34383577479586080980939

theorem tailTrace_225996 : CollatzResearch.WordTrace tailWord_225996 prefixEnd_225996 34383577479586080980939 := by
  unfold tailWord_225996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121375644631281944520921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5495167526175042592694561 4121375644631281944520921)
  ·
    refine ⟨3091031733473461458390691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4121375644631281944520921 3091031733473461458390691)
    ·
      refine ⟨4636547600210192187586037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091031733473461458390691 4636547600210192187586037)
      ·
        refine ⟨434676337519705517586191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4636547600210192187586037 434676337519705517586191)
        ·
          refine ⟨652014506279558276379287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434676337519705517586191 652014506279558276379287)
          ·
            refine ⟨978021759419337414568931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652014506279558276379287 978021759419337414568931)
            ·
              refine ⟨1467032639129006121853397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978021759419337414568931 1467032639129006121853397)
              ·
                refine ⟨34383577479586080980939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1467032639129006121853397 34383577479586080980939)
                ·
                  rfl

theorem cell20_225996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_225996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225996 prefixEnd_225996 := by exact prefixLift 225996
  have htrace : WordTrace (prefixWord ++ tailWord_225996) baseStart_225996 baseEnd_225996 := by
    simpa [prefixWord, tailWord_225996, baseEnd_225996] using wordTrace_append hprefix tailTrace_225996
  have hstable : (prefixWord ++ tailWord_225996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225996).length < 2 ^ (prefixWord ++ tailWord_225996).sum := by decide
  have hdescent : baseEnd_225996 < baseStart_225996 := by decide
  rcases family_descends (prefixWord ++ tailWord_225996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226010 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_226010 : Nat := 118140960795 + 226010 * 2 ^ 59
def prefixEnd_226010 : Nat := 4983230072969 + 3 ^ 40 * 226010 * 2
def baseEnd_226010 : Nat := 103157122420236416476093

theorem tailTrace_226010 : CollatzResearch.WordTrace tailWord_226010 prefixEnd_226010 103157122420236416476093 := by
  unfold tailWord_226010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060815477802961070012871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5495507940807896186700989 2060815477802961070012871)
  ·
    refine ⟨3091223216704441605019307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060815477802961070012871 3091223216704441605019307)
    ·
      refine ⟨4636834825056662407528961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091223216704441605019307 4636834825056662407528961)
      ·
        refine ⟨3477626118792496805646721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4636834825056662407528961 3477626118792496805646721)
        ·
          refine ⟨2608219589094372604235041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3477626118792496805646721 2608219589094372604235041)
          ·
            refine ⟨1956164691820779453176281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608219589094372604235041 1956164691820779453176281)
            ·
              refine ⟨1467123518865584589882211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956164691820779453176281 1467123518865584589882211)
              ·
                refine ⟨2200685278298376884823317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467123518865584589882211 2200685278298376884823317)
                ·
                  refine ⟨103157122420236416476093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2200685278298376884823317 103157122420236416476093)
                  ·
                    rfl

theorem cell20_226010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_226010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226010 prefixEnd_226010 := by exact prefixLift 226010
  have htrace : WordTrace (prefixWord ++ tailWord_226010) baseStart_226010 baseEnd_226010 := by
    simpa [prefixWord, tailWord_226010, baseEnd_226010] using wordTrace_append hprefix tailTrace_226010
  have hstable : (prefixWord ++ tailWord_226010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226010).length < 2 ^ (prefixWord ++ tailWord_226010).sum := by decide
  have hdescent : baseEnd_226010 < baseStart_226010 := by decide
  rcases family_descends (prefixWord ++ tailWord_226010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226027 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 2]
def baseStart_226027 : Nat := 118140960795 + 226027 * 2 ^ 59
def prefixEnd_226027 : Nat := 4983230072969 + 3 ^ 40 * 226027 * 2
def baseEnd_226027 : Nat := 103164881683459912909357

theorem tailTrace_226027 : CollatzResearch.WordTrace tailWord_226027 prefixEnd_226027 103164881683459912909357 := by
  unfold tailWord_226027
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243881952150256183420335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5495921301433504122280223 8243881952150256183420335)
  ·
    refine ⟨12365822928225384275130503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8243881952150256183420335 12365822928225384275130503)
    ·
      refine ⟨18548734392338076412695755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12365822928225384275130503 18548734392338076412695755)
      ·
        refine ⟨27823101588507114619043633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18548734392338076412695755 27823101588507114619043633)
        ·
          refine ⟨20867326191380335964282725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27823101588507114619043633 20867326191380335964282725)
          ·
            refine ⟨3912623660883812993303011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20867326191380335964282725 3912623660883812993303011)
            ·
              refine ⟨5868935491325719489954517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3912623660883812993303011 5868935491325719489954517)
              ·
                refine ⟨137553175577946550545809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5868935491325719489954517 137553175577946550545809)
                ·
                  refine ⟨103164881683459912909357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137553175577946550545809 103164881683459912909357)
                  ·
                    rfl

theorem cell20_226027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 2].length) (baseStart_226027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226027 prefixEnd_226027 := by exact prefixLift 226027
  have htrace : WordTrace (prefixWord ++ tailWord_226027) baseStart_226027 baseEnd_226027 := by
    simpa [prefixWord, tailWord_226027, baseEnd_226027] using wordTrace_append hprefix tailTrace_226027
  have hstable : (prefixWord ++ tailWord_226027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226027).length < 2 ^ (prefixWord ++ tailWord_226027).sum := by decide
  have hdescent : baseEnd_226027 < baseStart_226027 := by decide
  rcases family_descends (prefixWord ++ tailWord_226027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226036 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 2]
def baseStart_226036 : Nat := 118140960795 + 226036 * 2 ^ 59
def prefixEnd_226036 : Nat := 4983230072969 + 3 ^ 40 * 226036 * 2
def baseEnd_226036 : Nat := 103168989528695881609321

theorem tailTrace_226036 : CollatzResearch.WordTrace tailWord_226036 prefixEnd_226036 103168989528695881609321 := by
  unfold tailWord_226036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122105104558825360248981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5496140139411767146998641 4122105104558825360248981)
  ·
    refine ⟨193223676776194938761671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4122105104558825360248981 193223676776194938761671)
    ·
      refine ⟨289835515164292408142507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193223676776194938761671 289835515164292408142507)
      ·
        refine ⟨434753272746438612213761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289835515164292408142507 434753272746438612213761)
        ·
          refine ⟨326064954559828959160321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434753272746438612213761 326064954559828959160321)
          ·
            refine ⟨244548715919871719370241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326064954559828959160321 244548715919871719370241)
            ·
              refine ⟨183411536939903789527681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244548715919871719370241 183411536939903789527681)
              ·
                refine ⟨137558652704927842145761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183411536939903789527681 137558652704927842145761)
                ·
                  refine ⟨103168989528695881609321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137558652704927842145761 103168989528695881609321)
                  ·
                    rfl

theorem cell20_226036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_226036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226036 prefixEnd_226036 := by exact prefixLift 226036
  have htrace : WordTrace (prefixWord ++ tailWord_226036) baseStart_226036 baseEnd_226036 := by
    simpa [prefixWord, tailWord_226036, baseEnd_226036] using wordTrace_append hprefix tailTrace_226036
  have hstable : (prefixWord ++ tailWord_226036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226036).length < 2 ^ (prefixWord ++ tailWord_226036).sum := by decide
  have hdescent : baseEnd_226036 < baseStart_226036 := by decide
  rcases family_descends (prefixWord ++ tailWord_226036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226044 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 2]
def baseStart_226044 : Nat := 118140960795 + 226044 * 2 ^ 59
def prefixEnd_226044 : Nat := 4983230072969 + 3 ^ 40 * 226044 * 2
def baseEnd_226044 : Nat := 103172640946683409342621

theorem tailTrace_226044 : CollatzResearch.WordTrace tailWord_226044 prefixEnd_226044 103172640946683409342621 := by
  unfold tailWord_226044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122250996544334043394593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5496334662059112057859457 4122250996544334043394593)
  ·
    refine ⟨3091688247408250532545945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4122250996544334043394593 3091688247408250532545945)
    ·
      refine ⟨2318766185556187899409459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3091688247408250532545945 2318766185556187899409459)
      ·
        refine ⟨3478149278334281849114189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318766185556187899409459 3478149278334281849114189)
        ·
          refine ⟨1304305979375355693417821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3478149278334281849114189 1304305979375355693417821)
          ·
            refine ⟨489114742265758385031683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1304305979375355693417821 489114742265758385031683)
            ·
              refine ⟨733672113398637577547525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489114742265758385031683 733672113398637577547525)
              ·
                refine ⟨137563521262244545790161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733672113398637577547525 137563521262244545790161)
                ·
                  refine ⟨103172640946683409342621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137563521262244545790161 103172640946683409342621)
                  ·
                    rfl

theorem cell20_226044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_226044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226044 prefixEnd_226044 := by exact prefixLift 226044
  have htrace : WordTrace (prefixWord ++ tailWord_226044) baseStart_226044 baseEnd_226044 := by
    simpa [prefixWord, tailWord_226044, baseEnd_226044] using wordTrace_append hprefix tailTrace_226044
  have hstable : (prefixWord ++ tailWord_226044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226044).length < 2 ^ (prefixWord ++ tailWord_226044).sum := by decide
  have hdescent : baseEnd_226044 < baseStart_226044 := by decide
  rcases family_descends (prefixWord ++ tailWord_226044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226082 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_226082 : Nat := 118140960795 + 226082 * 2 ^ 59
def prefixEnd_226082 : Nat := 4983230072969 + 3 ^ 40 * 226082 * 2
def baseEnd_226082 : Nat := 103189985182124166075799

theorem tailTrace_226082 : CollatzResearch.WordTrace tailWord_226082 prefixEnd_226082 103189985182124166075799 := by
  unfold tailWord_226082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061471991737750144168125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5497258644634000384448333 2061471991737750144168125)
  ·
    refine ⟨773051996901656304063047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2061471991737750144168125 773051996901656304063047)
    ·
      refine ⟨1159577995352484456094571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773051996901656304063047 1159577995352484456094571)
      ·
        refine ⟨1739366993028726684141857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159577995352484456094571 1739366993028726684141857)
        ·
          refine ⟨1304525244771545013106393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739366993028726684141857 1304525244771545013106393)
          ·
            refine ⟨978393933578658759829795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304525244771545013106393 978393933578658759829795)
            ·
              refine ⟨1467590900367988139744693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978393933578658759829795 1467590900367988139744693)
              ·
                refine ⟨137586646909498888101065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467590900367988139744693 137586646909498888101065)
                ·
                  refine ⟨103189985182124166075799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137586646909498888101065 103189985182124166075799)
                  ·
                    rfl

theorem cell20_226082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_226082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226082 prefixEnd_226082 := by exact prefixLift 226082
  have htrace : WordTrace (prefixWord ++ tailWord_226082) baseStart_226082 baseEnd_226082 := by
    simpa [prefixWord, tailWord_226082, baseEnd_226082] using wordTrace_append hprefix tailTrace_226082
  have hstable : (prefixWord ++ tailWord_226082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226082).length < 2 ^ (prefixWord ++ tailWord_226082).sum := by decide
  have hdescent : baseEnd_226082 < baseStart_226082 := by decide
  rcases family_descends (prefixWord ++ tailWord_226082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226103 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 2]
def baseStart_226103 : Nat := 118140960795 + 226103 * 2 ^ 59
def prefixEnd_226103 : Nat := 4983230072969 + 3 ^ 40 * 226103 * 2
def baseEnd_226103 : Nat := 103199570154341426375713

theorem tailTrace_226103 : CollatzResearch.WordTrace tailWord_226103 prefixEnd_226103 103199570154341426375713 := by
  unfold tailWord_226103
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246653899874921163186963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5497769266583280775457975 8246653899874921163186963)
  ·
    refine ⟨12369980849812381744780445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8246653899874921163186963 12369980849812381744780445)
    ·
      refine ⟨4638742818679643154292667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12369980849812381744780445 4638742818679643154292667)
      ·
        refine ⟨6958114228019464731439001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638742818679643154292667 6958114228019464731439001)
        ·
          refine ⟨5218585671014598548579251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6958114228019464731439001 5218585671014598548579251)
          ·
            refine ⟨7827878506521897822868877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218585671014598548579251 7827878506521897822868877)
            ·
              refine ⟨2935454439945711683575829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7827878506521897822868877 2935454439945711683575829)
              ·
                refine ⟨137599426872455235167617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2935454439945711683575829 137599426872455235167617)
                ·
                  refine ⟨103199570154341426375713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137599426872455235167617 103199570154341426375713)
                  ·
                    rfl

theorem cell20_226103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 2].length) (baseStart_226103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226103 prefixEnd_226103 := by exact prefixLift 226103
  have htrace : WordTrace (prefixWord ++ tailWord_226103) baseStart_226103 baseEnd_226103 := by
    simpa [prefixWord, tailWord_226103, baseEnd_226103] using wordTrace_append hprefix tailTrace_226103
  have hstable : (prefixWord ++ tailWord_226103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226103).length < 2 ^ (prefixWord ++ tailWord_226103).sum := by decide
  have hdescent : baseEnd_226103 < baseStart_226103 := by decide
  rcases family_descends (prefixWord ++ tailWord_226103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226148 : List Nat := [2, 3, 1, 1, 4, 3, 6]
def baseStart_226148 : Nat := 118140960795 + 226148 * 2 ^ 59
def prefixEnd_226148 : Nat := 4983230072969 + 3 ^ 40 * 226148 * 2
def baseEnd_226148 : Nat := 11468901042280141097281

theorem tailTrace_226148 : CollatzResearch.WordTrace tailWord_226148 prefixEnd_226148 11468901042280141097281 := by
  unfold tailWord_226148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124147592355946924287549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5498863456474595899050065 4124147592355946924287549)
  ·
    refine ⟨1546555347133480096607831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4124147592355946924287549 1546555347133480096607831)
    ·
      refine ⟨2319833020700220144911747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546555347133480096607831 2319833020700220144911747)
      ·
        refine ⟨3479749531050330217367621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319833020700220144911747 3479749531050330217367621)
        ·
          refine ⟨652453037071936915756429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3479749531050330217367621 652453037071936915756429)
          ·
            refine ⟨244669888901976343408661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 652453037071936915756429 244669888901976343408661)
            ·
              refine ⟨11468901042280141097281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244669888901976343408661 11468901042280141097281)
              ·
                rfl

theorem cell20_226148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 6].length) (baseStart_226148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226148 prefixEnd_226148 := by exact prefixLift 226148
  have htrace : WordTrace (prefixWord ++ tailWord_226148) baseStart_226148 baseEnd_226148 := by
    simpa [prefixWord, tailWord_226148, baseEnd_226148] using wordTrace_append hprefix tailTrace_226148
  have hstable : (prefixWord ++ tailWord_226148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226148).length < 2 ^ (prefixWord ++ tailWord_226148).sum := by decide
  have hdescent : baseEnd_226148 < baseStart_226148 := by decide
  rcases family_descends (prefixWord ++ tailWord_226148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226169 : List Nat := [1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_226169 : Nat := 118140960795 + 226169 * 2 ^ 59
def prefixEnd_226169 : Nat := 4983230072969 + 3 ^ 40 * 226169 * 2
def baseEnd_226169 : Nat := 34409898117579510058481

theorem tailTrace_226169 : CollatzResearch.WordTrace tailWord_226169 prefixEnd_226169 34409898117579510058481 := by
  unfold tailWord_226169
  simp only [CollatzResearch.WordTrace]
  refine ⟨8249061117635814435089561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5499374078423876290059707 8249061117635814435089561)
  ·
    refine ⟨6186795838226860826317171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8249061117635814435089561 6186795838226860826317171)
    ·
      refine ⟨9280193757340291239475757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186795838226860826317171 9280193757340291239475757)
      ·
        refine ⟨3480072659002609214803409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9280193757340291239475757 3480072659002609214803409)
        ·
          refine ⟨2610054494251956911102557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3480072659002609214803409 2610054494251956911102557)
          ·
            refine ⟨978770435344483841663459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2610054494251956911102557 978770435344483841663459)
            ·
              refine ⟨1468155653016725762495189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978770435344483841663459 1468155653016725762495189)
              ·
                refine ⟨34409898117579510058481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1468155653016725762495189 34409898117579510058481)
                ·
                  rfl

theorem cell20_226169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_226169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226169 prefixEnd_226169 := by exact prefixLift 226169
  have htrace : WordTrace (prefixWord ++ tailWord_226169) baseStart_226169 baseEnd_226169 := by
    simpa [prefixWord, tailWord_226169, baseEnd_226169] using wordTrace_append hprefix tailTrace_226169
  have hstable : (prefixWord ++ tailWord_226169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226169).length < 2 ^ (prefixWord ++ tailWord_226169).sum := by decide
  have hdescent : baseEnd_226169 < baseStart_226169 := by decide
  rcases family_descends (prefixWord ++ tailWord_226169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226176 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_226176 : Nat := 118140960795 + 226176 * 2 ^ 59
def prefixEnd_226176 : Nat := 4983230072969 + 3 ^ 40 * 226176 * 2
def baseEnd_226176 : Nat := 103232889343477616942081

theorem tailTrace_226176 : CollatzResearch.WordTrace tailWord_226176 prefixEnd_226176 103232889343477616942081 := by
  unfold tailWord_226176
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124658214305227315297191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5499544285740303087062921 4124658214305227315297191)
  ·
    refine ⟨6186987321457840972945787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4124658214305227315297191 6186987321457840972945787)
    ·
      refine ⟨9280480982186761459418681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6186987321457840972945787 9280480982186761459418681)
      ·
        refine ⟨6960360736640071094564011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9280480982186761459418681 6960360736640071094564011)
        ·
          refine ⟨10440541104960106641846017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960360736640071094564011 10440541104960106641846017)
          ·
            refine ⟨7830405828720079981384513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10440541104960106641846017 7830405828720079981384513)
            ·
              refine ⟨5872804371540059986038385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7830405828720079981384513 5872804371540059986038385)
              ·
                refine ⟨4404603278655044989528789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872804371540059986038385 4404603278655044989528789)
                ·
                  refine ⟨103232889343477616942081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4404603278655044989528789 103232889343477616942081)
                  ·
                    rfl

theorem cell20_226176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_226176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226176 prefixEnd_226176 := by exact prefixLift 226176
  have htrace : WordTrace (prefixWord ++ tailWord_226176) baseStart_226176 baseEnd_226176 := by
    simpa [prefixWord, tailWord_226176, baseEnd_226176] using wordTrace_append hprefix tailTrace_226176
  have hstable : (prefixWord ++ tailWord_226176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226176).length < 2 ^ (prefixWord ++ tailWord_226176).sum := by decide
  have hdescent : baseEnd_226176 < baseStart_226176 := by decide
  rcases family_descends (prefixWord ++ tailWord_226176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226186 : List Nat := [3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_226186 : Nat := 118140960795 + 226186 * 2 ^ 59
def prefixEnd_226186 : Nat := 4983230072969 + 3 ^ 40 * 226186 * 2
def baseEnd_226186 : Nat := 34412484538654008869569

theorem tailTrace_226186 : CollatzResearch.WordTrace tailWord_226186 prefixEnd_226186 34412484538654008869569 := by
  unfold tailWord_226186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062420289643556584614603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5499787439049484225638941 2062420289643556584614603)
  ·
    refine ⟨3093630434465334876921905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2062420289643556584614603 3093630434465334876921905)
    ·
      refine ⟨2320222825849001157691429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3093630434465334876921905 2320222825849001157691429)
      ·
        refine ⟨435041779846687717067143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2320222825849001157691429 435041779846687717067143)
        ·
          refine ⟨652562669770031575600715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435041779846687717067143 652562669770031575600715)
          ·
            refine ⟨978844004655047363401073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652562669770031575600715 978844004655047363401073)
            ·
              refine ⟨734133003491285522550805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978844004655047363401073 734133003491285522550805)
              ·
                refine ⟨34412484538654008869569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 734133003491285522550805 34412484538654008869569)
                ·
                  rfl

theorem cell20_226186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_226186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226186 prefixEnd_226186 := by exact prefixLift 226186
  have htrace : WordTrace (prefixWord ++ tailWord_226186) baseStart_226186 baseEnd_226186 := by
    simpa [prefixWord, tailWord_226186, baseEnd_226186] using wordTrace_append hprefix tailTrace_226186
  have hstable : (prefixWord ++ tailWord_226186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226186).length < 2 ^ (prefixWord ++ tailWord_226186).sum := by decide
  have hdescent : baseEnd_226186 < baseStart_226186 := by decide
  rcases family_descends (prefixWord ++ tailWord_226186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226196 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 2]
def baseStart_226196 : Nat := 118140960795 + 226196 * 2 ^ 59
def prefixEnd_226196 : Nat := 4983230072969 + 3 ^ 40 * 226196 * 2
def baseEnd_226196 : Nat := 103242017888446436275333

theorem tailTrace_226196 : CollatzResearch.WordTrace tailWord_226196 prefixEnd_226196 103242017888446436275333 := by
  unfold tailWord_226196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125022944268999023161221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5500030592358665364214961 4125022944268999023161221)
  ·
    refine ⟨773441802050437316842729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4125022944268999023161221 773441802050437316842729)
    ·
      refine ⟨580081351537827987632047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 773441802050437316842729 580081351537827987632047)
      ·
        refine ⟨870122027306741981448071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580081351537827987632047 870122027306741981448071)
        ·
          refine ⟨1305183040960112972172107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870122027306741981448071 1305183040960112972172107)
          ·
            refine ⟨1957774561440169458258161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305183040960112972172107 1957774561440169458258161)
            ·
              refine ⟨1468330921080127093693621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957774561440169458258161 1468330921080127093693621)
              ·
                refine ⟨137656023851261915033777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1468330921080127093693621 137656023851261915033777)
                ·
                  refine ⟨103242017888446436275333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137656023851261915033777 103242017888446436275333)
                  ·
                    rfl

theorem cell20_226196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_226196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226196 prefixEnd_226196 := by exact prefixLift 226196
  have htrace : WordTrace (prefixWord ++ tailWord_226196) baseStart_226196 baseEnd_226196 := by
    simpa [prefixWord, tailWord_226196, baseEnd_226196] using wordTrace_append hprefix tailTrace_226196
  have hstable : (prefixWord ++ tailWord_226196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226196).length < 2 ^ (prefixWord ++ tailWord_226196).sum := by decide
  have hdescent : baseEnd_226196 < baseStart_226196 := by decide
  rcases family_descends (prefixWord ++ tailWord_226196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226207 : List Nat := [1, 1, 2, 5, 2, 9]
def baseStart_226207 : Nat := 118140960795 + 226207 * 2 ^ 59
def prefixEnd_226207 : Nat := 4983230072969 + 3 ^ 40 * 226207 * 2
def baseEnd_226207 : Nat := 3823964392154788404023

theorem tailTrace_226207 : CollatzResearch.WordTrace tailWord_226207 prefixEnd_226207 3823964392154788404023 := by
  unfold tailWord_226207
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250447091498146924972875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5500298060998764616648583 8250447091498146924972875)
  ·
    refine ⟨12375670637247220387459313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8250447091498146924972875 12375670637247220387459313)
    ·
      refine ⟨9281752977935415290594485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12375670637247220387459313 9281752977935415290594485)
      ·
        refine ⟨870164341681445183493233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9281752977935415290594485 870164341681445183493233)
        ·
          refine ⟨652623256261083887619925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870164341681445183493233 652623256261083887619925)
          ·
            refine ⟨3823964392154788404023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 652623256261083887619925 3823964392154788404023)
            ·
              rfl

theorem cell20_226207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 9].length) (baseStart_226207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226207 prefixEnd_226207 := by exact prefixLift 226207
  have htrace : WordTrace (prefixWord ++ tailWord_226207) baseStart_226207 baseEnd_226207 := by
    simpa [prefixWord, tailWord_226207, baseEnd_226207] using wordTrace_append hprefix tailTrace_226207
  have hstable : (prefixWord ++ tailWord_226207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226207).length < 2 ^ (prefixWord ++ tailWord_226207).sum := by decide
  have hdescent : baseEnd_226207 < baseStart_226207 := by decide
  rcases family_descends (prefixWord ++ tailWord_226207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226210 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_226210 : Nat := 118140960795 + 226210 * 2 ^ 59
def prefixEnd_226210 : Nat := 4983230072969 + 3 ^ 40 * 226210 * 2
def baseEnd_226210 : Nat := 103248407869924609808609

theorem tailTrace_226210 : CollatzResearch.WordTrace tailWord_226210 prefixEnd_226210 103248407869924609808609 := by
  unfold tailWord_226210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062639127621819609333021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5500371006991518958221389 2062639127621819609333021)
  ·
    refine ⟨773489672858182353499883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2062639127621819609333021 773489672858182353499883)
    ·
      refine ⟨1160234509287273530249825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773489672858182353499883 1160234509287273530249825)
      ·
        refine ⟨870175881965455147687369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1160234509287273530249825 870175881965455147687369)
        ·
          refine ⟨652631911474091360765527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870175881965455147687369 652631911474091360765527)
          ·
            refine ⟨978947867211137041148291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652631911474091360765527 978947867211137041148291)
            ·
              refine ⟨1468421800816705561722437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978947867211137041148291 1468421800816705561722437)
              ·
                refine ⟨275329087653132292822957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1468421800816705561722437 275329087653132292822957)
                ·
                  refine ⟨103248407869924609808609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275329087653132292822957 103248407869924609808609)
                  ·
                    rfl

theorem cell20_226210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_226210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226210 prefixEnd_226210 := by exact prefixLift 226210
  have htrace : WordTrace (prefixWord ++ tailWord_226210) baseStart_226210 baseEnd_226210 := by
    simpa [prefixWord, tailWord_226210, baseEnd_226210] using wordTrace_append hprefix tailTrace_226210
  have hstable : (prefixWord ++ tailWord_226210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226210).length < 2 ^ (prefixWord ++ tailWord_226210).sum := by decide
  have hdescent : baseEnd_226210 < baseStart_226210 := by decide
  rcases family_descends (prefixWord ++ tailWord_226210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226217 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 2]
def baseStart_226217 : Nat := 118140960795 + 226217 * 2 ^ 59
def prefixEnd_226217 : Nat := 4983230072969 + 3 ^ 40 * 226217 * 2
def baseEnd_226217 : Nat := 103251602860663696575247

theorem tailTrace_226217 : CollatzResearch.WordTrace tailWord_226217 prefixEnd_226217 103251602860663696575247 := by
  unfold tailWord_226217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8250811821461918632836905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5500541214307945755224603 8250811821461918632836905)
  ·
    refine ⟨6188108866096438974627679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8250811821461918632836905 6188108866096438974627679)
    ·
      refine ⟨9282163299144658461941519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188108866096438974627679 9282163299144658461941519)
      ·
        refine ⟨13923244948716987692912279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9282163299144658461941519 13923244948716987692912279)
        ·
          refine ⟨20884867423075481539368419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13923244948716987692912279 20884867423075481539368419)
          ·
            refine ⟨31327301134613222309052629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20884867423075481539368419 31327301134613222309052629)
            ·
              refine ⟨734233620342497397868421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31327301134613222309052629 734233620342497397868421)
              ·
                refine ⟨137668803814218262100329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734233620342497397868421 137668803814218262100329)
                ·
                  refine ⟨103251602860663696575247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137668803814218262100329 103251602860663696575247)
                  ·
                    rfl

theorem cell20_226217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_226217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226217 prefixEnd_226217 := by exact prefixLift 226217
  have htrace : WordTrace (prefixWord ++ tailWord_226217) baseStart_226217 baseEnd_226217 := by
    simpa [prefixWord, tailWord_226217, baseEnd_226217] using wordTrace_append hprefix tailTrace_226217
  have hstable : (prefixWord ++ tailWord_226217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226217).length < 2 ^ (prefixWord ++ tailWord_226217).sum := by decide
  have hdescent : baseEnd_226217 < baseStart_226217 := by decide
  rcases family_descends (prefixWord ++ tailWord_226217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226230 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_226230 : Nat := 118140960795 + 226230 * 2 ^ 59
def prefixEnd_226230 : Nat := 4983230072969 + 3 ^ 40 * 226230 * 2
def baseEnd_226230 : Nat := 103257536414893429141861

theorem tailTrace_226230 : CollatzResearch.WordTrace tailWord_226230 prefixEnd_226230 103257536414893429141861 := by
  unfold tailWord_226230
  simp only [CollatzResearch.WordTrace]
  refine ⟨515705373150926365816259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5500857313609881235373429 515705373150926365816259)
  ·
    refine ⟨773558059726389548724389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 515705373150926365816259 773558059726389548724389)
    ·
      refine ⟨145042136198698040385823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 773558059726389548724389 145042136198698040385823)
      ·
        refine ⟨217563204298047060578735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145042136198698040385823 217563204298047060578735)
        ·
          refine ⟨326344806447070590868103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217563204298047060578735 326344806447070590868103)
          ·
            refine ⟨489517209670605886302155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326344806447070590868103 489517209670605886302155)
            ·
              refine ⟨734275814505908829453233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489517209670605886302155 734275814505908829453233)
              ·
                refine ⟨550706860879431622089925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734275814505908829453233 550706860879431622089925)
                ·
                  refine ⟨103257536414893429141861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550706860879431622089925 103257536414893429141861)
                  ·
                    rfl

theorem cell20_226230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_226230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226230 prefixEnd_226230 := by exact prefixLift 226230
  have htrace : WordTrace (prefixWord ++ tailWord_226230) baseStart_226230 baseEnd_226230 := by
    simpa [prefixWord, tailWord_226230, baseEnd_226230] using wordTrace_append hprefix tailTrace_226230
  have hstable : (prefixWord ++ tailWord_226230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226230).length < 2 ^ (prefixWord ++ tailWord_226230).sum := by decide
  have hdescent : baseEnd_226230 < baseStart_226230 := by decide
  rcases family_descends (prefixWord ++ tailWord_226230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226231 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_226231 : Nat := 118140960795 + 226231 * 2 ^ 59
def prefixEnd_226231 : Nat := 4983230072969 + 3 ^ 40 * 226231 * 2
def baseEnd_226231 : Nat := 103257992842141870108523

theorem tailTrace_226231 : CollatzResearch.WordTrace tailWord_226231 prefixEnd_226231 103257992842141870108523 := by
  unfold tailWord_226231
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251322443411199023846547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5500881628940799349231031 8251322443411199023846547)
  ·
    refine ⟨12376983665116798535769821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251322443411199023846547 12376983665116798535769821)
    ·
      refine ⟨4641368874418799450913683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12376983665116798535769821 4641368874418799450913683)
      ·
        refine ⟨6962053311628199176370525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4641368874418799450913683 6962053311628199176370525)
        ·
          refine ⟨2610769991860574691138947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6962053311628199176370525 2610769991860574691138947)
          ·
            refine ⟨3916154987790862036708421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610769991860574691138947 3916154987790862036708421)
            ·
              refine ⟨734279060210786631882829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3916154987790862036708421 734279060210786631882829)
              ·
                refine ⟨275354647579044986956061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 734279060210786631882829 275354647579044986956061)
                ·
                  refine ⟨103257992842141870108523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275354647579044986956061 103257992842141870108523)
                  ·
                    rfl

theorem cell20_226231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_226231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226231 prefixEnd_226231 := by exact prefixLift 226231
  have htrace : WordTrace (prefixWord ++ tailWord_226231) baseStart_226231 baseEnd_226231 := by
    simpa [prefixWord, tailWord_226231, baseEnd_226231] using wordTrace_append hprefix tailTrace_226231
  have hstable : (prefixWord ++ tailWord_226231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226231).length < 2 ^ (prefixWord ++ tailWord_226231).sum := by decide
  have hdescent : baseEnd_226231 < baseStart_226231 := by decide
  rcases family_descends (prefixWord ++ tailWord_226231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226255 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 2]
def baseStart_226255 : Nat := 118140960795 + 226255 * 2 ^ 59
def prefixEnd_226255 : Nat := 4983230072969 + 3 ^ 40 * 226255 * 2
def baseEnd_226255 : Nat := 103268947096104453308425

theorem tailTrace_226255 : CollatzResearch.WordTrace tailWord_226255 prefixEnd_226255 103268947096104453308425 := by
  unfold tailWord_226255
  simp only [CollatzResearch.WordTrace]
  refine ⟨8252197795324251122720219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5501465196882834081813479 8252197795324251122720219)
  ·
    refine ⟨12378296692986376684080329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8252197795324251122720219 12378296692986376684080329)
    ·
      refine ⟨9283722519739782513060247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12378296692986376684080329 9283722519739782513060247)
      ·
        refine ⟨13925583779609673769590371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9283722519739782513060247 13925583779609673769590371)
        ·
          refine ⟨20888375669414510654385557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13925583779609673769590371 20888375669414510654385557)
          ·
            refine ⟨979142609503805186924323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20888375669414510654385557 979142609503805186924323)
            ·
              refine ⟨1468713914255707780386485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979142609503805186924323 1468713914255707780386485)
              ·
                refine ⟨137691929461472604411233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1468713914255707780386485 137691929461472604411233)
                ·
                  refine ⟨103268947096104453308425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137691929461472604411233 103268947096104453308425)
                  ·
                    rfl

theorem cell20_226255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 2].length) (baseStart_226255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226255 prefixEnd_226255 := by exact prefixLift 226255
  have htrace : WordTrace (prefixWord ++ tailWord_226255) baseStart_226255 baseEnd_226255 := by
    simpa [prefixWord, tailWord_226255, baseEnd_226255] using wordTrace_append hprefix tailTrace_226255
  have hstable : (prefixWord ++ tailWord_226255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226255).length < 2 ^ (prefixWord ++ tailWord_226255).sum := by decide
  have hdescent : baseEnd_226255 < baseStart_226255 := by decide
  rcases family_descends (prefixWord ++ tailWord_226255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226300 : List Nat := [2, 2, 2, 1, 2, 3, 4, 4]
def baseStart_226300 : Nat := 118140960795 + 226300 * 2 ^ 59
def prefixEnd_226300 : Nat := 4983230072969 + 3 ^ 40 * 226300 * 2
def baseEnd_226300 : Nat := 34429828774094765602747

theorem tailTrace_226300 : CollatzResearch.WordTrace tailWord_226300 prefixEnd_226300 34429828774094765602747 := by
  unfold tailWord_226300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126919540080611904054177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5502559386774149205405569 4126919540080611904054177)
  ·
    refine ⟨3095189655060458928040633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4126919540080611904054177 3095189655060458928040633)
    ·
      refine ⟨2321392241295344196030475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3095189655060458928040633 2321392241295344196030475)
      ·
        refine ⟨3482088361943016294045713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321392241295344196030475 3482088361943016294045713)
        ·
          refine ⟨2611566271457262220534285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482088361943016294045713 2611566271457262220534285)
          ·
            refine ⟨979337351796473332700357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2611566271457262220534285 979337351796473332700357)
            ·
              refine ⟨183625753461838749881317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 979337351796473332700357 183625753461838749881317)
              ·
                refine ⟨34429828774094765602747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183625753461838749881317 34429828774094765602747)
                ·
                  rfl

theorem cell20_226300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_226300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226300 prefixEnd_226300 := by exact prefixLift 226300
  have htrace : WordTrace (prefixWord ++ tailWord_226300) baseStart_226300 baseEnd_226300 := by
    simpa [prefixWord, tailWord_226300, baseEnd_226300] using wordTrace_append hprefix tailTrace_226300
  have hstable : (prefixWord ++ tailWord_226300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226300).length < 2 ^ (prefixWord ++ tailWord_226300).sum := by decide
  have hdescent : baseEnd_226300 < baseStart_226300 := by decide
  rcases family_descends (prefixWord ++ tailWord_226300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226327 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 2]
def baseStart_226327 : Nat := 118140960795 + 226327 * 2 ^ 59
def prefixEnd_226327 : Nat := 4983230072969 + 3 ^ 40 * 226327 * 2
def baseEnd_226327 : Nat := 103301809857992202908131

theorem tailTrace_226327 : CollatzResearch.WordTrace tailWord_226327 prefixEnd_226327 103301809857992202908131 := by
  unfold tailWord_226327
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254823851063407419341235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5503215900708938279560823 8254823851063407419341235)
  ·
    refine ⟨12382235776595111129011853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8254823851063407419341235 12382235776595111129011853)
    ·
      refine ⟨4643338416223166673379445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12382235776595111129011853 4643338416223166673379445)
      ·
        refine ⟨435312976520921875629323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4643338416223166673379445 435312976520921875629323)
        ·
          refine ⟨652969464781382813443985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435312976520921875629323 652969464781382813443985)
          ·
            refine ⟨489727098586037110082989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652969464781382813443985 489727098586037110082989)
            ·
              refine ⟨183647661969763916281121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489727098586037110082989 183647661969763916281121)
              ·
                refine ⟨137735746477322937210841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183647661969763916281121 137735746477322937210841)
                ·
                  refine ⟨103301809857992202908131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137735746477322937210841 103301809857992202908131)
                  ·
                    rfl

theorem cell20_226327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 2].length) (baseStart_226327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226327 prefixEnd_226327 := by exact prefixLift 226327
  have htrace : WordTrace (prefixWord ++ tailWord_226327) baseStart_226327 baseEnd_226327 := by
    simpa [prefixWord, tailWord_226327, baseEnd_226327] using wordTrace_append hprefix tailTrace_226327
  have hstable : (prefixWord ++ tailWord_226327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226327).length < 2 ^ (prefixWord ++ tailWord_226327).sum := by decide
  have hdescent : baseEnd_226327 < baseStart_226327 := by decide
  rcases family_descends (prefixWord ++ tailWord_226327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226338 : List Nat := [3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_226338 : Nat := 118140960795 + 226338 * 2 ^ 59
def prefixEnd_226338 : Nat := 4983230072969 + 3 ^ 40 * 226338 * 2
def baseEnd_226338 : Nat := 34435610185908351180473

theorem tailTrace_226338 : CollatzResearch.WordTrace tailWord_226338 prefixEnd_226338 34435610185908351180473 := by
  unfold tailWord_226338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063806263505889074497917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5503483369349037531994445 2063806263505889074497917)
  ·
    refine ⟨773927348814708402936719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2063806263505889074497917 773927348814708402936719)
    ·
      refine ⟨1160891023222062604405079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773927348814708402936719 1160891023222062604405079)
      ·
        refine ⟨1741336534833093906607619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160891023222062604405079 1741336534833093906607619)
        ·
          refine ⟨2612004802249640859911429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741336534833093906607619 2612004802249640859911429)
          ·
            refine ⟨489750900421807661233393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2612004802249640859911429 489750900421807661233393)
            ·
              refine ⟨367313175316355745925045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489750900421807661233393 367313175316355745925045)
              ·
                refine ⟨34435610185908351180473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367313175316355745925045 34435610185908351180473)
                ·
                  rfl

theorem cell20_226338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_226338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226338 prefixEnd_226338 := by exact prefixLift 226338
  have htrace : WordTrace (prefixWord ++ tailWord_226338) baseStart_226338 baseEnd_226338 := by
    simpa [prefixWord, tailWord_226338, baseEnd_226338] using wordTrace_append hprefix tailTrace_226338
  have hstable : (prefixWord ++ tailWord_226338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226338).length < 2 ^ (prefixWord ++ tailWord_226338).sum := by decide
  have hdescent : baseEnd_226338 < baseStart_226338 := by decide
  rcases family_descends (prefixWord ++ tailWord_226338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226386 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_226386 : Nat := 118140960795 + 226386 * 2 ^ 59
def prefixEnd_226386 : Nat := 4983230072969 + 3 ^ 40 * 226386 * 2
def baseEnd_226386 : Nat := 103328739065650219941223

theorem tailTrace_226386 : CollatzResearch.WordTrace tailWord_226386 prefixEnd_226386 103328739065650219941223 := by
  unfold tailWord_226386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064243939462415123934753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5504650505233106997159341 2064243939462415123934753)
  ·
    refine ⟨1548182954596811342951065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2064243939462415123934753 1548182954596811342951065)
    ·
      refine ⟨1161137215947608507213299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1548182954596811342951065 1161137215947608507213299)
      ·
        refine ⟨1741705823921412760819949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161137215947608507213299 1741705823921412760819949)
        ·
          refine ⟨653139683970529785307481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1741705823921412760819949 653139683970529785307481)
          ·
            refine ⟨489854762977897338980611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653139683970529785307481 489854762977897338980611)
            ·
              refine ⟨734782144466846008470917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489854762977897338980611 734782144466846008470917)
              ·
                refine ⟨137771652087533626588297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734782144466846008470917 137771652087533626588297)
                ·
                  refine ⟨103328739065650219941223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137771652087533626588297 103328739065650219941223)
                  ·
                    rfl

theorem cell20_226386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_226386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226386 prefixEnd_226386 := by exact prefixLift 226386
  have htrace : WordTrace (prefixWord ++ tailWord_226386) baseStart_226386 baseEnd_226386 := by
    simpa [prefixWord, tailWord_226386, baseEnd_226386] using wordTrace_append hprefix tailTrace_226386
  have hstable : (prefixWord ++ tailWord_226386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226386).length < 2 ^ (prefixWord ++ tailWord_226386).sum := by decide
  have hdescent : baseEnd_226386 < baseStart_226386 := by decide
  rcases family_descends (prefixWord ++ tailWord_226386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226404 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_226404 : Nat := 118140960795 + 226404 * 2 ^ 59
def prefixEnd_226404 : Nat := 4983230072969 + 3 ^ 40 * 226404 * 2
def baseEnd_226404 : Nat := 103336954756122157341149

theorem tailTrace_226404 : CollatzResearch.WordTrace tailWord_226404 prefixEnd_226404 103336954756122157341149 := by
  unfold tailWord_226404
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128816135892224784947133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5505088181189633046596177 4128816135892224784947133)
  ·
    refine ⟨1548306050959584294355175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4128816135892224784947133 1548306050959584294355175)
    ·
      refine ⟨2322459076439376441532763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548306050959584294355175 2322459076439376441532763)
      ·
        refine ⟨3483688614659064662299145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322459076439376441532763 3483688614659064662299145)
        ·
          refine ⟨2612766460994298496724359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3483688614659064662299145 2612766460994298496724359)
          ·
            refine ⟨3919149691491447745086539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612766460994298496724359 3919149691491447745086539)
            ·
              refine ⟨5878724537237171617629809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919149691491447745086539 5878724537237171617629809)
              ·
                refine ⟨4409043402927878713222357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5878724537237171617629809 4409043402927878713222357)
                ·
                  refine ⟨103336954756122157341149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4409043402927878713222357 103336954756122157341149)
                  ·
                    rfl

theorem cell20_226404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_226404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226404 prefixEnd_226404 := by exact prefixLift 226404
  have htrace : WordTrace (prefixWord ++ tailWord_226404) baseStart_226404 baseEnd_226404 := by
    simpa [prefixWord, tailWord_226404, baseEnd_226404] using wordTrace_append hprefix tailTrace_226404
  have hstable : (prefixWord ++ tailWord_226404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226404).length < 2 ^ (prefixWord ++ tailWord_226404).sum := by decide
  have hdescent : baseEnd_226404 < baseStart_226404 := by decide
  rcases family_descends (prefixWord ++ tailWord_226404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226430 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_226430 : Nat := 118140960795 + 226430 * 2 ^ 59
def prefixEnd_226430 : Nat := 4983230072969 + 3 ^ 40 * 226430 * 2
def baseEnd_226430 : Nat := 103348821864581622474377

theorem tailTrace_226430 : CollatzResearch.WordTrace tailWord_226430 prefixEnd_226430 103348821864581622474377 := by
  unfold tailWord_226430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032322571211282001292593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5505720379793504006893829 1032322571211282001292593)
  ·
    refine ⟨774241928408461500969445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1032322571211282001292593 774241928408461500969445)
    ·
      refine ⟨145170361576586531431771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 774241928408461500969445 145170361576586531431771)
      ·
        refine ⟨217755542364879797147657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145170361576586531431771 217755542364879797147657)
        ·
          refine ⟨163316656773659847860743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217755542364879797147657 163316656773659847860743)
          ·
            refine ⟨244974985160489771791115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163316656773659847860743 244974985160489771791115)
            ·
              refine ⟨367462477740734657686673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244974985160489771791115 367462477740734657686673)
              ·
                refine ⟨275596858305550993265005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367462477740734657686673 275596858305550993265005)
                ·
                  refine ⟨103348821864581622474377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275596858305550993265005 103348821864581622474377)
                  ·
                    rfl

theorem cell20_226430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_226430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226430 prefixEnd_226430 := by exact prefixLift 226430
  have htrace : WordTrace (prefixWord ++ tailWord_226430) baseStart_226430 baseEnd_226430 := by
    simpa [prefixWord, tailWord_226430, baseEnd_226430] using wordTrace_append hprefix tailTrace_226430
  have hstable : (prefixWord ++ tailWord_226430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226430).length < 2 ^ (prefixWord ++ tailWord_226430).sum := by decide
  have hdescent : baseEnd_226430 < baseStart_226430 := by decide
  rcases family_descends (prefixWord ++ tailWord_226430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226483 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 2]
def baseStart_226483 : Nat := 118140960795 + 226483 * 2 ^ 59
def prefixEnd_226483 : Nat := 4983230072969 + 3 ^ 40 * 226483 * 2
def baseEnd_226483 : Nat := 103373012508748993707493

theorem tailTrace_226483 : CollatzResearch.WordTrace tailWord_226483 prefixEnd_226483 103373012508748993707493 := by
  unfold tailWord_226483
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260513638498246062020103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5507009092332164041346735 8260513638498246062020103)
  ·
    refine ⟨12390770457747369093030155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8260513638498246062020103 12390770457747369093030155)
    ·
      refine ⟨18586155686621053639545233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390770457747369093030155 18586155686621053639545233)
      ·
        refine ⟨13939616764965790229658925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18586155686621053639545233 13939616764965790229658925)
        ·
          refine ⟨5227356286862171336122097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13939616764965790229658925 5227356286862171336122097)
          ·
            refine ⟨3920517215146628502091573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227356286862171336122097 3920517215146628502091573)
            ·
              refine ⟨367548488919996422071085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3920517215146628502091573 367548488919996422071085)
              ·
                refine ⟨137830683344998658276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367548488919996422071085 137830683344998658276657)
                ·
                  refine ⟨103373012508748993707493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137830683344998658276657 103373012508748993707493)
                  ·
                    rfl

theorem cell20_226483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 2].length) (baseStart_226483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226483 prefixEnd_226483 := by exact prefixLift 226483
  have htrace : WordTrace (prefixWord ++ tailWord_226483) baseStart_226483 baseEnd_226483 := by
    simpa [prefixWord, tailWord_226483, baseEnd_226483] using wordTrace_append hprefix tailTrace_226483
  have hstable : (prefixWord ++ tailWord_226483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226483).length < 2 ^ (prefixWord ++ tailWord_226483).sum := by decide
  have hdescent : baseEnd_226483 < baseStart_226483 := by decide
  rcases family_descends (prefixWord ++ tailWord_226483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226486 : List Nat := [5, 1, 3, 2, 1, 2, 6]
def baseStart_226486 : Nat := 118140960795 + 226486 * 2 ^ 59
def prefixEnd_226486 : Nat := 4983230072969 + 3 ^ 40 * 226486 * 2
def baseEnd_226486 : Nat := 11486042421166035178609

theorem tailTrace_226486 : CollatzResearch.WordTrace tailWord_226486 prefixEnd_226486 11486042421166035178609 := by
  unfold tailWord_226486
  simp only [CollatzResearch.WordTrace]
  refine ⟨516288941092961098398707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5507082038324918382919541 516288941092961098398707)
  ·
    refine ⟨774433411639441647598061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516288941092961098398707 774433411639441647598061)
    ·
      refine ⟨290412529364790617849273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 774433411639441647598061 290412529364790617849273)
      ·
        refine ⟨217809397023592963386955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290412529364790617849273 217809397023592963386955)
        ·
          refine ⟨326714095535389445080433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217809397023592963386955 326714095535389445080433)
          ·
            refine ⟨245035571651542083810325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326714095535389445080433 245035571651542083810325)
            ·
              refine ⟨11486042421166035178609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245035571651542083810325 11486042421166035178609)
              ·
                rfl

theorem cell20_226486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 6].length) (baseStart_226486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226486 prefixEnd_226486 := by exact prefixLift 226486
  have htrace : WordTrace (prefixWord ++ tailWord_226486) baseStart_226486 baseEnd_226486 := by
    simpa [prefixWord, tailWord_226486, baseEnd_226486] using wordTrace_append hprefix tailTrace_226486
  have hstable : (prefixWord ++ tailWord_226486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226486).length < 2 ^ (prefixWord ++ tailWord_226486).sum := by decide
  have hdescent : baseEnd_226486 < baseStart_226486 := by decide
  rcases family_descends (prefixWord ++ tailWord_226486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226500 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_226500 : Nat := 118140960795 + 226500 * 2 ^ 59
def prefixEnd_226500 : Nat := 4983230072969 + 3 ^ 40 * 226500 * 2
def baseEnd_226500 : Nat := 103380771771972490140757

theorem tailTrace_226500 : CollatzResearch.WordTrace tailWord_226500 prefixEnd_226500 103380771771972490140757 := by
  unfold tailWord_226500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130566839718328982694477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5507422452957771976925969 4130566839718328982694477)
  ·
    refine ⟨1548962564894373368510429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4130566839718328982694477 1548962564894373368510429)
    ·
      refine ⟨580860961835390013191411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1548962564894373368510429 580860961835390013191411)
      ·
        refine ⟨871291442753085019787117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580860961835390013191411 871291442753085019787117)
        ·
          refine ⟨326734291032406882420169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 871291442753085019787117 326734291032406882420169)
          ·
            refine ⟨245050718274305161815127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326734291032406882420169 245050718274305161815127)
            ·
              refine ⟨367576077411457742722691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245050718274305161815127 367576077411457742722691)
              ·
                refine ⟨551364116117186614084037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367576077411457742722691 551364116117186614084037)
                ·
                  refine ⟨103380771771972490140757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551364116117186614084037 103380771771972490140757)
                  ·
                    rfl

theorem cell20_226500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_226500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226500 prefixEnd_226500 := by exact prefixLift 226500
  have htrace : WordTrace (prefixWord ++ tailWord_226500) baseStart_226500 baseEnd_226500 := by
    simpa [prefixWord, tailWord_226500, baseEnd_226500] using wordTrace_append hprefix tailTrace_226500
  have hstable : (prefixWord ++ tailWord_226500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226500).length < 2 ^ (prefixWord ++ tailWord_226500).sum := by decide
  have hdescent : baseEnd_226500 < baseStart_226500 := by decide
  rcases family_descends (prefixWord ++ tailWord_226500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226504 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_226504 : Nat := 118140960795 + 226504 * 2 ^ 59
def prefixEnd_226504 : Nat := 4983230072969 + 3 ^ 40 * 226504 * 2
def baseEnd_226504 : Nat := 103382597480966254007407

theorem tailTrace_226504 : CollatzResearch.WordTrace tailWord_226504 prefixEnd_226504 103382597480966254007407 := by
  unfold tailWord_226504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4130639785711083324267283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5507519714281444432356377 4130639785711083324267283)
  ·
    refine ⟨6195959678566624986400925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4130639785711083324267283 6195959678566624986400925)
    ·
      refine ⟨2323484879462484369900347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6195959678566624986400925 2323484879462484369900347)
      ·
        refine ⟨3485227319193726554850521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323484879462484369900347 3485227319193726554850521)
        ·
          refine ⟨2613920489395294916137891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485227319193726554850521 2613920489395294916137891)
          ·
            refine ⟨3920880734092942374206837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613920489395294916137891 3920880734092942374206837)
            ·
              refine ⟨367582568821213347581891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3920880734092942374206837 367582568821213347581891)
              ·
                refine ⟨551373853231820021372837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367582568821213347581891 551373853231820021372837)
                ·
                  refine ⟨103382597480966254007407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551373853231820021372837 103382597480966254007407)
                  ·
                    rfl

theorem cell20_226504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_226504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226504 prefixEnd_226504 := by exact prefixLift 226504
  have htrace : WordTrace (prefixWord ++ tailWord_226504) baseStart_226504 baseEnd_226504 := by
    simpa [prefixWord, tailWord_226504, baseEnd_226504] using wordTrace_append hprefix tailTrace_226504
  have hstable : (prefixWord ++ tailWord_226504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226504).length < 2 ^ (prefixWord ++ tailWord_226504).sum := by decide
  have hdescent : baseEnd_226504 < baseStart_226504 := by decide
  rcases family_descends (prefixWord ++ tailWord_226504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226510 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_226510 : Nat := 118140960795 + 226510 * 2 ^ 59
def prefixEnd_226510 : Nat := 4983230072969 + 3 ^ 40 * 226510 * 2
def baseEnd_226510 : Nat := 103385336044456899807383

theorem tailTrace_226510 : CollatzResearch.WordTrace tailWord_226510 prefixEnd_226510 103385336044456899807383 := by
  unfold tailWord_226510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1032687301175053709156623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5507665606266953115501989 1032687301175053709156623)
  ·
    refine ⟨1549030951762580563734935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1032687301175053709156623 1549030951762580563734935)
    ·
      refine ⟨2323546427643870845602403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1549030951762580563734935 2323546427643870845602403)
      ·
        refine ⟨3485319641465806268403605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323546427643870845602403 3485319641465806268403605)
        ·
          refine ⟨163374358193709668831419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3485319641465806268403605 163374358193709668831419)
          ·
            refine ⟨245061537290564503247129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163374358193709668831419 245061537290564503247129)
            ·
              refine ⟨183796152967923377435347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245061537290564503247129 183796152967923377435347)
              ·
                refine ⟨275694229451885066153021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183796152967923377435347 275694229451885066153021)
                ·
                  refine ⟨103385336044456899807383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275694229451885066153021 103385336044456899807383)
                  ·
                    rfl

theorem cell20_226510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_226510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226510 prefixEnd_226510 := by exact prefixLift 226510
  have htrace : WordTrace (prefixWord ++ tailWord_226510) baseStart_226510 baseEnd_226510 := by
    simpa [prefixWord, tailWord_226510, baseEnd_226510] using wordTrace_append hprefix tailTrace_226510
  have hstable : (prefixWord ++ tailWord_226510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226510).length < 2 ^ (prefixWord ++ tailWord_226510).sum := by decide
  have hdescent : baseEnd_226510 < baseStart_226510 := by decide
  rcases family_descends (prefixWord ++ tailWord_226510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226559 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 2]
def baseStart_226559 : Nat := 118140960795 + 226559 * 2 ^ 59
def prefixEnd_226559 : Nat := 4983230072969 + 3 ^ 40 * 226559 * 2
def baseEnd_226559 : Nat := 103407700979630507173849

theorem tailTrace_226559 : CollatzResearch.WordTrace tailWord_226559 prefixEnd_226559 103407700979630507173849 := by
  unfold tailWord_226559
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263285586222911041786731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5508857057481940694524487 8263285586222911041786731)
  ·
    refine ⟨12394928379334366562680097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8263285586222911041786731 12394928379334366562680097)
    ·
      refine ⟨9296196284500774922010073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12394928379334366562680097 9296196284500774922010073)
      ·
        refine ⟨6972147213375581191507555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9296196284500774922010073 6972147213375581191507555)
        ·
          refine ⟨10458220820063371787261333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972147213375581191507555 10458220820063371787261333)
          ·
            refine ⟨490229100940470552527875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10458220820063371787261333 490229100940470552527875)
            ·
              refine ⟨735343651410705828791813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490229100940470552527875 735343651410705828791813)
              ·
                refine ⟨137876934639507342898465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735343651410705828791813 137876934639507342898465)
                ·
                  refine ⟨103407700979630507173849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137876934639507342898465 103407700979630507173849)
                  ·
                    rfl

theorem cell20_226559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 2].length) (baseStart_226559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226559 prefixEnd_226559 := by exact prefixLift 226559
  have htrace : WordTrace (prefixWord ++ tailWord_226559) baseStart_226559 baseEnd_226559 := by
    simpa [prefixWord, tailWord_226559, baseEnd_226559] using wordTrace_append hprefix tailTrace_226559
  have hstable : (prefixWord ++ tailWord_226559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226559).length < 2 ^ (prefixWord ++ tailWord_226559).sum := by decide
  have hdescent : baseEnd_226559 < baseStart_226559 := by decide
  rcases family_descends (prefixWord ++ tailWord_226559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226562 : List Nat := [3, 4, 1, 1, 4, 1, 1, 5]
def baseStart_226562 : Nat := 118140960795 + 226562 * 2 ^ 59
def prefixEnd_226562 : Nat := 4983230072969 + 3 ^ 40 * 226562 * 2
def baseEnd_226562 : Nat := 34469690087125276691279

theorem tailTrace_226562 : CollatzResearch.WordTrace tailWord_226562 prefixEnd_226562 34469690087125276691279 := by
  unfold tailWord_226562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065848751303010638536485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5508930003474695036097293 2065848751303010638536485)
  ·
    refine ⟨387346640869314494725591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2065848751303010638536485 387346640869314494725591)
    ·
      refine ⟨581019961303971742088387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387346640869314494725591 581019961303971742088387)
      ·
        refine ⟨871529941955957613132581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581019961303971742088387 871529941955957613132581)
        ·
          refine ⟨163411864116742052462359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 871529941955957613132581 163411864116742052462359)
          ·
            refine ⟨245117796175113078693539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163411864116742052462359 245117796175113078693539)
            ·
              refine ⟨367676694262669618040309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245117796175113078693539 367676694262669618040309)
              ·
                refine ⟨34469690087125276691279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367676694262669618040309 34469690087125276691279)
                ·
                  rfl

theorem cell20_226562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_226562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226562 prefixEnd_226562 := by exact prefixLift 226562
  have htrace : WordTrace (prefixWord ++ tailWord_226562) baseStart_226562 baseEnd_226562 := by
    simpa [prefixWord, tailWord_226562, baseEnd_226562] using wordTrace_append hprefix tailTrace_226562
  have hstable : (prefixWord ++ tailWord_226562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226562).length < 2 ^ (prefixWord ++ tailWord_226562).sum := by decide
  have hdescent : baseEnd_226562 < baseStart_226562 := by decide
  rcases family_descends (prefixWord ++ tailWord_226562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226597 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 2]
def baseStart_226597 : Nat := 118140960795 + 226597 * 2 ^ 59
def prefixEnd_226597 : Nat := 4983230072969 + 3 ^ 40 * 226597 * 2
def baseEnd_226597 : Nat := 103425045215071263907027

theorem tailTrace_226597 : CollatzResearch.WordTrace tailWord_226597 prefixEnd_226597 103425045215071263907027 := by
  unfold tailWord_226597
  simp only [CollatzResearch.WordTrace]
  refine ⟨8264671560085243531670045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5509781040056829021113363 8264671560085243531670045)
  ·
    refine ⟨3099251835031966324376267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8264671560085243531670045 3099251835031966324376267)
    ·
      refine ⟨4648877752547949486564401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099251835031966324376267 4648877752547949486564401)
      ·
        refine ⟨3486658314410962114923301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648877752547949486564401 3486658314410962114923301)
        ·
          refine ⟨653748433952055396548119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3486658314410962114923301 653748433952055396548119)
          ·
            refine ⟨980622650928083094822179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653748433952055396548119 980622650928083094822179)
            ·
              refine ⟨1470933976392124642233269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980622650928083094822179 1470933976392124642233269)
              ·
                refine ⟨137900060286761685209369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1470933976392124642233269 137900060286761685209369)
                ·
                  refine ⟨103425045215071263907027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137900060286761685209369 103425045215071263907027)
                  ·
                    rfl

theorem cell20_226597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_226597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226597 prefixEnd_226597 := by exact prefixLift 226597
  have htrace : WordTrace (prefixWord ++ tailWord_226597) baseStart_226597 baseEnd_226597 := by
    simpa [prefixWord, tailWord_226597, baseEnd_226597] using wordTrace_append hprefix tailTrace_226597
  have hstable : (prefixWord ++ tailWord_226597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226597).length < 2 ^ (prefixWord ++ tailWord_226597).sum := by decide
  have hdescent : baseEnd_226597 < baseStart_226597 := by decide
  rcases family_descends (prefixWord ++ tailWord_226597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226608 : List Nat := [2, 1, 1, 1, 2, 2, 11]
def baseStart_226608 : Nat := 118140960795 + 226608 * 2 ^ 59
def prefixEnd_226608 : Nat := 4983230072969 + 3 ^ 40 * 226608 * 2
def baseEnd_226608 : Nat := 11492229546089346060035

theorem tailTrace_226608 : CollatzResearch.WordTrace tailWord_226608 prefixEnd_226608 11492229546089346060035 := by
  unfold tailWord_226608
  simp only [CollatzResearch.WordTrace]
  refine ⟨4132536381522696205160239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5510048508696928273546985 4132536381522696205160239)
  ·
    refine ⟨6198804572284044307740359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4132536381522696205160239 6198804572284044307740359)
    ·
      refine ⟨9298206858426066461610539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6198804572284044307740359 9298206858426066461610539)
      ·
        refine ⟨13947310287639099692415809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9298206858426066461610539 13947310287639099692415809)
        ·
          refine ⟨10460482715729324769311857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13947310287639099692415809 10460482715729324769311857)
          ·
            refine ⟨7845362036796993576983893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10460482715729324769311857 7845362036796993576983893)
            ·
              refine ⟨11492229546089346060035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7845362036796993576983893 11492229546089346060035)
              ·
                rfl

theorem cell20_226608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_226608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226608 prefixEnd_226608 := by exact prefixLift 226608
  have htrace : WordTrace (prefixWord ++ tailWord_226608) baseStart_226608 baseEnd_226608 := by
    simpa [prefixWord, tailWord_226608, baseEnd_226608] using wordTrace_append hprefix tailTrace_226608
  have hstable : (prefixWord ++ tailWord_226608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226608).length < 2 ^ (prefixWord ++ tailWord_226608).sum := by decide
  have hdescent : baseEnd_226608 < baseStart_226608 := by decide
  rcases family_descends (prefixWord ++ tailWord_226608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226611 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_226611 : Nat := 118140960795 + 226611 * 2 ^ 59
def prefixEnd_226611 : Nat := 4983230072969 + 3 ^ 40 * 226611 * 2
def baseEnd_226611 : Nat := 103431435196549437440303

theorem tailTrace_226611 : CollatzResearch.WordTrace tailWord_226611 prefixEnd_226611 103431435196549437440303 := by
  unfold tailWord_226611
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265182182034523922679687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5510121454689682615119791 8265182182034523922679687)
  ·
    refine ⟨12397773273051785884019531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8265182182034523922679687 12397773273051785884019531)
    ·
      refine ⟨18596659909577678826029297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12397773273051785884019531 18596659909577678826029297)
      ·
        refine ⟨13947494932183259119521973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18596659909577678826029297 13947494932183259119521973)
        ·
          refine ⟨1307577649892180542455185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13947494932183259119521973 1307577649892180542455185)
          ·
            refine ⟨980683237419135406841389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307577649892180542455185 980683237419135406841389)
            ·
              refine ⟨367756214032175777565521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980683237419135406841389 367756214032175777565521)
              ·
                refine ⟨275817160524131833174141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367756214032175777565521 275817160524131833174141)
                ·
                  refine ⟨103431435196549437440303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275817160524131833174141 103431435196549437440303)
                  ·
                    rfl

theorem cell20_226611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_226611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226611 prefixEnd_226611 := by exact prefixLift 226611
  have htrace : WordTrace (prefixWord ++ tailWord_226611) baseStart_226611 baseEnd_226611 := by
    simpa [prefixWord, tailWord_226611, baseEnd_226611] using wordTrace_append hprefix tailTrace_226611
  have hstable : (prefixWord ++ tailWord_226611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226611).length < 2 ^ (prefixWord ++ tailWord_226611).sum := by decide
  have hdescent : baseEnd_226611 < baseStart_226611 := by decide
  rcases family_descends (prefixWord ++ tailWord_226611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226618 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_226618 : Nat := 118140960795 + 226618 * 2 ^ 59
def prefixEnd_226618 : Nat := 4983230072969 + 3 ^ 40 * 226618 * 2
def baseEnd_226618 : Nat := 103434630187288524206941

theorem tailTrace_226618 : CollatzResearch.WordTrace tailWord_226618 prefixEnd_226618 103434630187288524206941 := by
  unfold tailWord_226618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066359373252291029546127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5510291662006109412123005 2066359373252291029546127)
  ·
    refine ⟨3099539059878436544319191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2066359373252291029546127 3099539059878436544319191)
    ·
      refine ⟨4649308589817654816478787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099539059878436544319191 4649308589817654816478787)
      ·
        refine ⟨6973962884726482224718181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649308589817654816478787 6973962884726482224718181)
        ·
          refine ⟨1307618040886215417134659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6973962884726482224718181 1307618040886215417134659)
          ·
            refine ⟨1961427061329323125701989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307618040886215417134659 1961427061329323125701989)
            ·
              refine ⟨367767573999248086069123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1961427061329323125701989 367767573999248086069123)
              ·
                refine ⟨551651360998872129103685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367767573999248086069123 551651360998872129103685)
                ·
                  refine ⟨103434630187288524206941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551651360998872129103685 103434630187288524206941)
                  ·
                    rfl

theorem cell20_226618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_226618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226618 prefixEnd_226618 := by exact prefixLift 226618
  have htrace : WordTrace (prefixWord ++ tailWord_226618) baseStart_226618 baseEnd_226618 := by
    simpa [prefixWord, tailWord_226618, baseEnd_226618] using wordTrace_append hprefix tailTrace_226618
  have hstable : (prefixWord ++ tailWord_226618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226618).length < 2 ^ (prefixWord ++ tailWord_226618).sum := by decide
  have hdescent : baseEnd_226618 < baseStart_226618 := by decide
  rcases family_descends (prefixWord ++ tailWord_226618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226718 : List Nat := [4, 3, 1, 2, 2, 8]
def baseStart_226718 : Nat := 118140960795 + 226718 * 2 ^ 59
def prefixEnd_226718 : Nat := 4983230072969 + 3 ^ 40 * 226718 * 2
def baseEnd_226718 : Nat := 3832602700449356328637

theorem tailTrace_226718 : CollatzResearch.WordTrace tailWord_226718 prefixEnd_226718 3832602700449356328637 := by
  unfold tailWord_226718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033635599080860149603101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5512723195097920797883205 1033635599080860149603101)
  ·
    refine ⟨387613349655322556101163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1033635599080860149603101 387613349655322556101163)
    ·
      refine ⟨581420024482983834151745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387613349655322556101163 581420024482983834151745)
      ·
        refine ⟨436065018362237875613809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581420024482983834151745 436065018362237875613809)
        ·
          refine ⟨327048763771678406710357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436065018362237875613809 327048763771678406710357)
          ·
            refine ⟨3832602700449356328637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 327048763771678406710357 3832602700449356328637)
            ·
              rfl

theorem cell20_226718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 8].length) (baseStart_226718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226718 prefixEnd_226718 := by exact prefixLift 226718
  have htrace : WordTrace (prefixWord ++ tailWord_226718) baseStart_226718 baseEnd_226718 := by
    simpa [prefixWord, tailWord_226718, baseEnd_226718] using wordTrace_append hprefix tailTrace_226718
  have hstable : (prefixWord ++ tailWord_226718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226718).length < 2 ^ (prefixWord ++ tailWord_226718).sum := by decide
  have hdescent : baseEnd_226718 < baseStart_226718 := by decide
  rcases family_descends (prefixWord ++ tailWord_226718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226784 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_226784 : Nat := 118140960795 + 226784 * 2 ^ 59
def prefixEnd_226784 : Nat := 4983230072969 + 3 ^ 40 * 226784 * 2
def baseEnd_226784 : Nat := 103510397110529724672929

theorem tailTrace_226784 : CollatzResearch.WordTrace tailWord_226784 prefixEnd_226784 103510397110529724672929 := by
  unfold tailWord_226784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135746005203887234363703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5514328006938516312484937 4135746005203887234363703)
  ·
    refine ⟨6203619007805830851545555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4135746005203887234363703 6203619007805830851545555)
    ·
      refine ⟨9305428511708746277318333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6203619007805830851545555 9305428511708746277318333)
      ·
        refine ⟨3489535691890779853994375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9305428511708746277318333 3489535691890779853994375)
        ·
          refine ⟨5234303537836169780991563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3489535691890779853994375 5234303537836169780991563)
          ·
            refine ⟨7851455306754254671487345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234303537836169780991563 7851455306754254671487345)
            ·
              refine ⟨5888591480065691003615509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7851455306754254671487345 5888591480065691003615509)
              ·
                refine ⟨276027725628079265794477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5888591480065691003615509 276027725628079265794477)
                ·
                  refine ⟨103510397110529724672929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276027725628079265794477 103510397110529724672929)
                  ·
                    rfl

theorem cell20_226784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_226784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226784 prefixEnd_226784 := by exact prefixLift 226784
  have htrace : WordTrace (prefixWord ++ tailWord_226784) baseStart_226784 baseEnd_226784 := by
    simpa [prefixWord, tailWord_226784, baseEnd_226784] using wordTrace_append hprefix tailTrace_226784
  have hstable : (prefixWord ++ tailWord_226784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226784).length < 2 ^ (prefixWord ++ tailWord_226784).sum := by decide
  have hdescent : baseEnd_226784 < baseStart_226784 := by decide
  rcases family_descends (prefixWord ++ tailWord_226784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226787 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 2]
def baseStart_226787 : Nat := 118140960795 + 226787 * 2 ^ 59
def prefixEnd_226787 : Nat := 4983230072969 + 3 ^ 40 * 226787 * 2
def baseEnd_226787 : Nat := 103511766392275047572917

theorem tailTrace_226787 : CollatzResearch.WordTrace tailWord_226787 prefixEnd_226787 103511766392275047572917 := by
  unfold tailWord_226787
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271601429396905981086615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5514400952931270654057743 8271601429396905981086615)
  ·
    refine ⟨12407402144095358971629923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8271601429396905981086615 12407402144095358971629923)
    ·
      refine ⟨18611103216143038457444885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12407402144095358971629923 18611103216143038457444885)
      ·
        refine ⟨872395463256704927692729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18611103216143038457444885 872395463256704927692729)
        ·
          refine ⟨654296597442528695769547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872395463256704927692729 654296597442528695769547)
          ·
            refine ⟨981444896163793043654321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654296597442528695769547 981444896163793043654321)
            ·
              refine ⟨736083672122844782740741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981444896163793043654321 736083672122844782740741)
              ·
                refine ⟨138015688523033396763889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736083672122844782740741 138015688523033396763889)
                ·
                  refine ⟨103511766392275047572917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138015688523033396763889 103511766392275047572917)
                  ·
                    rfl

theorem cell20_226787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 2].length) (baseStart_226787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226787 prefixEnd_226787 := by exact prefixLift 226787
  have htrace : WordTrace (prefixWord ++ tailWord_226787) baseStart_226787 baseEnd_226787 := by
    simpa [prefixWord, tailWord_226787, baseEnd_226787] using wordTrace_append hprefix tailTrace_226787
  have hstable : (prefixWord ++ tailWord_226787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226787).length < 2 ^ (prefixWord ++ tailWord_226787).sum := by decide
  have hdescent : baseEnd_226787 < baseStart_226787 := by decide
  rcases family_descends (prefixWord ++ tailWord_226787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226797 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 3]
def baseStart_226797 : Nat := 118140960795 + 226797 * 2 ^ 59
def prefixEnd_226797 : Nat := 4983230072969 + 3 ^ 40 * 226797 * 2
def baseEnd_226797 : Nat := 103516330664759457239543

theorem tailTrace_226797 : CollatzResearch.WordTrace tailWord_226797 prefixEnd_226797 103516330664759457239543 := by
  unfold tailWord_226797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271966159360677688950645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5514644106240451792633763 8271966159360677688950645)
  ·
    refine ⟨775496827440063533339123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8271966159360677688950645 775496827440063533339123)
    ·
      refine ⟨1163245241160095300008685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775496827440063533339123 1163245241160095300008685)
      ·
        refine ⟨436216965435035737503257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1163245241160095300008685 436216965435035737503257)
        ·
          refine ⟨327162724076276803127443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436216965435035737503257 327162724076276803127443)
          ·
            refine ⟨490744086114415204691165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327162724076276803127443 490744086114415204691165)
            ·
              refine ⟨184029032292905701759187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490744086114415204691165 184029032292905701759187)
              ·
                refine ⟨276043548439358552638781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184029032292905701759187 276043548439358552638781)
                ·
                  refine ⟨103516330664759457239543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276043548439358552638781 103516330664759457239543)
                  ·
                    rfl

theorem cell20_226797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_226797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226797 prefixEnd_226797 := by exact prefixLift 226797
  have htrace : WordTrace (prefixWord ++ tailWord_226797) baseStart_226797 baseEnd_226797 := by
    simpa [prefixWord, tailWord_226797, baseEnd_226797] using wordTrace_append hprefix tailTrace_226797
  have hstable : (prefixWord ++ tailWord_226797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226797).length < 2 ^ (prefixWord ++ tailWord_226797).sum := by decide
  have hdescent : baseEnd_226797 < baseStart_226797 := by decide
  rcases family_descends (prefixWord ++ tailWord_226797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226856 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_226856 : Nat := 118140960795 + 226856 * 2 ^ 59
def prefixEnd_226856 : Nat := 4983230072969 + 3 ^ 40 * 226856 * 2
def baseEnd_226856 : Nat := 103543259872417474272635

theorem tailTrace_226856 : CollatzResearch.WordTrace tailWord_226856 prefixEnd_226856 103543259872417474272635 := by
  unfold tailWord_226856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137059033073465382674211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5516078710764620510232281 4137059033073465382674211)
  ·
    refine ⟨6205588549610198074011317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4137059033073465382674211 6205588549610198074011317)
    ·
      refine ⟨581773926525956069438561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6205588549610198074011317 581773926525956069438561)
      ·
        refine ⟨436330444894467052078921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581773926525956069438561 436330444894467052078921)
        ·
          refine ⟨327247833670850289059191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436330444894467052078921 327247833670850289059191)
          ·
            refine ⟨490871750506275433588787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327247833670850289059191 490871750506275433588787)
            ·
              refine ⟨736307625759413150383181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490871750506275433588787 736307625759413150383181)
              ·
                refine ⟨276115359659779931393693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736307625759413150383181 276115359659779931393693)
                ·
                  refine ⟨103543259872417474272635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276115359659779931393693 103543259872417474272635)
                  ·
                    rfl

theorem cell20_226856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_226856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226856 prefixEnd_226856 := by exact prefixLift 226856
  have htrace : WordTrace (prefixWord ++ tailWord_226856) baseStart_226856 baseEnd_226856 := by
    simpa [prefixWord, tailWord_226856, baseEnd_226856] using wordTrace_append hprefix tailTrace_226856
  have hstable : (prefixWord ++ tailWord_226856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226856).length < 2 ^ (prefixWord ++ tailWord_226856).sum := by decide
  have hdescent : baseEnd_226856 < baseStart_226856 := by decide
  rcases family_descends (prefixWord ++ tailWord_226856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226874 : List Nat := [3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_226874 : Nat := 118140960795 + 226874 * 2 ^ 59
def prefixEnd_226874 : Nat := 4983230072969 + 3 ^ 40 * 226874 * 2
def baseEnd_226874 : Nat := 34517158520963137224187

theorem tailTrace_226874 : CollatzResearch.WordTrace tailWord_226874 prefixEnd_226874 34517158520963137224187 := by
  unfold tailWord_226874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068693645020429959875919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5516516386721146559669117 2068693645020429959875919)
  ·
    refine ⟨3103040467530644939813879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2068693645020429959875919 3103040467530644939813879)
    ·
      refine ⟨4654560701295967409720819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103040467530644939813879 4654560701295967409720819)
      ·
        refine ⟨6981841051943951114581229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654560701295967409720819 6981841051943951114581229)
        ·
          refine ⟨2618190394478981667967961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6981841051943951114581229 2618190394478981667967961)
          ·
            refine ⟨1963642795859236250975971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618190394478981667967961 1963642795859236250975971)
            ·
              refine ⟨2945464193788854376463957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963642795859236250975971 2945464193788854376463957)
              ·
                refine ⟨34517158520963137224187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2945464193788854376463957 34517158520963137224187)
                ·
                  rfl

theorem cell20_226874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_226874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226874 prefixEnd_226874 := by exact prefixLift 226874
  have htrace : WordTrace (prefixWord ++ tailWord_226874) baseStart_226874 baseEnd_226874 := by
    simpa [prefixWord, tailWord_226874, baseEnd_226874] using wordTrace_append hprefix tailTrace_226874
  have hstable : (prefixWord ++ tailWord_226874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226874).length < 2 ^ (prefixWord ++ tailWord_226874).sum := by decide
  have hdescent : baseEnd_226874 < baseStart_226874 := by decide
  rcases family_descends (prefixWord ++ tailWord_226874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226908 : List Nat := [2, 2, 4, 1, 2, 3, 1, 5]
def baseStart_226908 : Nat := 118140960795 + 226908 * 2 ^ 59
def prefixEnd_226908 : Nat := 4983230072969 + 3 ^ 40 * 226908 * 2
def baseEnd_226908 : Nat := 34522331363112134846363

theorem tailTrace_226908 : CollatzResearch.WordTrace tailWord_226908 prefixEnd_226908 34522331363112134846363 := by
  unfold tailWord_226908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138007330979271823120689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5517343107972362430827585 4138007330979271823120689)
  ·
    refine ⟨3103505498234453867340517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4138007330979271823120689 3103505498234453867340517)
    ·
      refine ⟨581907280918960100126347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3103505498234453867340517 581907280918960100126347)
      ·
        refine ⟨872860921378440150189521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581907280918960100126347 872860921378440150189521)
        ·
          refine ⟨654645691033830112642141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872860921378440150189521 654645691033830112642141)
          ·
            refine ⟨245492134137686292240803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 654645691033830112642141 245492134137686292240803)
            ·
              refine ⟨368238201206529438361205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245492134137686292240803 368238201206529438361205)
              ·
                refine ⟨34522331363112134846363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368238201206529438361205 34522331363112134846363)
                ·
                  rfl

theorem cell20_226908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_226908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226908 prefixEnd_226908 := by exact prefixLift 226908
  have htrace : WordTrace (prefixWord ++ tailWord_226908) baseStart_226908 baseEnd_226908 := by
    simpa [prefixWord, tailWord_226908, baseEnd_226908] using wordTrace_append hprefix tailTrace_226908
  have hstable : (prefixWord ++ tailWord_226908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226908).length < 2 ^ (prefixWord ++ tailWord_226908).sum := by decide
  have hdescent : baseEnd_226908 < baseStart_226908 := by decide
  rcases family_descends (prefixWord ++ tailWord_226908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226922 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_226922 : Nat := 118140960795 + 226922 * 2 ^ 59
def prefixEnd_226922 : Nat := 4983230072969 + 3 ^ 40 * 226922 * 2
def baseEnd_226922 : Nat := 103573384070814578072365

theorem tailTrace_226922 : CollatzResearch.WordTrace tailWord_226922 prefixEnd_226922 103573384070814578072365 := by
  unfold tailWord_226922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069131320976956009312755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5517683522605216024834013 2069131320976956009312755)
  ·
    refine ⟨3103696981465434013969133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069131320976956009312755 3103696981465434013969133)
    ·
      refine ⟨1163886368049537755238425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3103696981465434013969133 1163886368049537755238425)
      ·
        refine ⟨872914776037153316428819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1163886368049537755238425 872914776037153316428819)
        ·
          refine ⟨1309372164055729974643229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872914776037153316428819 1309372164055729974643229)
          ·
            refine ⟨491014561520898740491211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1309372164055729974643229 491014561520898740491211)
            ·
              refine ⟨736521842281348110736817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491014561520898740491211 736521842281348110736817)
              ·
                refine ⟨552391381711011083052613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736521842281348110736817 552391381711011083052613)
                ·
                  refine ⟨103573384070814578072365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552391381711011083052613 103573384070814578072365)
                  ·
                    rfl

theorem cell20_226922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_226922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226922 prefixEnd_226922 := by exact prefixLift 226922
  have htrace : WordTrace (prefixWord ++ tailWord_226922) baseStart_226922 baseEnd_226922 := by
    simpa [prefixWord, tailWord_226922, baseEnd_226922] using wordTrace_append hprefix tailTrace_226922
  have hstable : (prefixWord ++ tailWord_226922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226922).length < 2 ^ (prefixWord ++ tailWord_226922).sum := by decide
  have hdescent : baseEnd_226922 < baseStart_226922 := by decide
  rcases family_descends (prefixWord ++ tailWord_226922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226981 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_226981 : Nat := 118140960795 + 226981 * 2 ^ 59
def prefixEnd_226981 : Nat := 4983230072969 + 3 ^ 40 * 226981 * 2
def baseEnd_226981 : Nat := 103600313278472595105457

theorem tailTrace_226981 : CollatzResearch.WordTrace tailWord_226981 prefixEnd_226981 103600313278472595105457 := by
  unfold tailWord_226981
  simp only [CollatzResearch.WordTrace]
  refine ⟨8278677190694077113648797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5519118127129384742432531 8278677190694077113648797)
  ·
    refine ⟨3104503946510278917618299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8278677190694077113648797 3104503946510278917618299)
    ·
      refine ⟨4656755919765418376427449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3104503946510278917618299 4656755919765418376427449)
      ·
        refine ⟨3492566939824063782320587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4656755919765418376427449 3492566939824063782320587)
        ·
          refine ⟨5238850409736095673480881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492566939824063782320587 5238850409736095673480881)
          ·
            refine ⟨3929137807302071755110661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238850409736095673480881 3929137807302071755110661)
            ·
              refine ⟨736713338869138454083249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3929137807302071755110661 736713338869138454083249)
              ·
                refine ⟨552535004151853840562437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736713338869138454083249 552535004151853840562437)
                ·
                  refine ⟨103600313278472595105457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552535004151853840562437 103600313278472595105457)
                  ·
                    rfl

theorem cell20_226981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_226981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226981 prefixEnd_226981 := by exact prefixLift 226981
  have htrace : WordTrace (prefixWord ++ tailWord_226981) baseStart_226981 baseEnd_226981 := by
    simpa [prefixWord, tailWord_226981, baseEnd_226981] using wordTrace_append hprefix tailTrace_226981
  have hstable : (prefixWord ++ tailWord_226981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226981).length < 2 ^ (prefixWord ++ tailWord_226981).sum := by decide
  have hdescent : baseEnd_226981 < baseStart_226981 := by decide
  rcases family_descends (prefixWord ++ tailWord_226981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226990 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_226990 : Nat := 118140960795 + 226990 * 2 ^ 59
def prefixEnd_226990 : Nat := 4983230072969 + 3 ^ 40 * 226990 * 2
def baseEnd_226990 : Nat := 103604421123708563805421

theorem tailTrace_226990 : CollatzResearch.WordTrace tailWord_226990 prefixEnd_226990 103604421123708563805421 := by
  unfold tailWord_226990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034875680957683956340803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5519336965107647767150949 1034875680957683956340803)
  ·
    refine ⟨1552313521436525934511205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034875680957683956340803 1552313521436525934511205)
    ·
      refine ⟨291058785269348612720851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1552313521436525934511205 291058785269348612720851)
      ·
        refine ⟨436588177904022919081277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291058785269348612720851 436588177904022919081277)
        ·
          refine ⟨163720566714008594655479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436588177904022919081277 163720566714008594655479)
          ·
            refine ⟨245580850071012891983219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163720566714008594655479 245580850071012891983219)
            ·
              refine ⟨368371275106519337974829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245580850071012891983219 368371275106519337974829)
              ·
                refine ⟨138139228164944751740561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368371275106519337974829 138139228164944751740561)
                ·
                  refine ⟨103604421123708563805421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138139228164944751740561 103604421123708563805421)
                  ·
                    rfl

theorem cell20_226990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_226990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226990 prefixEnd_226990 := by exact prefixLift 226990
  have htrace : WordTrace (prefixWord ++ tailWord_226990) baseStart_226990 baseEnd_226990 := by
    simpa [prefixWord, tailWord_226990, baseEnd_226990] using wordTrace_append hprefix tailTrace_226990
  have hstable : (prefixWord ++ tailWord_226990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226990).length < 2 ^ (prefixWord ++ tailWord_226990).sum := by decide
  have hdescent : baseEnd_226990 < baseStart_226990 := by decide
  rcases family_descends (prefixWord ++ tailWord_226990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226995 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_226995 : Nat := 118140960795 + 226995 * 2 ^ 59
def prefixEnd_226995 : Nat := 4983230072969 + 3 ^ 40 * 226995 * 2
def baseEnd_226995 : Nat := 103606703259950768638733

theorem tailTrace_226995 : CollatzResearch.WordTrace tailWord_226995 prefixEnd_226995 103606703259950768638733 := by
  unfold tailWord_226995
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279187812643357504658439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5519458541762238336438959 8279187812643357504658439)
  ·
    refine ⟨12418781718965036256987659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8279187812643357504658439 12418781718965036256987659)
    ·
      refine ⟨18628172578447554385481489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12418781718965036256987659 18628172578447554385481489)
      ·
        refine ⟨13971129433835665789111117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18628172578447554385481489 13971129433835665789111117)
        ·
          refine ⟨5239173537688374670916669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13971129433835665789111117 5239173537688374670916669)
          ·
            refine ⟨1964690076633140501593751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5239173537688374670916669 1964690076633140501593751)
            ·
              refine ⟨2947035114949710752390627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964690076633140501593751 2947035114949710752390627)
              ·
                refine ⟨4420552672424566128585941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947035114949710752390627 4420552672424566128585941)
                ·
                  refine ⟨103606703259950768638733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4420552672424566128585941 103606703259950768638733)
                  ·
                    rfl

theorem cell20_226995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_226995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_226995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_226995 prefixEnd_226995 := by exact prefixLift 226995
  have htrace : WordTrace (prefixWord ++ tailWord_226995) baseStart_226995 baseEnd_226995 := by
    simpa [prefixWord, tailWord_226995, baseEnd_226995] using wordTrace_append hprefix tailTrace_226995
  have hstable : (prefixWord ++ tailWord_226995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226995).length < 2 ^ (prefixWord ++ tailWord_226995).sum := by decide
  have hdescent : baseEnd_226995 < baseStart_226995 := by decide
  rcases family_descends (prefixWord ++ tailWord_226995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227012 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_227012 : Nat := 118140960795 + 227012 * 2 ^ 59
def prefixEnd_227012 : Nat := 4983230072969 + 3 ^ 40 * 227012 * 2
def baseEnd_227012 : Nat := 103614462523174265071997

theorem tailTrace_227012 : CollatzResearch.WordTrace tailWord_227012 prefixEnd_227012 103614462523174265071997 := by
  unfold tailWord_227012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139903926790884704013645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5519871902387846272018193 4139903926790884704013645)
  ·
    refine ⟨1552463972546581764005117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4139903926790884704013645 1552463972546581764005117)
    ·
      refine ⟨582173989704968161501919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1552463972546581764005117 582173989704968161501919)
      ·
        refine ⟨873260984557452242252879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582173989704968161501919 873260984557452242252879)
        ·
          refine ⟨1309891476836178363379319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873260984557452242252879 1309891476836178363379319)
          ·
            refine ⟨1964837215254267545068979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309891476836178363379319 1964837215254267545068979)
            ·
              refine ⟨2947255822881401317603469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964837215254267545068979 2947255822881401317603469)
              ·
                refine ⟨1105220933580525494101301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2947255822881401317603469 1105220933580525494101301)
                ·
                  refine ⟨103614462523174265071997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1105220933580525494101301 103614462523174265071997)
                  ·
                    rfl

theorem cell20_227012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_227012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227012 prefixEnd_227012 := by exact prefixLift 227012
  have htrace : WordTrace (prefixWord ++ tailWord_227012) baseStart_227012 baseEnd_227012 := by
    simpa [prefixWord, tailWord_227012, baseEnd_227012] using wordTrace_append hprefix tailTrace_227012
  have hstable : (prefixWord ++ tailWord_227012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227012).length < 2 ^ (prefixWord ++ tailWord_227012).sum := by decide
  have hdescent : baseEnd_227012 < baseStart_227012 := by decide
  rcases family_descends (prefixWord ++ tailWord_227012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227015 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 2]
def baseStart_227015 : Nat := 118140960795 + 227015 * 2 ^ 59
def prefixEnd_227015 : Nat := 4983230072969 + 3 ^ 40 * 227015 * 2
def baseEnd_227015 : Nat := 103615831804919587971985

theorem tailTrace_227015 : CollatzResearch.WordTrace tailWord_227015 prefixEnd_227015 103615831804919587971985 := by
  unfold tailWord_227015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279917272570900920386499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5519944848380600613590999 8279917272570900920386499)
  ·
    refine ⟨12419875908856351380579749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8279917272570900920386499 12419875908856351380579749)
    ·
      refine ⟨2328726732910565883858703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12419875908856351380579749 2328726732910565883858703)
      ·
        refine ⟨3493090099365848825788055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328726732910565883858703 3493090099365848825788055)
        ·
          refine ⟨5239635149048773238682083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493090099365848825788055 5239635149048773238682083)
          ·
            refine ⟨7859452723573159858023125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239635149048773238682083 7859452723573159858023125)
            ·
              refine ⟨184205923208745934172417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7859452723573159858023125 184205923208745934172417)
              ·
                refine ⟨138154442406559450629313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184205923208745934172417 138154442406559450629313)
                ·
                  refine ⟨103615831804919587971985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138154442406559450629313 103615831804919587971985)
                  ·
                    rfl

theorem cell20_227015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 2].length) (baseStart_227015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227015 prefixEnd_227015 := by exact prefixLift 227015
  have htrace : WordTrace (prefixWord ++ tailWord_227015) baseStart_227015 baseEnd_227015 := by
    simpa [prefixWord, tailWord_227015, baseEnd_227015] using wordTrace_append hprefix tailTrace_227015
  have hstable : (prefixWord ++ tailWord_227015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227015).length < 2 ^ (prefixWord ++ tailWord_227015).sum := by decide
  have hdescent : baseEnd_227015 < baseStart_227015 := by decide
  rcases family_descends (prefixWord ++ tailWord_227015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227060 : List Nat := [2, 6, 1, 1, 1, 9]
def baseStart_227060 : Nat := 118140960795 + 227060 * 2 ^ 59
def prefixEnd_227060 : Nat := 4983230072969 + 3 ^ 40 * 227060 * 2
def baseEnd_227060 : Nat := 3838384112262941906363

theorem tailTrace_227060 : CollatzResearch.WordTrace tailWord_227060 prefixEnd_227060 3838384112262941906363 := by
  unfold tailWord_227060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140779278703936802887317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5521039038271915737183089 4140779278703936802887317)
  ·
    refine ⟨194099028689247037635343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4140779278703936802887317 194099028689247037635343)
    ·
      refine ⟨291148543033870556453015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194099028689247037635343 291148543033870556453015)
      ·
        refine ⟨436722814550805834679523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291148543033870556453015 436722814550805834679523)
        ·
          refine ⟨655084221826208752019285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436722814550805834679523 655084221826208752019285)
          ·
            refine ⟨3838384112262941906363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 655084221826208752019285 3838384112262941906363)
            ·
              rfl

theorem cell20_227060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 9].length) (baseStart_227060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227060 prefixEnd_227060 := by exact prefixLift 227060
  have htrace : WordTrace (prefixWord ++ tailWord_227060) baseStart_227060 baseEnd_227060 := by
    simpa [prefixWord, tailWord_227060, baseEnd_227060] using wordTrace_append hprefix tailTrace_227060
  have hstable : (prefixWord ++ tailWord_227060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227060).length < 2 ^ (prefixWord ++ tailWord_227060).sum := by decide
  have hdescent : baseEnd_227060 < baseStart_227060 := by decide
  rcases family_descends (prefixWord ++ tailWord_227060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227070 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_227070 : Nat := 118140960795 + 227070 * 2 ^ 59
def prefixEnd_227070 : Nat := 4983230072969 + 3 ^ 40 * 227070 * 2
def baseEnd_227070 : Nat := 103640935303583841138427

theorem tailTrace_227070 : CollatzResearch.WordTrace tailWord_227070 prefixEnd_227070 103640935303583841138427 := by
  unfold tailWord_227070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035240410921455664204833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5521282191581096875759109 1035240410921455664204833)
  ·
    refine ⟨776430308191091748153625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1035240410921455664204833 776430308191091748153625)
    ·
      refine ⟨582322731143318811115219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776430308191091748153625 582322731143318811115219)
      ·
        refine ⟨873484096714978216672829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582322731143318811115219 873484096714978216672829)
        ·
          refine ⟨327556536268116831252311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 873484096714978216672829 327556536268116831252311)
          ·
            refine ⟨491334804402175246878467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327556536268116831252311 491334804402175246878467)
            ·
              refine ⟨737002206603262870317701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491334804402175246878467 737002206603262870317701)
              ·
                refine ⟨138187913738111788184569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737002206603262870317701 138187913738111788184569)
                ·
                  refine ⟨103640935303583841138427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138187913738111788184569 103640935303583841138427)
                  ·
                    rfl

theorem cell20_227070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_227070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227070 prefixEnd_227070 := by exact prefixLift 227070
  have htrace : WordTrace (prefixWord ++ tailWord_227070) baseStart_227070 baseEnd_227070 := by
    simpa [prefixWord, tailWord_227070, baseEnd_227070] using wordTrace_append hprefix tailTrace_227070
  have hstable : (prefixWord ++ tailWord_227070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227070).length < 2 ^ (prefixWord ++ tailWord_227070).sum := by decide
  have hdescent : baseEnd_227070 < baseStart_227070 := by decide
  rcases family_descends (prefixWord ++ tailWord_227070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227071 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_227071 : Nat := 118140960795 + 227071 * 2 ^ 59
def prefixEnd_227071 : Nat := 4983230072969 + 3 ^ 40 * 227071 * 2
def baseEnd_227071 : Nat := 103641391730832282105089

theorem tailTrace_227071 : CollatzResearch.WordTrace tailWord_227071 prefixEnd_227071 103641391730832282105089 := by
  unfold tailWord_227071
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281959760368022484425067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5521306506912014989616711 8281959760368022484425067)
  ·
    refine ⟨12422939640552033726637601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8281959760368022484425067 12422939640552033726637601)
    ·
      refine ⟨9317204730414025294978201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12422939640552033726637601 9317204730414025294978201)
      ·
        refine ⟨6987903547810518971233651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9317204730414025294978201 6987903547810518971233651)
        ·
          refine ⟨10481855321715778456850477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987903547810518971233651 10481855321715778456850477)
          ·
            refine ⟨3930695745643416921318929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10481855321715778456850477 3930695745643416921318929)
            ·
              refine ⟨2948021809232562690989197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930695745643416921318929 2948021809232562690989197)
              ·
                refine ⟨1105508178462211009120949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2948021809232562690989197 1105508178462211009120949)
                ·
                  refine ⟨103641391730832282105089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1105508178462211009120949 103641391730832282105089)
                  ·
                    rfl

theorem cell20_227071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_227071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227071 prefixEnd_227071 := by exact prefixLift 227071
  have htrace : WordTrace (prefixWord ++ tailWord_227071) baseStart_227071 baseEnd_227071 := by
    simpa [prefixWord, tailWord_227071, baseEnd_227071] using wordTrace_append hprefix tailTrace_227071
  have hstable : (prefixWord ++ tailWord_227071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227071).length < 2 ^ (prefixWord ++ tailWord_227071).sum := by decide
  have hdescent : baseEnd_227071 < baseStart_227071 := by decide
  rcases family_descends (prefixWord ++ tailWord_227071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227074 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_227074 : Nat := 118140960795 + 227074 * 2 ^ 59
def prefixEnd_227074 : Nat := 4983230072969 + 3 ^ 40 * 227074 * 2
def baseEnd_227074 : Nat := 103642761012577605005077

theorem tailTrace_227074 : CollatzResearch.WordTrace tailWord_227074 prefixEnd_227074 103642761012577605005077 := by
  unfold tailWord_227074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070517294839288499196069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5521379452904769331189517 2070517294839288499196069)
  ·
    refine ⟨388221992782366593599263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2070517294839288499196069 388221992782366593599263)
    ·
      refine ⟨582332989173549890398895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388221992782366593599263 582332989173549890398895)
      ·
        refine ⟨873499483760324835598343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582332989173549890398895 873499483760324835598343)
        ·
          refine ⟨1310249225640487253397515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873499483760324835598343 1310249225640487253397515)
          ·
            refine ⟨1965373838460730880096273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310249225640487253397515 1965373838460730880096273)
            ·
              refine ⟨1474030378845548160072205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965373838460730880096273 1474030378845548160072205)
              ·
                refine ⟨552761392067080560027077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474030378845548160072205 552761392067080560027077)
                ·
                  refine ⟨103642761012577605005077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552761392067080560027077 103642761012577605005077)
                  ·
                    rfl

theorem cell20_227074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_227074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227074 prefixEnd_227074 := by exact prefixLift 227074
  have htrace : WordTrace (prefixWord ++ tailWord_227074) baseStart_227074 baseEnd_227074 := by
    simpa [prefixWord, tailWord_227074, baseEnd_227074] using wordTrace_append hprefix tailTrace_227074
  have hstable : (prefixWord ++ tailWord_227074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227074).length < 2 ^ (prefixWord ++ tailWord_227074).sum := by decide
  have hdescent : baseEnd_227074 < baseStart_227074 := by decide
  rcases family_descends (prefixWord ++ tailWord_227074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227095 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_227095 : Nat := 118140960795 + 227095 * 2 ^ 59
def prefixEnd_227095 : Nat := 4983230072969 + 3 ^ 40 * 227095 * 2
def baseEnd_227095 : Nat := 103652345984794865304991

theorem tailTrace_227095 : CollatzResearch.WordTrace tailWord_227095 prefixEnd_227095 103652345984794865304991 := by
  unfold tailWord_227095
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282835112281074583298739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5521890074854049722199159 8282835112281074583298739)
  ·
    refine ⟨12424252668421611874948109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8282835112281074583298739 12424252668421611874948109)
    ·
      refine ⟨4659094750658104453105541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12424252668421611874948109 4659094750658104453105541)
      ·
        refine ⟨873580265748394584957289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4659094750658104453105541 873580265748394584957289)
        ·
          refine ⟨655185199311295938717967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873580265748394584957289 655185199311295938717967)
          ·
            refine ⟨982777798966943908076951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655185199311295938717967 982777798966943908076951)
            ·
              refine ⟨1474166698450415862115427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982777798966943908076951 1474166698450415862115427)
              ·
                refine ⟨2211250047675623793173141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474166698450415862115427 2211250047675623793173141)
                ·
                  refine ⟨103652345984794865304991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2211250047675623793173141 103652345984794865304991)
                  ·
                    rfl

theorem cell20_227095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_227095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227095 prefixEnd_227095 := by exact prefixLift 227095
  have htrace : WordTrace (prefixWord ++ tailWord_227095) baseStart_227095 baseEnd_227095 := by
    simpa [prefixWord, tailWord_227095, baseEnd_227095] using wordTrace_append hprefix tailTrace_227095
  have hstable : (prefixWord ++ tailWord_227095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227095).length < 2 ^ (prefixWord ++ tailWord_227095).sum := by decide
  have hdescent : baseEnd_227095 < baseStart_227095 := by decide
  rcases family_descends (prefixWord ++ tailWord_227095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227129 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 4]
def baseStart_227129 : Nat := 118140960795 + 227129 * 2 ^ 59
def prefixEnd_227129 : Nat := 4983230072969 + 3 ^ 40 * 227129 * 2
def baseEnd_227129 : Nat := 103667864511241858171519

theorem tailTrace_227129 : CollatzResearch.WordTrace tailWord_227129 prefixEnd_227129 103667864511241858171519 := by
  unfold tailWord_227129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284075194157898390036441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5522716796105265593357627 8284075194157898390036441)
  ·
    refine ⟨6213056395618423792527331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8284075194157898390036441 6213056395618423792527331)
    ·
      refine ⟨9319584593427635688790997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6213056395618423792527331 9319584593427635688790997)
      ·
        refine ⟨218427763908460211456039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9319584593427635688790997 218427763908460211456039)
        ·
          refine ⟨327641645862690317184059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218427763908460211456039 327641645862690317184059)
          ·
            refine ⟨491462468794035475776089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327641645862690317184059 491462468794035475776089)
            ·
              refine ⟨368596851595526606832067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491462468794035475776089 368596851595526606832067)
              ·
                refine ⟨552895277393289910248101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368596851595526606832067 552895277393289910248101)
                ·
                  refine ⟨103667864511241858171519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552895277393289910248101 103667864511241858171519)
                  ·
                    rfl

theorem cell20_227129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_227129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227129 prefixEnd_227129 := by exact prefixLift 227129
  have htrace : WordTrace (prefixWord ++ tailWord_227129) baseStart_227129 baseEnd_227129 := by
    simpa [prefixWord, tailWord_227129, baseEnd_227129] using wordTrace_append hprefix tailTrace_227129
  have hstable : (prefixWord ++ tailWord_227129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227129).length < 2 ^ (prefixWord ++ tailWord_227129).sum := by decide
  have hdescent : baseEnd_227129 < baseStart_227129 := by decide
  rcases family_descends (prefixWord ++ tailWord_227129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227157 : List Nat := [1, 3, 2, 2, 2, 2, 4, 4]
def baseStart_227157 : Nat := 118140960795 + 227157 * 2 ^ 59
def prefixEnd_227157 : Nat := 4983230072969 + 3 ^ 40 * 227157 * 2
def baseEnd_227157 : Nat := 34560214824732735079357

theorem tailTrace_227157 : CollatzResearch.WordTrace tailWord_227157 prefixEnd_227157 34560214824732735079357 := by
  unfold tailWord_227157
  simp only [CollatzResearch.WordTrace]
  refine ⟨8285096438056459172055725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5523397625370972781370483 8285096438056459172055725)
  ·
    refine ⟨3106911164271172189520897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8285096438056459172055725 3106911164271172189520897)
    ·
      refine ⟨2330183373203379142140673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3106911164271172189520897 2330183373203379142140673)
      ·
        refine ⟨1747637529902534356605505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330183373203379142140673 1747637529902534356605505)
        ·
          refine ⟨1310728147426900767454129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1747637529902534356605505 1310728147426900767454129)
          ·
            refine ⟨983046110570175575590597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1310728147426900767454129 983046110570175575590597)
            ·
              refine ⟨184321145731907920423237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 983046110570175575590597 184321145731907920423237)
              ·
                refine ⟨34560214824732735079357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184321145731907920423237 34560214824732735079357)
                ·
                  rfl

theorem cell20_227157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_227157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227157 prefixEnd_227157 := by exact prefixLift 227157
  have htrace : WordTrace (prefixWord ++ tailWord_227157) baseStart_227157 baseEnd_227157 := by
    simpa [prefixWord, tailWord_227157, baseEnd_227157] using wordTrace_append hprefix tailTrace_227157
  have hstable : (prefixWord ++ tailWord_227157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227157).length < 2 ^ (prefixWord ++ tailWord_227157).sum := by decide
  have hdescent : baseEnd_227157 < baseStart_227157 := by decide
  rcases family_descends (prefixWord ++ tailWord_227157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227167 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 2]
def baseStart_227167 : Nat := 118140960795 + 227167 * 2 ^ 59
def prefixEnd_227167 : Nat := 4983230072969 + 3 ^ 40 * 227167 * 2
def baseEnd_227167 : Nat := 103685208746682614904697

theorem tailTrace_227167 : CollatzResearch.WordTrace tailWord_227167 prefixEnd_227167 103685208746682614904697 := by
  unfold tailWord_227167
  simp only [CollatzResearch.WordTrace]
  refine ⟨8285461168020230879919755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5523640778680153919946503 8285461168020230879919755)
  ·
    refine ⟨12428191752030346319879633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8285461168020230879919755 12428191752030346319879633)
    ·
      refine ⟨9321143814022759739909725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12428191752030346319879633 9321143814022759739909725)
      ·
        refine ⟨3495428930258534902466147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9321143814022759739909725 3495428930258534902466147)
        ·
          refine ⟨5243143395387802353699221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495428930258534902466147 5243143395387802353699221)
          ·
            refine ⟨245772346658803235329651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5243143395387802353699221 245772346658803235329651)
            ·
              refine ⟨368658519988204852994477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245772346658803235329651 368658519988204852994477)
              ·
                refine ⟨138246944995576819872929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368658519988204852994477 138246944995576819872929)
                ·
                  refine ⟨103685208746682614904697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138246944995576819872929 103685208746682614904697)
                  ·
                    rfl

theorem cell20_227167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 2].length) (baseStart_227167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227167 prefixEnd_227167 := by exact prefixLift 227167
  have htrace : WordTrace (prefixWord ++ tailWord_227167) baseStart_227167 baseEnd_227167 := by
    simpa [prefixWord, tailWord_227167, baseEnd_227167] using wordTrace_append hprefix tailTrace_227167
  have hstable : (prefixWord ++ tailWord_227167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227167).length < 2 ^ (prefixWord ++ tailWord_227167).sum := by decide
  have hdescent : baseEnd_227167 < baseStart_227167 := by decide
  rcases family_descends (prefixWord ++ tailWord_227167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227185 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_227185 : Nat := 118140960795 + 227185 * 2 ^ 59
def prefixEnd_227185 : Nat := 4983230072969 + 3 ^ 40 * 227185 * 2
def baseEnd_227185 : Nat := 103693424437154552304623

theorem tailTrace_227185 : CollatzResearch.WordTrace tailWord_227185 prefixEnd_227185 103693424437154552304623 := by
  unfold tailWord_227185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286117681955019954075009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5524078454636679969383339 8286117681955019954075009)
  ·
    refine ⟨6214588261466264965556257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8286117681955019954075009 6214588261466264965556257)
    ·
      refine ⟨4660941196099698724167193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6214588261466264965556257 4660941196099698724167193)
      ·
        refine ⟨3495705897074774043125395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4660941196099698724167193 3495705897074774043125395)
        ·
          refine ⟨5243558845612161064688093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495705897074774043125395 5243558845612161064688093)
          ·
            refine ⟨1966334567104560399258035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5243558845612161064688093 1966334567104560399258035)
            ·
              refine ⟨2949501850656840598887053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966334567104560399258035 2949501850656840598887053)
              ·
                refine ⟨1106063193996315224582645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2949501850656840598887053 1106063193996315224582645)
                ·
                  refine ⟨103693424437154552304623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106063193996315224582645 103693424437154552304623)
                  ·
                    rfl

theorem cell20_227185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_227185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227185 prefixEnd_227185 := by exact prefixLift 227185
  have htrace : WordTrace (prefixWord ++ tailWord_227185) baseStart_227185 baseEnd_227185 := by
    simpa [prefixWord, tailWord_227185, baseEnd_227185] using wordTrace_append hprefix tailTrace_227185
  have hstable : (prefixWord ++ tailWord_227185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227185).length < 2 ^ (prefixWord ++ tailWord_227185).sum := by decide
  have hdescent : baseEnd_227185 < baseStart_227185 := by decide
  rcases family_descends (prefixWord ++ tailWord_227185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227198 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_227198 : Nat := 118140960795 + 227198 * 2 ^ 59
def prefixEnd_227198 : Nat := 4983230072969 + 3 ^ 40 * 227198 * 2
def baseEnd_227198 : Nat := 103699357991384284871237

theorem tailTrace_227198 : CollatzResearch.WordTrace tailWord_227198 prefixEnd_227198 103699357991384284871237 := by
  unfold tailWord_227198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035823978863490396787281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5524394553938615449532165 1035823978863490396787281)
  ·
    refine ⟨776867984147617797590461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1035823978863490396787281 776867984147617797590461)
    ·
      refine ⟨291325494055356674096423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 776867984147617797590461 291325494055356674096423)
      ·
        refine ⟨436988241083035011144635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291325494055356674096423 436988241083035011144635)
        ·
          refine ⟨655482361624552516716953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436988241083035011144635 655482361624552516716953)
          ·
            refine ⟨491611771218414387537715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655482361624552516716953 491611771218414387537715)
            ·
              refine ⟨737417656827621581306573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491611771218414387537715 737417656827621581306573)
              ·
                refine ⟨276531621310358092989965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737417656827621581306573 276531621310358092989965)
                ·
                  refine ⟨103699357991384284871237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276531621310358092989965 103699357991384284871237)
                  ·
                    rfl

theorem cell20_227198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_227198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227198 prefixEnd_227198 := by exact prefixLift 227198
  have htrace : WordTrace (prefixWord ++ tailWord_227198) baseStart_227198 baseEnd_227198 := by
    simpa [prefixWord, tailWord_227198, baseEnd_227198] using wordTrace_append hprefix tailTrace_227198
  have hstable : (prefixWord ++ tailWord_227198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227198).length < 2 ^ (prefixWord ++ tailWord_227198).sum := by decide
  have hdescent : baseEnd_227198 < baseStart_227198 := by decide
  rcases family_descends (prefixWord ++ tailWord_227198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227233 : List Nat := [1, 2, 3, 4, 3, 7]
def baseStart_227233 : Nat := 118140960795 + 227233 * 2 ^ 59
def prefixEnd_227233 : Nat := 4983230072969 + 3 ^ 40 * 227233 * 2
def baseEnd_227233 : Nat := 3841308627595545137201

theorem tailTrace_227233 : CollatzResearch.WordTrace tailWord_227233 prefixEnd_227233 3841308627595545137201 := by
  unfold tailWord_227233
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287868385781124151822353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5525245590520749434548235 8287868385781124151822353)
  ·
    refine ⟨6215901289335843113866765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8287868385781124151822353 6215901289335843113866765)
    ·
      refine ⟨2330962983500941167700037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6215901289335843113866765 2330962983500941167700037)
      ·
        refine ⟨437055559406426468943757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2330962983500941167700037 437055559406426468943757)
        ·
          refine ⟨163895834777409925853909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437055559406426468943757 163895834777409925853909)
          ·
            refine ⟨3841308627595545137201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 163895834777409925853909 3841308627595545137201)
            ·
              rfl

theorem cell20_227233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 7].length) (baseStart_227233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227233 prefixEnd_227233 := by exact prefixLift 227233
  have htrace : WordTrace (prefixWord ++ tailWord_227233) baseStart_227233 baseEnd_227233 := by
    simpa [prefixWord, tailWord_227233, baseEnd_227233] using wordTrace_append hprefix tailTrace_227233
  have hstable : (prefixWord ++ tailWord_227233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227233).length < 2 ^ (prefixWord ++ tailWord_227233).sum := by decide
  have hdescent : baseEnd_227233 < baseStart_227233 := by decide
  rcases family_descends (prefixWord ++ tailWord_227233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227246 : List Nat := [4, 1, 5, 1, 1, 2, 1, 5]
def baseStart_227246 : Nat := 118140960795 + 227246 * 2 ^ 59
def prefixEnd_227246 : Nat := 4983230072969 + 3 ^ 40 * 227246 * 2
def baseEnd_227246 : Nat := 34573755499769817090347

theorem tailTrace_227246 : CollatzResearch.WordTrace tailWord_227246 prefixEnd_227246 34573755499769817090347 := by
  unfold tailWord_227246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036042816841753421505699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5525561689822684914697061 1036042816841753421505699)
  ·
    refine ⟨1554064225262630132258549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1036042816841753421505699 1554064225262630132258549)
    ·
      refine ⟨145693521118371574899239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1554064225262630132258549 145693521118371574899239)
      ·
        refine ⟨218540281677557362348859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145693521118371574899239 218540281677557362348859)
        ·
          refine ⟨327810422516336043523289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218540281677557362348859 327810422516336043523289)
          ·
            refine ⟨245857816887252032642467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327810422516336043523289 245857816887252032642467)
            ·
              refine ⟨368786725330878048963701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245857816887252032642467 368786725330878048963701)
              ·
                refine ⟨34573755499769817090347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368786725330878048963701 34573755499769817090347)
                ·
                  rfl

theorem cell20_227246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_227246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227246 prefixEnd_227246 := by exact prefixLift 227246
  have htrace : WordTrace (prefixWord ++ tailWord_227246) baseStart_227246 baseEnd_227246 := by
    simpa [prefixWord, tailWord_227246, baseEnd_227246] using wordTrace_append hprefix tailTrace_227246
  have hstable : (prefixWord ++ tailWord_227246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227246).length < 2 ^ (prefixWord ++ tailWord_227246).sum := by decide
  have hdescent : baseEnd_227246 < baseStart_227246 := by decide
  rcases family_descends (prefixWord ++ tailWord_227246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227295 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 3]
def baseStart_227295 : Nat := 118140960795 + 227295 * 2 ^ 59
def prefixEnd_227295 : Nat := 4983230072969 + 3 ^ 40 * 227295 * 2
def baseEnd_227295 : Nat := 103743631434483058637507

theorem tailTrace_227295 : CollatzResearch.WordTrace tailWord_227295 prefixEnd_227295 103743631434483058637507 := by
  unfold tailWord_227295
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290129711556508740579339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5526753141037672493719559 8290129711556508740579339)
  ·
    refine ⟨12435194567334763110869009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290129711556508740579339 12435194567334763110869009)
    ·
      refine ⟨9326395925501072333151757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12435194567334763110869009 9326395925501072333151757)
      ·
        refine ⟨3497398472062902124931909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9326395925501072333151757 3497398472062902124931909)
        ·
          refine ⟨655762213511794148424733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3497398472062902124931909 655762213511794148424733)
          ·
            refine ⟨245910830066922805659275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655762213511794148424733 245910830066922805659275)
            ·
              refine ⟨368866245100384208488913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245910830066922805659275 368866245100384208488913)
              ·
                refine ⟨276649683825288156366685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368866245100384208488913 276649683825288156366685)
                ·
                  refine ⟨103743631434483058637507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276649683825288156366685 103743631434483058637507)
                  ·
                    rfl

theorem cell20_227295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_227295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227295 prefixEnd_227295 := by exact prefixLift 227295
  have htrace : WordTrace (prefixWord ++ tailWord_227295) baseStart_227295 baseEnd_227295 := by
    simpa [prefixWord, tailWord_227295, baseEnd_227295] using wordTrace_append hprefix tailTrace_227295
  have hstable : (prefixWord ++ tailWord_227295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227295).length < 2 ^ (prefixWord ++ tailWord_227295).sum := by decide
  have hdescent : baseEnd_227295 < baseStart_227295 := by decide
  rcases family_descends (prefixWord ++ tailWord_227295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227326 : List Nat := [4, 2, 2, 2, 1, 1, 4, 4]
def baseStart_227326 : Nat := 118140960795 + 227326 * 2 ^ 59
def prefixEnd_227326 : Nat := 4983230072969 + 3 ^ 40 * 227326 * 2
def baseEnd_227326 : Nat := 34585926893061576201349

theorem tailTrace_227326 : CollatzResearch.WordTrace tailWord_227326 prefixEnd_227326 34585926893061576201349 := by
  unfold tailWord_227326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036407546805525129369729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5527506916296134023305221 1036407546805525129369729)
  ·
    refine ⟨777305660104143847027297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1036407546805525129369729 777305660104143847027297)
    ·
      refine ⟨582979245078107885270473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 777305660104143847027297 582979245078107885270473)
      ·
        refine ⟨437234433808580913952855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582979245078107885270473 437234433808580913952855)
        ·
          refine ⟨655851650712871370929283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437234433808580913952855 655851650712871370929283)
          ·
            refine ⟨983777476069307056393925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655851650712871370929283 983777476069307056393925)
            ·
              refine ⟨184458276762995073073861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 983777476069307056393925 184458276762995073073861)
              ·
                refine ⟨34585926893061576201349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184458276762995073073861 34585926893061576201349)
                ·
                  rfl

theorem cell20_227326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_227326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227326 prefixEnd_227326 := by exact prefixLift 227326
  have htrace : WordTrace (prefixWord ++ tailWord_227326) baseStart_227326 baseEnd_227326 := by
    simpa [prefixWord, tailWord_227326, baseEnd_227326] using wordTrace_append hprefix tailTrace_227326
  have hstable : (prefixWord ++ tailWord_227326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227326).length < 2 ^ (prefixWord ++ tailWord_227326).sum := by decide
  have hdescent : baseEnd_227326 < baseStart_227326 := by decide
  rcases family_descends (prefixWord ++ tailWord_227326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227367 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 3]
def baseStart_227367 : Nat := 118140960795 + 227367 * 2 ^ 59
def prefixEnd_227367 : Nat := 4983230072969 + 3 ^ 40 * 227367 * 2
def baseEnd_227367 : Nat := 103776494196370808237213

theorem tailTrace_227367 : CollatzResearch.WordTrace tailWord_227367 prefixEnd_227367 103776494196370808237213 := by
  unfold tailWord_227367
  simp only [CollatzResearch.WordTrace]
  refine ⟨8292755767295665037200355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5528503844863776691466903 8292755767295665037200355)
  ·
    refine ⟨12439133650943497555800533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8292755767295665037200355 12439133650943497555800533)
    ·
      refine ⟨291542194943988223964075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12439133650943497555800533 291542194943988223964075)
      ·
        refine ⟨437313292415982335946113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291542194943988223964075 437313292415982335946113)
        ·
          refine ⟨327984969311986751959585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437313292415982335946113 327984969311986751959585)
          ·
            refine ⟨245988726983990063969689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327984969311986751959585 245988726983990063969689)
            ·
              refine ⟨184491545237992547977267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245988726983990063969689 184491545237992547977267)
              ·
                refine ⟨276737317856988821965901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184491545237992547977267 276737317856988821965901)
                ·
                  refine ⟨103776494196370808237213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276737317856988821965901 103776494196370808237213)
                  ·
                    rfl

theorem cell20_227367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_227367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227367 prefixEnd_227367 := by exact prefixLift 227367
  have htrace : WordTrace (prefixWord ++ tailWord_227367) baseStart_227367 baseEnd_227367 := by
    simpa [prefixWord, tailWord_227367, baseEnd_227367] using wordTrace_append hprefix tailTrace_227367
  have hstable : (prefixWord ++ tailWord_227367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227367).length < 2 ^ (prefixWord ++ tailWord_227367).sum := by decide
  have hdescent : baseEnd_227367 < baseStart_227367 := by decide
  rcases family_descends (prefixWord ++ tailWord_227367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227416 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 2]
def baseStart_227416 : Nat := 118140960795 + 227416 * 2 ^ 59
def prefixEnd_227416 : Nat := 4983230072969 + 3 ^ 40 * 227416 * 2
def baseEnd_227416 : Nat := 103798859131544415603679

theorem tailTrace_227416 : CollatzResearch.WordTrace tailWord_227416 prefixEnd_227416 103798859131544415603679 := by
  unfold tailWord_227416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4147271472059073202867051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5529695296078764270489401 4147271472059073202867051)
  ·
    refine ⟨6220907208088609804300577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4147271472059073202867051 6220907208088609804300577)
    ·
      refine ⟨4665680406066457353225433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6220907208088609804300577 4665680406066457353225433)
      ·
        refine ⟨3499260304549843014919075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4665680406066457353225433 3499260304549843014919075)
        ·
          refine ⟨5248890456824764522378613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499260304549843014919075 5248890456824764522378613)
          ·
            refine ⟨492083480327321673972995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5248890456824764522378613 492083480327321673972995)
            ·
              refine ⟨738125220490982510959493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492083480327321673972995 738125220490982510959493)
              ·
                refine ⟨138398478842059220804905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738125220490982510959493 138398478842059220804905)
                ·
                  refine ⟨103798859131544415603679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138398478842059220804905 103798859131544415603679)
                  ·
                    rfl

theorem cell20_227416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_227416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227416 prefixEnd_227416 := by exact prefixLift 227416
  have htrace : WordTrace (prefixWord ++ tailWord_227416) baseStart_227416 baseEnd_227416 := by
    simpa [prefixWord, tailWord_227416, baseEnd_227416] using wordTrace_append hprefix tailTrace_227416
  have hstable : (prefixWord ++ tailWord_227416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227416).length < 2 ^ (prefixWord ++ tailWord_227416).sum := by decide
  have hdescent : baseEnd_227416 < baseStart_227416 := by decide
  rcases family_descends (prefixWord ++ tailWord_227416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227437 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_227437 : Nat := 118140960795 + 227437 * 2 ^ 59
def prefixEnd_227437 : Nat := 4983230072969 + 3 ^ 40 * 227437 * 2
def baseEnd_227437 : Nat := 103808444103761675903593

theorem tailTrace_227437 : CollatzResearch.WordTrace tailWord_227437 prefixEnd_227437 103808444103761675903593 := by
  unfold tailWord_227437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295308877042066992248565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5530205918028044661499043 8295308877042066992248565)
  ·
    refine ⟨777685207222693780523303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8295308877042066992248565 777685207222693780523303)
    ·
      refine ⟨1166527810834040670784955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777685207222693780523303 1166527810834040670784955)
      ·
        refine ⟨1749791716251061006177433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166527810834040670784955 1749791716251061006177433)
        ·
          refine ⟨1312343787188295754633075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749791716251061006177433 1312343787188295754633075)
          ·
            refine ⟨1968515680782443631949613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312343787188295754633075 1968515680782443631949613)
            ·
              refine ⟨738193380293416361981105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1968515680782443631949613 738193380293416361981105)
              ·
                refine ⟨553645035220062271485829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738193380293416361981105 553645035220062271485829)
                ·
                  refine ⟨103808444103761675903593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553645035220062271485829 103808444103761675903593)
                  ·
                    rfl

theorem cell20_227437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_227437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227437 prefixEnd_227437 := by exact prefixLift 227437
  have htrace : WordTrace (prefixWord ++ tailWord_227437) baseStart_227437 baseEnd_227437 := by
    simpa [prefixWord, tailWord_227437, baseEnd_227437] using wordTrace_append hprefix tailTrace_227437
  have hstable : (prefixWord ++ tailWord_227437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227437).length < 2 ^ (prefixWord ++ tailWord_227437).sum := by decide
  have hdescent : baseEnd_227437 < baseStart_227437 := by decide
  rcases family_descends (prefixWord ++ tailWord_227437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227465 : List Nat := [1, 2, 1, 1, 4, 2, 9]
def baseStart_227465 : Nat := 118140960795 + 227465 * 2 ^ 59
def prefixEnd_227465 : Nat := 4983230072969 + 3 ^ 40 * 227465 * 2
def baseEnd_227465 : Nat := 11535691562968669218905

theorem tailTrace_227465 : CollatzResearch.WordTrace tailWord_227465 prefixEnd_227465 11535691562968669218905 := by
  unfold tailWord_227465
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296330120940627774267849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5530886747293751849511899 8296330120940627774267849)
  ·
    refine ⟨6222247590705470830700887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8296330120940627774267849 6222247590705470830700887)
    ·
      refine ⟨9333371386058206246051331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6222247590705470830700887 9333371386058206246051331)
      ·
        refine ⟨14000057079087309369076997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9333371386058206246051331 14000057079087309369076997)
        ·
          refine ⟨2625010702328870506701937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14000057079087309369076997 2625010702328870506701937)
          ·
            refine ⟨1968758026746652880026453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625010702328870506701937 1968758026746652880026453)
            ·
              refine ⟨11535691562968669218905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1968758026746652880026453 11535691562968669218905)
              ·
                rfl

theorem cell20_227465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_227465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227465 prefixEnd_227465 := by exact prefixLift 227465
  have htrace : WordTrace (prefixWord ++ tailWord_227465) baseStart_227465 baseEnd_227465 := by
    simpa [prefixWord, tailWord_227465, baseEnd_227465] using wordTrace_append hprefix tailTrace_227465
  have hstable : (prefixWord ++ tailWord_227465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227465).length < 2 ^ (prefixWord ++ tailWord_227465).sum := by decide
  have hdescent : baseEnd_227465 < baseStart_227465 := by decide
  rcases family_descends (prefixWord ++ tailWord_227465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227485 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 3]
def baseStart_227485 : Nat := 118140960795 + 227485 * 2 ^ 59
def prefixEnd_227485 : Nat := 4983230072969 + 3 ^ 40 * 227485 * 2
def baseEnd_227485 : Nat := 103830352611686842303397

theorem tailTrace_227485 : CollatzResearch.WordTrace tailWord_227485 prefixEnd_227485 103830352611686842303397 := by
  unfold tailWord_227485
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297059580868171189995909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5531373053912114126663939 8297059580868171189995909)
  ·
    refine ⟨1555698671412782098124233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8297059580868171189995909 1555698671412782098124233)
    ·
      refine ⟨1166774003559586573593175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1555698671412782098124233 1166774003559586573593175)
      ·
        refine ⟨1750161005339379860389763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166774003559586573593175 1750161005339379860389763)
        ·
          refine ⟨2625241508009069790584645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750161005339379860389763 2625241508009069790584645)
          ·
            refine ⟨492232782751700585734621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2625241508009069790584645 492232782751700585734621)
            ·
              refine ⟨184587293531887719650483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492232782751700585734621 184587293531887719650483)
              ·
                refine ⟨276880940297831579475725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184587293531887719650483 276880940297831579475725)
                ·
                  refine ⟨103830352611686842303397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276880940297831579475725 103830352611686842303397)
                  ·
                    rfl

theorem cell20_227485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_227485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227485 prefixEnd_227485 := by exact prefixLift 227485
  have htrace : WordTrace (prefixWord ++ tailWord_227485) baseStart_227485 baseEnd_227485 := by
    simpa [prefixWord, tailWord_227485, baseEnd_227485] using wordTrace_append hprefix tailTrace_227485
  have hstable : (prefixWord ++ tailWord_227485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227485).length < 2 ^ (prefixWord ++ tailWord_227485).sum := by decide
  have hdescent : baseEnd_227485 < baseStart_227485 := by decide
  rcases family_descends (prefixWord ++ tailWord_227485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227495 : List Nat := [1, 1, 6, 2, 3, 1, 2, 4]
def baseStart_227495 : Nat := 118140960795 + 227495 * 2 ^ 59
def prefixEnd_227495 : Nat := 4983230072969 + 3 ^ 40 * 227495 * 2
def baseEnd_227495 : Nat := 34611638961390417323341

theorem tailTrace_227495 : CollatzResearch.WordTrace tailWord_227495 prefixEnd_227495 34611638961390417323341 := by
  unfold tailWord_227495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297424310831942897859939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5531616207221295265239959 8297424310831942897859939)
  ·
    refine ⟨12446136466247914346789909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8297424310831942897859939 12446136466247914346789909)
    ·
      refine ⟨583412646855370985005777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12446136466247914346789909 583412646855370985005777)
      ·
        refine ⟨437559485141528238754333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583412646855370985005777 437559485141528238754333)
        ·
          refine ⟨164084806928073089532875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437559485141528238754333 164084806928073089532875)
          ·
            refine ⟨246127210392109634299313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164084806928073089532875 246127210392109634299313)
            ·
              refine ⟨184595407794082225724485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246127210392109634299313 184595407794082225724485)
              ·
                refine ⟨34611638961390417323341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184595407794082225724485 34611638961390417323341)
                ·
                  rfl

theorem cell20_227495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].length) (baseStart_227495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227495 prefixEnd_227495 := by exact prefixLift 227495
  have htrace : WordTrace (prefixWord ++ tailWord_227495) baseStart_227495 baseEnd_227495 := by
    simpa [prefixWord, tailWord_227495, baseEnd_227495] using wordTrace_append hprefix tailTrace_227495
  have hstable : (prefixWord ++ tailWord_227495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227495).length < 2 ^ (prefixWord ++ tailWord_227495).sum := by decide
  have hdescent : baseEnd_227495 < baseStart_227495 := by decide
  rcases family_descends (prefixWord ++ tailWord_227495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227520 : List Nat := [2, 1, 1, 2, 5, 3, 6]
def baseStart_227520 : Nat := 118140960795 + 227520 * 2 ^ 59
def prefixEnd_227520 : Nat := 4983230072969 + 3 ^ 40 * 227520 * 2
def baseEnd_227520 : Nat := 11538480840598030681843

theorem tailTrace_227520 : CollatzResearch.WordTrace tailWord_227520 prefixEnd_227520 11538480840598030681843 := by
  unfold tailWord_227520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149168067870686083760007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5532224090494248111680009 4149168067870686083760007)
  ·
    refine ⟨6223752101806029125640011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149168067870686083760007 6223752101806029125640011)
    ·
      refine ⟨9335628152709043688460017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223752101806029125640011 9335628152709043688460017)
      ·
        refine ⟨7001721114531782766345013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9335628152709043688460017 7001721114531782766345013)
        ·
          refine ⟨656411354487354634344845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7001721114531782766345013 656411354487354634344845)
          ·
            refine ⟨246154257932757987879317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656411354487354634344845 246154257932757987879317)
            ·
              refine ⟨11538480840598030681843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246154257932757987879317 11538480840598030681843)
              ·
                rfl

theorem cell20_227520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 6].length) (baseStart_227520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227520 prefixEnd_227520 := by exact prefixLift 227520
  have htrace : WordTrace (prefixWord ++ tailWord_227520) baseStart_227520 baseEnd_227520 := by
    simpa [prefixWord, tailWord_227520, baseEnd_227520] using wordTrace_append hprefix tailTrace_227520
  have hstable : (prefixWord ++ tailWord_227520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227520).length < 2 ^ (prefixWord ++ tailWord_227520).sum := by decide
  have hdescent : baseEnd_227520 < baseStart_227520 := by decide
  rcases family_descends (prefixWord ++ tailWord_227520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227544 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_227544 : Nat := 118140960795 + 227544 * 2 ^ 59
def prefixEnd_227544 : Nat := 4983230072969 + 3 ^ 40 * 227544 * 2
def baseEnd_227544 : Nat := 103857281819344859336489

theorem tailTrace_227544 : CollatzResearch.WordTrace tailWord_227544 prefixEnd_227544 103857281819344859336489 := by
  unfold tailWord_227544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149605743827212133196843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5532807658436282844262457 4149605743827212133196843)
  ·
    refine ⟨6224408615740818199795265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149605743827212133196843 6224408615740818199795265)
    ·
      refine ⟨4668306461805613649846449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6224408615740818199795265 4668306461805613649846449)
      ·
        refine ⟨3501229846354210237384837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4668306461805613649846449 3501229846354210237384837)
        ·
          refine ⟨656480596191414419509657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3501229846354210237384837 656480596191414419509657)
          ·
            refine ⟨492360447143560814632243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656480596191414419509657 492360447143560814632243)
            ·
              refine ⟨738540670715341221948365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492360447143560814632243 738540670715341221948365)
              ·
                refine ⟨276952751518252958230637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738540670715341221948365 276952751518252958230637)
                ·
                  refine ⟨103857281819344859336489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276952751518252958230637 103857281819344859336489)
                  ·
                    rfl

theorem cell20_227544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_227544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227544 prefixEnd_227544 := by exact prefixLift 227544
  have htrace : WordTrace (prefixWord ++ tailWord_227544) baseStart_227544 baseEnd_227544 := by
    simpa [prefixWord, tailWord_227544, baseEnd_227544] using wordTrace_append hprefix tailTrace_227544
  have hstable : (prefixWord ++ tailWord_227544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227544).length < 2 ^ (prefixWord ++ tailWord_227544).sum := by decide
  have hdescent : baseEnd_227544 < baseStart_227544 := by decide
  rcases family_descends (prefixWord ++ tailWord_227544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227617 : List Nat := [1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_227617 : Nat := 118140960795 + 227617 * 2 ^ 59
def prefixEnd_227617 : Nat := 4983230072969 + 3 ^ 40 * 227617 * 2
def baseEnd_227617 : Nat := 34630200336160349967619

theorem tailTrace_227617 : CollatzResearch.WordTrace tailWord_227617 prefixEnd_227617 34630200336160349967619 := by
  unfold tailWord_227617
  simp only [CollatzResearch.WordTrace]
  refine ⟨8301874016389957733801105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5534582677593305155867403 8301874016389957733801105)
  ·
    refine ⟨6226405512292468300350829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8301874016389957733801105 6226405512292468300350829)
    ·
      refine ⟨2334902067109675612631561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6226405512292468300350829 2334902067109675612631561)
      ·
        refine ⟨1751176550332256709473671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334902067109675612631561 1751176550332256709473671)
        ·
          refine ⟨2626764825498385064210507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751176550332256709473671 2626764825498385064210507)
          ·
            refine ⟨3940147238247577596315761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626764825498385064210507 3940147238247577596315761)
            ·
              refine ⟨2955110428685683197236821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940147238247577596315761 2955110428685683197236821)
              ·
                refine ⟨34630200336160349967619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2955110428685683197236821 34630200336160349967619)
                ·
                  rfl

theorem cell20_227617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_227617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227617 prefixEnd_227617 := by exact prefixLift 227617
  have htrace : WordTrace (prefixWord ++ tailWord_227617) baseStart_227617 baseEnd_227617 := by
    simpa [prefixWord, tailWord_227617, baseEnd_227617] using wordTrace_append hprefix tailTrace_227617
  have hstable : (prefixWord ++ tailWord_227617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227617).length < 2 ^ (prefixWord ++ tailWord_227617).sum := by decide
  have hdescent : baseEnd_227617 < baseStart_227617 := by decide
  rcases family_descends (prefixWord ++ tailWord_227617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227634 : List Nat := [3, 2, 1, 1, 5, 1, 7]
def baseStart_227634 : Nat := 118140960795 + 227634 * 2 ^ 59
def prefixEnd_227634 : Nat := 4983230072969 + 3 ^ 40 * 227634 * 2
def baseEnd_227634 : Nat := 11544262252411616259569

theorem tailTrace_227634 : CollatzResearch.WordTrace tailWord_227634 prefixEnd_227634 11544262252411616259569 := by
  unfold tailWord_227634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075623514332092409292489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5534996038218913091446637 2075623514332092409292489)
  ·
    refine ⟨1556717635749069306969367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2075623514332092409292489 1556717635749069306969367)
    ·
      refine ⟨2335076453623603960454051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556717635749069306969367 2335076453623603960454051)
      ·
        refine ⟨3502614680435405940681077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2335076453623603960454051 3502614680435405940681077)
        ·
          refine ⟨328370126290819306938851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3502614680435405940681077 328370126290819306938851)
          ·
            refine ⟨492555189436228960408277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328370126290819306938851 492555189436228960408277)
            ·
              refine ⟨11544262252411616259569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 492555189436228960408277 11544262252411616259569)
              ·
                rfl

theorem cell20_227634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 7].length) (baseStart_227634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227634 prefixEnd_227634 := by exact prefixLift 227634
  have htrace : WordTrace (prefixWord ++ tailWord_227634) baseStart_227634 baseEnd_227634 := by
    simpa [prefixWord, tailWord_227634, baseEnd_227634] using wordTrace_append hprefix tailTrace_227634
  have hstable : (prefixWord ++ tailWord_227634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227634).length < 2 ^ (prefixWord ++ tailWord_227634).sum := by decide
  have hdescent : baseEnd_227634 < baseStart_227634 := by decide
  rcases family_descends (prefixWord ++ tailWord_227634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227655 : List Nat := [1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_227655 : Nat := 118140960795 + 227655 * 2 ^ 59
def prefixEnd_227655 : Nat := 4983230072969 + 3 ^ 40 * 227655 * 2
def baseEnd_227655 : Nat := 34635981747973935545345

theorem tailTrace_227655 : CollatzResearch.WordTrace tailWord_227655 prefixEnd_227655 34635981747973935545345 := by
  unfold tailWord_227655
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303259990252290223684419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5535506660168193482456279 8303259990252290223684419)
  ·
    refine ⟨12454889985378435335526629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8303259990252290223684419 12454889985378435335526629)
    ·
      refine ⟨2335291872258456625411243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12454889985378435335526629 2335291872258456625411243)
      ·
        refine ⟨3502937808387684938116865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2335291872258456625411243 3502937808387684938116865)
        ·
          refine ⟨2627203356290763703587649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502937808387684938116865 2627203356290763703587649)
          ·
            refine ⟨1970402517218072777690737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627203356290763703587649 1970402517218072777690737)
            ·
              refine ⟨1477801887913554583268053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970402517218072777690737 1477801887913554583268053)
              ·
                refine ⟨34635981747973935545345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1477801887913554583268053 34635981747973935545345)
                ·
                  rfl

theorem cell20_227655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_227655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227655 prefixEnd_227655 := by exact prefixLift 227655
  have htrace : WordTrace (prefixWord ++ tailWord_227655) baseStart_227655 baseEnd_227655 := by
    simpa [prefixWord, tailWord_227655, baseEnd_227655] using wordTrace_append hprefix tailTrace_227655
  have hstable : (prefixWord ++ tailWord_227655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227655).length < 2 ^ (prefixWord ++ tailWord_227655).sum := by decide
  have hdescent : baseEnd_227655 < baseStart_227655 := by decide
  rcases family_descends (prefixWord ++ tailWord_227655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227713 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 3]
def baseStart_227713 : Nat := 118140960795 + 227713 * 2 ^ 59
def prefixEnd_227713 : Nat := 4983230072969 + 3 ^ 40 * 227713 * 2
def baseEnd_227713 : Nat := 103934418024331382702465

theorem tailTrace_227713 : CollatzResearch.WordTrace tailWord_227713 prefixEnd_227713 103934418024331382702465 := by
  unfold tailWord_227713
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305375424042166129295793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5536916949361444086197195 8305375424042166129295793)
  ·
    refine ⟨6229031568031624596971845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8305375424042166129295793 6229031568031624596971845)
    ·
      refine ⟨1167943419005929611932221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6229031568031624596971845 1167943419005929611932221)
      ·
        refine ⟨437978782127223604474583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1167943419005929611932221 437978782127223604474583)
        ·
          refine ⟨656968173190835406711875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437978782127223604474583 656968173190835406711875)
          ·
            refine ⟨985452259786253110067813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656968173190835406711875 985452259786253110067813)
            ·
              refine ⟨184772298709922458137715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 985452259786253110067813 184772298709922458137715)
              ·
                refine ⟨277158448064883687206573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184772298709922458137715 277158448064883687206573)
                ·
                  refine ⟨103934418024331382702465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277158448064883687206573 103934418024331382702465)
                  ·
                    rfl

theorem cell20_227713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_227713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227713 prefixEnd_227713 := by exact prefixLift 227713
  have htrace : WordTrace (prefixWord ++ tailWord_227713) baseStart_227713 baseEnd_227713 := by
    simpa [prefixWord, tailWord_227713, baseEnd_227713] using wordTrace_append hprefix tailTrace_227713
  have hstable : (prefixWord ++ tailWord_227713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227713).length < 2 ^ (prefixWord ++ tailWord_227713).sum := by decide
  have hdescent : baseEnd_227713 < baseStart_227713 := by decide
  rcases family_descends (prefixWord ++ tailWord_227713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227762 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_227762 : Nat := 118140960795 + 227762 * 2 ^ 59
def prefixEnd_227762 : Nat := 4983230072969 + 3 ^ 40 * 227762 * 2
def baseEnd_227762 : Nat := 103956782959504990068931

theorem tailTrace_227762 : CollatzResearch.WordTrace tailWord_227762 prefixEnd_227762 103956782959504990068931 := by
  unfold tailWord_227762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076790650216161874457385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5538108400576431665219693 2076790650216161874457385)
  ·
    refine ⟨1557592987662121405843039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2076790650216161874457385 1557592987662121405843039)
    ·
      refine ⟨2336389481493182108764559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1557592987662121405843039 2336389481493182108764559)
      ·
        refine ⟨3504584222239773163146839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336389481493182108764559 3504584222239773163146839)
        ·
          refine ⟨5256876333359659744720259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504584222239773163146839 5256876333359659744720259)
          ·
            refine ⟨7885314500039489617080389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256876333359659744720259 7885314500039489617080389)
            ·
              refine ⟨1478496468757404303202573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7885314500039489617080389 1478496468757404303202573)
              ·
                refine ⟨554436175784026613700965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1478496468757404303202573 554436175784026613700965)
                ·
                  refine ⟨103956782959504990068931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554436175784026613700965 103956782959504990068931)
                  ·
                    rfl

theorem cell20_227762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_227762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227762 prefixEnd_227762 := by exact prefixLift 227762
  have htrace : WordTrace (prefixWord ++ tailWord_227762) baseStart_227762 baseEnd_227762 := by
    simpa [prefixWord, tailWord_227762, baseEnd_227762] using wordTrace_append hprefix tailTrace_227762
  have hstable : (prefixWord ++ tailWord_227762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227762).length < 2 ^ (prefixWord ++ tailWord_227762).sum := by decide
  have hdescent : baseEnd_227762 < baseStart_227762 := by decide
  rcases family_descends (prefixWord ++ tailWord_227762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227765 : List Nat := [1, 3, 3, 2, 3, 2, 1, 5]
def baseStart_227765 : Nat := 118140960795 + 227765 * 2 ^ 59
def prefixEnd_227765 : Nat := 4983230072969 + 3 ^ 40 * 227765 * 2
def baseEnd_227765 : Nat := 34652717413750104322973

theorem tailTrace_227765 : CollatzResearch.WordTrace tailWord_227765 prefixEnd_227765 34652717413750104322973 := by
  unfold tailWord_227765
  simp only [CollatzResearch.WordTrace]
  refine ⟨8307272019853779010188749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5538181346569186006792499 8307272019853779010188749)
  ·
    refine ⟨3115227007445167128820781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8307272019853779010188749 3115227007445167128820781)
    ·
      refine ⟨1168210127791937673307793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3115227007445167128820781 1168210127791937673307793)
      ·
        refine ⟨876157595843953254980845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168210127791937673307793 876157595843953254980845)
        ·
          refine ⟨328559098441482470617817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 876157595843953254980845 328559098441482470617817)
          ·
            refine ⟨246419323831111852963363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328559098441482470617817 246419323831111852963363)
            ·
              refine ⟨369628985746667779445045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246419323831111852963363 369628985746667779445045)
              ·
                refine ⟨34652717413750104322973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369628985746667779445045 34652717413750104322973)
                ·
                  rfl

theorem cell20_227765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_227765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227765 prefixEnd_227765 := by exact prefixLift 227765
  have htrace : WordTrace (prefixWord ++ tailWord_227765) baseStart_227765 baseEnd_227765 := by
    simpa [prefixWord, tailWord_227765, baseEnd_227765] using wordTrace_append hprefix tailTrace_227765
  have hstable : (prefixWord ++ tailWord_227765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227765).length < 2 ^ (prefixWord ++ tailWord_227765).sum := by decide
  have hdescent : baseEnd_227765 < baseStart_227765 := by decide
  rcases family_descends (prefixWord ++ tailWord_227765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227772 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_227772 : Nat := 118140960795 + 227772 * 2 ^ 59
def prefixEnd_227772 : Nat := 4983230072969 + 3 ^ 40 * 227772 * 2
def baseEnd_227772 : Nat := 103961347231989399735557

theorem tailTrace_227772 : CollatzResearch.WordTrace tailWord_227772 prefixEnd_227772 103961347231989399735557 := by
  unfold tailWord_227772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153763665414209602846785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5538351553885612803795713 4153763665414209602846785)
  ·
    refine ⟨3115322749060657202135089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4153763665414209602846785 3115322749060657202135089)
    ·
      refine ⟨2336492061795492901601317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115322749060657202135089 2336492061795492901601317)
      ·
        refine ⟨438092261586654919050247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2336492061795492901601317 438092261586654919050247)
        ·
          refine ⟨657138392379982378575371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438092261586654919050247 657138392379982378575371)
          ·
            refine ⟨985707588569973567863057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657138392379982378575371 985707588569973567863057)
            ·
              refine ⟨739280691427480175897293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985707588569973567863057 739280691427480175897293)
              ·
                refine ⟨277230259285305065961485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739280691427480175897293 277230259285305065961485)
                ·
                  refine ⟨103961347231989399735557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277230259285305065961485 103961347231989399735557)
                  ·
                    rfl

theorem cell20_227772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_227772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227772 prefixEnd_227772 := by exact prefixLift 227772
  have htrace : WordTrace (prefixWord ++ tailWord_227772) baseStart_227772 baseEnd_227772 := by
    simpa [prefixWord, tailWord_227772, baseEnd_227772] using wordTrace_append hprefix tailTrace_227772
  have hstable : (prefixWord ++ tailWord_227772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227772).length < 2 ^ (prefixWord ++ tailWord_227772).sum := by decide
  have hdescent : baseEnd_227772 < baseStart_227772 := by decide
  rcases family_descends (prefixWord ++ tailWord_227772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227776 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_227776 : Nat := 118140960795 + 227776 * 2 ^ 59
def prefixEnd_227776 : Nat := 4983230072969 + 3 ^ 40 * 227776 * 2
def baseEnd_227776 : Nat := 103963172940983163602207

theorem tailTrace_227776 : CollatzResearch.WordTrace tailWord_227776 prefixEnd_227776 103963172940983163602207 := by
  unfold tailWord_227776
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153836611406963944419591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5538448815209285259226121 4153836611406963944419591)
  ·
    refine ⟨6230754917110445916629387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4153836611406963944419591 6230754917110445916629387)
    ·
      refine ⟨9346132375665668874944081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6230754917110445916629387 9346132375665668874944081)
      ·
        refine ⟨7009599281749251656208061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9346132375665668874944081 7009599281749251656208061)
        ·
          refine ⟨2628599730655969371078023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7009599281749251656208061 2628599730655969371078023)
          ·
            refine ⟨3942899595983954056617035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628599730655969371078023 3942899595983954056617035)
            ·
              refine ⟨5914349393975931084925553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942899595983954056617035 5914349393975931084925553)
              ·
                refine ⟨4435762045481948313694165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5914349393975931084925553 4435762045481948313694165)
                ·
                  refine ⟨103963172940983163602207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4435762045481948313694165 103963172940983163602207)
                  ·
                    rfl

theorem cell20_227776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_227776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227776 prefixEnd_227776 := by exact prefixLift 227776
  have htrace : WordTrace (prefixWord ++ tailWord_227776) baseStart_227776 baseEnd_227776 := by
    simpa [prefixWord, tailWord_227776, baseEnd_227776] using wordTrace_append hprefix tailTrace_227776
  have hstable : (prefixWord ++ tailWord_227776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227776).length < 2 ^ (prefixWord ++ tailWord_227776).sum := by decide
  have hdescent : baseEnd_227776 < baseStart_227776 := by decide
  rcases family_descends (prefixWord ++ tailWord_227776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227786 : List Nat := [3, 1, 2, 1, 2, 2, 5, 4]
def baseStart_227786 : Nat := 118140960795 + 227786 * 2 ^ 59
def prefixEnd_227786 : Nat := 4983230072969 + 3 ^ 40 * 227786 * 2
def baseEnd_227786 : Nat := 34655912404489191089611

theorem tailTrace_227786 : CollatzResearch.WordTrace tailWord_227786 prefixEnd_227786 34655912404489191089611 := by
  unfold tailWord_227786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077009488194424899175803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5538691968518466397802141 2077009488194424899175803)
  ·
    refine ⟨3115514232291637348763705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2077009488194424899175803 3115514232291637348763705)
    ·
      refine ⟨2336635674218728011572779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3115514232291637348763705 2336635674218728011572779)
      ·
        refine ⟨3504953511328092017359169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336635674218728011572779 3504953511328092017359169)
        ·
          refine ⟨2628715133496069013019377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504953511328092017359169 2628715133496069013019377)
          ·
            refine ⟨1971536350122051759764533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2628715133496069013019377 1971536350122051759764533)
            ·
              refine ⟨184831532823942352477925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1971536350122051759764533 184831532823942352477925)
              ·
                refine ⟨34655912404489191089611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184831532823942352477925 34655912404489191089611)
                ·
                  rfl

theorem cell20_227786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_227786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227786 prefixEnd_227786 := by exact prefixLift 227786
  have htrace : WordTrace (prefixWord ++ tailWord_227786) baseStart_227786 baseEnd_227786 := by
    simpa [prefixWord, tailWord_227786, baseEnd_227786] using wordTrace_append hprefix tailTrace_227786
  have hstable : (prefixWord ++ tailWord_227786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227786).length < 2 ^ (prefixWord ++ tailWord_227786).sum := by decide
  have hdescent : baseEnd_227786 < baseStart_227786 := by decide
  rcases family_descends (prefixWord ++ tailWord_227786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227796 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 2]
def baseStart_227796 : Nat := 118140960795 + 227796 * 2 ^ 59
def prefixEnd_227796 : Nat := 4983230072969 + 3 ^ 40 * 227796 * 2
def baseEnd_227796 : Nat := 103972301485951982935459

theorem tailTrace_227796 : CollatzResearch.WordTrace tailWord_227796 prefixEnd_227796 103972301485951982935459 := by
  unfold tailWord_227796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154201341370735652283621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5538935121827647536378161 4154201341370735652283621)
  ·
    refine ⟨778912751507012934803179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4154201341370735652283621 778912751507012934803179)
    ·
      refine ⟨1168369127260519402204769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778912751507012934803179 1168369127260519402204769)
      ·
        refine ⟨876276845445389551653577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168369127260519402204769 876276845445389551653577)
        ·
          refine ⟨657207634084042163740183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876276845445389551653577 657207634084042163740183)
          ·
            refine ⟨985811451126063245610275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657207634084042163740183 985811451126063245610275)
            ·
              refine ⟨1478717176689094868415413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985811451126063245610275 1478717176689094868415413)
              ·
                refine ⟨138629735314602643913945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1478717176689094868415413 138629735314602643913945)
                ·
                  refine ⟨103972301485951982935459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138629735314602643913945 103972301485951982935459)
                  ·
                    rfl

theorem cell20_227796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_227796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227796 prefixEnd_227796 := by exact prefixLift 227796
  have htrace : WordTrace (prefixWord ++ tailWord_227796) baseStart_227796 baseEnd_227796 := by
    simpa [prefixWord, tailWord_227796, baseEnd_227796] using wordTrace_append hprefix tailTrace_227796
  have hstable : (prefixWord ++ tailWord_227796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227796).length < 2 ^ (prefixWord ++ tailWord_227796).sum := by decide
  have hdescent : baseEnd_227796 < baseStart_227796 := by decide
  rcases family_descends (prefixWord ++ tailWord_227796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227807 : List Nat := [1, 1, 2, 3, 3, 3, 7]
def baseStart_227807 : Nat := 118140960795 + 227807 * 2 ^ 59
def prefixEnd_227807 : Nat := 4983230072969 + 3 ^ 40 * 227807 * 2
def baseEnd_227807 : Nat := 11553035798409425952083

theorem tailTrace_227807 : CollatzResearch.WordTrace tailWord_227807 prefixEnd_227807 11553035798409425952083 := by
  unfold tailWord_227807
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308803885701620183217675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5539202590467746788811783 8308803885701620183217675)
  ·
    refine ⟨12463205828552430274826513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8308803885701620183217675 12463205828552430274826513)
    ·
      refine ⟨9347404371414322706119885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12463205828552430274826513 9347404371414322706119885)
      ·
        refine ⟨3505276639280371014794957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9347404371414322706119885 3505276639280371014794957)
        ·
          refine ⟨1314478739730139130548109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3505276639280371014794957 1314478739730139130548109)
          ·
            refine ⟨492929527398802173955541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1314478739730139130548109 492929527398802173955541)
            ·
              refine ⟨11553035798409425952083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 492929527398802173955541 11553035798409425952083)
              ·
                rfl

theorem cell20_227807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_227807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227807 prefixEnd_227807 := by exact prefixLift 227807
  have htrace : WordTrace (prefixWord ++ tailWord_227807) baseStart_227807 baseEnd_227807 := by
    simpa [prefixWord, tailWord_227807, baseEnd_227807] using wordTrace_append hprefix tailTrace_227807
  have hstable : (prefixWord ++ tailWord_227807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227807).length < 2 ^ (prefixWord ++ tailWord_227807).sum := by decide
  have hdescent : baseEnd_227807 < baseStart_227807 := by decide
  rcases family_descends (prefixWord ++ tailWord_227807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227841 : List Nat := [1, 2, 4, 1, 3, 3, 2, 4]
def baseStart_227841 : Nat := 118140960795 + 227841 * 2 ^ 59
def prefixEnd_227841 : Nat := 4983230072969 + 3 ^ 40 * 227841 * 2
def baseEnd_227841 : Nat := 34664280237377275478425

theorem tailTrace_227841 : CollatzResearch.WordTrace tailWord_227841 prefixEnd_227841 34664280237377275478425 := by
  unfold tailWord_227841
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310043967578443989955377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5540029311718962659970251 8310043967578443989955377)
  ·
    refine ⟨6232532975683832992466533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8310043967578443989955377 6232532975683832992466533)
    ·
      refine ⟨1168599932940718686087475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6232532975683832992466533 1168599932940718686087475)
      ·
        refine ⟨1752899899411078029131213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168599932940718686087475 1752899899411078029131213)
        ·
          refine ⟨657337462279154260924205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1752899899411078029131213 657337462279154260924205)
          ·
            refine ⟨246501548354682847846577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 657337462279154260924205 246501548354682847846577)
            ·
              refine ⟨184876161266012135884933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246501548354682847846577 184876161266012135884933)
              ·
                refine ⟨34664280237377275478425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184876161266012135884933 34664280237377275478425)
                ·
                  rfl

theorem cell20_227841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_227841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227841 prefixEnd_227841 := by exact prefixLift 227841
  have htrace : WordTrace (prefixWord ++ tailWord_227841) baseStart_227841 baseEnd_227841 := by
    simpa [prefixWord, tailWord_227841, baseEnd_227841] using wordTrace_append hprefix tailTrace_227841
  have hstable : (prefixWord ++ tailWord_227841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227841).length < 2 ^ (prefixWord ++ tailWord_227841).sum := by decide
  have hdescent : baseEnd_227841 < baseStart_227841 := by decide
  rcases family_descends (prefixWord ++ tailWord_227841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227869 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_227869 : Nat := 118140960795 + 227869 * 2 ^ 59
def prefixEnd_227869 : Nat := 4983230072969 + 3 ^ 40 * 227869 * 2
def baseEnd_227869 : Nat := 104005620675088173501827

theorem tailTrace_227869 : CollatzResearch.WordTrace tailWord_227869 prefixEnd_227869 104005620675088173501827 := by
  unfold tailWord_227869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311065211477004771974661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5540710140984669847983107 8311065211477004771974661)
  ·
    refine ⟨1558324727151938394745249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8311065211477004771974661 1558324727151938394745249)
    ·
      refine ⟨1168743545363953796058937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1558324727151938394745249 1168743545363953796058937)
      ·
        refine ⟨876557659022965347044203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168743545363953796058937 876557659022965347044203)
        ·
          refine ⟨1314836488534448020566305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876557659022965347044203 1314836488534448020566305)
          ·
            refine ⟨986127366400836015424729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314836488534448020566305 986127366400836015424729)
            ·
              refine ⟨739595524800627011568547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986127366400836015424729 739595524800627011568547)
              ·
                refine ⟨1109393287200940517352821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739595524800627011568547 1109393287200940517352821)
                ·
                  refine ⟨104005620675088173501827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1109393287200940517352821 104005620675088173501827)
                  ·
                    rfl

theorem cell20_227869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_227869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227869 prefixEnd_227869 := by exact prefixLift 227869
  have htrace : WordTrace (prefixWord ++ tailWord_227869) baseStart_227869 baseEnd_227869 := by
    simpa [prefixWord, tailWord_227869, baseEnd_227869] using wordTrace_append hprefix tailTrace_227869
  have hstable : (prefixWord ++ tailWord_227869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227869).length < 2 ^ (prefixWord ++ tailWord_227869).sum := by decide
  have hdescent : baseEnd_227869 < baseStart_227869 := by decide
  rcases family_descends (prefixWord ++ tailWord_227869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227872 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_227872 : Nat := 118140960795 + 227872 * 2 ^ 59
def prefixEnd_227872 : Nat := 4983230072969 + 3 ^ 40 * 227872 * 2
def baseEnd_227872 : Nat := 104006989956833496401815

theorem tailTrace_227872 : CollatzResearch.WordTrace tailWord_227872 prefixEnd_227872 104006989956833496401815 := by
  unfold tailWord_227872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155587315233068142166935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5540783086977424189555913 4155587315233068142166935)
  ·
    refine ⟨6233380972849602213250403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155587315233068142166935 6233380972849602213250403)
    ·
      refine ⟨9350071459274403319875605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233380972849602213250403 9350071459274403319875605)
      ·
        refine ⟨438284599653487655619169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9350071459274403319875605 438284599653487655619169)
        ·
          refine ⟨328713449740115741714377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438284599653487655619169 328713449740115741714377)
          ·
            refine ⟨246535087305086806285783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328713449740115741714377 246535087305086806285783)
            ·
              refine ⟨369802630957630209428675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246535087305086806285783 369802630957630209428675)
              ·
                refine ⟨554703946436445314143013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369802630957630209428675 554703946436445314143013)
                ·
                  refine ⟨104006989956833496401815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554703946436445314143013 104006989956833496401815)
                  ·
                    rfl

theorem cell20_227872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_227872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227872 prefixEnd_227872 := by exact prefixLift 227872
  have htrace : WordTrace (prefixWord ++ tailWord_227872) baseStart_227872 baseEnd_227872 := by
    simpa [prefixWord, tailWord_227872, baseEnd_227872] using wordTrace_append hprefix tailTrace_227872
  have hstable : (prefixWord ++ tailWord_227872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227872).length < 2 ^ (prefixWord ++ tailWord_227872).sum := by decide
  have hdescent : baseEnd_227872 < baseStart_227872 := by decide
  rcases family_descends (prefixWord ++ tailWord_227872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227924 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_227924 : Nat := 118140960795 + 227924 * 2 ^ 59
def prefixEnd_227924 : Nat := 4983230072969 + 3 ^ 40 * 227924 * 2
def baseEnd_227924 : Nat := 104030724173752426668269

theorem tailTrace_227924 : CollatzResearch.WordTrace tailWord_227924 prefixEnd_227924 104030724173752426668269 := by
  unfold tailWord_227924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156535613138874582613413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5542047484185166110151217 4156535613138874582613413)
  ·
    refine ⟨779350427463538984240015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4156535613138874582613413 779350427463538984240015)
    ·
      refine ⟨1169025641195308476360023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779350427463538984240015 1169025641195308476360023)
      ·
        refine ⟨1753538461792962714540035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169025641195308476360023 1753538461792962714540035)
        ·
          refine ⟨2630307692689444071810053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753538461792962714540035 2630307692689444071810053)
          ·
            refine ⟨493182692379270763464385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2630307692689444071810053 493182692379270763464385)
            ·
              refine ⟨369887019284453072598289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493182692379270763464385 369887019284453072598289)
              ·
                refine ⟨277415264463339804448717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369887019284453072598289 277415264463339804448717)
                ·
                  refine ⟨104030724173752426668269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277415264463339804448717 104030724173752426668269)
                  ·
                    rfl

theorem cell20_227924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_227924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227924 prefixEnd_227924 := by exact prefixLift 227924
  have htrace : WordTrace (prefixWord ++ tailWord_227924) baseStart_227924 baseEnd_227924 := by
    simpa [prefixWord, tailWord_227924, baseEnd_227924] using wordTrace_append hprefix tailTrace_227924
  have hstable : (prefixWord ++ tailWord_227924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227924).length < 2 ^ (prefixWord ++ tailWord_227924).sum := by decide
  have hdescent : baseEnd_227924 < baseStart_227924 := by decide
  rcases family_descends (prefixWord ++ tailWord_227924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227928 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_227928 : Nat := 118140960795 + 227928 * 2 ^ 59
def prefixEnd_227928 : Nat := 4983230072969 + 3 ^ 40 * 227928 * 2
def baseEnd_227928 : Nat := 104032549882746190534919

theorem tailTrace_227928 : CollatzResearch.WordTrace tailWord_227928 prefixEnd_227928 104032549882746190534919 := by
  unfold tailWord_227928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156608559131628924186219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5542144745508838565581625 4156608559131628924186219)
  ·
    refine ⟨6234912838697443386279329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4156608559131628924186219 6234912838697443386279329)
    ·
      refine ⟨4676184629023082539709497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6234912838697443386279329 4676184629023082539709497)
      ·
        refine ⟨3507138471767311904782123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4676184629023082539709497 3507138471767311904782123)
        ·
          refine ⟨5260707707650967857173185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507138471767311904782123 5260707707650967857173185)
          ·
            refine ⟨3945530780738225892879889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5260707707650967857173185 3945530780738225892879889)
            ·
              refine ⟨2959148085553669419659917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945530780738225892879889 2959148085553669419659917)
              ·
                refine ⟨1109680532082626032372469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2959148085553669419659917 1109680532082626032372469)
                ·
                  refine ⟨104032549882746190534919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1109680532082626032372469 104032549882746190534919)
                  ·
                    rfl

theorem cell20_227928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_227928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227928 prefixEnd_227928 := by exact prefixLift 227928
  have htrace : WordTrace (prefixWord ++ tailWord_227928) baseStart_227928 baseEnd_227928 := by
    simpa [prefixWord, tailWord_227928, baseEnd_227928] using wordTrace_append hprefix tailTrace_227928
  have hstable : (prefixWord ++ tailWord_227928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227928).length < 2 ^ (prefixWord ++ tailWord_227928).sum := by decide
  have hdescent : baseEnd_227928 < baseStart_227928 := by decide
  rcases family_descends (prefixWord ++ tailWord_227928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227935 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_227935 : Nat := 118140960795 + 227935 * 2 ^ 59
def prefixEnd_227935 : Nat := 4983230072969 + 3 ^ 40 * 227935 * 2
def baseEnd_227935 : Nat := 104035744873485277301557

theorem tailTrace_227935 : CollatzResearch.WordTrace tailWord_227935 prefixEnd_227935 104035744873485277301557 := by
  unfold tailWord_227935
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313472429237898043877259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5542314952825265362584839 8313472429237898043877259)
  ·
    refine ⟨12470208643856847065815889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8313472429237898043877259 12470208643856847065815889)
    ·
      refine ⟨9352656482892635299361917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12470208643856847065815889 9352656482892635299361917)
      ·
        refine ⟨3507246181084738237260719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9352656482892635299361917 3507246181084738237260719)
        ·
          refine ⟨5260869271627107355891079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507246181084738237260719 5260869271627107355891079)
          ·
            refine ⟨7891303907440661033836619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260869271627107355891079 7891303907440661033836619)
            ·
              refine ⟨11836955861160991550754929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891303907440661033836619 11836955861160991550754929)
              ·
                refine ⟨8877716895870743663066197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11836955861160991550754929 8877716895870743663066197)
                ·
                  refine ⟨104035744873485277301557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8877716895870743663066197 104035744873485277301557)
                  ·
                    rfl

theorem cell20_227935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_227935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227935 prefixEnd_227935 := by exact prefixLift 227935
  have htrace : WordTrace (prefixWord ++ tailWord_227935) baseStart_227935 baseEnd_227935 := by
    simpa [prefixWord, tailWord_227935, baseEnd_227935] using wordTrace_append hprefix tailTrace_227935
  have hstable : (prefixWord ++ tailWord_227935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227935).length < 2 ^ (prefixWord ++ tailWord_227935).sum := by decide
  have hdescent : baseEnd_227935 < baseStart_227935 := by decide
  rcases family_descends (prefixWord ++ tailWord_227935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227986 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_227986 : Nat := 118140960795 + 227986 * 2 ^ 59
def prefixEnd_227986 : Nat := 4983230072969 + 3 ^ 40 * 227986 * 2
def baseEnd_227986 : Nat := 104059022663155766601349

theorem tailTrace_227986 : CollatzResearch.WordTrace tailWord_227986 prefixEnd_227986 104059022663155766601349 := by
  unfold tailWord_227986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078833138013283438495953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5543555034702089169322541 2078833138013283438495953)
  ·
    refine ⟨1559124853509962578871965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2078833138013283438495953 1559124853509962578871965)
    ·
      refine ⟨584671820066235967076987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1559124853509962578871965 584671820066235967076987)
      ·
        refine ⟨877007730099353950615481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584671820066235967076987 877007730099353950615481)
        ·
          refine ⟨657755797574515462961611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877007730099353950615481 657755797574515462961611)
          ·
            refine ⟨986633696361773194442417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657755797574515462961611 986633696361773194442417)
            ·
              refine ⟨739975272271329895831813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986633696361773194442417 739975272271329895831813)
              ·
                refine ⟨138745363550874355468465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739975272271329895831813 138745363550874355468465)
                ·
                  refine ⟨104059022663155766601349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138745363550874355468465 104059022663155766601349)
                  ·
                    rfl

theorem cell20_227986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_227986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_227986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_227986 prefixEnd_227986 := by exact prefixLift 227986
  have htrace : WordTrace (prefixWord ++ tailWord_227986) baseStart_227986 baseEnd_227986 := by
    simpa [prefixWord, tailWord_227986, baseEnd_227986] using wordTrace_append hprefix tailTrace_227986
  have hstable : (prefixWord ++ tailWord_227986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227986).length < 2 ^ (prefixWord ++ tailWord_227986).sum := by decide
  have hdescent : baseEnd_227986 < baseStart_227986 := by decide
  rcases family_descends (prefixWord ++ tailWord_227986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228021 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_228021 : Nat := 118140960795 + 228021 * 2 ^ 59
def prefixEnd_228021 : Nat := 4983230072969 + 3 ^ 40 * 228021 * 2
def baseEnd_228021 : Nat := 104074997616851200434539

theorem tailTrace_228021 : CollatzResearch.WordTrace tailWord_228021 prefixEnd_228021 104074997616851200434539 := by
  unfold tailWord_228021
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316609106926334731507917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5544406071284223154338611 8316609106926334731507917)
  ·
    refine ⟨3118728415097375524315469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8316609106926334731507917 3118728415097375524315469)
    ·
      refine ⟨1169523155661515821618301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3118728415097375524315469 1169523155661515821618301)
      ·
        refine ⟨438571183373068433106863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1169523155661515821618301 438571183373068433106863)
        ·
          refine ⟨657856775059602649660295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438571183373068433106863 657856775059602649660295)
          ·
            refine ⟨986785162589403974490443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657856775059602649660295 986785162589403974490443)
            ·
              refine ⟨1480177743884105961735665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986785162589403974490443 1480177743884105961735665)
              ·
                refine ⟨1110133307913079471301749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480177743884105961735665 1110133307913079471301749)
                ·
                  refine ⟨104074997616851200434539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1110133307913079471301749 104074997616851200434539)
                  ·
                    rfl

theorem cell20_228021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_228021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228021 prefixEnd_228021 := by exact prefixLift 228021
  have htrace : WordTrace (prefixWord ++ tailWord_228021) baseStart_228021 baseEnd_228021 := by
    simpa [prefixWord, tailWord_228021, baseEnd_228021] using wordTrace_append hprefix tailTrace_228021
  have hstable : (prefixWord ++ tailWord_228021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228021).length < 2 ^ (prefixWord ++ tailWord_228021).sum := by decide
  have hdescent : baseEnd_228021 < baseStart_228021 := by decide
  rcases family_descends (prefixWord ++ tailWord_228021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228128 : List Nat := [2, 1, 1, 5, 1, 3, 3, 4]
def baseStart_228128 : Nat := 118140960795 + 228128 * 2 ^ 59
def prefixEnd_228128 : Nat := 4983230072969 + 3 ^ 40 * 228128 * 2
def baseEnd_228128 : Nat := 34707945110811461289145

theorem tailTrace_228128 : CollatzResearch.WordTrace tailWord_228128 prefixEnd_228128 34707945110811461289145 := by
  unfold tailWord_228128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160255858769346002826519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5547007811692461337102025 4160255858769346002826519)
  ·
    refine ⟨6240383788154019004239779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4160255858769346002826519 6240383788154019004239779)
    ·
      refine ⟨9360575682231028506359669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240383788154019004239779 9360575682231028506359669)
      ·
        refine ⟨877553970209158922471219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9360575682231028506359669 877553970209158922471219)
        ·
          refine ⟨1316330955313738383706829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877553970209158922471219 1316330955313738383706829)
          ·
            refine ⟨493624108242651893890061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1316330955313738383706829 493624108242651893890061)
            ·
              refine ⟨185109040590994460208773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493624108242651893890061 185109040590994460208773)
              ·
                refine ⟨34707945110811461289145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185109040590994460208773 34707945110811461289145)
                ·
                  rfl

theorem cell20_228128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_228128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228128 prefixEnd_228128 := by exact prefixLift 228128
  have htrace : WordTrace (prefixWord ++ tailWord_228128) baseStart_228128 baseEnd_228128 := by
    simpa [prefixWord, tailWord_228128, baseEnd_228128] using wordTrace_append hprefix tailTrace_228128
  have hstable : (prefixWord ++ tailWord_228128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228128).length < 2 ^ (prefixWord ++ tailWord_228128).sum := by decide
  have hdescent : baseEnd_228128 < baseStart_228128 := by decide
  rcases family_descends (prefixWord ++ tailWord_228128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228148 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 3]
def baseStart_228148 : Nat := 118140960795 + 228148 * 2 ^ 59
def prefixEnd_228148 : Nat := 4983230072969 + 3 ^ 40 * 228148 * 2
def baseEnd_228148 : Nat := 104132963877403203200687

theorem tailTrace_228148 : CollatzResearch.WordTrace tailWord_228148 prefixEnd_228148 104132963877403203200687 := by
  unfold tailWord_228148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160620588733117710690549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5547494118310823614254065 4160620588733117710690549)
  ·
    refine ⟨390058180193729785377239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4160620588733117710690549 390058180193729785377239)
    ·
      refine ⟨585087270290594678065859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390058180193729785377239 585087270290594678065859)
      ·
        refine ⟨877630905435892017098789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585087270290594678065859 877630905435892017098789)
        ·
          refine ⟨164555794769229753206023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 877630905435892017098789 164555794769229753206023)
          ·
            refine ⟨246833692153844629809035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164555794769229753206023 246833692153844629809035)
            ·
              refine ⟨370250538230766944713553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246833692153844629809035 370250538230766944713553)
              ·
                refine ⟨277687903673075208535165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370250538230766944713553 277687903673075208535165)
                ·
                  refine ⟨104132963877403203200687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277687903673075208535165 104132963877403203200687)
                  ·
                    rfl

theorem cell20_228148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_228148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228148 prefixEnd_228148 := by exact prefixLift 228148
  have htrace : WordTrace (prefixWord ++ tailWord_228148) baseStart_228148 baseEnd_228148 := by
    simpa [prefixWord, tailWord_228148, baseEnd_228148] using wordTrace_append hprefix tailTrace_228148
  have hstable : (prefixWord ++ tailWord_228148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228148).length < 2 ^ (prefixWord ++ tailWord_228148).sum := by decide
  have hdescent : baseEnd_228148 < baseStart_228148 := by decide
  rcases family_descends (prefixWord ++ tailWord_228148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228149 : List Nat := [1, 3, 3, 1, 3, 2, 7]
def baseStart_228149 : Nat := 118140960795 + 228149 * 2 ^ 59
def prefixEnd_228149 : Nat := 4983230072969 + 3 ^ 40 * 228149 * 2
def baseEnd_228149 : Nat := 11570380033850182685261

theorem tailTrace_228149 : CollatzResearch.WordTrace tailWord_228149 prefixEnd_228149 11570380033850182685261 := by
  unfold tailWord_228149
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321277650462612592167501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5547518433641741728111667 8321277650462612592167501)
  ·
    refine ⟨3120479118923479722062813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8321277650462612592167501 3120479118923479722062813)
    ·
      refine ⟨1170179669596304895773555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3120479118923479722062813 1170179669596304895773555)
      ·
        refine ⟨1755269504394457343660333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170179669596304895773555 1755269504394457343660333)
        ·
          refine ⟨658226064147921503872625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1755269504394457343660333 658226064147921503872625)
          ·
            refine ⟨493669548110941127904469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658226064147921503872625 493669548110941127904469)
            ·
              refine ⟨11570380033850182685261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 493669548110941127904469 11570380033850182685261)
              ·
                rfl

theorem cell20_228149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_228149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228149 prefixEnd_228149 := by exact prefixLift 228149
  have htrace : WordTrace (prefixWord ++ tailWord_228149) baseStart_228149 baseEnd_228149 := by
    simpa [prefixWord, tailWord_228149, baseEnd_228149] using wordTrace_append hprefix tailTrace_228149
  have hstable : (prefixWord ++ tailWord_228149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228149).length < 2 ^ (prefixWord ++ tailWord_228149).sum := by decide
  have hdescent : baseEnd_228149 < baseStart_228149 := by decide
  rcases family_descends (prefixWord ++ tailWord_228149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228159 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 2]
def baseStart_228159 : Nat := 118140960795 + 228159 * 2 ^ 59
def prefixEnd_228159 : Nat := 4983230072969 + 3 ^ 40 * 228159 * 2
def baseEnd_228159 : Nat := 104137984577136053833975

theorem tailTrace_228159 : CollatzResearch.WordTrace tailWord_228159 prefixEnd_228159 104137984577136053833975 := by
  unfold tailWord_228159
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321642380426384300031531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5547761586950922866687687 8321642380426384300031531)
  ·
    refine ⟨12482463570639576450047297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8321642380426384300031531 12482463570639576450047297)
    ·
      refine ⟨9361847677979682337535473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12482463570639576450047297 9361847677979682337535473)
      ·
        refine ⟨7021385758484761753151605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9361847677979682337535473 7021385758484761753151605)
        ·
          refine ⟨658254914857946414357963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7021385758484761753151605 658254914857946414357963)
          ·
            refine ⟨987382372286919621536945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658254914857946414357963 987382372286919621536945)
            ·
              refine ⟨740536779215189716152709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987382372286919621536945 740536779215189716152709)
              ·
                refine ⟨138850646102848071778633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740536779215189716152709 138850646102848071778633)
                ·
                  refine ⟨104137984577136053833975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138850646102848071778633 104137984577136053833975)
                  ·
                    rfl

theorem cell20_228159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 2].length) (baseStart_228159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228159 prefixEnd_228159 := by exact prefixLift 228159
  have htrace : WordTrace (prefixWord ++ tailWord_228159) baseStart_228159 baseEnd_228159 := by
    simpa [prefixWord, tailWord_228159, baseEnd_228159] using wordTrace_append hprefix tailTrace_228159
  have hstable : (prefixWord ++ tailWord_228159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228159).length < 2 ^ (prefixWord ++ tailWord_228159).sum := by decide
  have hdescent : baseEnd_228159 < baseStart_228159 := by decide
  rcases family_descends (prefixWord ++ tailWord_228159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228197 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 2]
def baseStart_228197 : Nat := 118140960795 + 228197 * 2 ^ 59
def prefixEnd_228197 : Nat := 4983230072969 + 3 ^ 40 * 228197 * 2
def baseEnd_228197 : Nat := 104155328812576810567153

theorem tailTrace_228197 : CollatzResearch.WordTrace tailWord_228197 prefixEnd_228197 104155328812576810567153 := by
  unfold tailWord_228197
  simp only [CollatzResearch.WordTrace]
  refine ⟨8323028354288716789914845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5548685569525811193276563 8323028354288716789914845)
  ·
    refine ⟨3121135632858268796218067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8323028354288716789914845 3121135632858268796218067)
    ·
      refine ⟨4681703449287403194327101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121135632858268796218067 4681703449287403194327101)
      ·
        refine ⟨1755638793482776197872663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4681703449287403194327101 1755638793482776197872663)
        ·
          refine ⟨2633458190224164296808995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755638793482776197872663 2633458190224164296808995)
          ·
            refine ⟨3950187285336246445213493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633458190224164296808995 3950187285336246445213493)
            ·
              refine ⟨370330058000273104238765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3950187285336246445213493 370330058000273104238765)
              ·
                refine ⟨138873771750102414089537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370330058000273104238765 138873771750102414089537)
                ·
                  refine ⟨104155328812576810567153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138873771750102414089537 104155328812576810567153)
                  ·
                    rfl

theorem cell20_228197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_228197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228197 prefixEnd_228197 := by exact prefixLift 228197
  have htrace : WordTrace (prefixWord ++ tailWord_228197) baseStart_228197 baseEnd_228197 := by
    simpa [prefixWord, tailWord_228197, baseEnd_228197] using wordTrace_append hprefix tailTrace_228197
  have hstable : (prefixWord ++ tailWord_228197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228197).length < 2 ^ (prefixWord ++ tailWord_228197).sum := by decide
  have hdescent : baseEnd_228197 < baseStart_228197 := by decide
  rcases family_descends (prefixWord ++ tailWord_228197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228208 : List Nat := [2, 1, 1, 1, 4, 1, 10]
def baseStart_228208 : Nat := 118140960795 + 228208 * 2 ^ 59
def prefixEnd_228208 : Nat := 4983230072969 + 3 ^ 40 * 228208 * 2
def baseEnd_228208 : Nat := 11573372168034406800049

theorem tailTrace_228208 : CollatzResearch.WordTrace tailWord_228208 prefixEnd_228208 11573372168034406800049 := by
  unfold tailWord_228208
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161714778624432834282639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5548953038165910445710185 4161714778624432834282639)
  ·
    refine ⟨6242572167936649251423959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4161714778624432834282639 6242572167936649251423959)
    ·
      refine ⟨9363858251904973877135939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242572167936649251423959 9363858251904973877135939)
      ·
        refine ⟨14045787377857460815703909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9363858251904973877135939 14045787377857460815703909)
        ·
          refine ⟨2633585133348273902944483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14045787377857460815703909 2633585133348273902944483)
          ·
            refine ⟨3950377700022410854416725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633585133348273902944483 3950377700022410854416725)
            ·
              refine ⟨11573372168034406800049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3950377700022410854416725 11573372168034406800049)
              ·
                rfl

theorem cell20_228208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_228208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228208 prefixEnd_228208 := by exact prefixLift 228208
  have htrace : WordTrace (prefixWord ++ tailWord_228208) baseStart_228208 baseEnd_228208 := by
    simpa [prefixWord, tailWord_228208, baseEnd_228208] using wordTrace_append hprefix tailTrace_228208
  have hstable : (prefixWord ++ tailWord_228208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228208).length < 2 ^ (prefixWord ++ tailWord_228208).sum := by decide
  have hdescent : baseEnd_228208 < baseStart_228208 := by decide
  rcases family_descends (prefixWord ++ tailWord_228208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228214 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_228214 : Nat := 118140960795 + 228214 * 2 ^ 59
def prefixEnd_228214 : Nat := 4983230072969 + 3 ^ 40 * 228214 * 2
def baseEnd_228214 : Nat := 104163088075800307000417

theorem tailTrace_228214 : CollatzResearch.WordTrace tailWord_228214 prefixEnd_228214 104163088075800307000417 := by
  unfold tailWord_228214
  simp only [CollatzResearch.WordTrace]
  refine ⟨520228024701695543330231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5549098930151419128855797 520228024701695543330231)
  ·
    refine ⟨780342037052543314995347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520228024701695543330231 780342037052543314995347)
    ·
      refine ⟨1170513055578814972493021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780342037052543314995347 1170513055578814972493021)
      ·
        refine ⟨438942395842055614684883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1170513055578814972493021 438942395842055614684883)
        ·
          refine ⟨658413593763083422027325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438942395842055614684883 658413593763083422027325)
          ·
            refine ⟨246905097661156283260247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658413593763083422027325 246905097661156283260247)
            ·
              refine ⟨370357646491734424890371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246905097661156283260247 370357646491734424890371)
              ·
                refine ⟨555536469737601637335557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370357646491734424890371 555536469737601637335557)
                ·
                  refine ⟨104163088075800307000417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555536469737601637335557 104163088075800307000417)
                  ·
                    rfl

theorem cell20_228214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_228214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228214 prefixEnd_228214 := by exact prefixLift 228214
  have htrace : WordTrace (prefixWord ++ tailWord_228214) baseStart_228214 baseEnd_228214 := by
    simpa [prefixWord, tailWord_228214, baseEnd_228214] using wordTrace_append hprefix tailTrace_228214
  have hstable : (prefixWord ++ tailWord_228214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228214).length < 2 ^ (prefixWord ++ tailWord_228214).sum := by decide
  have hdescent : baseEnd_228214 < baseStart_228214 := by decide
  rcases family_descends (prefixWord ++ tailWord_228214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228263 : List Nat := [1, 1, 6, 1, 3, 8]
def baseStart_228263 : Nat := 118140960795 + 228263 * 2 ^ 59
def prefixEnd_228263 : Nat := 4983230072969 + 3 ^ 40 * 228263 * 2
def baseEnd_228263 : Nat := 3858720481887922754329

theorem tailTrace_228263 : CollatzResearch.WordTrace tailWord_228263 prefixEnd_228263 3858720481887922754329 := by
  unfold tailWord_228263
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325435572049610061817443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5550290381366406707878295 8325435572049610061817443)
  ·
    refine ⟨12488153358074415092726165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8325435572049610061817443 12488153358074415092726165)
    ·
      refine ⟨585382188659738207471539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12488153358074415092726165 585382188659738207471539)
      ·
        refine ⟨878073282989607311207309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585382188659738207471539 878073282989607311207309)
        ·
          refine ⟨329277481121102741702741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878073282989607311207309 329277481121102741702741)
          ·
            refine ⟨3858720481887922754329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 329277481121102741702741 3858720481887922754329)
            ·
              rfl

theorem cell20_228263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 8].length) (baseStart_228263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228263 prefixEnd_228263 := by exact prefixLift 228263
  have htrace : WordTrace (prefixWord ++ tailWord_228263) baseStart_228263 baseEnd_228263 := by
    simpa [prefixWord, tailWord_228263, baseEnd_228263] using wordTrace_append hprefix tailTrace_228263
  have hstable : (prefixWord ++ tailWord_228263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228263).length < 2 ^ (prefixWord ++ tailWord_228263).sum := by decide
  have hdescent : baseEnd_228263 < baseStart_228263 := by decide
  rcases family_descends (prefixWord ++ tailWord_228263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228269 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 2]
def baseStart_228269 : Nat := 118140960795 + 228269 * 2 ^ 59
def prefixEnd_228269 : Nat := 4983230072969 + 3 ^ 40 * 228269 * 2
def baseEnd_228269 : Nat := 104188191574464560166859

theorem tailTrace_228269 : CollatzResearch.WordTrace tailWord_228269 prefixEnd_228269 104188191574464560166859 := by
  unfold tailWord_228269
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325654410027873086535861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5550436273351915391023907 8325654410027873086535861)
  ·
    refine ⟨780530100940113101862737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8325654410027873086535861 780530100940113101862737)
    ·
      refine ⟨585397575705084826397053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 780530100940113101862737 585397575705084826397053)
      ·
        refine ⟨219524090889406809898895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585397575705084826397053 219524090889406809898895)
        ·
          refine ⟨329286136334110214848343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219524090889406809898895 329286136334110214848343)
          ·
            refine ⟨493929204501165322272515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329286136334110214848343 493929204501165322272515)
            ·
              refine ⟨740893806751747983408773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493929204501165322272515 740893806751747983408773)
              ·
                refine ⟨138917588765952746889145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740893806751747983408773 138917588765952746889145)
                ·
                  refine ⟨104188191574464560166859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138917588765952746889145 104188191574464560166859)
                  ·
                    rfl

theorem cell20_228269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_228269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228269 prefixEnd_228269 := by exact prefixLift 228269
  have htrace : WordTrace (prefixWord ++ tailWord_228269) baseStart_228269 baseEnd_228269 := by
    simpa [prefixWord, tailWord_228269, baseEnd_228269] using wordTrace_append hprefix tailTrace_228269
  have hstable : (prefixWord ++ tailWord_228269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228269).length < 2 ^ (prefixWord ++ tailWord_228269).sum := by decide
  have hdescent : baseEnd_228269 < baseStart_228269 := by decide
  rcases family_descends (prefixWord ++ tailWord_228269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228346 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_228346 : Nat := 118140960795 + 228346 * 2 ^ 59
def prefixEnd_228346 : Nat := 4983230072969 + 3 ^ 40 * 228346 * 2
def baseEnd_228346 : Nat := 104223336472594514599877

theorem tailTrace_228346 : CollatzResearch.WordTrace tailWord_228346 prefixEnd_228346 104223336472594514599877 := by
  unfold tailWord_228346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082115707687228809272223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5552308553832610158059261 2082115707687228809272223)
  ·
    refine ⟨3123173561530843213908335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082115707687228809272223 3123173561530843213908335)
    ·
      refine ⟨4684760342296264820862503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123173561530843213908335 4684760342296264820862503)
      ·
        refine ⟨7027140513444397231293755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684760342296264820862503 7027140513444397231293755)
        ·
          refine ⟨10540710770166595846940633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027140513444397231293755 10540710770166595846940633)
          ·
            refine ⟨7905533077624946885205475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540710770166595846940633 7905533077624946885205475)
            ·
              refine ⟨11858299616437420327808213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905533077624946885205475 11858299616437420327808213)
              ·
                refine ⟨277928897260252038933005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11858299616437420327808213 277928897260252038933005)
                ·
                  refine ⟨104223336472594514599877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277928897260252038933005 104223336472594514599877)
                  ·
                    rfl

theorem cell20_228346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_228346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228346 prefixEnd_228346 := by exact prefixLift 228346
  have htrace : WordTrace (prefixWord ++ tailWord_228346) baseStart_228346 baseEnd_228346 := by
    simpa [prefixWord, tailWord_228346, baseEnd_228346] using wordTrace_append hprefix tailTrace_228346
  have hstable : (prefixWord ++ tailWord_228346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228346).length < 2 ^ (prefixWord ++ tailWord_228346).sum := by decide
  have hdescent : baseEnd_228346 < baseStart_228346 := by decide
  rcases family_descends (prefixWord ++ tailWord_228346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228366 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_228366 : Nat := 118140960795 + 228366 * 2 ^ 59
def prefixEnd_228366 : Nat := 4983230072969 + 3 ^ 40 * 228366 * 2
def baseEnd_228366 : Nat := 104232465017563333933129

theorem tailTrace_228366 : CollatzResearch.WordTrace tailWord_228366 prefixEnd_228366 104232465017563333933129 := by
  unfold tailWord_228366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041149036334557331602119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5552794860450972435211301 1041149036334557331602119)
  ·
    refine ⟨1561723554501835997403179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1041149036334557331602119 1561723554501835997403179)
    ·
      refine ⟨2342585331752753996104769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1561723554501835997403179 2342585331752753996104769)
      ·
        refine ⟨1756938998814565497078577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2342585331752753996104769 1756938998814565497078577)
        ·
          refine ⟨1317704249110924122808933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756938998814565497078577 1317704249110924122808933)
          ·
            refine ⟨247069546708298273026675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1317704249110924122808933 247069546708298273026675)
            ·
              refine ⟨370604320062447409540013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247069546708298273026675 370604320062447409540013)
              ·
                refine ⟨138976620023417778577505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370604320062447409540013 138976620023417778577505)
                ·
                  refine ⟨104232465017563333933129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138976620023417778577505 104232465017563333933129)
                  ·
                    rfl

theorem cell20_228366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_228366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228366 prefixEnd_228366 := by exact prefixLift 228366
  have htrace : WordTrace (prefixWord ++ tailWord_228366) baseStart_228366 baseEnd_228366 := by
    simpa [prefixWord, tailWord_228366, baseEnd_228366] using wordTrace_append hprefix tailTrace_228366
  have hstable : (prefixWord ++ tailWord_228366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228366).length < 2 ^ (prefixWord ++ tailWord_228366).sum := by decide
  have hdescent : baseEnd_228366 < baseStart_228366 := by decide
  rcases family_descends (prefixWord ++ tailWord_228366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228394 : List Nat := [3, 1, 4, 1, 3, 1, 2, 5]
def baseStart_228394 : Nat := 118140960795 + 228394 * 2 ^ 59
def prefixEnd_228394 : Nat := 4983230072969 + 3 ^ 40 * 228394 * 2
def baseEnd_228394 : Nat := 34748414993506560333227

theorem tailTrace_228394 : CollatzResearch.WordTrace tailWord_228394 prefixEnd_228394 34748414993506560333227 := by
  unfold tailWord_228394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082553383643754858709059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5553475689716679623224157 2082553383643754858709059)
  ·
    refine ⟨3123830075465632288063589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082553383643754858709059 3123830075465632288063589)
    ·
      refine ⟨585718139149806054011923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3123830075465632288063589 585718139149806054011923)
      ·
        refine ⟨878577208724709081017885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585718139149806054011923 878577208724709081017885)
        ·
          refine ⟨329466453271765905381707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878577208724709081017885 329466453271765905381707)
          ·
            refine ⟨494199679907648858072561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329466453271765905381707 494199679907648858072561)
            ·
              refine ⟨370649759930736643554421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494199679907648858072561 370649759930736643554421)
              ·
                refine ⟨34748414993506560333227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370649759930736643554421 34748414993506560333227)
                ·
                  rfl

theorem cell20_228394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_228394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228394 prefixEnd_228394 := by exact prefixLift 228394
  have htrace : WordTrace (prefixWord ++ tailWord_228394) baseStart_228394 baseEnd_228394 := by
    simpa [prefixWord, tailWord_228394, baseEnd_228394] using wordTrace_append hprefix tailTrace_228394
  have hstable : (prefixWord ++ tailWord_228394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228394).length < 2 ^ (prefixWord ++ tailWord_228394).sum := by decide
  have hdescent : baseEnd_228394 < baseStart_228394 := by decide
  rcases family_descends (prefixWord ++ tailWord_228394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228460 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_228460 : Nat := 118140960795 + 228460 * 2 ^ 59
def prefixEnd_228460 : Nat := 4983230072969 + 3 ^ 40 * 228460 * 2
def baseEnd_228460 : Nat := 104275369178916784799411

theorem tailTrace_228460 : CollatzResearch.WordTrace tailWord_228460 prefixEnd_228460 104275369178916784799411 := by
  unfold tailWord_228460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166310376167956353369417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5555080501557275137825889 4166310376167956353369417)
  ·
    refine ⟨3124732782125967265027063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4166310376167956353369417 3124732782125967265027063)
    ·
      refine ⟨4687099173188950897540595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124732782125967265027063 4687099173188950897540595)
      ·
        refine ⟨7030648759783426346310893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687099173188950897540595 7030648759783426346310893)
        ·
          refine ⟨2636493284918784879866585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7030648759783426346310893 2636493284918784879866585)
          ·
            refine ⟨1977369963689088659899939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2636493284918784879866585 1977369963689088659899939)
            ·
              refine ⟨2966054945533632989849909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977369963689088659899939 2966054945533632989849909)
              ·
                refine ⟨278067651143778092798429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2966054945533632989849909 278067651143778092798429)
                ·
                  refine ⟨104275369178916784799411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278067651143778092798429 104275369178916784799411)
                  ·
                    rfl

theorem cell20_228460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_228460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228460 prefixEnd_228460 := by exact prefixLift 228460
  have htrace : WordTrace (prefixWord ++ tailWord_228460) baseStart_228460 baseEnd_228460 := by
    simpa [prefixWord, tailWord_228460, baseEnd_228460] using wordTrace_append hprefix tailTrace_228460
  have hstable : (prefixWord ++ tailWord_228460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228460).length < 2 ^ (prefixWord ++ tailWord_228460).sum := by decide
  have hdescent : baseEnd_228460 < baseStart_228460 := by decide
  rcases family_descends (prefixWord ++ tailWord_228460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228470 : List Nat := [5, 1, 1, 2, 1, 1, 5, 4]
def baseStart_228470 : Nat := 118140960795 + 228470 * 2 ^ 59
def prefixEnd_228470 : Nat := 4983230072969 + 3 ^ 40 * 228470 * 2
def baseEnd_228470 : Nat := 34759977817133731488679

theorem tailTrace_228470 : CollatzResearch.WordTrace tailWord_228470 prefixEnd_228470 34759977817133731488679 := by
  unfold tailWord_228470
  simp only [CollatzResearch.WordTrace]
  refine ⟨520811592643730275912679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5555323654866456276401909 520811592643730275912679)
  ·
    refine ⟨781217388965595413869019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520811592643730275912679 781217388965595413869019)
    ·
      refine ⟨1171826083448393120803529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781217388965595413869019 1171826083448393120803529)
      ·
        refine ⟨878869562586294840602647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171826083448393120803529 878869562586294840602647)
        ·
          refine ⟨1318304343879442260903971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878869562586294840602647 1318304343879442260903971)
          ·
            refine ⟨1977456515819163391355957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318304343879442260903971 1977456515819163391355957)
            ·
              refine ⟨185386548358046567939621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1977456515819163391355957 185386548358046567939621)
              ·
                refine ⟨34759977817133731488679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185386548358046567939621 34759977817133731488679)
                ·
                  rfl

theorem cell20_228470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_228470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228470 prefixEnd_228470 := by exact prefixLift 228470
  have htrace : WordTrace (prefixWord ++ tailWord_228470) baseStart_228470 baseEnd_228470 := by
    simpa [prefixWord, tailWord_228470, baseEnd_228470] using wordTrace_append hprefix tailTrace_228470
  have hstable : (prefixWord ++ tailWord_228470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228470).length < 2 ^ (prefixWord ++ tailWord_228470).sum := by decide
  have hdescent : baseEnd_228470 < baseStart_228470 := by decide
  rcases family_descends (prefixWord ++ tailWord_228470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228494 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_228494 : Nat := 118140960795 + 228494 * 2 ^ 59
def prefixEnd_228494 : Nat := 4983230072969 + 3 ^ 40 * 228494 * 2
def baseEnd_228494 : Nat := 104290887705363777665939

theorem tailTrace_228494 : CollatzResearch.WordTrace tailWord_228494 prefixEnd_228494 104290887705363777665939 := by
  unfold tailWord_228494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041732604276592064184567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5555907222808491008984357 1041732604276592064184567)
  ·
    refine ⟨1562598906414888096276851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1041732604276592064184567 1562598906414888096276851)
    ·
      refine ⟨2343898359622332144415277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562598906414888096276851 2343898359622332144415277)
      ·
        refine ⟨878961884858374554155729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2343898359622332144415277 878961884858374554155729)
        ·
          refine ⟨659221413643780915616797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878961884858374554155729 659221413643780915616797)
          ·
            refine ⟨247208030116417843356299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659221413643780915616797 247208030116417843356299)
            ·
              refine ⟨370812045174626765034449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247208030116417843356299 370812045174626765034449)
              ·
                refine ⟨278109033880970073775837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370812045174626765034449 278109033880970073775837)
                ·
                  refine ⟨104290887705363777665939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278109033880970073775837 104290887705363777665939)
                  ·
                    rfl

theorem cell20_228494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_228494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228494 prefixEnd_228494 := by exact prefixLift 228494
  have htrace : WordTrace (prefixWord ++ tailWord_228494) baseStart_228494 baseEnd_228494 := by
    simpa [prefixWord, tailWord_228494, baseEnd_228494] using wordTrace_append hprefix tailTrace_228494
  have hstable : (prefixWord ++ tailWord_228494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228494).length < 2 ^ (prefixWord ++ tailWord_228494).sum := by decide
  have hdescent : baseEnd_228494 < baseStart_228494 := by decide
  rcases family_descends (prefixWord ++ tailWord_228494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228512 : List Nat := [2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_228512 : Nat := 118140960795 + 228512 * 2 ^ 59
def prefixEnd_228512 : Nat := 4983230072969 + 3 ^ 40 * 228512 * 2
def baseEnd_228512 : Nat := 34766367798611905021955

theorem tailTrace_228512 : CollatzResearch.WordTrace tailWord_228512 prefixEnd_228512 34766367798611905021955 := by
  unfold tailWord_228512
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167258674073762793815895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5556344898765017058421193 4167258674073762793815895)
  ·
    refine ⟨6250888011110644190723843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4167258674073762793815895 6250888011110644190723843)
    ·
      refine ⟨9376332016665966286085765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6250888011110644190723843 9376332016665966286085765)
      ·
        refine ⟨1758062253124868678641081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9376332016665966286085765 1758062253124868678641081)
        ·
          refine ⟨1318546689843651508980811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1758062253124868678641081 1318546689843651508980811)
          ·
            refine ⟨1977820034765477263471217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318546689843651508980811 1977820034765477263471217)
            ·
              refine ⟨1483365026074107947603413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977820034765477263471217 1483365026074107947603413)
              ·
                refine ⟨34766367798611905021955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1483365026074107947603413 34766367798611905021955)
                ·
                  rfl

theorem cell20_228512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_228512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228512 prefixEnd_228512 := by exact prefixLift 228512
  have htrace : WordTrace (prefixWord ++ tailWord_228512) baseStart_228512 baseEnd_228512 := by
    simpa [prefixWord, tailWord_228512, baseEnd_228512] using wordTrace_append hprefix tailTrace_228512
  have hstable : (prefixWord ++ tailWord_228512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228512).length < 2 ^ (prefixWord ++ tailWord_228512).sum := by decide
  have hdescent : baseEnd_228512 < baseStart_228512 := by decide
  rcases family_descends (prefixWord ++ tailWord_228512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228525 : List Nat := [1, 5, 2, 1, 3, 2, 2, 4]
def baseStart_228525 : Nat := 118140960795 + 228525 * 2 ^ 59
def prefixEnd_228525 : Nat := 4983230072969 + 3 ^ 40 * 228525 * 2
def baseEnd_228525 : Nat := 34768345650021815877493

theorem tailTrace_228525 : CollatzResearch.WordTrace tailWord_228525 prefixEnd_228525 34768345650021815877493 := by
  unfold tailWord_228525
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334991497100428807855029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5556660998066952538570019 8334991497100428807855029)
  ·
    refine ⟨781405452853165200736409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8334991497100428807855029 781405452853165200736409)
    ·
      refine ⟨586054089639873900552307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781405452853165200736409 586054089639873900552307)
      ·
        refine ⟨879081134459810850828461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586054089639873900552307 879081134459810850828461)
        ·
          refine ⟨329655425422429069060673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879081134459810850828461 329655425422429069060673)
          ·
            refine ⟨247241569066821801795505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329655425422429069060673 247241569066821801795505)
            ·
              refine ⟨185431176800116351346629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247241569066821801795505 185431176800116351346629)
              ·
                refine ⟨34768345650021815877493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185431176800116351346629 34768345650021815877493)
                ·
                  rfl

theorem cell20_228525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_228525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228525 prefixEnd_228525 := by exact prefixLift 228525
  have htrace : WordTrace (prefixWord ++ tailWord_228525) baseStart_228525 baseEnd_228525 := by
    simpa [prefixWord, tailWord_228525, baseEnd_228525] using wordTrace_append hprefix tailTrace_228525
  have hstable : (prefixWord ++ tailWord_228525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228525).length < 2 ^ (prefixWord ++ tailWord_228525).sum := by decide
  have hdescent : baseEnd_228525 < baseStart_228525 := by decide
  rcases family_descends (prefixWord ++ tailWord_228525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228529 : List Nat := [1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_228529 : Nat := 118140960795 + 228529 * 2 ^ 59
def prefixEnd_228529 : Nat := 4983230072969 + 3 ^ 40 * 228529 * 2
def baseEnd_228529 : Nat := 34768954219686403833043

theorem tailTrace_228529 : CollatzResearch.WordTrace tailWord_228529 prefixEnd_228529 34768954219686403833043 := by
  unfold tailWord_228529
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335137389085937491000641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5556758259390624994000427 8335137389085937491000641)
  ·
    refine ⟨6251353041814453118250481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8335137389085937491000641 6251353041814453118250481)
    ·
      refine ⟨4688514781360839838687861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6251353041814453118250481 4688514781360839838687861)
      ·
        refine ⟨439548260752578734876987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4688514781360839838687861 439548260752578734876987)
        ·
          refine ⟨659322391128868102315481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439548260752578734876987 659322391128868102315481)
          ·
            refine ⟨494491793346651076736611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659322391128868102315481 494491793346651076736611)
            ·
              refine ⟨741737690019976615104917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494491793346651076736611 741737690019976615104917)
              ·
                refine ⟨34768954219686403833043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 741737690019976615104917 34768954219686403833043)
                ·
                  rfl

theorem cell20_228529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_228529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228529 prefixEnd_228529 := by exact prefixLift 228529
  have htrace : WordTrace (prefixWord ++ tailWord_228529) baseStart_228529 baseEnd_228529 := by
    simpa [prefixWord, tailWord_228529, baseEnd_228529] using wordTrace_append hprefix tailTrace_228529
  have hstable : (prefixWord ++ tailWord_228529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228529).length < 2 ^ (prefixWord ++ tailWord_228529).sum := by decide
  have hdescent : baseEnd_228529 < baseStart_228529 := by decide
  rcases family_descends (prefixWord ++ tailWord_228529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228566 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_228566 : Nat := 118140960795 + 228566 * 2 ^ 59
def prefixEnd_228566 : Nat := 4983230072969 + 3 ^ 40 * 228566 * 2
def baseEnd_228566 : Nat := 104323750467251527265645

theorem tailTrace_228566 : CollatzResearch.WordTrace tailWord_228566 prefixEnd_228566 104323750467251527265645 := by
  unfold tailWord_228566
  simp only [CollatzResearch.WordTrace]
  refine ⟨521030430621993300631097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5557657926634595206731701 521030430621993300631097)
  ·
    refine ⟨390772822966494975473323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521030430621993300631097 390772822966494975473323)
    ·
      refine ⟨586159234449742463209985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390772822966494975473323 586159234449742463209985)
      ·
        refine ⟨439619425837306847407489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586159234449742463209985 439619425837306847407489)
        ·
          refine ⟨329714569377980135555617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439619425837306847407489 329714569377980135555617)
          ·
            refine ⟨247285927033485101666713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329714569377980135555617 247285927033485101666713)
            ·
              refine ⟨185464445275113826250035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247285927033485101666713 185464445275113826250035)
              ·
                refine ⟨278196667912670739375053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185464445275113826250035 278196667912670739375053)
                ·
                  refine ⟨104323750467251527265645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278196667912670739375053 104323750467251527265645)
                  ·
                    rfl

theorem cell20_228566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_228566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228566 prefixEnd_228566 := by exact prefixLift 228566
  have htrace : WordTrace (prefixWord ++ tailWord_228566) baseStart_228566 baseEnd_228566 := by
    simpa [prefixWord, tailWord_228566, baseEnd_228566] using wordTrace_append hprefix tailTrace_228566
  have hstable : (prefixWord ++ tailWord_228566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228566).length < 2 ^ (prefixWord ++ tailWord_228566).sum := by decide
  have hdescent : baseEnd_228566 < baseStart_228566 := by decide
  rcases family_descends (prefixWord ++ tailWord_228566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228588 : List Nat := [2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_228588 : Nat := 118140960795 + 228588 * 2 ^ 59
def prefixEnd_228588 : Nat := 4983230072969 + 3 ^ 40 * 228588 * 2
def baseEnd_228588 : Nat := 34777930622239076177407

theorem tailTrace_228588 : CollatzResearch.WordTrace tailWord_228588 prefixEnd_228588 34777930622239076177407 := by
  unfold tailWord_228588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168644647936095283699209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5558192863914793711598945 4168644647936095283699209)
  ·
    refine ⟨3126483485952071462774407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4168644647936095283699209 3126483485952071462774407)
    ·
      refine ⟨4689725228928107194161611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3126483485952071462774407 4689725228928107194161611)
      ·
        refine ⟨7034587843392160791242417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689725228928107194161611 7034587843392160791242417)
        ·
          refine ⟨5275940882544120593431813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7034587843392160791242417 5275940882544120593431813)
          ·
            refine ⟨989238915477022611268465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5275940882544120593431813 989238915477022611268465)
            ·
              refine ⟨741929186607766958451349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989238915477022611268465 741929186607766958451349)
              ·
                refine ⟨34777930622239076177407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 741929186607766958451349 34777930622239076177407)
                ·
                  rfl

theorem cell20_228588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_228588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228588 prefixEnd_228588 := by exact prefixLift 228588
  have htrace : WordTrace (prefixWord ++ tailWord_228588) baseStart_228588 baseEnd_228588 := by
    simpa [prefixWord, tailWord_228588, baseEnd_228588] using wordTrace_append hprefix tailTrace_228588
  have hstable : (prefixWord ++ tailWord_228588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228588).length < 2 ^ (prefixWord ++ tailWord_228588).sum := by decide
  have hdescent : baseEnd_228588 < baseStart_228588 := by decide
  rcases family_descends (prefixWord ++ tailWord_228588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228643 : List Nat := [1, 1, 1, 4, 2, 4, 3, 4]
def baseStart_228643 : Nat := 118140960795 + 228643 * 2 ^ 59
def prefixEnd_228643 : Nat := 4983230072969 + 3 ^ 40 * 228643 * 2
def baseEnd_228643 : Nat := 34786298455127160566221

theorem tailTrace_228643 : CollatzResearch.WordTrace tailWord_228643 prefixEnd_228643 34786298455127160566221 := by
  unfold tailWord_228643
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339295310672934960650583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5559530207115289973767055 8339295310672934960650583)
  ·
    refine ⟨12508942966009402440975875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8339295310672934960650583 12508942966009402440975875)
    ·
      refine ⟨18763414449014103661463813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508942966009402440975875 18763414449014103661463813)
      ·
        refine ⟨3518140209190144436524465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18763414449014103661463813 3518140209190144436524465)
        ·
          refine ⟨2638605156892608327393349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518140209190144436524465 2638605156892608327393349)
          ·
            refine ⟨494738466917364061386253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2638605156892608327393349 494738466917364061386253)
            ·
              refine ⟨185526925094011523019845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494738466917364061386253 185526925094011523019845)
              ·
                refine ⟨34786298455127160566221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185526925094011523019845 34786298455127160566221)
                ·
                  rfl

theorem cell20_228643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_228643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228643 prefixEnd_228643 := by exact prefixLift 228643
  have htrace : WordTrace (prefixWord ++ tailWord_228643) baseStart_228643 baseEnd_228643 := by
    simpa [prefixWord, tailWord_228643, baseEnd_228643] using wordTrace_append hprefix tailTrace_228643
  have hstable : (prefixWord ++ tailWord_228643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228643).length < 2 ^ (prefixWord ++ tailWord_228643).sum := by decide
  have hdescent : baseEnd_228643 < baseStart_228643 := by decide
  rcases family_descends (prefixWord ++ tailWord_228643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228694 : List Nat := [5, 2, 3, 1, 1, 1, 1, 6]
def baseStart_228694 : Nat := 118140960795 + 228694 * 2 ^ 59
def prefixEnd_228694 : Nat := 4983230072969 + 3 ^ 40 * 228694 * 2
def baseEnd_228694 : Nat := 34794057718350656999485

theorem tailTrace_228694 : CollatzResearch.WordTrace tailWord_228694 prefixEnd_228694 34794057718350656999485 := by
  unfold tailWord_228694
  simp only [CollatzResearch.WordTrace]
  refine ⟨521322214593010666922321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5560770288992113780504757 521322214593010666922321)
  ·
    refine ⟨390991660944758000191741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521322214593010666922321 390991660944758000191741)
    ·
      refine ⟨146621872854284250071903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 390991660944758000191741 146621872854284250071903)
      ·
        refine ⟨219932809281426375107855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146621872854284250071903 219932809281426375107855)
        ·
          refine ⟨329899213922139562661783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219932809281426375107855 329899213922139562661783)
          ·
            refine ⟨494848820883209343992675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329899213922139562661783 494848820883209343992675)
            ·
              refine ⟨742273231324814015989013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494848820883209343992675 742273231324814015989013)
              ·
                refine ⟨34794057718350656999485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 742273231324814015989013 34794057718350656999485)
                ·
                  rfl

theorem cell20_228694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_228694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228694 prefixEnd_228694 := by exact prefixLift 228694
  have htrace : WordTrace (prefixWord ++ tailWord_228694) baseStart_228694 baseEnd_228694 := by
    simpa [prefixWord, tailWord_228694, baseEnd_228694] using wordTrace_append hprefix tailTrace_228694
  have hstable : (prefixWord ++ tailWord_228694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228694).length < 2 ^ (prefixWord ++ tailWord_228694).sum := by decide
  have hdescent : baseEnd_228694 < baseStart_228694 := by decide
  rcases family_descends (prefixWord ++ tailWord_228694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228695 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_228695 : Nat := 118140960795 + 228695 * 2 ^ 59
def prefixEnd_228695 : Nat := 4983230072969 + 3 ^ 40 * 228695 * 2
def baseEnd_228695 : Nat := 104382629582300411965117

theorem tailTrace_228695 : CollatzResearch.WordTrace tailWord_228695 prefixEnd_228695 104382629582300411965117 := by
  unfold tailWord_228695
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341191906484547841543539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5560794604323031894362359 8341191906484547841543539)
  ·
    refine ⟨12511787859726821762315309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8341191906484547841543539 12511787859726821762315309)
    ·
      refine ⟨4691920447397558160868241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12511787859726821762315309 4691920447397558160868241)
      ·
        refine ⟨3518940335548168620651181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4691920447397558160868241 3518940335548168620651181)
        ·
          refine ⟨1319602625830563232744193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3518940335548168620651181 1319602625830563232744193)
          ·
            refine ⟨989701969372922424558145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319602625830563232744193 989701969372922424558145)
            ·
              refine ⟨742276477029691818418609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989701969372922424558145 742276477029691818418609)
              ·
                refine ⟨556707357772268863813957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 742276477029691818418609 556707357772268863813957)
                ·
                  refine ⟨104382629582300411965117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556707357772268863813957 104382629582300411965117)
                  ·
                    rfl

theorem cell20_228695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_228695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228695 prefixEnd_228695 := by exact prefixLift 228695
  have htrace : WordTrace (prefixWord ++ tailWord_228695) baseStart_228695 baseEnd_228695 := by
    simpa [prefixWord, tailWord_228695, baseEnd_228695] using wordTrace_append hprefix tailTrace_228695
  have hstable : (prefixWord ++ tailWord_228695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228695).length < 2 ^ (prefixWord ++ tailWord_228695).sum := by decide
  have hdescent : baseEnd_228695 < baseStart_228695 := by decide
  rcases family_descends (prefixWord ++ tailWord_228695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228709 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_228709 : Nat := 118140960795 + 228709 * 2 ^ 59
def prefixEnd_228709 : Nat := 4983230072969 + 3 ^ 40 * 228709 * 2
def baseEnd_228709 : Nat := 104389019563778585498393

theorem tailTrace_228709 : CollatzResearch.WordTrace tailWord_228709 prefixEnd_228709 104389019563778585498393 := by
  unfold tailWord_228709
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341702528433828232553181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5561135018955885488368787 8341702528433828232553181)
  ·
    refine ⟨3128138448162685587207443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8341702528433828232553181 3128138448162685587207443)
    ·
      refine ⟨4692207672244028380811165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128138448162685587207443 4692207672244028380811165)
      ·
        refine ⟨1759577877091510642804187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4692207672244028380811165 1759577877091510642804187)
        ·
          refine ⟨2639366815637265964206281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759577877091510642804187 2639366815637265964206281)
          ·
            refine ⟨1979525111727949473154711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639366815637265964206281 1979525111727949473154711)
            ·
              refine ⟨2969287667591924209732067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979525111727949473154711 2969287667591924209732067)
              ·
                refine ⟨4453931501387886314598101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969287667591924209732067 4453931501387886314598101)
                ·
                  refine ⟨104389019563778585498393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4453931501387886314598101 104389019563778585498393)
                  ·
                    rfl

theorem cell20_228709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_228709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228709 prefixEnd_228709 := by exact prefixLift 228709
  have htrace : WordTrace (prefixWord ++ tailWord_228709) baseStart_228709 baseEnd_228709 := by
    simpa [prefixWord, tailWord_228709, baseEnd_228709] using wordTrace_append hprefix tailTrace_228709
  have hstable : (prefixWord ++ tailWord_228709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228709).length < 2 ^ (prefixWord ++ tailWord_228709).sum := by decide
  have hdescent : baseEnd_228709 < baseStart_228709 := by decide
  rcases family_descends (prefixWord ++ tailWord_228709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228740 : List Nat := [2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_228740 : Nat := 118140960795 + 228740 * 2 ^ 59
def prefixEnd_228740 : Nat := 4983230072969 + 3 ^ 40 * 228740 * 2
def baseEnd_228740 : Nat := 34801056269493418488311

theorem tailTrace_228740 : CollatzResearch.WordTrace tailWord_228740 prefixEnd_228740 34801056269493418488311 := by
  unfold tailWord_228740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171416595660760263465837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5561888794214347017954449 4171416595660760263465837)
  ·
    refine ⟨1564281223372785098799689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4171416595660760263465837 1564281223372785098799689)
    ·
      refine ⟨1173210917529588824099767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1564281223372785098799689 1173210917529588824099767)
      ·
        refine ⟨1759816376294383236149651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173210917529588824099767 1759816376294383236149651)
        ·
          refine ⟨2639724564441574854224477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759816376294383236149651 2639724564441574854224477)
          ·
            refine ⟨989896711665590570334179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2639724564441574854224477 989896711665590570334179)
            ·
              refine ⟨1484845067498385855501269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989896711665590570334179 1484845067498385855501269)
              ·
                refine ⟨34801056269493418488311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1484845067498385855501269 34801056269493418488311)
                ·
                  rfl

theorem cell20_228740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_228740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228740 prefixEnd_228740 := by exact prefixLift 228740
  have htrace : WordTrace (prefixWord ++ tailWord_228740) baseStart_228740 baseEnd_228740 := by
    simpa [prefixWord, tailWord_228740, baseEnd_228740] using wordTrace_append hprefix tailTrace_228740
  have hstable : (prefixWord ++ tailWord_228740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228740).length < 2 ^ (prefixWord ++ tailWord_228740).sum := by decide
  have hdescent : baseEnd_228740 < baseStart_228740 := by decide
  rcases family_descends (prefixWord ++ tailWord_228740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228743 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 3]
def baseStart_228743 : Nat := 118140960795 + 228743 * 2 ^ 59
def prefixEnd_228743 : Nat := 4983230072969 + 3 ^ 40 * 228743 * 2
def baseEnd_228743 : Nat := 104404538090225578364921

theorem tailTrace_228743 : CollatzResearch.WordTrace tailWord_228743 prefixEnd_228743 104404538090225578364921 := by
  unfold tailWord_228743
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342942610310652039290883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5561961740207101359527255 8342942610310652039290883)
  ·
    refine ⟨12514413915465978058936325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8342942610310652039290883 12514413915465978058936325)
    ·
      refine ⟨2346452609149870886050561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12514413915465978058936325 2346452609149870886050561)
      ·
        refine ⟨1759839456862403164537921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2346452609149870886050561 1759839456862403164537921)
        ·
          refine ⟨1319879592646802373403441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1759839456862403164537921 1319879592646802373403441)
          ·
            refine ⟨989909694485101780052581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319879592646802373403441 989909694485101780052581)
            ·
              refine ⟨185608067715956583759859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 989909694485101780052581 185608067715956583759859)
              ·
                refine ⟨278412101573934875639789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185608067715956583759859 278412101573934875639789)
                ·
                  refine ⟨104404538090225578364921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278412101573934875639789 104404538090225578364921)
                  ·
                    rfl

theorem cell20_228743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_228743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228743 prefixEnd_228743 := by exact prefixLift 228743
  have htrace : WordTrace (prefixWord ++ tailWord_228743) baseStart_228743 baseEnd_228743 := by
    simpa [prefixWord, tailWord_228743, baseEnd_228743] using wordTrace_append hprefix tailTrace_228743
  have hstable : (prefixWord ++ tailWord_228743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228743).length < 2 ^ (prefixWord ++ tailWord_228743).sum := by decide
  have hdescent : baseEnd_228743 < baseStart_228743 := by decide
  rcases family_descends (prefixWord ++ tailWord_228743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228781 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_228781 : Nat := 118140960795 + 228781 * 2 ^ 59
def prefixEnd_228781 : Nat := 4983230072969 + 3 ^ 40 * 228781 * 2
def baseEnd_228781 : Nat := 104421882325666335098099

theorem tailTrace_228781 : CollatzResearch.WordTrace tailWord_228781 prefixEnd_228781 104421882325666335098099 := by
  unfold tailWord_228781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344328584172984529174197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5562885722781989686116131 8344328584172984529174197)
  ·
    refine ⟨782280804766217299610081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8344328584172984529174197 782280804766217299610081)
    ·
      refine ⟨586710603574662974707561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 782280804766217299610081 586710603574662974707561)
      ·
        refine ⟨440032952680997231030671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586710603574662974707561 440032952680997231030671)
        ·
          refine ⟨660049429021495846546007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440032952680997231030671 660049429021495846546007)
          ·
            refine ⟨990074143532243769819011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660049429021495846546007 990074143532243769819011)
            ·
              refine ⟨1485111215298365654728517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990074143532243769819011 1485111215298365654728517)
              ·
                refine ⟨278458352868443560261597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1485111215298365654728517 278458352868443560261597)
                ·
                  refine ⟨104421882325666335098099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278458352868443560261597 104421882325666335098099)
                  ·
                    rfl

theorem cell20_228781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_228781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228781 prefixEnd_228781 := by exact prefixLift 228781
  have htrace : WordTrace (prefixWord ++ tailWord_228781) baseStart_228781 baseEnd_228781 := by
    simpa [prefixWord, tailWord_228781, baseEnd_228781] using wordTrace_append hprefix tailTrace_228781
  have hstable : (prefixWord ++ tailWord_228781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228781).length < 2 ^ (prefixWord ++ tailWord_228781).sum := by decide
  have hdescent : baseEnd_228781 < baseStart_228781 := by decide
  rcases family_descends (prefixWord ++ tailWord_228781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228822 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_228822 : Nat := 118140960795 + 228822 * 2 ^ 59
def prefixEnd_228822 : Nat := 4983230072969 + 3 ^ 40 * 228822 * 2
def baseEnd_228822 : Nat := 104440595842852414731265

theorem tailTrace_228822 : CollatzResearch.WordTrace tailWord_228822 prefixEnd_228822 104440595842852414731265 := by
  unfold tailWord_228822
  simp only [CollatzResearch.WordTrace]
  refine ⟨521613998564028033213545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5563882651349632354277813 521613998564028033213545)
  ·
    refine ⟨391210498923021024910159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521613998564028033213545 391210498923021024910159)
    ·
      refine ⟨586815748384531537365239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391210498923021024910159 586815748384531537365239)
      ·
        refine ⟨880223622576797306047859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586815748384531537365239 880223622576797306047859)
        ·
          refine ⟨1320335433865195959071789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880223622576797306047859 1320335433865195959071789)
          ·
            refine ⟨495125787699448484651921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1320335433865195959071789 495125787699448484651921)
            ·
              refine ⟨371344340774586363488941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495125787699448484651921 371344340774586363488941)
              ·
                refine ⟨139254127790469886308353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371344340774586363488941 139254127790469886308353)
                ·
                  refine ⟨104440595842852414731265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139254127790469886308353 104440595842852414731265)
                  ·
                    rfl

theorem cell20_228822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_228822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228822 prefixEnd_228822 := by exact prefixLift 228822
  have htrace : WordTrace (prefixWord ++ tailWord_228822) baseStart_228822 baseEnd_228822 := by
    simpa [prefixWord, tailWord_228822, baseEnd_228822] using wordTrace_append hprefix tailTrace_228822
  have hstable : (prefixWord ++ tailWord_228822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228822).length < 2 ^ (prefixWord ++ tailWord_228822).sum := by decide
  have hdescent : baseEnd_228822 < baseStart_228822 := by decide
  rcases family_descends (prefixWord ++ tailWord_228822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228826 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_228826 : Nat := 118140960795 + 228826 * 2 ^ 59
def prefixEnd_228826 : Nat := 4983230072969 + 3 ^ 40 * 228826 * 2
def baseEnd_228826 : Nat := 104442421551846178597915

theorem tailTrace_228826 : CollatzResearch.WordTrace tailWord_228826 prefixEnd_228826 104442421551846178597915 := by
  unfold tailWord_228826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086492467252489303640583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5563979912673304809708221 2086492467252489303640583)
  ·
    refine ⟨3129738700878733955460875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2086492467252489303640583 3129738700878733955460875)
    ·
      refine ⟨4694608051318100933191313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129738700878733955460875 4694608051318100933191313)
      ·
        refine ⟨3520956038488575699893485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4694608051318100933191313 3520956038488575699893485)
        ·
          refine ⟨1320358514433215887460057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3520956038488575699893485 1320358514433215887460057)
          ·
            refine ⟨990268885824911915595043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320358514433215887460057 990268885824911915595043)
            ·
              refine ⟨1485403328737367873392565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990268885824911915595043 1485403328737367873392565)
              ·
                refine ⟨139256562069128238130553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1485403328737367873392565 139256562069128238130553)
                ·
                  refine ⟨104442421551846178597915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139256562069128238130553 104442421551846178597915)
                  ·
                    rfl

theorem cell20_228826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_228826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228826 prefixEnd_228826 := by exact prefixLift 228826
  have htrace : WordTrace (prefixWord ++ tailWord_228826) baseStart_228826 baseEnd_228826 := by
    simpa [prefixWord, tailWord_228826, baseEnd_228826] using wordTrace_append hprefix tailTrace_228826
  have hstable : (prefixWord ++ tailWord_228826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228826).length < 2 ^ (prefixWord ++ tailWord_228826).sum := by decide
  have hdescent : baseEnd_228826 < baseStart_228826 := by decide
  rcases family_descends (prefixWord ++ tailWord_228826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228871 : List Nat := [1, 1, 4, 3, 2, 1, 4, 4]
def baseStart_228871 : Nat := 118140960795 + 228871 * 2 ^ 59
def prefixEnd_228871 : Nat := 4983230072969 + 3 ^ 40 * 228871 * 2
def baseEnd_228871 : Nat := 34820986926008674032577

theorem tailTrace_228871 : CollatzResearch.WordTrace tailWord_228871 prefixEnd_228871 34820986926008674032577 := by
  unfold tailWord_228871
  simp only [CollatzResearch.WordTrace]
  refine ⟨8347611153846929899950467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5565074102564619933300311 8347611153846929899950467)
  ·
    refine ⟨12521416730770394849925701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8347611153846929899950467 12521416730770394849925701)
    ·
      refine ⟨2347765637019449034361069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12521416730770394849925701 2347765637019449034361069)
      ·
        refine ⟨880412113882293387885401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2347765637019449034361069 880412113882293387885401)
        ·
          refine ⟨660309085411720040914051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880412113882293387885401 660309085411720040914051)
          ·
            refine ⟨990463628117580061371077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660309085411720040914051 990463628117580061371077)
            ·
              refine ⟨185711930272046261507077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 990463628117580061371077 185711930272046261507077)
              ·
                refine ⟨34820986926008674032577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185711930272046261507077 34820986926008674032577)
                ·
                  rfl

theorem cell20_228871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_228871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228871 prefixEnd_228871 := by exact prefixLift 228871
  have htrace : WordTrace (prefixWord ++ tailWord_228871) baseStart_228871 baseEnd_228871 := by
    simpa [prefixWord, tailWord_228871, baseEnd_228871] using wordTrace_append hprefix tailTrace_228871
  have hstable : (prefixWord ++ tailWord_228871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228871).length < 2 ^ (prefixWord ++ tailWord_228871).sum := by decide
  have hdescent : baseEnd_228871 < baseStart_228871 := by decide
  rcases family_descends (prefixWord ++ tailWord_228871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228894 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_228894 : Nat := 118140960795 + 228894 * 2 ^ 59
def prefixEnd_228894 : Nat := 4983230072969 + 3 ^ 40 * 228894 * 2
def baseEnd_228894 : Nat := 104473458604740164330971

theorem tailTrace_228894 : CollatzResearch.WordTrace tailWord_228894 prefixEnd_228894 104473458604740164330971 := by
  unfold tailWord_228894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043556254095450603504717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5565633355175736552025157 1043556254095450603504717)
  ·
    refine ⟨391333595285793976314269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1043556254095450603504717 391333595285793976314269)
    ·
      refine ⟨146750098232172741117851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 391333595285793976314269 146750098232172741117851)
      ·
        refine ⟨220125147348259111676777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146750098232172741117851 220125147348259111676777)
        ·
          refine ⟨165093860511194333757583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220125147348259111676777 165093860511194333757583)
          ·
            refine ⟨247640790766791500636375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165093860511194333757583 247640790766791500636375)
            ·
              refine ⟨371461186150187250954563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247640790766791500636375 371461186150187250954563)
              ·
                refine ⟨557191779225280876431845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371461186150187250954563 557191779225280876431845)
                ·
                  refine ⟨104473458604740164330971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557191779225280876431845 104473458604740164330971)
                  ·
                    rfl

theorem cell20_228894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_228894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228894 prefixEnd_228894 := by exact prefixLift 228894
  have htrace : WordTrace (prefixWord ++ tailWord_228894) baseStart_228894 baseEnd_228894 := by
    simpa [prefixWord, tailWord_228894, baseEnd_228894] using wordTrace_append hprefix tailTrace_228894
  have hstable : (prefixWord ++ tailWord_228894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228894).length < 2 ^ (prefixWord ++ tailWord_228894).sum := by decide
  have hdescent : baseEnd_228894 < baseStart_228894 := by decide
  rcases family_descends (prefixWord ++ tailWord_228894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228951 : List Nat := [1, 1, 3, 2, 2, 11]
def baseStart_228951 : Nat := 118140960795 + 228951 * 2 ^ 59
def prefixEnd_228951 : Nat := 4983230072969 + 3 ^ 40 * 228951 * 2
def baseEnd_228951 : Nat := 3870350924366714793731

theorem tailTrace_228951 : CollatzResearch.WordTrace tailWord_228951 prefixEnd_228951 3870350924366714793731 := by
  unfold tailWord_228951
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350528993557103562862707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5567019329038069041908471 8350528993557103562862707)
  ·
    refine ⟨12525793490335655344294061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8350528993557103562862707 12525793490335655344294061)
    ·
      refine ⟨4697172558875870754110273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12525793490335655344294061 4697172558875870754110273)
      ·
        refine ⟨3522879419156903065582705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4697172558875870754110273 3522879419156903065582705)
        ·
          refine ⟨2642159564367677299187029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522879419156903065582705 2642159564367677299187029)
          ·
            refine ⟨3870350924366714793731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2642159564367677299187029 3870350924366714793731)
            ·
              rfl

theorem cell20_228951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 11].length) (baseStart_228951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_228951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_228951 prefixEnd_228951 := by exact prefixLift 228951
  have htrace : WordTrace (prefixWord ++ tailWord_228951) baseStart_228951 baseEnd_228951 := by
    simpa [prefixWord, tailWord_228951, baseEnd_228951] using wordTrace_append hprefix tailTrace_228951
  have hstable : (prefixWord ++ tailWord_228951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228951).length < 2 ^ (prefixWord ++ tailWord_228951).sum := by decide
  have hdescent : baseEnd_228951 < baseStart_228951 := by decide
  rcases family_descends (prefixWord ++ tailWord_228951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229006 : List Nat := [4, 1, 1, 3, 1, 3, 7]
def baseStart_229006 : Nat := 118140960795 + 229006 * 2 ^ 59
def prefixEnd_229006 : Nat := 4983230072969 + 3 ^ 40 * 229006 * 2
def baseEnd_229006 : Nat := 11613842050729505844131

theorem tailTrace_229006 : CollatzResearch.WordTrace tailWord_229006 prefixEnd_229006 11613842050729505844131 := by
  unfold tailWord_229006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044066876044730994514359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5568356672238565304076581 1044066876044730994514359)
  ·
    refine ⟨1566100314067096491771539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1044066876044730994514359 1566100314067096491771539)
    ·
      refine ⟨2349150471100644737657309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566100314067096491771539 2349150471100644737657309)
      ·
        refine ⟨880931426662741776621491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2349150471100644737657309 880931426662741776621491)
        ·
          refine ⟨1321397139994112664932237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880931426662741776621491 1321397139994112664932237)
          ·
            refine ⟨495523927497792249349589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321397139994112664932237 495523927497792249349589)
            ·
              refine ⟨11613842050729505844131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 495523927497792249349589 11613842050729505844131)
              ·
                rfl

theorem cell20_229006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_229006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229006 prefixEnd_229006 := by exact prefixLift 229006
  have htrace : WordTrace (prefixWord ++ tailWord_229006) baseStart_229006 baseEnd_229006 := by
    simpa [prefixWord, tailWord_229006, baseEnd_229006] using wordTrace_append hprefix tailTrace_229006
  have hstable : (prefixWord ++ tailWord_229006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229006).length < 2 ^ (prefixWord ++ tailWord_229006).sum := by decide
  have hdescent : baseEnd_229006 < baseStart_229006 := by decide
  rcases family_descends (prefixWord ++ tailWord_229006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229016 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 2]
def baseStart_229016 : Nat := 118140960795 + 229016 * 2 ^ 59
def prefixEnd_229016 : Nat := 4983230072969 + 3 ^ 40 * 229016 * 2
def baseEnd_229016 : Nat := 104529142729049962263805

theorem tailTrace_229016 : CollatzResearch.WordTrace tailWord_229016 prefixEnd_229016 104529142729049962263805 := by
  unfold tailWord_229016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176449869160809831989451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5568599825547746442652601 4176449869160809831989451)
  ·
    refine ⟨6264674803741214747984177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4176449869160809831989451 6264674803741214747984177)
    ·
      refine ⟨4698506102805911060988133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6264674803741214747984177 4698506102805911060988133)
      ·
        refine ⟨880969894276108323935275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4698506102805911060988133 880969894276108323935275)
        ·
          refine ⟨1321454841414162485902913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880969894276108323935275 1321454841414162485902913)
          ·
            refine ⟨991091131060621864427185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321454841414162485902913 991091131060621864427185)
            ·
              refine ⟨743318348295466398320389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991091131060621864427185 743318348295466398320389)
              ·
                refine ⟨139372190305399949685073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743318348295466398320389 139372190305399949685073)
                ·
                  refine ⟨104529142729049962263805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139372190305399949685073 104529142729049962263805)
                  ·
                    rfl

theorem cell20_229016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_229016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229016 prefixEnd_229016 := by exact prefixLift 229016
  have htrace : WordTrace (prefixWord ++ tailWord_229016) baseStart_229016 baseEnd_229016 := by
    simpa [prefixWord, tailWord_229016, baseEnd_229016] using wordTrace_append hprefix tailTrace_229016
  have hstable : (prefixWord ++ tailWord_229016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229016).length < 2 ^ (prefixWord ++ tailWord_229016).sum := by decide
  have hdescent : baseEnd_229016 < baseStart_229016 := by decide
  rcases family_descends (prefixWord ++ tailWord_229016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229027 : List Nat := [1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_229027 : Nat := 118140960795 + 229027 * 2 ^ 59
def prefixEnd_229027 : Nat := 4983230072969 + 3 ^ 40 * 229027 * 2
def baseEnd_229027 : Nat := 34844721142927604299031

theorem tailTrace_229027 : CollatzResearch.WordTrace tailWord_229027 prefixEnd_229027 34844721142927604299031 := by
  unfold tailWord_229027
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353300941281768542629335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5568867294187845695086223 8353300941281768542629335)
  ·
    refine ⟨12529951411922652813944003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353300941281768542629335 12529951411922652813944003)
    ·
      refine ⟨18794927117883979220916005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12529951411922652813944003 18794927117883979220916005)
      ·
        refine ⟨3524048834603246103921751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18794927117883979220916005 3524048834603246103921751)
        ·
          refine ⟨5286073251904869155882627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524048834603246103921751 5286073251904869155882627)
          ·
            refine ⟨7929109877857303733823941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286073251904869155882627 7929109877857303733823941)
            ·
              refine ⟨1486708102098244450091989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7929109877857303733823941 1486708102098244450091989)
              ·
                refine ⟨34844721142927604299031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1486708102098244450091989 34844721142927604299031)
                ·
                  rfl

theorem cell20_229027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_229027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229027 prefixEnd_229027 := by exact prefixLift 229027
  have htrace : WordTrace (prefixWord ++ tailWord_229027) baseStart_229027 baseEnd_229027 := by
    simpa [prefixWord, tailWord_229027, baseEnd_229027] using wordTrace_append hprefix tailTrace_229027
  have hstable : (prefixWord ++ tailWord_229027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229027).length < 2 ^ (prefixWord ++ tailWord_229027).sum := by decide
  have hdescent : baseEnd_229027 < baseStart_229027 := by decide
  rcases family_descends (prefixWord ++ tailWord_229027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229037 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_229037 : Nat := 118140960795 + 229037 * 2 ^ 59
def prefixEnd_229037 : Nat := 4983230072969 + 3 ^ 40 * 229037 * 2
def baseEnd_229037 : Nat := 104538727701267222563719

theorem tailTrace_229037 : CollatzResearch.WordTrace tailWord_229037 prefixEnd_229037 104538727701267222563719 := by
  unfold tailWord_229037
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353665671245540250493365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5569110447497026833662243 8353665671245540250493365)
  ·
    refine ⟨783156156679269398483753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8353665671245540250493365 783156156679269398483753)
    ·
      refine ⟨587367117509452048862815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 783156156679269398483753 587367117509452048862815)
      ·
        refine ⟨881050676264178073294223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587367117509452048862815 881050676264178073294223)
        ·
          refine ⟨1321576014396267109941335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881050676264178073294223 1321576014396267109941335)
          ·
            refine ⟨1982364021594400664912003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321576014396267109941335 1982364021594400664912003)
            ·
              refine ⟨2973546032391600997368005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982364021594400664912003 2973546032391600997368005)
              ·
                refine ⟨557539881073425187006501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2973546032391600997368005 557539881073425187006501)
                ·
                  refine ⟨104538727701267222563719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557539881073425187006501 104538727701267222563719)
                  ·
                    rfl

theorem cell20_229037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_229037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229037 prefixEnd_229037 := by exact prefixLift 229037
  have htrace : WordTrace (prefixWord ++ tailWord_229037) baseStart_229037 baseEnd_229037 := by
    simpa [prefixWord, tailWord_229037, baseEnd_229037] using wordTrace_append hprefix tailTrace_229037
  have hstable : (prefixWord ++ tailWord_229037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229037).length < 2 ^ (prefixWord ++ tailWord_229037).sum := by decide
  have hdescent : baseEnd_229037 < baseStart_229037 := by decide
  rcases family_descends (prefixWord ++ tailWord_229037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229082 : List Nat := [3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_229082 : Nat := 118140960795 + 229082 * 2 ^ 59
def prefixEnd_229082 : Nat := 4983230072969 + 3 ^ 40 * 229082 * 2
def baseEnd_229082 : Nat := 34853088975815688687845

theorem tailTrace_229082 : CollatzResearch.WordTrace tailWord_229082 prefixEnd_229082 34853088975815688687845 := by
  unfold tailWord_229082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088826739020628233970375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5570204637388341957254333 2088826739020628233970375)
  ·
    refine ⟨3133240108530942350955563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2088826739020628233970375 3133240108530942350955563)
    ·
      refine ⟨4699860162796413526433345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133240108530942350955563 4699860162796413526433345)
      ·
        refine ⟨3524895122097310144825009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4699860162796413526433345 3524895122097310144825009)
        ·
          refine ⟨2643671341572982608618757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3524895122097310144825009 2643671341572982608618757)
          ·
            refine ⟨495688376544934239116017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2643671341572982608618757 495688376544934239116017)
            ·
              refine ⟨371766282408700679337013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495688376544934239116017 371766282408700679337013)
              ·
                refine ⟨34853088975815688687845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 371766282408700679337013 34853088975815688687845)
                ·
                  rfl

theorem cell20_229082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_229082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229082 prefixEnd_229082 := by exact prefixLift 229082
  have htrace : WordTrace (prefixWord ++ tailWord_229082) baseStart_229082 baseEnd_229082 := by
    simpa [prefixWord, tailWord_229082, baseEnd_229082] using wordTrace_append hprefix tailTrace_229082
  have hstable : (prefixWord ++ tailWord_229082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229082).length < 2 ^ (prefixWord ++ tailWord_229082).sum := by decide
  have hdescent : baseEnd_229082 < baseStart_229082 := by decide
  rcases family_descends (prefixWord ++ tailWord_229082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229103 : List Nat := [1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_229103 : Nat := 118140960795 + 229103 * 2 ^ 59
def prefixEnd_229103 : Nat := 4983230072969 + 3 ^ 40 * 229103 * 2
def baseEnd_229103 : Nat := 34856283966554775454483

theorem tailTrace_229103 : CollatzResearch.WordTrace tailWord_229103 prefixEnd_229103 34856283966554775454483 := by
  unfold tailWord_229103
  simp only [CollatzResearch.WordTrace]
  refine ⟨8356072889006433522395963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5570715259337622348263975 8356072889006433522395963)
  ·
    refine ⟨12534109333509650283593945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8356072889006433522395963 12534109333509650283593945)
    ·
      refine ⟨9400582000132237712695459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12534109333509650283593945 9400582000132237712695459)
      ·
        refine ⟨14100873000198356569043189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9400582000132237712695459 14100873000198356569043189)
        ·
          refine ⟨1321956843768595928347799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14100873000198356569043189 1321956843768595928347799)
          ·
            refine ⟨1982935265652893892521699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321956843768595928347799 1982935265652893892521699)
            ·
              refine ⟨2974402898479340838782549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982935265652893892521699 2974402898479340838782549)
              ·
                refine ⟨34856283966554775454483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2974402898479340838782549 34856283966554775454483)
                ·
                  rfl

theorem cell20_229103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_229103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229103 prefixEnd_229103 := by exact prefixLift 229103
  have htrace : WordTrace (prefixWord ++ tailWord_229103) baseStart_229103 baseEnd_229103 := by
    simpa [prefixWord, tailWord_229103, baseEnd_229103] using wordTrace_append hprefix tailTrace_229103
  have hstable : (prefixWord ++ tailWord_229103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229103).length < 2 ^ (prefixWord ++ tailWord_229103).sum := by decide
  have hdescent : baseEnd_229103 < baseStart_229103 := by decide
  rcases family_descends (prefixWord ++ tailWord_229103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229130 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_229130 : Nat := 118140960795 + 229130 * 2 ^ 59
def prefixEnd_229130 : Nat := 4983230072969 + 3 ^ 40 * 229130 * 2
def baseEnd_229130 : Nat := 104581175435372232463339

theorem tailTrace_229130 : CollatzResearch.WordTrace tailWord_229130 prefixEnd_229130 104581175435372232463339 := by
  unfold tailWord_229130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089264414977154283407211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5571371773272411422419229 2089264414977154283407211)
  ·
    refine ⟨3133896622465731425110817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089264414977154283407211 3133896622465731425110817)
    ·
      refine ⟨2350422466849298568833113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3133896622465731425110817 2350422466849298568833113)
      ·
        refine ⟨1762816850136973926624835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350422466849298568833113 1762816850136973926624835)
        ·
          refine ⟨2644225275205460889937253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762816850136973926624835 2644225275205460889937253)
          ·
            refine ⟨495792239101023916863235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2644225275205460889937253 495792239101023916863235)
            ·
              refine ⟨743688358651535875294853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495792239101023916863235 743688358651535875294853)
              ·
                refine ⟨139441567247162976617785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743688358651535875294853 139441567247162976617785)
                ·
                  refine ⟨104581175435372232463339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139441567247162976617785 104581175435372232463339)
                  ·
                    rfl

theorem cell20_229130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_229130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229130 prefixEnd_229130 := by exact prefixLift 229130
  have htrace : WordTrace (prefixWord ++ tailWord_229130) baseStart_229130 baseEnd_229130 := by
    simpa [prefixWord, tailWord_229130, baseEnd_229130] using wordTrace_append hprefix tailTrace_229130
  have hstable : (prefixWord ++ tailWord_229130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229130).length < 2 ^ (prefixWord ++ tailWord_229130).sum := by decide
  have hdescent : baseEnd_229130 < baseStart_229130 := by decide
  rcases family_descends (prefixWord ++ tailWord_229130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229182 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_229182 : Nat := 118140960795 + 229182 * 2 ^ 59
def prefixEnd_229182 : Nat := 4983230072969 + 3 ^ 40 * 229182 * 2
def baseEnd_229182 : Nat := 104604909652291162729793

theorem tailTrace_229182 : CollatzResearch.WordTrace tailWord_229182 prefixEnd_229182 104604909652291162729793 := by
  unfold tailWord_229182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044869281965028751815225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5572636170480153343014533 1044869281965028751815225)
  ·
    refine ⟨783651961473771563861419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1044869281965028751815225 783651961473771563861419)
    ·
      refine ⟨1175477942210657345792129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783651961473771563861419 1175477942210657345792129)
      ·
        refine ⟨881608456657993009344097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175477942210657345792129 881608456657993009344097)
        ·
          refine ⟨661206342493494757008073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881608456657993009344097 661206342493494757008073)
          ·
            refine ⟨495904756870121067756055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661206342493494757008073 495904756870121067756055)
            ·
              refine ⟨743857135305181601634083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495904756870121067756055 743857135305181601634083)
              ·
                refine ⟨1115785702957772402451125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743857135305181601634083 1115785702957772402451125)
                ·
                  refine ⟨104604909652291162729793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1115785702957772402451125 104604909652291162729793)
                  ·
                    rfl

theorem cell20_229182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_229182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229182 prefixEnd_229182 := by exact prefixLift 229182
  have htrace : WordTrace (prefixWord ++ tailWord_229182) baseStart_229182 baseEnd_229182 := by
    simpa [prefixWord, tailWord_229182, baseEnd_229182] using wordTrace_append hprefix tailTrace_229182
  have hstable : (prefixWord ++ tailWord_229182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229182).length < 2 ^ (prefixWord ++ tailWord_229182).sum := by decide
  have hdescent : baseEnd_229182 < baseStart_229182 := by decide
  rcases family_descends (prefixWord ++ tailWord_229182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229189 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 2]
def baseStart_229189 : Nat := 118140960795 + 229189 * 2 ^ 59
def prefixEnd_229189 : Nat := 4983230072969 + 3 ^ 40 * 229189 * 2
def baseEnd_229189 : Nat := 104608104643030249496431

theorem tailTrace_229189 : CollatzResearch.WordTrace tailWord_229189 prefixEnd_229189 104608104643030249496431 := by
  unfold tailWord_229189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359209566694870210026621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5572806377796580140017747 8359209566694870210026621)
  ·
    refine ⟨3134703587510576328759983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8359209566694870210026621 3134703587510576328759983)
    ·
      refine ⟨4702055381265864493139975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134703587510576328759983 4702055381265864493139975)
      ·
        refine ⟨7053083071898796739709963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702055381265864493139975 7053083071898796739709963)
        ·
          refine ⟨10579624607848195109564945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053083071898796739709963 10579624607848195109564945)
          ·
            refine ⟨7934718455886146332173709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10579624607848195109564945 7934718455886146332173709)
            ·
              refine ⟨2975519420957304874565141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7934718455886146332173709 2975519420957304874565141)
              ·
                refine ⟨139477472857373665995241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2975519420957304874565141 139477472857373665995241)
                ·
                  refine ⟨104608104643030249496431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139477472857373665995241 104608104643030249496431)
                  ·
                    rfl

theorem cell20_229189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_229189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229189 prefixEnd_229189 := by exact prefixLift 229189
  have htrace : WordTrace (prefixWord ++ tailWord_229189) baseStart_229189 baseEnd_229189 := by
    simpa [prefixWord, tailWord_229189, baseEnd_229189] using wordTrace_append hprefix tailTrace_229189
  have hstable : (prefixWord ++ tailWord_229189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229189).length < 2 ^ (prefixWord ++ tailWord_229189).sum := by decide
  have hdescent : baseEnd_229189 < baseStart_229189 := by decide
  rcases family_descends (prefixWord ++ tailWord_229189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229210 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_229210 : Nat := 118140960795 + 229210 * 2 ^ 59
def prefixEnd_229210 : Nat := 4983230072969 + 3 ^ 40 * 229210 * 2
def baseEnd_229210 : Nat := 104617689615247509796345

theorem tailTrace_229210 : CollatzResearch.WordTrace tailWord_229210 prefixEnd_229210 104617689615247509796345 := by
  unfold tailWord_229210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089993874904697699135271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5573316999745860531027389 2089993874904697699135271)
  ·
    refine ⟨3134990812357046548702907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089993874904697699135271 3134990812357046548702907)
    ·
      refine ⟨4702486218535569823054361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134990812357046548702907 4702486218535569823054361)
      ·
        refine ⟨3526864663901677367290771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4702486218535569823054361 3526864663901677367290771)
        ·
          refine ⟨5290296995852516050936157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526864663901677367290771 5290296995852516050936157)
          ·
            refine ⟨1983861373444693519101059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5290296995852516050936157 1983861373444693519101059)
            ·
              refine ⟨2975792060167040278651589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983861373444693519101059 2975792060167040278651589)
              ·
                refine ⟨557961011281320052247173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2975792060167040278651589 557961011281320052247173)
                ·
                  refine ⟨104617689615247509796345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557961011281320052247173 104617689615247509796345)
                  ·
                    rfl

theorem cell20_229210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_229210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229210 prefixEnd_229210 := by exact prefixLift 229210
  have htrace : WordTrace (prefixWord ++ tailWord_229210) baseStart_229210 baseEnd_229210 := by
    simpa [prefixWord, tailWord_229210, baseEnd_229210] using wordTrace_append hprefix tailTrace_229210
  have hstable : (prefixWord ++ tailWord_229210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229210).length < 2 ^ (prefixWord ++ tailWord_229210).sum := by decide
  have hdescent : baseEnd_229210 < baseStart_229210 := by decide
  rcases family_descends (prefixWord ++ tailWord_229210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229217 : List Nat := [1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_229217 : Nat := 118140960795 + 229217 * 2 ^ 59
def prefixEnd_229217 : Nat := 4983230072969 + 3 ^ 40 * 229217 * 2
def baseEnd_229217 : Nat := 34873628201995532187661

theorem tailTrace_229217 : CollatzResearch.WordTrace tailWord_229217 prefixEnd_229217 34873628201995532187661 := by
  unfold tailWord_229217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360230810593430992045905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5573487207062287328030603 8360230810593430992045905)
  ·
    refine ⟨6270173107945073244034429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8360230810593430992045905 6270173107945073244034429)
    ·
      refine ⟨2351314915479402466512911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6270173107945073244034429 2351314915479402466512911)
      ·
        refine ⟨3526972373219103699769367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351314915479402466512911 3526972373219103699769367)
        ·
          refine ⟨5290458559828655549654051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526972373219103699769367 5290458559828655549654051)
          ·
            refine ⟨7935687839742983324481077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290458559828655549654051 7935687839742983324481077)
            ·
              refine ⟨743970734975904686670101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7935687839742983324481077 743970734975904686670101)
              ·
                refine ⟨34873628201995532187661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 743970734975904686670101 34873628201995532187661)
                ·
                  rfl

theorem cell20_229217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_229217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229217 prefixEnd_229217 := by exact prefixLift 229217
  have htrace : WordTrace (prefixWord ++ tailWord_229217) baseStart_229217 baseEnd_229217 := by
    simpa [prefixWord, tailWord_229217, baseEnd_229217] using wordTrace_append hprefix tailTrace_229217
  have hstable : (prefixWord ++ tailWord_229217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229217).length < 2 ^ (prefixWord ++ tailWord_229217).sum := by decide
  have hdescent : baseEnd_229217 < baseStart_229217 := by decide
  rcases family_descends (prefixWord ++ tailWord_229217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229241 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_229241 : Nat := 118140960795 + 229241 * 2 ^ 59
def prefixEnd_229241 : Nat := 4983230072969 + 3 ^ 40 * 229241 * 2
def baseEnd_229241 : Nat := 104631838859949179762885

theorem tailTrace_229241 : CollatzResearch.WordTrace tailWord_229241 prefixEnd_229241 104631838859949179762885 := by
  unfold tailWord_229241
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361106162506483090919577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5574070775004322060613051 8361106162506483090919577)
  ·
    refine ⟨6270829621879862318189683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8361106162506483090919577 6270829621879862318189683)
    ·
      refine ⟨9406244432819793477284525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270829621879862318189683 9406244432819793477284525)
      ·
        refine ⟨3527341662307422553981697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9406244432819793477284525 3527341662307422553981697)
        ·
          refine ⟨2645506246730566915486273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3527341662307422553981697 2645506246730566915486273)
          ·
            refine ⟨1984129685047925186614705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645506246730566915486273 1984129685047925186614705)
            ·
              refine ⟨1488097263785943889961029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984129685047925186614705 1488097263785943889961029)
              ·
                refine ⟨279018236959864479367693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1488097263785943889961029 279018236959864479367693)
                ·
                  refine ⟨104631838859949179762885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279018236959864479367693 104631838859949179762885)
                  ·
                    rfl

theorem cell20_229241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_229241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229241 prefixEnd_229241 := by exact prefixLift 229241
  have htrace : WordTrace (prefixWord ++ tailWord_229241) baseStart_229241 baseEnd_229241 := by
    simpa [prefixWord, tailWord_229241, baseEnd_229241] using wordTrace_append hprefix tailTrace_229241
  have hstable : (prefixWord ++ tailWord_229241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229241).length < 2 ^ (prefixWord ++ tailWord_229241).sum := by decide
  have hdescent : baseEnd_229241 < baseStart_229241 := by decide
  rcases family_descends (prefixWord ++ tailWord_229241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229293 : List Nat := [1, 5, 2, 12]
def baseStart_229293 : Nat := 118140960795 + 229293 * 2 ^ 59
def prefixEnd_229293 : Nat := 4983230072969 + 3 ^ 40 * 229293 * 2
def baseEnd_229293 : Nat := 430681370686700041273

theorem tailTrace_229293 : CollatzResearch.WordTrace tailWord_229293 prefixEnd_229293 430681370686700041273 := by
  unfold tailWord_229293
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363002758318095971812533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5575335172212063981208355 8363002758318095971812533)
  ·
    refine ⟨784031508592321497357425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8363002758318095971812533 784031508592321497357425)
    ·
      refine ⟨588023631444241123018069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784031508592321497357425 588023631444241123018069)
      ·
        refine ⟨430681370686700041273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 588023631444241123018069 430681370686700041273)
        ·
          rfl

theorem cell20_229293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 12].length) (baseStart_229293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229293 prefixEnd_229293 := by exact prefixLift 229293
  have htrace : WordTrace (prefixWord ++ tailWord_229293) baseStart_229293 baseEnd_229293 := by
    simpa [prefixWord, tailWord_229293, baseEnd_229293] using wordTrace_append hprefix tailTrace_229293
  have hstable : (prefixWord ++ tailWord_229293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229293).length < 2 ^ (prefixWord ++ tailWord_229293).sum := by decide
  have hdescent : baseEnd_229293 < baseStart_229293 := by decide
  rcases family_descends (prefixWord ++ tailWord_229293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229310 : List Nat := [4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_229310 : Nat := 118140960795 + 229310 * 2 ^ 59
def prefixEnd_229310 : Nat := 4983230072969 + 3 ^ 40 * 229310 * 2
def baseEnd_229310 : Nat := 34887777446697202154201

theorem tailTrace_229310 : CollatzResearch.WordTrace tailWord_229310 prefixEnd_229310 34887777446697202154201 := by
  unfold tailWord_229310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045452849907063484397673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5575748532837671916787589 1045452849907063484397673)
  ·
    refine ⟨784089637430297613298255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1045452849907063484397673 784089637430297613298255)
    ·
      refine ⟨1176134456145446419947383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784089637430297613298255 1176134456145446419947383)
      ·
        refine ⟨1764201684218169629921075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176134456145446419947383 1764201684218169629921075)
        ·
          refine ⟨2646302526327254444881613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764201684218169629921075 2646302526327254444881613)
          ·
            refine ⟨992363447372720416830605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2646302526327254444881613 992363447372720416830605)
            ·
              refine ⟨372136292764770156311477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992363447372720416830605 372136292764770156311477)
              ·
                refine ⟨34887777446697202154201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 372136292764770156311477 34887777446697202154201)
                ·
                  rfl

theorem cell20_229310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_229310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229310 prefixEnd_229310 := by exact prefixLift 229310
  have htrace : WordTrace (prefixWord ++ tailWord_229310) baseStart_229310 baseEnd_229310 := by
    simpa [prefixWord, tailWord_229310, baseEnd_229310] using wordTrace_append hprefix tailTrace_229310
  have hstable : (prefixWord ++ tailWord_229310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229310).length < 2 ^ (prefixWord ++ tailWord_229310).sum := by decide
  have hdescent : baseEnd_229310 < baseStart_229310 := by decide
  rcases family_descends (prefixWord ++ tailWord_229310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229324 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_229324 : Nat := 118140960795 + 229324 * 2 ^ 59
def prefixEnd_229324 : Nat := 4983230072969 + 3 ^ 40 * 229324 * 2
def baseEnd_229324 : Nat := 104669722321569779995879

theorem tailTrace_229324 : CollatzResearch.WordTrace tailWord_229324 prefixEnd_229324 104669722321569779995879 := by
  unfold tailWord_229324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182066710602894133095513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5576088947470525510794017 4182066710602894133095513)
  ·
    refine ⟨3136550032952170599821635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4182066710602894133095513 3136550032952170599821635)
    ·
      refine ⟨4704825049428255899732453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136550032952170599821635 4704825049428255899732453)
      ·
        refine ⟨882154696767797981199835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4704825049428255899732453 882154696767797981199835)
        ·
          refine ⟨1323232045151696971799753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882154696767797981199835 1323232045151696971799753)
          ·
            refine ⟨992424033863772728849815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323232045151696971799753 992424033863772728849815)
            ·
              refine ⟨1488636050795659093274723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992424033863772728849815 1488636050795659093274723)
              ·
                refine ⟨2232954076193488639912085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488636050795659093274723 2232954076193488639912085)
                ·
                  refine ⟨104669722321569779995879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2232954076193488639912085 104669722321569779995879)
                  ·
                    rfl

theorem cell20_229324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_229324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229324 prefixEnd_229324 := by exact prefixLift 229324
  have htrace : WordTrace (prefixWord ++ tailWord_229324) baseStart_229324 baseEnd_229324 := by
    simpa [prefixWord, tailWord_229324, baseEnd_229324] using wordTrace_append hprefix tailTrace_229324
  have hstable : (prefixWord ++ tailWord_229324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229324).length < 2 ^ (prefixWord ++ tailWord_229324).sum := by decide
  have hdescent : baseEnd_229324 < baseStart_229324 := by decide
  rcases family_descends (prefixWord ++ tailWord_229324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229351 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 3]
def baseStart_229351 : Nat := 118140960795 + 229351 * 2 ^ 59
def prefixEnd_229351 : Nat := 4983230072969 + 3 ^ 40 * 229351 * 2
def baseEnd_229351 : Nat := 104682045857277686095769

theorem tailTrace_229351 : CollatzResearch.WordTrace tailWord_229351 prefixEnd_229351 104682045857277686095769 := by
  unfold tailWord_229351
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365118192107971877423907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5576745461405314584949271 8365118192107971877423907)
  ·
    refine ⟨12547677288161957816135861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8365118192107971877423907 12547677288161957816135861)
    ·
      refine ⟨1176344745765183545262737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12547677288161957816135861 1176344745765183545262737)
      ·
        refine ⟨882258559323887658947053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176344745765183545262737 882258559323887658947053)
        ·
          refine ⟨330846959746457872105145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 882258559323887658947053 330846959746457872105145)
          ·
            refine ⟨248135219809843404078859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330846959746457872105145 248135219809843404078859)
            ·
              refine ⟨372202829714765106118289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248135219809843404078859 372202829714765106118289)
              ·
                refine ⟨279152122286073829588717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372202829714765106118289 279152122286073829588717)
                ·
                  refine ⟨104682045857277686095769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279152122286073829588717 104682045857277686095769)
                  ·
                    rfl

theorem cell20_229351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_229351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229351 prefixEnd_229351 := by exact prefixLift 229351
  have htrace : WordTrace (prefixWord ++ tailWord_229351) baseStart_229351 baseEnd_229351 := by
    simpa [prefixWord, tailWord_229351, baseEnd_229351] using wordTrace_append hprefix tailTrace_229351
  have hstable : (prefixWord ++ tailWord_229351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229351).length < 2 ^ (prefixWord ++ tailWord_229351).sum := by decide
  have hdescent : baseEnd_229351 < baseStart_229351 := by decide
  rcases family_descends (prefixWord ++ tailWord_229351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229358 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_229358 : Nat := 118140960795 + 229358 * 2 ^ 59
def prefixEnd_229358 : Nat := 4983230072969 + 3 ^ 40 * 229358 * 2
def baseEnd_229358 : Nat := 104685240848016772862407

theorem tailTrace_229358 : CollatzResearch.WordTrace tailWord_229358 prefixEnd_229358 104685240848016772862407 := by
  unfold tailWord_229358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045671687885326509116091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5576915668721741381952485 1045671687885326509116091)
  ·
    refine ⟨1568507531827989763674137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1045671687885326509116091 1568507531827989763674137)
    ·
      refine ⟨1176380648870992322755603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568507531827989763674137 1176380648870992322755603)
      ·
        refine ⟨1764570973306488484133405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176380648870992322755603 1764570973306488484133405)
        ·
          refine ⟨661714114989933181550027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1764570973306488484133405 661714114989933181550027)
          ·
            refine ⟨992571172484899772325041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661714114989933181550027 992571172484899772325041)
            ·
              refine ⟨744428379363674829243781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992571172484899772325041 744428379363674829243781)
              ·
                refine ⟨139580321130689030483209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744428379363674829243781 139580321130689030483209)
                ·
                  refine ⟨104685240848016772862407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139580321130689030483209 104685240848016772862407)
                  ·
                    rfl

theorem cell20_229358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_229358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229358 prefixEnd_229358 := by exact prefixLift 229358
  have htrace : WordTrace (prefixWord ++ tailWord_229358) baseStart_229358 baseEnd_229358 := by
    simpa [prefixWord, tailWord_229358, baseEnd_229358] using wordTrace_append hprefix tailTrace_229358
  have hstable : (prefixWord ++ tailWord_229358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229358).length < 2 ^ (prefixWord ++ tailWord_229358).sum := by decide
  have hdescent : baseEnd_229358 < baseStart_229358 := by decide
  rcases family_descends (prefixWord ++ tailWord_229358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229372 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_229372 : Nat := 118140960795 + 229372 * 2 ^ 59
def prefixEnd_229372 : Nat := 4983230072969 + 3 ^ 40 * 229372 * 2
def baseEnd_229372 : Nat := 104691630829494946395683

theorem tailTrace_229372 : CollatzResearch.WordTrace tailWord_229372 prefixEnd_229372 104691630829494946395683 := by
  unfold tailWord_229372
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182942062515946231969185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5577256083354594975958913 4182942062515946231969185)
  ·
    refine ⟨3137206546886959673976889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4182942062515946231969185 3137206546886959673976889)
    ·
      refine ⟨2352904910165219755482667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3137206546886959673976889 2352904910165219755482667)
      ·
        refine ⟨3529357365247829633224001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352904910165219755482667 3529357365247829633224001)
        ·
          refine ⟨2647018023935872224918001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529357365247829633224001 2647018023935872224918001)
          ·
            refine ⟨1985263517951904168688501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647018023935872224918001 1985263517951904168688501)
            ·
              refine ⟨186118454807991015814547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1985263517951904168688501 186118454807991015814547)
              ·
                refine ⟨279177682211986523721821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186118454807991015814547 279177682211986523721821)
                ·
                  refine ⟨104691630829494946395683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279177682211986523721821 104691630829494946395683)
                  ·
                    rfl

theorem cell20_229372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_229372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229372 prefixEnd_229372 := by exact prefixLift 229372
  have htrace : WordTrace (prefixWord ++ tailWord_229372) baseStart_229372 baseEnd_229372 := by
    simpa [prefixWord, tailWord_229372, baseEnd_229372] using wordTrace_append hprefix tailTrace_229372
  have hstable : (prefixWord ++ tailWord_229372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229372).length < 2 ^ (prefixWord ++ tailWord_229372).sum := by decide
  have hdescent : baseEnd_229372 < baseStart_229372 := by decide
  rcases family_descends (prefixWord ++ tailWord_229372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229386 : List Nat := [3, 1, 2, 2, 4, 1, 1, 6]
def baseStart_229386 : Nat := 118140960795 + 229386 * 2 ^ 59
def prefixEnd_229386 : Nat := 4983230072969 + 3 ^ 40 * 229386 * 2
def baseEnd_229386 : Nat := 34899340270324373309653

theorem tailTrace_229386 : CollatzResearch.WordTrace tailWord_229386 prefixEnd_229386 34899340270324373309653 := by
  unfold tailWord_229386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091598686745293213737003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5577596497987448569965341 2091598686745293213737003)
  ·
    refine ⟨3137398030117939820605505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2091598686745293213737003 3137398030117939820605505)
    ·
      refine ⟨2353048522588454865454129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3137398030117939820605505 2353048522588454865454129)
      ·
        refine ⟨1764786391941341149090597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2353048522588454865454129 1764786391941341149090597)
        ·
          refine ⟨330897448489001465454487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1764786391941341149090597 330897448489001465454487)
          ·
            refine ⟨496346172733502198181731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330897448489001465454487 496346172733502198181731)
            ·
              refine ⟨744519259100253297272597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496346172733502198181731 744519259100253297272597)
              ·
                refine ⟨34899340270324373309653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 744519259100253297272597 34899340270324373309653)
                ·
                  rfl

theorem cell20_229386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_229386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229386 prefixEnd_229386 := by exact prefixLift 229386
  have htrace : WordTrace (prefixWord ++ tailWord_229386) baseStart_229386 baseEnd_229386 := by
    simpa [prefixWord, tailWord_229386, baseEnd_229386] using wordTrace_append hprefix tailTrace_229386
  have hstable : (prefixWord ++ tailWord_229386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229386).length < 2 ^ (prefixWord ++ tailWord_229386).sum := by decide
  have hdescent : baseEnd_229386 < baseStart_229386 := by decide
  rcases family_descends (prefixWord ++ tailWord_229386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229452 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_229452 : Nat := 118140960795 + 229452 * 2 ^ 59
def prefixEnd_229452 : Nat := 4983230072969 + 3 ^ 40 * 229452 * 2
def baseEnd_229452 : Nat := 104728145009370223728689

theorem tailTrace_229452 : CollatzResearch.WordTrace tailWord_229452 prefixEnd_229452 104728145009370223728689 := by
  unfold tailWord_229452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184400982371033063425305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5579201309828044084567073 4184400982371033063425305)
  ·
    refine ⟨3138300736778274797568979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4184400982371033063425305 3138300736778274797568979)
    ·
      refine ⟨4707451105167412196353469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138300736778274797568979 4707451105167412196353469)
      ·
        refine ⟨1765294164437779573632551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4707451105167412196353469 1765294164437779573632551)
        ·
          refine ⟨2647941246656669360448827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765294164437779573632551 2647941246656669360448827)
          ·
            refine ⟨3971911869985004040673241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647941246656669360448827 3971911869985004040673241)
            ·
              refine ⟨2978933902488753030504931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971911869985004040673241 2978933902488753030504931)
              ·
                refine ⟨4468400853733129545757397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978933902488753030504931 4468400853733129545757397)
                ·
                  refine ⟨104728145009370223728689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4468400853733129545757397 104728145009370223728689)
                  ·
                    rfl

theorem cell20_229452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_229452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229452 prefixEnd_229452 := by exact prefixLift 229452
  have htrace : WordTrace (prefixWord ++ tailWord_229452) baseStart_229452 baseEnd_229452 := by
    simpa [prefixWord, tailWord_229452, baseEnd_229452] using wordTrace_append hprefix tailTrace_229452
  have hstable : (prefixWord ++ tailWord_229452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229452).length < 2 ^ (prefixWord ++ tailWord_229452).sum := by decide
  have hdescent : baseEnd_229452 < baseStart_229452 := by decide
  rcases family_descends (prefixWord ++ tailWord_229452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229472 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 2]
def baseStart_229472 : Nat := 118140960795 + 229472 * 2 ^ 59
def prefixEnd_229472 : Nat := 4983230072969 + 3 ^ 40 * 229472 * 2
def baseEnd_229472 : Nat := 104737273554339043061941

theorem tailTrace_229472 : CollatzResearch.WordTrace tailWord_229472 prefixEnd_229472 104737273554339043061941 := by
  unfold tailWord_229472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184765712334804771289335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5579687616446406361719113 4184765712334804771289335)
  ·
    refine ⟨6277148568502207156934003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4184765712334804771289335 6277148568502207156934003)
    ·
      refine ⟨9415722852753310735401005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6277148568502207156934003 9415722852753310735401005)
      ·
        refine ⟨3530896069782491525775377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9415722852753310735401005 3530896069782491525775377)
        ·
          refine ⟨2648172052336868644331533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530896069782491525775377 2648172052336868644331533)
          ·
            refine ⟨993064519626325741624325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2648172052336868644331533 993064519626325741624325)
            ·
              refine ⟨186199597429936076554561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 993064519626325741624325 186199597429936076554561)
              ·
                refine ⟨139649698072452057415921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186199597429936076554561 139649698072452057415921)
                ·
                  refine ⟨104737273554339043061941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139649698072452057415921 104737273554339043061941)
                  ·
                    rfl

theorem cell20_229472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_229472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229472 prefixEnd_229472 := by exact prefixLift 229472
  have htrace : WordTrace (prefixWord ++ tailWord_229472) baseStart_229472 baseEnd_229472 := by
    simpa [prefixWord, tailWord_229472, baseEnd_229472] using wordTrace_append hprefix tailTrace_229472
  have hstable : (prefixWord ++ tailWord_229472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229472).length < 2 ^ (prefixWord ++ tailWord_229472).sum := by decide
  have hdescent : baseEnd_229472 < baseStart_229472 := by decide
  rcases family_descends (prefixWord ++ tailWord_229472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229500 : List Nat := [2, 2, 2, 1, 1, 5, 3, 4]
def baseStart_229500 : Nat := 118140960795 + 229500 * 2 ^ 59
def prefixEnd_229500 : Nat := 4983230072969 + 3 ^ 40 * 229500 * 2
def baseEnd_229500 : Nat := 34916684505765130042831

theorem tailTrace_229500 : CollatzResearch.WordTrace tailWord_229500 prefixEnd_229500 34916684505765130042831 := by
  unfold tailWord_229500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185276334284085162298977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5580368445712113549731969 4185276334284085162298977)
  ·
    refine ⟨3138957250713063871724233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4185276334284085162298977 3138957250713063871724233)
    ·
      refine ⟨2354217938034797903793175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3138957250713063871724233 2354217938034797903793175)
      ·
        refine ⟨3531326907052196855689763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354217938034797903793175 3531326907052196855689763)
        ·
          refine ⟨5296990360578295283534645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531326907052196855689763 5296990360578295283534645)
          ·
            refine ⟨496592846304215182831373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5296990360578295283534645 496592846304215182831373)
            ·
              refine ⟨186222317364080693561765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496592846304215182831373 186222317364080693561765)
              ·
                refine ⟨34916684505765130042831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186222317364080693561765 34916684505765130042831)
                ·
                  rfl

theorem cell20_229500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_229500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229500 prefixEnd_229500 := by exact prefixLift 229500
  have htrace : WordTrace (prefixWord ++ tailWord_229500) baseStart_229500 baseEnd_229500 := by
    simpa [prefixWord, tailWord_229500, baseEnd_229500] using wordTrace_append hprefix tailTrace_229500
  have hstable : (prefixWord ++ tailWord_229500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229500).length < 2 ^ (prefixWord ++ tailWord_229500).sum := by decide
  have hdescent : baseEnd_229500 < baseStart_229500 := by decide
  rcases family_descends (prefixWord ++ tailWord_229500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229559 : List Nat := [1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_229559 : Nat := 118140960795 + 229559 * 2 ^ 59
def prefixEnd_229559 : Nat := 4983230072969 + 3 ^ 40 * 229559 * 2
def baseEnd_229559 : Nat := 34925660908317802387195

theorem tailTrace_229559 : CollatzResearch.WordTrace tailWord_229559 prefixEnd_229559 34925660908317802387195 := by
  unfold tailWord_229559
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372704575354423400995731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5581803050236282267330487 8372704575354423400995731)
  ·
    refine ⟨12559056863031635101493597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8372704575354423400995731 12559056863031635101493597)
    ·
      refine ⟨4709646323636863163060099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12559056863031635101493597 4709646323636863163060099)
      ·
        refine ⟨7064469485455294744590149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709646323636863163060099 7064469485455294744590149)
        ·
          refine ⟨1324588028522867764610653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7064469485455294744590149 1324588028522867764610653)
          ·
            refine ⟨496720510696075411728995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1324588028522867764610653 496720510696075411728995)
            ·
              refine ⟨745080766044113117593493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496720510696075411728995 745080766044113117593493)
              ·
                refine ⟨34925660908317802387195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 745080766044113117593493 34925660908317802387195)
                ·
                  rfl

theorem cell20_229559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_229559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229559 prefixEnd_229559 := by exact prefixLift 229559
  have htrace : WordTrace (prefixWord ++ tailWord_229559) baseStart_229559 baseEnd_229559 := by
    simpa [prefixWord, tailWord_229559, baseEnd_229559] using wordTrace_append hprefix tailTrace_229559
  have hstable : (prefixWord ++ tailWord_229559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229559).length < 2 ^ (prefixWord ++ tailWord_229559).sum := by decide
  have hdescent : baseEnd_229559 < baseStart_229559 := by decide
  rcases family_descends (prefixWord ++ tailWord_229559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229573 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_229573 : Nat := 118140960795 + 229573 * 2 ^ 59
def prefixEnd_229573 : Nat := 4983230072969 + 3 ^ 40 * 229573 * 2
def baseEnd_229573 : Nat := 104783372706431580694861

theorem tailTrace_229573 : CollatzResearch.WordTrace tailWord_229573 prefixEnd_229573 104783372706431580694861 := by
  unfold tailWord_229573
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373215197303703792005373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5582143464869135861336915 8373215197303703792005373)
  ·
    refine ⟨3139955698988888922002015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8373215197303703792005373 3139955698988888922002015)
    ·
      refine ⟨4709933548483333383003023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139955698988888922002015 4709933548483333383003023)
      ·
        refine ⟨7064900322725000074504535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709933548483333383003023 7064900322725000074504535)
        ·
          refine ⟨10597350484087500111756803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064900322725000074504535 10597350484087500111756803)
          ·
            refine ⟨15896025726131250167635205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10597350484087500111756803 15896025726131250167635205)
            ·
              refine ⟨2980504823649609406431601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15896025726131250167635205 2980504823649609406431601)
              ·
                refine ⟨2235378617737207054823701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980504823649609406431601 2235378617737207054823701)
                ·
                  refine ⟨104783372706431580694861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2235378617737207054823701 104783372706431580694861)
                  ·
                    rfl

theorem cell20_229573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_229573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229573 prefixEnd_229573 := by exact prefixLift 229573
  have htrace : WordTrace (prefixWord ++ tailWord_229573) baseStart_229573 baseEnd_229573 := by
    simpa [prefixWord, tailWord_229573, baseEnd_229573] using wordTrace_append hprefix tailTrace_229573
  have hstable : (prefixWord ++ tailWord_229573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229573).length < 2 ^ (prefixWord ++ tailWord_229573).sum := by decide
  have hdescent : baseEnd_229573 < baseStart_229573 := by decide
  rcases family_descends (prefixWord ++ tailWord_229573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229611 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_229611 : Nat := 118140960795 + 229611 * 2 ^ 59
def prefixEnd_229611 : Nat := 4983230072969 + 3 ^ 40 * 229611 * 2
def baseEnd_229611 : Nat := 104800716941872337428039

theorem tailTrace_229611 : CollatzResearch.WordTrace tailWord_229611 prefixEnd_229611 104800716941872337428039 := by
  unfold tailWord_229611
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374601171166036281888687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5583067447444024187925791 8374601171166036281888687)
  ·
    refine ⟨12561901756749054422833031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374601171166036281888687 12561901756749054422833031)
    ·
      refine ⟨18842852635123581634249547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12561901756749054422833031 18842852635123581634249547)
      ·
        refine ⟨28264278952685372451374321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18842852635123581634249547 28264278952685372451374321)
        ·
          refine ⟨21198209214514029338530741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28264278952685372451374321 21198209214514029338530741)
          ·
            refine ⟨1987332113860690250487257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21198209214514029338530741 1987332113860690250487257)
            ·
              refine ⟨1490499085395517687865443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987332113860690250487257 1490499085395517687865443)
              ·
                refine ⟨2235748628093276531798165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490499085395517687865443 2235748628093276531798165)
                ·
                  refine ⟨104800716941872337428039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2235748628093276531798165 104800716941872337428039)
                  ·
                    rfl

theorem cell20_229611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_229611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229611 prefixEnd_229611 := by exact prefixLift 229611
  have htrace : WordTrace (prefixWord ++ tailWord_229611) baseStart_229611 baseEnd_229611 := by
    simpa [prefixWord, tailWord_229611, baseEnd_229611] using wordTrace_append hprefix tailTrace_229611
  have hstable : (prefixWord ++ tailWord_229611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229611).length < 2 ^ (prefixWord ++ tailWord_229611).sum := by decide
  have hdescent : baseEnd_229611 < baseStart_229611 := by decide
  rcases family_descends (prefixWord ++ tailWord_229611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229642 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_229642 : Nat := 118140960795 + 229642 * 2 ^ 59
def prefixEnd_229642 : Nat := 4983230072969 + 3 ^ 40 * 229642 * 2
def baseEnd_229642 : Nat := 104814866186574007394579

theorem tailTrace_229642 : CollatzResearch.WordTrace tailWord_229642 prefixEnd_229642 104814866186574007394579 := by
  unfold tailWord_229642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093932958513432144066795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5583821222702485717511453 2093932958513432144066795)
  ·
    refine ⟨3140899437770148216100193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2093932958513432144066795 3140899437770148216100193)
    ·
      refine ⟨2355674578327611162075145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3140899437770148216100193 2355674578327611162075145)
      ·
        refine ⟨1766755933745708371556359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355674578327611162075145 1766755933745708371556359)
        ·
          refine ⟨2650133900618562557334539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766755933745708371556359 2650133900618562557334539)
          ·
            refine ⟨3975200850927843836001809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650133900618562557334539 3975200850927843836001809)
            ·
              refine ⟨2981400638195882877001357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975200850927843836001809 2981400638195882877001357)
              ·
                refine ⟨1118025239323456078875509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2981400638195882877001357 1118025239323456078875509)
                ·
                  refine ⟨104814866186574007394579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1118025239323456078875509 104814866186574007394579)
                  ·
                    rfl

theorem cell20_229642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_229642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229642 prefixEnd_229642 := by exact prefixLift 229642
  have htrace : WordTrace (prefixWord ++ tailWord_229642) baseStart_229642 baseEnd_229642 := by
    simpa [prefixWord, tailWord_229642, baseEnd_229642] using wordTrace_append hprefix tailTrace_229642
  have hstable : (prefixWord ++ tailWord_229642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229642).length < 2 ^ (prefixWord ++ tailWord_229642).sum := by decide
  have hdescent : baseEnd_229642 < baseStart_229642 := by decide
  rcases family_descends (prefixWord ++ tailWord_229642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229662 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_229662 : Nat := 118140960795 + 229662 * 2 ^ 59
def prefixEnd_229662 : Nat := 4983230072969 + 3 ^ 40 * 229662 * 2
def baseEnd_229662 : Nat := 104823994731542826727831

theorem tailTrace_229662 : CollatzResearch.WordTrace tailWord_229662 prefixEnd_229662 104823994731542826727831 := by
  unfold tailWord_229662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047057661747658998999405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5584307529320847994663493 1047057661747658998999405)
  ·
    refine ⟨392646623155372124624777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1047057661747658998999405 392646623155372124624777)
    ·
      refine ⟨294484967366529093468583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392646623155372124624777 294484967366529093468583)
      ·
        refine ⟨441727451049793640202875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294484967366529093468583 441727451049793640202875)
        ·
          refine ⟨662591176574690460304313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441727451049793640202875 662591176574690460304313)
          ·
            refine ⟨496943382431017845228235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662591176574690460304313 496943382431017845228235)
            ·
              refine ⟨745415073646526767842353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496943382431017845228235 745415073646526767842353)
              ·
                refine ⟨559061305234895075881765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745415073646526767842353 559061305234895075881765)
                ·
                  refine ⟨104823994731542826727831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559061305234895075881765 104823994731542826727831)
                  ·
                    rfl

theorem cell20_229662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_229662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229662 prefixEnd_229662 := by exact prefixLift 229662
  have htrace : WordTrace (prefixWord ++ tailWord_229662) baseStart_229662 baseEnd_229662 := by
    simpa [prefixWord, tailWord_229662, baseEnd_229662] using wordTrace_append hprefix tailTrace_229662
  have hstable : (prefixWord ++ tailWord_229662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229662).length < 2 ^ (prefixWord ++ tailWord_229662).sum := by decide
  have hdescent : baseEnd_229662 < baseStart_229662 := by decide
  rcases family_descends (prefixWord ++ tailWord_229662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229666 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_229666 : Nat := 118140960795 + 229666 * 2 ^ 59
def prefixEnd_229666 : Nat := 4983230072969 + 3 ^ 40 * 229666 * 2
def baseEnd_229666 : Nat := 104825820440536590594481

theorem tailTrace_229666 : CollatzResearch.WordTrace tailWord_229666 prefixEnd_229666 104825820440536590594481 := by
  unfold tailWord_229666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094151796491695168785213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5584404790644520450093901 2094151796491695168785213)
  ·
    refine ⟨785306923684385688294455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2094151796491695168785213 785306923684385688294455)
    ·
      refine ⟨1177960385526578532441683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785306923684385688294455 1177960385526578532441683)
      ·
        refine ⟨1766940578289867798662525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177960385526578532441683 1766940578289867798662525)
        ·
          refine ⟨662602716858700424498447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1766940578289867798662525 662602716858700424498447)
          ·
            refine ⟨993904075288050636747671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662602716858700424498447 993904075288050636747671)
            ·
              refine ⟨1490856112932075955121507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993904075288050636747671 1490856112932075955121507)
              ·
                refine ⟨2236284169398113932682261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490856112932075955121507 2236284169398113932682261)
                ·
                  refine ⟨104825820440536590594481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2236284169398113932682261 104825820440536590594481)
                  ·
                    rfl

theorem cell20_229666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_229666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229666 prefixEnd_229666 := by exact prefixLift 229666
  have htrace : WordTrace (prefixWord ++ tailWord_229666) baseStart_229666 baseEnd_229666 := by
    simpa [prefixWord, tailWord_229666, baseEnd_229666] using wordTrace_append hprefix tailTrace_229666
  have hstable : (prefixWord ++ tailWord_229666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229666).length < 2 ^ (prefixWord ++ tailWord_229666).sum := by decide
  have hdescent : baseEnd_229666 < baseStart_229666 := by decide
  rcases family_descends (prefixWord ++ tailWord_229666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229683 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 2]
def baseStart_229683 : Nat := 118140960795 + 229683 * 2 ^ 59
def prefixEnd_229683 : Nat := 4983230072969 + 3 ^ 40 * 229683 * 2
def baseEnd_229683 : Nat := 104833579703760087027745

theorem tailTrace_229683 : CollatzResearch.WordTrace tailWord_229683 prefixEnd_229683 104833579703760087027745 := by
  unfold tailWord_229683
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377227226905192578509703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5584818151270128385673135 8377227226905192578509703)
  ·
    refine ⟨12565840840357788867764555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8377227226905192578509703 12565840840357788867764555)
    ·
      refine ⟨18848761260536683301646833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12565840840357788867764555 18848761260536683301646833)
      ·
        refine ⟨14136570945402512476235125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18848761260536683301646833 14136570945402512476235125)
        ·
          refine ⟨1325303526131485544647043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14136570945402512476235125 1325303526131485544647043)
          ·
            refine ⟨1987955289197228316970565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325303526131485544647043 1987955289197228316970565)
            ·
              refine ⟨372741616724480309431981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1987955289197228316970565 372741616724480309431981)
              ·
                refine ⟨139778106271680116036993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372741616724480309431981 139778106271680116036993)
                ·
                  refine ⟨104833579703760087027745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139778106271680116036993 104833579703760087027745)
                  ·
                    rfl

theorem cell20_229683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 2].length) (baseStart_229683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229683 prefixEnd_229683 := by exact prefixLift 229683
  have htrace : WordTrace (prefixWord ++ tailWord_229683) baseStart_229683 baseEnd_229683 := by
    simpa [prefixWord, tailWord_229683, baseEnd_229683] using wordTrace_append hprefix tailTrace_229683
  have hstable : (prefixWord ++ tailWord_229683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229683).length < 2 ^ (prefixWord ++ tailWord_229683).sum := by decide
  have hdescent : baseEnd_229683 < baseStart_229683 := by decide
  rcases family_descends (prefixWord ++ tailWord_229683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229700 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_229700 : Nat := 118140960795 + 229700 * 2 ^ 59
def prefixEnd_229700 : Nat := 4983230072969 + 3 ^ 40 * 229700 * 2
def baseEnd_229700 : Nat := 104841338966983583461009

theorem tailTrace_229700 : CollatzResearch.WordTrace tailWord_229700 prefixEnd_229700 104841338966983583461009 := by
  unfold tailWord_229700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4188923633921802240939277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5585231511895736321252369 4188923633921802240939277)
  ·
    refine ⟨1570846362720675840352229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4188923633921802240939277 1570846362720675840352229)
    ·
      refine ⟨294533693010126720066043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1570846362720675840352229 294533693010126720066043)
      ·
        refine ⟨441800539515190080099065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294533693010126720066043 441800539515190080099065)
        ·
          refine ⟨331350404636392560074299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441800539515190080099065 331350404636392560074299)
          ·
            refine ⟨497025606954588840111449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331350404636392560074299 497025606954588840111449)
            ·
              refine ⟨372769205215941630083587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497025606954588840111449 372769205215941630083587)
              ·
                refine ⟨559153807823912445125381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372769205215941630083587 559153807823912445125381)
                ·
                  refine ⟨104841338966983583461009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559153807823912445125381 104841338966983583461009)
                  ·
                    rfl

theorem cell20_229700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_229700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229700 prefixEnd_229700 := by exact prefixLift 229700
  have htrace : WordTrace (prefixWord ++ tailWord_229700) baseStart_229700 baseEnd_229700 := by
    simpa [prefixWord, tailWord_229700, baseEnd_229700] using wordTrace_append hprefix tailTrace_229700
  have hstable : (prefixWord ++ tailWord_229700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229700).length < 2 ^ (prefixWord ++ tailWord_229700).sum := by decide
  have hdescent : baseEnd_229700 < baseStart_229700 := by decide
  rcases family_descends (prefixWord ++ tailWord_229700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229724 : List Nat := [2, 2, 4, 3, 1, 2, 2, 4]
def baseStart_229724 : Nat := 118140960795 + 229724 * 2 ^ 59
def prefixEnd_229724 : Nat := 4983230072969 + 3 ^ 40 * 229724 * 2
def baseEnd_229724 : Nat := 34950764406982055553637

theorem tailTrace_229724 : CollatzResearch.WordTrace tailWord_229724 prefixEnd_229724 34950764406982055553637 := by
  unfold tailWord_229724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4189361309878328290376113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5585815079837771053834817 4189361309878328290376113)
  ·
    refine ⟨3142020982408746217782085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4189361309878328290376113 3142020982408746217782085)
    ·
      refine ⟨589128934201639915834141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3142020982408746217782085 589128934201639915834141)
      ·
        refine ⟨220923350325614968437803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589128934201639915834141 220923350325614968437803)
        ·
          refine ⟨331385025488422452656705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220923350325614968437803 331385025488422452656705)
          ·
            refine ⟨248538769116316839492529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331385025488422452656705 248538769116316839492529)
            ·
              refine ⟨186404076837237629619397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248538769116316839492529 186404076837237629619397)
              ·
                refine ⟨34950764406982055553637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186404076837237629619397 34950764406982055553637)
                ·
                  rfl

theorem cell20_229724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_229724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229724 prefixEnd_229724 := by exact prefixLift 229724
  have htrace : WordTrace (prefixWord ++ tailWord_229724) baseStart_229724 baseEnd_229724 := by
    simpa [prefixWord, tailWord_229724, baseEnd_229724] using wordTrace_append hprefix tailTrace_229724
  have hstable : (prefixWord ++ tailWord_229724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229724).length < 2 ^ (prefixWord ++ tailWord_229724).sum := by decide
  have hdescent : baseEnd_229724 < baseStart_229724 := by decide
  rcases family_descends (prefixWord ++ tailWord_229724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229738 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_229738 : Nat := 118140960795 + 229738 * 2 ^ 59
def prefixEnd_229738 : Nat := 4983230072969 + 3 ^ 40 * 229738 * 2
def baseEnd_229738 : Nat := 104858683202424340194187

theorem tailTrace_229738 : CollatzResearch.WordTrace tailWord_229738 prefixEnd_229738 104858683202424340194187 := by
  unfold tailWord_229738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094808310426484242940467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5586155494470624647841245 2094808310426484242940467)
  ·
    refine ⟨3142212465639726364410701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2094808310426484242940467 3142212465639726364410701)
    ·
      refine ⟨1178329674614897386654013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3142212465639726364410701 1178329674614897386654013)
      ·
        refine ⟨441873627980586519995255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1178329674614897386654013 441873627980586519995255)
        ·
          refine ⟨662810441970879779992883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441873627980586519995255 662810441970879779992883)
          ·
            refine ⟨994215662956319669989325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662810441970879779992883 994215662956319669989325)
            ·
              refine ⟨372830873608619876245997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994215662956319669989325 372830873608619876245997)
              ·
                refine ⟨139811577603232453592249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372830873608619876245997 139811577603232453592249)
                ·
                  refine ⟨104858683202424340194187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139811577603232453592249 104858683202424340194187)
                  ·
                    rfl

theorem cell20_229738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_229738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229738 prefixEnd_229738 := by exact prefixLift 229738
  have htrace : WordTrace (prefixWord ++ tailWord_229738) baseStart_229738 baseEnd_229738 := by
    simpa [prefixWord, tailWord_229738, baseEnd_229738] using wordTrace_append hprefix tailTrace_229738
  have hstable : (prefixWord ++ tailWord_229738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229738).length < 2 ^ (prefixWord ++ tailWord_229738).sum := by decide
  have hdescent : baseEnd_229738 < baseStart_229738 := by decide
  rcases family_descends (prefixWord ++ tailWord_229738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229749 : List Nat := [1, 3, 4, 1, 2, 1, 8]
def baseStart_229749 : Nat := 118140960795 + 229749 * 2 ^ 59
def prefixEnd_229749 : Nat := 4983230072969 + 3 ^ 40 * 229749 * 2
def baseEnd_229749 : Nat := 11651522655795243425275

theorem tailTrace_229749 : CollatzResearch.WordTrace tailWord_229749 prefixEnd_229749 11651522655795243425275 := by
  unfold tailWord_229749
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379634444666085850412301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5586422963110723900274867 8379634444666085850412301)
  ·
    refine ⟨3142362916749782193904613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8379634444666085850412301 3142362916749782193904613)
    ·
      refine ⟨589193046890584161357115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3142362916749782193904613 589193046890584161357115)
      ·
        refine ⟨883789570335876242035673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589193046890584161357115 883789570335876242035673)
        ·
          refine ⟨662842177751907181526755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883789570335876242035673 662842177751907181526755)
          ·
            refine ⟨994263266627860772290133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662842177751907181526755 994263266627860772290133)
            ·
              refine ⟨11651522655795243425275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 994263266627860772290133 11651522655795243425275)
              ·
                rfl

theorem cell20_229749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_229749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229749 prefixEnd_229749 := by exact prefixLift 229749
  have htrace : WordTrace (prefixWord ++ tailWord_229749) baseStart_229749 baseEnd_229749 := by
    simpa [prefixWord, tailWord_229749, baseEnd_229749] using wordTrace_append hprefix tailTrace_229749
  have hstable : (prefixWord ++ tailWord_229749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229749).length < 2 ^ (prefixWord ++ tailWord_229749).sum := by decide
  have hdescent : baseEnd_229749 < baseStart_229749 := by decide
  rcases family_descends (prefixWord ++ tailWord_229749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229866 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_229866 : Nat := 118140960795 + 229866 * 2 ^ 59
def prefixEnd_229866 : Nat := 4983230072969 + 3 ^ 40 * 229866 * 2
def baseEnd_229866 : Nat := 104917105890224783926997

theorem tailTrace_229866 : CollatzResearch.WordTrace tailWord_229866 prefixEnd_229866 104917105890224783926997 := by
  unfold tailWord_229866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095975446310553708105363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5589267856828143221614301 2095975446310553708105363)
  ·
    refine ⟨3143963169465830562158045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095975446310553708105363 3143963169465830562158045)
    ·
      refine ⟨1178986188549686460809267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3143963169465830562158045 1178986188549686460809267)
      ·
        refine ⟨1768479282824529691213901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178986188549686460809267 1768479282824529691213901)
        ·
          refine ⟨663179731059198634205213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1768479282824529691213901 663179731059198634205213)
          ·
            refine ⟨248692399147199487826955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663179731059198634205213 248692399147199487826955)
            ·
              refine ⟨373038598720799231740433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248692399147199487826955 373038598720799231740433)
              ·
                refine ⟨279778949040599423805325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373038598720799231740433 279778949040599423805325)
                ·
                  refine ⟨104917105890224783926997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279778949040599423805325 104917105890224783926997)
                  ·
                    rfl

theorem cell20_229866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_229866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229866 prefixEnd_229866 := by exact prefixLift 229866
  have htrace : WordTrace (prefixWord ++ tailWord_229866) baseStart_229866 baseEnd_229866 := by
    simpa [prefixWord, tailWord_229866, baseEnd_229866] using wordTrace_append hprefix tailTrace_229866
  have hstable : (prefixWord ++ tailWord_229866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229866).length < 2 ^ (prefixWord ++ tailWord_229866).sum := by decide
  have hdescent : baseEnd_229866 < baseStart_229866 := by decide
  rcases family_descends (prefixWord ++ tailWord_229866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229884 : List Nat := [2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_229884 : Nat := 118140960795 + 229884 * 2 ^ 59
def prefixEnd_229884 : Nat := 4983230072969 + 3 ^ 40 * 229884 * 2
def baseEnd_229884 : Nat := 34975107193565573775641

theorem tailTrace_229884 : CollatzResearch.WordTrace tailWord_229884 prefixEnd_229884 34975107193565573775641 := by
  unfold tailWord_229884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192279149588501953288353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5589705532784669271051137 4192279149588501953288353)
  ·
    refine ⟨3144209362191376464966265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4192279149588501953288353 3144209362191376464966265)
    ·
      refine ⟨2358157021643532348724699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3144209362191376464966265 2358157021643532348724699)
      ·
        refine ⟨3537235532465298523087049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358157021643532348724699 3537235532465298523087049)
        ·
          refine ⟨2652926649348973892315287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3537235532465298523087049 2652926649348973892315287)
          ·
            refine ⟨3979389974023460838472931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652926649348973892315287 3979389974023460838472931)
            ·
              refine ⟨5969084961035191257709397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979389974023460838472931 5969084961035191257709397)
              ·
                refine ⟨34975107193565573775641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5969084961035191257709397 34975107193565573775641)
                ·
                  rfl

theorem cell20_229884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_229884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229884 prefixEnd_229884 := by exact prefixLift 229884
  have htrace : WordTrace (prefixWord ++ tailWord_229884) baseStart_229884 baseEnd_229884 := by
    simpa [prefixWord, tailWord_229884, baseEnd_229884] using wordTrace_append hprefix tailTrace_229884
  have hstable : (prefixWord ++ tailWord_229884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229884).length < 2 ^ (prefixWord ++ tailWord_229884).sum := by decide
  have hdescent : baseEnd_229884 < baseStart_229884 := by decide
  rcases family_descends (prefixWord ++ tailWord_229884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229887 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 3]
def baseStart_229887 : Nat := 118140960795 + 229887 * 2 ^ 59
def prefixEnd_229887 : Nat := 4983230072969 + 3 ^ 40 * 229887 * 2
def baseEnd_229887 : Nat := 104926690862442044226911

theorem tailTrace_229887 : CollatzResearch.WordTrace tailWord_229887 prefixEnd_229887 104926690862442044226911 := by
  unfold tailWord_229887
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384667718166135418935915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5589778478777423612623943 8384667718166135418935915)
  ·
    refine ⟨12577001577249203128403873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8384667718166135418935915 12577001577249203128403873)
    ·
      refine ⟨9432751182936902346302905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12577001577249203128403873 9432751182936902346302905)
      ·
        refine ⟨7074563387202676759727179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9432751182936902346302905 7074563387202676759727179)
        ·
          refine ⟨10611845080804015139590769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074563387202676759727179 10611845080804015139590769)
          ·
            refine ⟨7958883810603011354693077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10611845080804015139590769 7958883810603011354693077)
            ·
              refine ⟨186536339311008078625619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7958883810603011354693077 186536339311008078625619)
              ·
                refine ⟨279804508966512117938429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186536339311008078625619 279804508966512117938429)
                ·
                  refine ⟨104926690862442044226911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279804508966512117938429 104926690862442044226911)
                  ·
                    rfl

theorem cell20_229887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 3].length) (baseStart_229887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229887 prefixEnd_229887 := by exact prefixLift 229887
  have htrace : WordTrace (prefixWord ++ tailWord_229887) baseStart_229887 baseEnd_229887 := by
    simpa [prefixWord, tailWord_229887, baseEnd_229887] using wordTrace_append hprefix tailTrace_229887
  have hstable : (prefixWord ++ tailWord_229887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229887).length < 2 ^ (prefixWord ++ tailWord_229887).sum := by decide
  have hdescent : baseEnd_229887 < baseStart_229887 := by decide
  rcases family_descends (prefixWord ++ tailWord_229887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229932 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 2]
def baseStart_229932 : Nat := 118140960795 + 229932 * 2 ^ 59
def prefixEnd_229932 : Nat := 4983230072969 + 3 ^ 40 * 229932 * 2
def baseEnd_229932 : Nat := 104947230088621887726727

theorem tailTrace_229932 : CollatzResearch.WordTrace tailWord_229932 prefixEnd_229932 104947230088621887726727 := by
  unfold tailWord_229932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193154501501554052162025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5590872668668738736216033 4193154501501554052162025)
  ·
    refine ⟨3144865876126165539121519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4193154501501554052162025 3144865876126165539121519)
    ·
      refine ⟨4717298814189248308682279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144865876126165539121519 4717298814189248308682279)
      ·
        refine ⟨7075948221283872463023419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717298814189248308682279 7075948221283872463023419)
        ·
          refine ⟨10613922331925808694535129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7075948221283872463023419 10613922331925808694535129)
          ·
            refine ⟨7960441748944356520901347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10613922331925808694535129 7960441748944356520901347)
            ·
              refine ⟨11940662623416534781352021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960441748944356520901347 11940662623416534781352021)
              ·
                refine ⟨139929640118162516968969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11940662623416534781352021 139929640118162516968969)
                ·
                  refine ⟨104947230088621887726727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139929640118162516968969 104947230088621887726727)
                  ·
                    rfl

theorem cell20_229932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_229932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229932 prefixEnd_229932 := by exact prefixLift 229932
  have htrace : WordTrace (prefixWord ++ tailWord_229932) baseStart_229932 baseEnd_229932 := by
    simpa [prefixWord, tailWord_229932, baseEnd_229932] using wordTrace_append hprefix tailTrace_229932
  have hstable : (prefixWord ++ tailWord_229932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229932).length < 2 ^ (prefixWord ++ tailWord_229932).sum := by decide
  have hdescent : baseEnd_229932 < baseStart_229932 := by decide
  rcases family_descends (prefixWord ++ tailWord_229932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229942 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_229942 : Nat := 118140960795 + 229942 * 2 ^ 59
def prefixEnd_229942 : Nat := 4983230072969 + 3 ^ 40 * 229942 * 2
def baseEnd_229942 : Nat := 104951794361106297393353

theorem tailTrace_229942 : CollatzResearch.WordTrace tailWord_229942 prefixEnd_229942 104951794361106297393353 := by
  unfold tailWord_229942
  simp only [CollatzResearch.WordTrace]
  refine ⟨524167108310429988261755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5591115821977919874792053 524167108310429988261755)
  ·
    refine ⟨786250662465644982392633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524167108310429988261755 786250662465644982392633)
    ·
      refine ⟨589687996849233736794475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 786250662465644982392633 589687996849233736794475)
      ·
        refine ⟨884531995273850605191713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589687996849233736794475 884531995273850605191713)
        ·
          refine ⟨663398996455387953893785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884531995273850605191713 663398996455387953893785)
          ·
            refine ⟨497549247341540965420339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663398996455387953893785 497549247341540965420339)
            ·
              refine ⟨746323871012311448130509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497549247341540965420339 746323871012311448130509)
              ·
                refine ⟨279871451629616793048941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746323871012311448130509 279871451629616793048941)
                ·
                  refine ⟨104951794361106297393353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279871451629616793048941 104951794361106297393353)
                  ·
                    rfl

theorem cell20_229942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_229942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229942 prefixEnd_229942 := by exact prefixLift 229942
  have htrace : WordTrace (prefixWord ++ tailWord_229942) baseStart_229942 baseEnd_229942 := by
    simpa [prefixWord, tailWord_229942, baseEnd_229942] using wordTrace_append hprefix tailTrace_229942
  have hstable : (prefixWord ++ tailWord_229942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229942).length < 2 ^ (prefixWord ++ tailWord_229942).sum := by decide
  have hdescent : baseEnd_229942 < baseStart_229942 := by decide
  rcases family_descends (prefixWord ++ tailWord_229942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229967 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_229967 : Nat := 118140960795 + 229967 * 2 ^ 59
def prefixEnd_229967 : Nat := 4983230072969 + 3 ^ 40 * 229967 * 2
def baseEnd_229967 : Nat := 104963205042317321559917

theorem tailTrace_229967 : CollatzResearch.WordTrace tailWord_229967 prefixEnd_229967 104963205042317321559917 := by
  unfold tailWord_229967
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387585557876309081848155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5591723705250872721232103 8387585557876309081848155)
  ·
    refine ⟨12581378336814463622772233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8387585557876309081848155 12581378336814463622772233)
    ·
      refine ⟨9436033752610847717079175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12581378336814463622772233 9436033752610847717079175)
      ·
        refine ⟨14154050628916271575618763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436033752610847717079175 14154050628916271575618763)
        ·
          refine ⟨21231075943374407363428145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14154050628916271575618763 21231075943374407363428145)
          ·
            refine ⟨15923306957530805522571109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21231075943374407363428145 15923306957530805522571109)
            ·
              refine ⟨2985620054537026035482083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15923306957530805522571109 2985620054537026035482083)
              ·
                refine ⟨4478430081805539053223125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985620054537026035482083 4478430081805539053223125)
                ·
                  refine ⟨104963205042317321559917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4478430081805539053223125 104963205042317321559917)
                  ·
                    rfl

theorem cell20_229967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_229967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229967 prefixEnd_229967 := by exact prefixLift 229967
  have htrace : WordTrace (prefixWord ++ tailWord_229967) baseStart_229967 baseEnd_229967 := by
    simpa [prefixWord, tailWord_229967, baseEnd_229967] using wordTrace_append hprefix tailTrace_229967
  have hstable : (prefixWord ++ tailWord_229967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229967).length < 2 ^ (prefixWord ++ tailWord_229967).sum := by decide
  have hdescent : baseEnd_229967 < baseStart_229967 := by decide
  rcases family_descends (prefixWord ++ tailWord_229967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229980 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_229980 : Nat := 118140960795 + 229980 * 2 ^ 59
def prefixEnd_229980 : Nat := 4983230072969 + 3 ^ 40 * 229980 * 2
def baseEnd_229980 : Nat := 104969138596547054126531

theorem tailTrace_229980 : CollatzResearch.WordTrace tailWord_229980 prefixEnd_229980 104969138596547054126531 := by
  unfold tailWord_229980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194029853414606151035697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5592039804552808201380929 4194029853414606151035697)
  ·
    refine ⟨3145522390060954613276773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4194029853414606151035697 3145522390060954613276773)
    ·
      refine ⟨589785448136428989989395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3145522390060954613276773 589785448136428989989395)
      ·
        refine ⟨884678172204643484984093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589785448136428989989395 884678172204643484984093)
        ·
          refine ⟨331754314576741306869035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 884678172204643484984093 331754314576741306869035)
          ·
            refine ⟨497631471865111960303553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331754314576741306869035 497631471865111960303553)
            ·
              refine ⟨373223603898833970227665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497631471865111960303553 373223603898833970227665)
              ·
                refine ⟨279917702924125477670749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373223603898833970227665 279917702924125477670749)
                ·
                  refine ⟨104969138596547054126531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279917702924125477670749 104969138596547054126531)
                  ·
                    rfl

theorem cell20_229980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_229980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229980 prefixEnd_229980 := by exact prefixLift 229980
  have htrace : WordTrace (prefixWord ++ tailWord_229980) baseStart_229980 baseEnd_229980 := by
    simpa [prefixWord, tailWord_229980, baseEnd_229980] using wordTrace_append hprefix tailTrace_229980
  have hstable : (prefixWord ++ tailWord_229980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229980).length < 2 ^ (prefixWord ++ tailWord_229980).sum := by decide
  have hdescent : baseEnd_229980 < baseStart_229980 := by decide
  rcases family_descends (prefixWord ++ tailWord_229980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229984 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_229984 : Nat := 118140960795 + 229984 * 2 ^ 59
def prefixEnd_229984 : Nat := 4983230072969 + 3 ^ 40 * 229984 * 2
def baseEnd_229984 : Nat := 104970964305540817993181

theorem tailTrace_229984 : CollatzResearch.WordTrace tailWord_229984 prefixEnd_229984 104970964305540817993181 := by
  unfold tailWord_229984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194102799407360492608503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5592137065876480656811337 4194102799407360492608503)
  ·
    refine ⟨6291154199111040738912755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4194102799407360492608503 6291154199111040738912755)
    ·
      refine ⟨9436731298666561108369133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291154199111040738912755 9436731298666561108369133)
      ·
        refine ⟨3538774236999960415638425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9436731298666561108369133 3538774236999960415638425)
        ·
          refine ⟨2654080677749970311728819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3538774236999960415638425 2654080677749970311728819)
          ·
            refine ⟨3981121016624955467593229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654080677749970311728819 3981121016624955467593229)
            ·
              refine ⟨1492920381234358300347461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3981121016624955467593229 1492920381234358300347461)
              ·
                refine ⟨279922571481442181315149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1492920381234358300347461 279922571481442181315149)
                ·
                  refine ⟨104970964305540817993181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279922571481442181315149 104970964305540817993181)
                  ·
                    rfl

theorem cell20_229984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_229984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229984 prefixEnd_229984 := by exact prefixLift 229984
  have htrace : WordTrace (prefixWord ++ tailWord_229984) baseStart_229984 baseEnd_229984 := by
    simpa [prefixWord, tailWord_229984, baseEnd_229984] using wordTrace_append hprefix tailTrace_229984
  have hstable : (prefixWord ++ tailWord_229984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229984).length < 2 ^ (prefixWord ++ tailWord_229984).sum := by decide
  have hdescent : baseEnd_229984 < baseStart_229984 := by decide
  rcases family_descends (prefixWord ++ tailWord_229984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229991 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_229991 : Nat := 118140960795 + 229991 * 2 ^ 59
def prefixEnd_229991 : Nat := 4983230072969 + 3 ^ 40 * 229991 * 2
def baseEnd_229991 : Nat := 104974159296279904759819

theorem tailTrace_229991 : CollatzResearch.WordTrace tailWord_229991 prefixEnd_229991 104974159296279904759819 := by
  unfold tailWord_229991
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388460909789361180721827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5592307273192907453814551 8388460909789361180721827)
  ·
    refine ⟨12582691364684041771082741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8388460909789361180721827 12582691364684041771082741)
    ·
      refine ⟨1179627315439128916039007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12582691364684041771082741 1179627315439128916039007)
      ·
        refine ⟨1769440973158693374058511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179627315439128916039007 1769440973158693374058511)
        ·
          refine ⟨2654161459738040061087767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769440973158693374058511 2654161459738040061087767)
          ·
            refine ⟨3981242189607060091631651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654161459738040061087767 3981242189607060091631651)
            ·
              refine ⟨5971863284410590137447477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981242189607060091631651 5971863284410590137447477)
              ·
                refine ⟨559862182913492825385701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5971863284410590137447477 559862182913492825385701)
                ·
                  refine ⟨104974159296279904759819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559862182913492825385701 104974159296279904759819)
                  ·
                    rfl

theorem cell20_229991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_229991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_229991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_229991 prefixEnd_229991 := by exact prefixLift 229991
  have htrace : WordTrace (prefixWord ++ tailWord_229991) baseStart_229991 baseEnd_229991 := by
    simpa [prefixWord, tailWord_229991, baseEnd_229991] using wordTrace_append hprefix tailTrace_229991
  have hstable : (prefixWord ++ tailWord_229991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229991).length < 2 ^ (prefixWord ++ tailWord_229991).sum := by decide
  have hdescent : baseEnd_229991 < baseStart_229991 := by decide
  rcases family_descends (prefixWord ++ tailWord_229991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230067 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_230067 : Nat := 118140960795 + 230067 * 2 ^ 59
def prefixEnd_230067 : Nat := 4983230072969 + 3 ^ 40 * 230067 * 2
def baseEnd_230067 : Nat := 105008847767161418226175

theorem tailTrace_230067 : CollatzResearch.WordTrace tailWord_230067 prefixEnd_230067 105008847767161418226175 := by
  unfold tailWord_230067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391232857514026160488455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5594155238342684106992303 8391232857514026160488455)
  ·
    refine ⟨12586849286271039240732683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8391232857514026160488455 12586849286271039240732683)
    ·
      refine ⟨18880273929406558861099025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12586849286271039240732683 18880273929406558861099025)
      ·
        refine ⟨14160205447054919145824269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18880273929406558861099025 14160205447054919145824269)
        ·
          refine ⟨5310077042645594679684101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14160205447054919145824269 5310077042645594679684101)
          ·
            refine ⟨995639445496049002440769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5310077042645594679684101 995639445496049002440769)
            ·
              refine ⟨746729584122036751830577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995639445496049002440769 746729584122036751830577)
              ·
                refine ⟨560047188091527563872933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746729584122036751830577 560047188091527563872933)
                ·
                  refine ⟨105008847767161418226175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560047188091527563872933 105008847767161418226175)
                  ·
                    rfl

theorem cell20_230067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_230067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230067 prefixEnd_230067 := by exact prefixLift 230067
  have htrace : WordTrace (prefixWord ++ tailWord_230067) baseStart_230067 baseEnd_230067 := by
    simpa [prefixWord, tailWord_230067, baseEnd_230067] using wordTrace_append hprefix tailTrace_230067
  have hstable : (prefixWord ++ tailWord_230067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230067).length < 2 ^ (prefixWord ++ tailWord_230067).sum := by decide
  have hdescent : baseEnd_230067 < baseStart_230067 := by decide
  rcases family_descends (prefixWord ++ tailWord_230067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230074 : List Nat := [3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_230074 : Nat := 118140960795 + 230074 * 2 ^ 59
def prefixEnd_230074 : Nat := 4983230072969 + 3 ^ 40 * 230074 * 2
def baseEnd_230074 : Nat := 35004014252633501664271

theorem tailTrace_230074 : CollatzResearch.WordTrace tailWord_230074 prefixEnd_230074 35004014252633501664271 := by
  unfold tailWord_230074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097872042122166588998319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5594325445659110903995517 2097872042122166588998319)
  ·
    refine ⟨3146808063183249883497479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2097872042122166588998319 3146808063183249883497479)
    ·
      refine ⟨4720212094774874825246219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3146808063183249883497479 4720212094774874825246219)
      ·
        refine ⟨7080318142162312237869329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720212094774874825246219 7080318142162312237869329)
        ·
          refine ⟨5310238606621734178401997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7080318142162312237869329 5310238606621734178401997)
          ·
            refine ⟨1991339477483150316900749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5310238606621734178401997 1991339477483150316900749)
            ·
              refine ⟨746752304056181368837781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991339477483150316900749 746752304056181368837781)
              ·
                refine ⟨35004014252633501664271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 746752304056181368837781 35004014252633501664271)
                ·
                  rfl

theorem cell20_230074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_230074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230074 prefixEnd_230074 := by exact prefixLift 230074
  have htrace : WordTrace (prefixWord ++ tailWord_230074) baseStart_230074 baseEnd_230074 := by
    simpa [prefixWord, tailWord_230074, baseEnd_230074] using wordTrace_append hprefix tailTrace_230074
  have hstable : (prefixWord ++ tailWord_230074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230074).length < 2 ^ (prefixWord ++ tailWord_230074).sum := by decide
  have hdescent : baseEnd_230074 < baseStart_230074 := by decide
  rcases family_descends (prefixWord ++ tailWord_230074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230108 : List Nat := [2, 2, 5, 1, 1, 2, 2, 5]
def baseStart_230108 : Nat := 118140960795 + 230108 * 2 ^ 59
def prefixEnd_230108 : Nat := 4983230072969 + 3 ^ 40 * 230108 * 2
def baseEnd_230108 : Nat := 35009187094782499286447

theorem tailTrace_230108 : CollatzResearch.WordTrace tailWord_230108 prefixEnd_230108 35009187094782499286447 := by
  unfold tailWord_230108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196364125182745081365489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5595152166910326775153985 4196364125182745081365489)
  ·
    refine ⟨3147273093887058811024117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4196364125182745081365489 3147273093887058811024117)
    ·
      refine ⟨295056852551911763533511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3147273093887058811024117 295056852551911763533511)
      ·
        refine ⟨442585278827867645300267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295056852551911763533511 442585278827867645300267)
        ·
          refine ⟨663877918241801467950401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442585278827867645300267 663877918241801467950401)
          ·
            refine ⟨497908438681351100962801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663877918241801467950401 497908438681351100962801)
            ·
              refine ⟨373431329011013325722101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497908438681351100962801 373431329011013325722101)
              ·
                refine ⟨35009187094782499286447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 373431329011013325722101 35009187094782499286447)
                ·
                  rfl

theorem cell20_230108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_230108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230108 prefixEnd_230108 := by exact prefixLift 230108
  have htrace : WordTrace (prefixWord ++ tailWord_230108) baseStart_230108 baseEnd_230108 := by
    simpa [prefixWord, tailWord_230108, baseEnd_230108] using wordTrace_append hprefix tailTrace_230108
  have hstable : (prefixWord ++ tailWord_230108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230108).length < 2 ^ (prefixWord ++ tailWord_230108).sum := by decide
  have hdescent : baseEnd_230108 < baseStart_230108 := by decide
  rcases family_descends (prefixWord ++ tailWord_230108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230115 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_230115 : Nat := 118140960795 + 230115 * 2 ^ 59
def prefixEnd_230115 : Nat := 4983230072969 + 3 ^ 40 * 230115 * 2
def baseEnd_230115 : Nat := 105030756275086584625979

theorem tailTrace_230115 : CollatzResearch.WordTrace tailWord_230115 prefixEnd_230115 105030756275086584625979 := by
  unfold tailWord_230115
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392983561340130358235799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5595322374226753572157199 8392983561340130358235799)
  ·
    refine ⟨12589475342010195537353699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392983561340130358235799 12589475342010195537353699)
    ·
      refine ⟨18884213013015293306030549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12589475342010195537353699 18884213013015293306030549)
      ·
        refine ⟨442598742492545936860091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18884213013015293306030549 442598742492545936860091)
        ·
          refine ⟨663898113738818905290137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442598742492545936860091 663898113738818905290137)
          ·
            refine ⟨497923585304114178967603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663898113738818905290137 497923585304114178967603)
            ·
              refine ⟨746885377956171268451405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497923585304114178967603 746885377956171268451405)
              ·
                refine ⟨280082016733564225669277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 746885377956171268451405 280082016733564225669277)
                ·
                  refine ⟨105030756275086584625979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280082016733564225669277 105030756275086584625979)
                  ·
                    rfl

theorem cell20_230115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_230115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230115 prefixEnd_230115 := by exact prefixLift 230115
  have htrace : WordTrace (prefixWord ++ tailWord_230115) baseStart_230115 baseEnd_230115 := by
    simpa [prefixWord, tailWord_230115, baseEnd_230115] using wordTrace_append hprefix tailTrace_230115
  have hstable : (prefixWord ++ tailWord_230115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230115).length < 2 ^ (prefixWord ++ tailWord_230115).sum := by decide
  have hdescent : baseEnd_230115 < baseStart_230115 := by decide
  rcases family_descends (prefixWord ++ tailWord_230115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230181 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_230181 : Nat := 118140960795 + 230181 * 2 ^ 59
def prefixEnd_230181 : Nat := 4983230072969 + 3 ^ 40 * 230181 * 2
def baseEnd_230181 : Nat := 105060880473483688425709

theorem tailTrace_230181 : CollatzResearch.WordTrace tailWord_230181 prefixEnd_230181 105060880473483688425709 := by
  unfold tailWord_230181
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395390779101023630138397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5596927186067349086758931 8395390779101023630138397)
  ·
    refine ⟨3148271542162883861301899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8395390779101023630138397 3148271542162883861301899)
    ·
      refine ⟨4722407313244325791952849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148271542162883861301899 4722407313244325791952849)
      ·
        refine ⟨3541805484933244343964637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4722407313244325791952849 3541805484933244343964637)
        ·
          refine ⟨1328177056849966628986739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3541805484933244343964637 1328177056849966628986739)
          ·
            refine ⟨1992265585274949943480109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328177056849966628986739 1992265585274949943480109)
            ·
              refine ⟨747099594478106228805041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1992265585274949943480109 747099594478106228805041)
              ·
                refine ⟨560324695858579671603781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747099594478106228805041 560324695858579671603781)
                ·
                  refine ⟨105060880473483688425709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560324695858579671603781 105060880473483688425709)
                  ·
                    rfl

theorem cell20_230181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_230181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230181 prefixEnd_230181 := by exact prefixLift 230181
  have htrace : WordTrace (prefixWord ++ tailWord_230181) baseStart_230181 baseEnd_230181 := by
    simpa [prefixWord, tailWord_230181, baseEnd_230181] using wordTrace_append hprefix tailTrace_230181
  have hstable : (prefixWord ++ tailWord_230181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230181).length < 2 ^ (prefixWord ++ tailWord_230181).sum := by decide
  have hdescent : baseEnd_230181 < baseStart_230181 := by decide
  rcases family_descends (prefixWord ++ tailWord_230181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230205 : List Nat := [1, 4, 1, 4, 2, 1, 7]
def baseStart_230205 : Nat := 118140960795 + 230205 * 2 ^ 59
def prefixEnd_230205 : Nat := 4983230072969 + 3 ^ 40 * 230205 * 2
def baseEnd_230205 : Nat := 11674648303049585736179

theorem tailTrace_230205 : CollatzResearch.WordTrace tailWord_230205 prefixEnd_230205 11674648303049585736179 := by
  unfold tailWord_230205
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396266131014075729012069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5597510754009383819341379 8396266131014075729012069)
  ·
    refine ⟨1574299899565139199189763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8396266131014075729012069 1574299899565139199189763)
    ·
      refine ⟨2361449849347708798784645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574299899565139199189763 2361449849347708798784645)
      ·
        refine ⟨442771846752695399772121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2361449849347708798784645 442771846752695399772121)
        ·
          refine ⟨332078885064521549829091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442771846752695399772121 332078885064521549829091)
          ·
            refine ⟨498118327596782324743637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332078885064521549829091 498118327596782324743637)
            ·
              refine ⟨11674648303049585736179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498118327596782324743637 11674648303049585736179)
              ·
                rfl

theorem cell20_230205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_230205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230205 prefixEnd_230205 := by exact prefixLift 230205
  have htrace : WordTrace (prefixWord ++ tailWord_230205) baseStart_230205 baseEnd_230205 := by
    simpa [prefixWord, tailWord_230205, baseEnd_230205] using wordTrace_append hprefix tailTrace_230205
  have hstable : (prefixWord ++ tailWord_230205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230205).length < 2 ^ (prefixWord ++ tailWord_230205).sum := by decide
  have hdescent : baseEnd_230205 < baseStart_230205 := by decide
  rcases family_descends (prefixWord ++ tailWord_230205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230226 : List Nat := [3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_230226 : Nat := 118140960795 + 230226 * 2 ^ 59
def prefixEnd_230226 : Nat := 4983230072969 + 3 ^ 40 * 230226 * 2
def baseEnd_230226 : Nat := 35027139899887843975175

theorem tailTrace_230226 : CollatzResearch.WordTrace tailWord_230226 prefixEnd_230226 35027139899887843975175 := by
  unfold tailWord_230226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099258015984499078881633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5598021375958664210351021 2099258015984499078881633)
  ·
    refine ⟨1574443511988374309161225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2099258015984499078881633 1574443511988374309161225)
    ·
      refine ⟨1180832633991280731870919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1574443511988374309161225 1180832633991280731870919)
      ·
        refine ⟨1771248950986921097806379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180832633991280731870919 1771248950986921097806379)
        ·
          refine ⟨2656873426480381646709569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771248950986921097806379 2656873426480381646709569)
          ·
            refine ⟨1992655069860286235032177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656873426480381646709569 1992655069860286235032177)
            ·
              refine ⟨1494491302395214676274133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992655069860286235032177 1494491302395214676274133)
              ·
                refine ⟨35027139899887843975175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1494491302395214676274133 35027139899887843975175)
                ·
                  rfl

theorem cell20_230226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_230226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230226 prefixEnd_230226 := by exact prefixLift 230226
  have htrace : WordTrace (prefixWord ++ tailWord_230226) baseStart_230226 baseEnd_230226 := by
    simpa [prefixWord, tailWord_230226, baseEnd_230226] using wordTrace_append hprefix tailTrace_230226
  have hstable : (prefixWord ++ tailWord_230226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230226).length < 2 ^ (prefixWord ++ tailWord_230226).sum := by decide
  have hdescent : baseEnd_230226 < baseStart_230226 := by decide
  rcases family_descends (prefixWord ++ tailWord_230226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230229 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 3]
def baseStart_230229 : Nat := 118140960795 + 230229 * 2 ^ 59
def prefixEnd_230229 : Nat := 4983230072969 + 3 ^ 40 * 230229 * 2
def baseEnd_230229 : Nat := 105082788981408854825513

theorem tailTrace_230229 : CollatzResearch.WordTrace tailWord_230229 prefixEnd_230229 105082788981408854825513 := by
  unfold tailWord_230229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397141482927127827885741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5598094321951418551923827 8397141482927127827885741)
  ·
    refine ⟨3148928056097672935457153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8397141482927127827885741 3148928056097672935457153)
    ·
      refine ⟨2361696042073254701592865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3148928056097672935457153 2361696042073254701592865)
      ·
        refine ⟨1771272031554941026194649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2361696042073254701592865 1771272031554941026194649)
        ·
          refine ⟨1328454023666205769645987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771272031554941026194649 1328454023666205769645987)
          ·
            refine ⟨1992681035499308654468981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328454023666205769645987 1992681035499308654468981)
            ·
              refine ⟨186813847078060186356467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1992681035499308654468981 186813847078060186356467)
              ·
                refine ⟨280220770617090279534701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186813847078060186356467 280220770617090279534701)
                ·
                  refine ⟨105082788981408854825513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280220770617090279534701 105082788981408854825513)
                  ·
                    rfl

theorem cell20_230229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_230229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230229 prefixEnd_230229 := by exact prefixLift 230229
  have htrace : WordTrace (prefixWord ++ tailWord_230229) baseStart_230229 baseEnd_230229 := by
    simpa [prefixWord, tailWord_230229, baseEnd_230229] using wordTrace_append hprefix tailTrace_230229
  have hstable : (prefixWord ++ tailWord_230229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230229).length < 2 ^ (prefixWord ++ tailWord_230229).sum := by decide
  have hdescent : baseEnd_230229 < baseStart_230229 := by decide
  rcases family_descends (prefixWord ++ tailWord_230229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230236 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_230236 : Nat := 118140960795 + 230236 * 2 ^ 59
def prefixEnd_230236 : Nat := 4983230072969 + 3 ^ 40 * 230236 * 2
def baseEnd_230236 : Nat := 105085983972147941592151

theorem tailTrace_230236 : CollatzResearch.WordTrace tailWord_230236 prefixEnd_230236 105085983972147941592151 := by
  unfold tailWord_230236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198698396950884011695281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5598264529267845348927041 4198698396950884011695281)
  ·
    refine ⟨3149023797713163008771461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4198698396950884011695281 3149023797713163008771461)
    ·
      refine ⟨590441962071218064144649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3149023797713163008771461 590441962071218064144649)
      ·
        refine ⟨442831471553413548108487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590441962071218064144649 442831471553413548108487)
        ·
          refine ⟨664247207330120322162731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442831471553413548108487 664247207330120322162731)
          ·
            refine ⟨996370810995180483244097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664247207330120322162731 996370810995180483244097)
            ·
              refine ⟨747278108246385362433073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996370810995180483244097 747278108246385362433073)
              ·
                refine ⟨560458581184789021824805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747278108246385362433073 560458581184789021824805)
                ·
                  refine ⟨105085983972147941592151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560458581184789021824805 105085983972147941592151)
                  ·
                    rfl

theorem cell20_230236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_230236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230236 prefixEnd_230236 := by exact prefixLift 230236
  have htrace : WordTrace (prefixWord ++ tailWord_230236) baseStart_230236 baseEnd_230236 := by
    simpa [prefixWord, tailWord_230236, baseEnd_230236] using wordTrace_append hprefix tailTrace_230236
  have hstable : (prefixWord ++ tailWord_230236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230236).length < 2 ^ (prefixWord ++ tailWord_230236).sum := by decide
  have hdescent : baseEnd_230236 < baseStart_230236 := by decide
  rcases family_descends (prefixWord ++ tailWord_230236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230243 : List Nat := [1, 1, 1, 5, 3, 1, 4, 4]
def baseStart_230243 : Nat := 118140960795 + 230243 * 2 ^ 59
def prefixEnd_230243 : Nat := 4983230072969 + 3 ^ 40 * 230243 * 2
def baseEnd_230243 : Nat := 35029726320962342786263

theorem tailTrace_230243 : CollatzResearch.WordTrace tailWord_230243 prefixEnd_230243 35029726320962342786263 := by
  unfold tailWord_230243
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397652104876408218895383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5598434736584272145930255 8397652104876408218895383)
  ·
    refine ⟨12596478157314612328343075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8397652104876408218895383 12596478157314612328343075)
    ·
      refine ⟨18894717235971918492514613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12596478157314612328343075 18894717235971918492514613)
      ·
        refine ⟨1771379740872367358673245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18894717235971918492514613 1771379740872367358673245)
        ·
          refine ⟨664267402827137759502467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1771379740872367358673245 664267402827137759502467)
          ·
            refine ⟨996401104240706639253701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664267402827137759502467 996401104240706639253701)
            ·
              refine ⟨186825207045132494860069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 996401104240706639253701 186825207045132494860069)
              ·
                refine ⟨35029726320962342786263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186825207045132494860069 35029726320962342786263)
                ·
                  rfl

theorem cell20_230243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_230243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230243 prefixEnd_230243 := by exact prefixLift 230243
  have htrace : WordTrace (prefixWord ++ tailWord_230243) baseStart_230243 baseEnd_230243 := by
    simpa [prefixWord, tailWord_230243, baseEnd_230243] using wordTrace_append hprefix tailTrace_230243
  have hstable : (prefixWord ++ tailWord_230243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230243).length < 2 ^ (prefixWord ++ tailWord_230243).sum := by decide
  have hdescent : baseEnd_230243 < baseStart_230243 := by decide
  rcases family_descends (prefixWord ++ tailWord_230243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230270 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_230270 : Nat := 118140960795 + 230270 * 2 ^ 59
def prefixEnd_230270 : Nat := 4983230072969 + 3 ^ 40 * 230270 * 2
def baseEnd_230270 : Nat := 105101502498594934458679

theorem tailTrace_230270 : CollatzResearch.WordTrace tailWord_230270 prefixEnd_230270 105101502498594934458679 := by
  unfold tailWord_230270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049829609472323978766033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5599091250519061220085509 1049829609472323978766033)
  ·
    refine ⟨787372207104242984074525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1049829609472323978766033 787372207104242984074525)
    ·
      refine ⟨295264577664091119027947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 787372207104242984074525 295264577664091119027947)
      ·
        refine ⟨442896866496136678541921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295264577664091119027947 442896866496136678541921)
        ·
          refine ⟨332172649872102508906441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442896866496136678541921 332172649872102508906441)
          ·
            refine ⟨249129487404076881679831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332172649872102508906441 249129487404076881679831)
            ·
              refine ⟨373694231106115322519747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249129487404076881679831 373694231106115322519747)
              ·
                refine ⟨560541346659172983779621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373694231106115322519747 560541346659172983779621)
                ·
                  refine ⟨105101502498594934458679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560541346659172983779621 105101502498594934458679)
                  ·
                    rfl

theorem cell20_230270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_230270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230270 prefixEnd_230270 := by exact prefixLift 230270
  have htrace : WordTrace (prefixWord ++ tailWord_230270) baseStart_230270 baseEnd_230270 := by
    simpa [prefixWord, tailWord_230270, baseEnd_230270] using wordTrace_append hprefix tailTrace_230270
  have hstable : (prefixWord ++ tailWord_230270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230270).length < 2 ^ (prefixWord ++ tailWord_230270).sum := by decide
  have hdescent : baseEnd_230270 < baseStart_230270 := by decide
  rcases family_descends (prefixWord ++ tailWord_230270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230271 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_230271 : Nat := 118140960795 + 230271 * 2 ^ 59
def prefixEnd_230271 : Nat := 4983230072969 + 3 ^ 40 * 230271 * 2
def baseEnd_230271 : Nat := 105101958925843375425341

theorem tailTrace_230271 : CollatzResearch.WordTrace tailWord_230271 prefixEnd_230271 105101958925843375425341 := by
  unfold tailWord_230271
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398673348774969000914667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5599115565849979333943111 8398673348774969000914667)
  ·
    refine ⟨12598010023162453501372001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8398673348774969000914667 12598010023162453501372001)
    ·
      refine ⟨9448507517371840126029001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12598010023162453501372001 9448507517371840126029001)
      ·
        refine ⟨7086380638028880094521751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448507517371840126029001 7086380638028880094521751)
        ·
          refine ⟨10629570957043320141782627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7086380638028880094521751 10629570957043320141782627)
          ·
            refine ⟨15944356435564980212673941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629570957043320141782627 15944356435564980212673941)
            ·
              refine ⟨747391707917108447469091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15944356435564980212673941 747391707917108447469091)
              ·
                refine ⟨1121087561875662671203637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747391707917108447469091 1121087561875662671203637)
                ·
                  refine ⟨105101958925843375425341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1121087561875662671203637 105101958925843375425341)
                  ·
                    rfl

theorem cell20_230271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_230271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230271 prefixEnd_230271 := by exact prefixLift 230271
  have htrace : WordTrace (prefixWord ++ tailWord_230271) baseStart_230271 baseEnd_230271 := by
    simpa [prefixWord, tailWord_230271, baseEnd_230271] using wordTrace_append hprefix tailTrace_230271
  have hstable : (prefixWord ++ tailWord_230271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230271).length < 2 ^ (prefixWord ++ tailWord_230271).sum := by decide
  have hdescent : baseEnd_230271 < baseStart_230271 := by decide
  rcases family_descends (prefixWord ++ tailWord_230271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230316 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_230316 : Nat := 118140960795 + 230316 * 2 ^ 59
def prefixEnd_230316 : Nat := 4983230072969 + 3 ^ 40 * 230316 * 2
def baseEnd_230316 : Nat := 105122498152023218925157

theorem tailTrace_230316 : CollatzResearch.WordTrace tailWord_230316 prefixEnd_230316 105122498152023218925157 := by
  unfold tailWord_230316
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200157316805970843151401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5600209755741294457535201 4200157316805970843151401)
  ·
    refine ⟨3150117987604478132363551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4200157316805970843151401 3150117987604478132363551)
    ·
      refine ⟨4725176981406717198545327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150117987604478132363551 4725176981406717198545327)
      ·
        refine ⟨7087765472110075797817991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725176981406717198545327 7087765472110075797817991)
        ·
          refine ⟨10631648208165113696726987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087765472110075797817991 10631648208165113696726987)
          ·
            refine ⟨15947472312247670545090481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631648208165113696726987 15947472312247670545090481)
            ·
              refine ⟨11960604234185752908817861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15947472312247670545090481 11960604234185752908817861)
              ·
                refine ⟨2242613293909828670403349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11960604234185752908817861 2242613293909828670403349)
                ·
                  refine ⟨105122498152023218925157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2242613293909828670403349 105122498152023218925157)
                  ·
                    rfl

theorem cell20_230316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_230316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230316 prefixEnd_230316 := by exact prefixLift 230316
  have htrace : WordTrace (prefixWord ++ tailWord_230316) baseStart_230316 baseEnd_230316 := by
    simpa [prefixWord, tailWord_230316, baseEnd_230316] using wordTrace_append hprefix tailTrace_230316
  have hstable : (prefixWord ++ tailWord_230316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230316).length < 2 ^ (prefixWord ++ tailWord_230316).sum := by decide
  have hdescent : baseEnd_230316 < baseStart_230316 := by decide
  rcases family_descends (prefixWord ++ tailWord_230316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230329 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 2]
def baseStart_230329 : Nat := 118140960795 + 230329 * 2 ^ 59
def prefixEnd_230329 : Nat := 4983230072969 + 3 ^ 40 * 230329 * 2
def baseEnd_230329 : Nat := 105128431706252951491771

theorem tailTrace_230329 : CollatzResearch.WordTrace tailWord_230329 prefixEnd_230329 105128431706252951491771 := by
  unfold tailWord_230329
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400788782564844906526041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5600525855043229937684027 8400788782564844906526041)
  ·
    refine ⟨6300591586923633679894531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8400788782564844906526041 6300591586923633679894531)
    ·
      refine ⟨9450887380385450519841797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6300591586923633679894531 9450887380385450519841797)
      ·
        refine ⟨1772041383822271972470337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9450887380385450519841797 1772041383822271972470337)
        ·
          refine ⟨1329031037866703979352753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772041383822271972470337 1329031037866703979352753)
          ·
            refine ⟨996773278400027984514565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329031037866703979352753 996773278400027984514565)
            ·
              refine ⟨186894989700005247096481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 996773278400027984514565 186894989700005247096481)
              ·
                refine ⟨140171242275003935322361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186894989700005247096481 140171242275003935322361)
                ·
                  refine ⟨105128431706252951491771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140171242275003935322361 105128431706252951491771)
                  ·
                    rfl

theorem cell20_230329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_230329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230329 prefixEnd_230329 := by exact prefixLift 230329
  have htrace : WordTrace (prefixWord ++ tailWord_230329) baseStart_230329 baseEnd_230329 := by
    simpa [prefixWord, tailWord_230329, baseEnd_230329] using wordTrace_append hprefix tailTrace_230329
  have hstable : (prefixWord ++ tailWord_230329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230329).length < 2 ^ (prefixWord ++ tailWord_230329).sum := by decide
  have hdescent : baseEnd_230329 < baseStart_230329 := by decide
  rcases family_descends (prefixWord ++ tailWord_230329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230367 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 2]
def baseStart_230367 : Nat := 118140960795 + 230367 * 2 ^ 59
def prefixEnd_230367 : Nat := 4983230072969 + 3 ^ 40 * 230367 * 2
def baseEnd_230367 : Nat := 105145775941693708224949

theorem tailTrace_230367 : CollatzResearch.WordTrace tailWord_230367 prefixEnd_230367 105145775941693708224949 := by
  unfold tailWord_230367
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402174756427177396409355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5601449837618118264272903 8402174756427177396409355)
  ·
    refine ⟨12603262134640766094614033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8402174756427177396409355 12603262134640766094614033)
    ·
      refine ⟨9452446600980574570960525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12603262134640766094614033 9452446600980574570960525)
      ·
        refine ⟨3544667475367715464110197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9452446600980574570960525 3544667475367715464110197)
        ·
          refine ⟨332312575815723324760331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3544667475367715464110197 332312575815723324760331)
          ·
            refine ⟨498468863723584987140497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332312575815723324760331 498468863723584987140497)
            ·
              refine ⟨373851647792688740355373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498468863723584987140497 373851647792688740355373)
              ·
                refine ⟨140194367922258277633265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373851647792688740355373 140194367922258277633265)
                ·
                  refine ⟨105145775941693708224949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140194367922258277633265 105145775941693708224949)
                  ·
                    rfl

theorem cell20_230367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 2].length) (baseStart_230367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230367 prefixEnd_230367 := by exact prefixLift 230367
  have htrace : WordTrace (prefixWord ++ tailWord_230367) baseStart_230367 baseEnd_230367 := by
    simpa [prefixWord, tailWord_230367, baseEnd_230367] using wordTrace_append hprefix tailTrace_230367
  have hstable : (prefixWord ++ tailWord_230367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230367).length < 2 ^ (prefixWord ++ tailWord_230367).sum := by decide
  have hdescent : baseEnd_230367 < baseStart_230367 := by decide
  rcases family_descends (prefixWord ++ tailWord_230367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230378 : List Nat := [3, 1, 3, 1, 2, 3, 7]
def baseStart_230378 : Nat := 118140960795 + 230378 * 2 ^ 59
def prefixEnd_230378 : Nat := 4983230072969 + 3 ^ 40 * 230378 * 2
def baseEnd_230378 : Nat := 11683421849047395428693

theorem tailTrace_230378 : CollatzResearch.WordTrace tailWord_230378 prefixEnd_230378 11683421849047395428693 := by
  unfold tailWord_230378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100643989846831568764947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5601717306258217516706525 2100643989846831568764947)
  ·
    refine ⟨3150965984770247353147421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100643989846831568764947 3150965984770247353147421)
    ·
      refine ⟨1181612244288842757430283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3150965984770247353147421 1181612244288842757430283)
      ·
        refine ⟨1772418366433264136145425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181612244288842757430283 1772418366433264136145425)
        ·
          refine ⟨1329313774824948102109069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772418366433264136145425 1329313774824948102109069)
          ·
            refine ⟨498492665559355538290901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1329313774824948102109069 498492665559355538290901)
            ·
              refine ⟨11683421849047395428693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498492665559355538290901 11683421849047395428693)
              ·
                rfl

theorem cell20_230378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_230378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230378 prefixEnd_230378 := by exact prefixLift 230378
  have htrace : WordTrace (prefixWord ++ tailWord_230378) baseStart_230378 baseEnd_230378 := by
    simpa [prefixWord, tailWord_230378, baseEnd_230378] using wordTrace_append hprefix tailTrace_230378
  have hstable : (prefixWord ++ tailWord_230378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230378).length < 2 ^ (prefixWord ++ tailWord_230378).sum := by decide
  have hdescent : baseEnd_230378 < baseStart_230378 := by decide
  rcases family_descends (prefixWord ++ tailWord_230378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230418 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_230418 : Nat := 118140960795 + 230418 * 2 ^ 59
def prefixEnd_230418 : Nat := 4983230072969 + 3 ^ 40 * 230418 * 2
def baseEnd_230418 : Nat := 105169053731364197524741

theorem tailTrace_230418 : CollatzResearch.WordTrace tailWord_230418 prefixEnd_230418 105169053731364197524741 := by
  unfold tailWord_230418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101008719810603276628977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5602689919494942071010605 2101008719810603276628977)
  ·
    refine ⟨1575756539857952457471733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2101008719810603276628977 1575756539857952457471733)
    ·
      refine ⟨147727175611683042887975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1575756539857952457471733 147727175611683042887975)
      ·
        refine ⟨221590763417524564331963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147727175611683042887975 221590763417524564331963)
        ·
          refine ⟨332386145126286846497945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221590763417524564331963 332386145126286846497945)
          ·
            refine ⟨249289608844715134873459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332386145126286846497945 249289608844715134873459)
            ·
              refine ⟨373934413267072702310189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249289608844715134873459 373934413267072702310189)
              ·
                refine ⟨140225404975152263366321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373934413267072702310189 140225404975152263366321)
                ·
                  refine ⟨105169053731364197524741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140225404975152263366321 105169053731364197524741)
                  ·
                    rfl

theorem cell20_230418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_230418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230418 prefixEnd_230418 := by exact prefixLift 230418
  have htrace : WordTrace (prefixWord ++ tailWord_230418) baseStart_230418 baseEnd_230418 := by
    simpa [prefixWord, tailWord_230418, baseEnd_230418] using wordTrace_append hprefix tailTrace_230418
  have hstable : (prefixWord ++ tailWord_230418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230418).length < 2 ^ (prefixWord ++ tailWord_230418).sum := by decide
  have hdescent : baseEnd_230418 < baseStart_230418 := by decide
  rcases family_descends (prefixWord ++ tailWord_230418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230457 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 3]
def baseStart_230457 : Nat := 118140960795 + 230457 * 2 ^ 59
def prefixEnd_230457 : Nat := 4983230072969 + 3 ^ 40 * 230457 * 2
def baseEnd_230457 : Nat := 105186854394053395224581

theorem tailTrace_230457 : CollatzResearch.WordTrace tailWord_230457 prefixEnd_230457 105186854394053395224581 := by
  unfold tailWord_230457
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405457326101122767185625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5603638217400748511457083 8405457326101122767185625)
  ·
    refine ⟨6304092994575842075389219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8405457326101122767185625 6304092994575842075389219)
    ·
      refine ⟨9456139491863763113083829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6304092994575842075389219 9456139491863763113083829)
      ·
        refine ⟨886513077362227791851609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9456139491863763113083829 886513077362227791851609)
        ·
          refine ⟨664884808021670843888707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886513077362227791851609 664884808021670843888707)
          ·
            refine ⟨997327212032506265833061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664884808021670843888707 997327212032506265833061)
            ·
              refine ⟨186998852256094924843699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 997327212032506265833061 186998852256094924843699)
              ·
                refine ⟨280498278384142387265549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186998852256094924843699 280498278384142387265549)
                ·
                  refine ⟨105186854394053395224581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280498278384142387265549 105186854394053395224581)
                  ·
                    rfl

theorem cell20_230457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_230457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230457 prefixEnd_230457 := by exact prefixLift 230457
  have htrace : WordTrace (prefixWord ++ tailWord_230457) baseStart_230457 baseEnd_230457 := by
    simpa [prefixWord, tailWord_230457, baseEnd_230457] using wordTrace_append hprefix tailTrace_230457
  have hstable : (prefixWord ++ tailWord_230457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230457).length < 2 ^ (prefixWord ++ tailWord_230457).sum := by decide
  have hdescent : baseEnd_230457 < baseStart_230457 := by decide
  rcases family_descends (prefixWord ++ tailWord_230457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230494 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_230494 : Nat := 118140960795 + 230494 * 2 ^ 59
def prefixEnd_230494 : Nat := 4983230072969 + 3 ^ 40 * 230494 * 2
def baseEnd_230494 : Nat := 105203742202245710991097

theorem tailTrace_230494 : CollatzResearch.WordTrace tailWord_230494 prefixEnd_230494 105203742202245710991097 := by
  unfold tailWord_230494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050850853370884760785317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5604537884644718724188357 1050850853370884760785317)
  ·
    refine ⟨197034535007040892647247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1050850853370884760785317 197034535007040892647247)
    ·
      refine ⟨295551802510561338970871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197034535007040892647247 295551802510561338970871)
      ·
        refine ⟨443327703765842008456307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295551802510561338970871 443327703765842008456307)
        ·
          refine ⟨664991555648763012684461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443327703765842008456307 664991555648763012684461)
          ·
            refine ⟨249371833368286129756673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664991555648763012684461 249371833368286129756673)
            ·
              refine ⟨187028875026214597317505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249371833368286129756673 187028875026214597317505)
              ·
                refine ⟨140271656269660947988129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187028875026214597317505 140271656269660947988129)
                ·
                  refine ⟨105203742202245710991097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140271656269660947988129 105203742202245710991097)
                  ·
                    rfl

theorem cell20_230494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_230494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230494 prefixEnd_230494 := by exact prefixLift 230494
  have htrace : WordTrace (prefixWord ++ tailWord_230494) baseStart_230494 baseEnd_230494 := by
    simpa [prefixWord, tailWord_230494, baseEnd_230494] using wordTrace_append hprefix tailTrace_230494
  have hstable : (prefixWord ++ tailWord_230494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230494).length < 2 ^ (prefixWord ++ tailWord_230494).sum := by decide
  have hdescent : baseEnd_230494 < baseStart_230494 := by decide
  rcases family_descends (prefixWord ++ tailWord_230494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230498 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_230498 : Nat := 118140960795 + 230498 * 2 ^ 59
def prefixEnd_230498 : Nat := 4983230072969 + 3 ^ 40 * 230498 * 2
def baseEnd_230498 : Nat := 105205567911239474857747

theorem tailTrace_230498 : CollatzResearch.WordTrace tailWord_230498 prefixEnd_230498 105205567911239474857747 := by
  unfold tailWord_230498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101738179738146692357037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5604635145968391179618765 2101738179738146692357037)
  ·
    refine ⟨788151817401805009633889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2101738179738146692357037 788151817401805009633889)
    ·
      refine ⟨591113863051353757225417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 788151817401805009633889 591113863051353757225417)
      ·
        refine ⟨443335397288515317919063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591113863051353757225417 443335397288515317919063)
        ·
          refine ⟨665003095932772976878595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443335397288515317919063 665003095932772976878595)
          ·
            refine ⟨997504643899159465317893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665003095932772976878595 997504643899159465317893)
            ·
              refine ⟨187032120731092399747105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 997504643899159465317893 187032120731092399747105)
              ·
                refine ⟨140274090548319299810329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187032120731092399747105 140274090548319299810329)
                ·
                  refine ⟨105205567911239474857747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140274090548319299810329 105205567911239474857747)
                  ·
                    rfl

theorem cell20_230498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_230498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230498 prefixEnd_230498 := by exact prefixLift 230498
  have htrace : WordTrace (prefixWord ++ tailWord_230498) baseStart_230498 baseEnd_230498 := by
    simpa [prefixWord, tailWord_230498, baseEnd_230498] using wordTrace_append hprefix tailTrace_230498
  have hstable : (prefixWord ++ tailWord_230498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230498).length < 2 ^ (prefixWord ++ tailWord_230498).sum := by decide
  have hdescent : baseEnd_230498 < baseStart_230498 := by decide
  rcases family_descends (prefixWord ++ tailWord_230498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230509 : List Nat := [1, 5, 1, 1, 2, 4, 1, 5]
def baseStart_230509 : Nat := 118140960795 + 230509 * 2 ^ 59
def prefixEnd_230509 : Nat := 4983230072969 + 3 ^ 40 * 230509 * 2
def baseEnd_230509 : Nat := 35070196203657441830345

theorem tailTrace_230509 : CollatzResearch.WordTrace tailWord_230509 prefixEnd_230509 35070196203657441830345 := by
  unfold tailWord_230509
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407353921912735648078581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5604902614608490432052387 8407353921912735648078581)
  ·
    refine ⟨788189430179318967007367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8407353921912735648078581 788189430179318967007367)
    ·
      refine ⟨1182284145268978450511051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788189430179318967007367 1182284145268978450511051)
      ·
        refine ⟨1773426217903467675766577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182284145268978450511051 1773426217903467675766577)
        ·
          refine ⟨1330069663427600756824933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773426217903467675766577 1330069663427600756824933)
          ·
            refine ⟨249388061892675141904675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1330069663427600756824933 249388061892675141904675)
            ·
              refine ⟨374082092839012712857013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249388061892675141904675 374082092839012712857013)
              ·
                refine ⟨35070196203657441830345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374082092839012712857013 35070196203657441830345)
                ·
                  rfl

theorem cell20_230509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_230509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230509 prefixEnd_230509 := by exact prefixLift 230509
  have htrace : WordTrace (prefixWord ++ tailWord_230509) baseStart_230509 baseEnd_230509 := by
    simpa [prefixWord, tailWord_230509, baseEnd_230509] using wordTrace_append hprefix tailTrace_230509
  have hstable : (prefixWord ++ tailWord_230509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230509).length < 2 ^ (prefixWord ++ tailWord_230509).sum := by decide
  have hdescent : baseEnd_230509 < baseStart_230509 := by decide
  rcases family_descends (prefixWord ++ tailWord_230509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230513 : List Nat := [1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_230513 : Nat := 118140960795 + 230513 * 2 ^ 59
def prefixEnd_230513 : Nat := 4983230072969 + 3 ^ 40 * 230513 * 2
def baseEnd_230513 : Nat := 35070804773322029785895

theorem tailTrace_230513 : CollatzResearch.WordTrace tailWord_230513 prefixEnd_230513 35070804773322029785895 := by
  unfold tailWord_230513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407499813898244331224193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5604999875932162887482795 8407499813898244331224193)
  ·
    refine ⟨6305624860423683248418145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8407499813898244331224193 6305624860423683248418145)
    ·
      refine ⟨4729218645317762436313609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6305624860423683248418145 4729218645317762436313609)
      ·
        refine ⟨3546913983988321827235207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4729218645317762436313609 3546913983988321827235207)
        ·
          refine ⟨5320370975982482740852811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546913983988321827235207 5320370975982482740852811)
          ·
            refine ⟨7980556463973724111279217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320370975982482740852811 7980556463973724111279217)
            ·
              refine ⟨5985417347980293083459413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980556463973724111279217 5985417347980293083459413)
              ·
                refine ⟨35070804773322029785895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5985417347980293083459413 35070804773322029785895)
                ·
                  rfl

theorem cell20_230513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_230513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230513 prefixEnd_230513 := by exact prefixLift 230513
  have htrace : WordTrace (prefixWord ++ tailWord_230513) baseStart_230513 baseEnd_230513 := by
    simpa [prefixWord, tailWord_230513, baseEnd_230513] using wordTrace_append hprefix tailTrace_230513
  have hstable : (prefixWord ++ tailWord_230513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230513).length < 2 ^ (prefixWord ++ tailWord_230513).sum := by decide
  have hdescent : baseEnd_230513 < baseStart_230513 := by decide
  rcases family_descends (prefixWord ++ tailWord_230513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230554 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_230554 : Nat := 118140960795 + 230554 * 2 ^ 59
def prefixEnd_230554 : Nat := 4983230072969 + 3 ^ 40 * 230554 * 2
def baseEnd_230554 : Nat := 105231127837152168990851

theorem tailTrace_230554 : CollatzResearch.WordTrace tailWord_230554 prefixEnd_230554 105231127837152168990851 := by
  unfold tailWord_230554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102248801687427083366679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5605996804499805555644477 2102248801687427083366679)
  ·
    refine ⟨3153373202531140625050019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2102248801687427083366679 3153373202531140625050019)
    ·
      refine ⟨4730059803796710937575029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3153373202531140625050019 4730059803796710937575029)
      ·
        refine ⟨443443106605941650397659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4730059803796710937575029 443443106605941650397659)
        ·
          refine ⟨665164659908912475596489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443443106605941650397659 665164659908912475596489)
          ·
            refine ⟨498873494931684356697367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665164659908912475596489 498873494931684356697367)
            ·
              refine ⟨748310242397526535046051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498873494931684356697367 748310242397526535046051)
              ·
                refine ⟨1122465363596289802569077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748310242397526535046051 1122465363596289802569077)
                ·
                  refine ⟨105231127837152168990851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122465363596289802569077 105231127837152168990851)
                  ·
                    rfl

theorem cell20_230554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_230554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230554 prefixEnd_230554 := by exact prefixLift 230554
  have htrace : WordTrace (prefixWord ++ tailWord_230554) baseStart_230554 baseEnd_230554 := by
    simpa [prefixWord, tailWord_230554, baseEnd_230554] using wordTrace_append hprefix tailTrace_230554
  have hstable : (prefixWord ++ tailWord_230554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230554).length < 2 ^ (prefixWord ++ tailWord_230554).sum := by decide
  have hdescent : baseEnd_230554 < baseStart_230554 := by decide
  rcases family_descends (prefixWord ++ tailWord_230554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230561 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_230561 : Nat := 118140960795 + 230561 * 2 ^ 59
def prefixEnd_230561 : Nat := 4983230072969 + 3 ^ 40 * 230561 * 2
def baseEnd_230561 : Nat := 105234322827891255757489

theorem tailTrace_230561 : CollatzResearch.WordTrace tailWord_230561 prefixEnd_230561 105234322827891255757489 := by
  unfold tailWord_230561
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409250517724348528971537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5606167011816232352647691 8409250517724348528971537)
  ·
    refine ⟨6306937888293261396728653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8409250517724348528971537 6306937888293261396728653)
    ·
      refine ⟨2365101708109973023773245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6306937888293261396728653 2365101708109973023773245)
      ·
        refine ⟨886913140541239883914967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2365101708109973023773245 886913140541239883914967)
        ·
          refine ⟨1330369710811859825872451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886913140541239883914967 1330369710811859825872451)
          ·
            refine ⟨1995554566217789738808677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330369710811859825872451 1995554566217789738808677)
            ·
              refine ⟨374166481165835576026627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1995554566217789738808677 374166481165835576026627)
              ·
                refine ⟨561249721748753364039941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374166481165835576026627 561249721748753364039941)
                ·
                  refine ⟨105234322827891255757489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561249721748753364039941 105234322827891255757489)
                  ·
                    rfl

theorem cell20_230561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_230561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230561 prefixEnd_230561 := by exact prefixLift 230561
  have htrace : WordTrace (prefixWord ++ tailWord_230561) baseStart_230561 baseEnd_230561 := by
    simpa [prefixWord, tailWord_230561, baseEnd_230561] using wordTrace_append hprefix tailTrace_230561
  have hstable : (prefixWord ++ tailWord_230561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230561).length < 2 ^ (prefixWord ++ tailWord_230561).sum := by decide
  have hdescent : baseEnd_230561 < baseStart_230561 := by decide
  rcases family_descends (prefixWord ++ tailWord_230561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230575 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_230575 : Nat := 118140960795 + 230575 * 2 ^ 59
def prefixEnd_230575 : Nat := 4983230072969 + 3 ^ 40 * 230575 * 2
def baseEnd_230575 : Nat := 105240712809369429290765

theorem tailTrace_230575 : CollatzResearch.WordTrace tailWord_230575 prefixEnd_230575 105240712809369429290765 := by
  unfold tailWord_230575
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409761139673628919981179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5606507426449085946654119 8409761139673628919981179)
  ·
    refine ⟨12614641709510443379971769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8409761139673628919981179 12614641709510443379971769)
    ·
      refine ⟨9460981282132832534978827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12614641709510443379971769 9460981282132832534978827)
      ·
        refine ⟨14191471923199248802468241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9460981282132832534978827 14191471923199248802468241)
        ·
          refine ⟨10643603942399436601851181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14191471923199248802468241 10643603942399436601851181)
          ·
            refine ⟨3991351478399788725694193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10643603942399436601851181 3991351478399788725694193)
            ·
              refine ⟨2993513608799841544270645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991351478399788725694193 2993513608799841544270645)
              ·
                refine ⟨280641900824985144775373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2993513608799841544270645 280641900824985144775373)
                ·
                  refine ⟨105240712809369429290765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280641900824985144775373 105240712809369429290765)
                  ·
                    rfl

theorem cell20_230575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_230575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230575 prefixEnd_230575 := by exact prefixLift 230575
  have htrace : WordTrace (prefixWord ++ tailWord_230575) baseStart_230575 baseEnd_230575 := by
    simpa [prefixWord, tailWord_230575, baseEnd_230575] using wordTrace_append hprefix tailTrace_230575
  have hstable : (prefixWord ++ tailWord_230575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230575).length < 2 ^ (prefixWord ++ tailWord_230575).sum := by decide
  have hdescent : baseEnd_230575 < baseStart_230575 := by decide
  rcases family_descends (prefixWord ++ tailWord_230575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230585 : List Nat := [1, 2, 1, 4, 1, 5, 2, 4]
def baseStart_230585 : Nat := 118140960795 + 230585 * 2 ^ 59
def prefixEnd_230585 : Nat := 4983230072969 + 3 ^ 40 * 230585 * 2
def baseEnd_230585 : Nat := 35081759027284612985797

theorem tailTrace_230585 : CollatzResearch.WordTrace tailWord_230585 prefixEnd_230585 35081759027284612985797 := by
  unfold tailWord_230585
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410125869637400627845209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5606750579758267085230139 8410125869637400627845209)
  ·
    refine ⟨6307594402228050470883907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8410125869637400627845209 6307594402228050470883907)
    ·
      refine ⟨9461391603342075706325861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6307594402228050470883907 9461391603342075706325861)
      ·
        refine ⟨1774010925626639194936099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9461391603342075706325861 1774010925626639194936099)
        ·
          refine ⟨2661016388439958792404149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774010925626639194936099 2661016388439958792404149)
          ·
            refine ⟨249470286416246136787889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2661016388439958792404149 249470286416246136787889)
            ·
              refine ⟨187102714812184602590917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249470286416246136787889 187102714812184602590917)
              ·
                refine ⟨35081759027284612985797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187102714812184602590917 35081759027284612985797)
                ·
                  rfl

theorem cell20_230585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_230585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230585 prefixEnd_230585 := by exact prefixLift 230585
  have htrace : WordTrace (prefixWord ++ tailWord_230585) baseStart_230585 baseEnd_230585 := by
    simpa [prefixWord, tailWord_230585, baseEnd_230585] using wordTrace_append hprefix tailTrace_230585
  have hstable : (prefixWord ++ tailWord_230585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230585).length < 2 ^ (prefixWord ++ tailWord_230585).sum := by decide
  have hdescent : baseEnd_230585 < baseStart_230585 := by decide
  rcases family_descends (prefixWord ++ tailWord_230585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230598 : List Nat := [6, 1, 2, 2, 2, 1, 6]
def baseStart_230598 : Nat := 118140960795 + 230598 * 2 ^ 59
def prefixEnd_230598 : Nat := 4983230072969 + 3 ^ 40 * 230598 * 2
def baseEnd_230598 : Nat := 11694578959564841280445

theorem tailTrace_230598 : CollatzResearch.WordTrace tailWord_230598 prefixEnd_230598 11694578959564841280445 := by
  unfold tailWord_230598
  simp only [CollatzResearch.WordTrace]
  refine ⟨262831250580946995252139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5607066679060202565378965 262831250580946995252139)
  ·
    refine ⟨394246875871420492878209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262831250580946995252139 394246875871420492878209)
    ·
      refine ⟨295685156903565369658657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394246875871420492878209 295685156903565369658657)
      ·
        refine ⟨221763867677674027243993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295685156903565369658657 221763867677674027243993)
        ·
          refine ⟨166322900758255520432995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221763867677674027243993 166322900758255520432995)
          ·
            refine ⟨249484351137383280649493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166322900758255520432995 249484351137383280649493)
            ·
              refine ⟨11694578959564841280445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249484351137383280649493 11694578959564841280445)
              ·
                rfl

theorem cell20_230598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 6].length) (baseStart_230598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230598 prefixEnd_230598 := by exact prefixLift 230598
  have htrace : WordTrace (prefixWord ++ tailWord_230598) baseStart_230598 baseEnd_230598 := by
    simpa [prefixWord, tailWord_230598, baseEnd_230598] using wordTrace_append hprefix tailTrace_230598
  have hstable : (prefixWord ++ tailWord_230598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230598).length < 2 ^ (prefixWord ++ tailWord_230598).sum := by decide
  have hdescent : baseEnd_230598 < baseStart_230598 := by decide
  rcases family_descends (prefixWord ++ tailWord_230598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230612 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 4]
def baseStart_230612 : Nat := 118140960795 + 230612 * 2 ^ 59
def prefixEnd_230612 : Nat := 4983230072969 + 3 ^ 40 * 230612 * 2
def baseEnd_230612 : Nat := 105257600617561745057281

theorem tailTrace_230612 : CollatzResearch.WordTrace tailWord_230612 prefixEnd_230612 105257600617561745057281 := by
  unfold tailWord_230612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205555320269792119539045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5607407093693056159385393 4205555320269792119539045)
  ·
    refine ⟨788541622550586022413571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4205555320269792119539045 788541622550586022413571)
    ·
      refine ⟨1182812433825879033620357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788541622550586022413571 1182812433825879033620357)
      ·
        refine ⟨221777331342352318803817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1182812433825879033620357 221777331342352318803817)
        ·
          refine ⟨166332998506764239102863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221777331342352318803817 166332998506764239102863)
          ·
            refine ⟨249499497760146358654295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166332998506764239102863 249499497760146358654295)
            ·
              refine ⟨374249246640219537981443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249499497760146358654295 374249246640219537981443)
              ·
                refine ⟨561373869960329306972165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374249246640219537981443 561373869960329306972165)
                ·
                  refine ⟨105257600617561745057281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561373869960329306972165 105257600617561745057281)
                  ·
                    rfl

theorem cell20_230612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_230612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230612 prefixEnd_230612 := by exact prefixLift 230612
  have htrace : WordTrace (prefixWord ++ tailWord_230612) baseStart_230612 baseEnd_230612 := by
    simpa [prefixWord, tailWord_230612, baseEnd_230612] using wordTrace_append hprefix tailTrace_230612
  have hstable : (prefixWord ++ tailWord_230612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230612).length < 2 ^ (prefixWord ++ tailWord_230612).sum := by decide
  have hdescent : baseEnd_230612 < baseStart_230612 := by decide
  rcases family_descends (prefixWord ++ tailWord_230612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230616 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_230616 : Nat := 118140960795 + 230616 * 2 ^ 59
def prefixEnd_230616 : Nat := 4983230072969 + 3 ^ 40 * 230616 * 2
def baseEnd_230616 : Nat := 105259426326555508923931

theorem tailTrace_230616 : CollatzResearch.WordTrace tailWord_230616 prefixEnd_230616 105259426326555508923931 := by
  unfold tailWord_230616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205628266262546461111851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5607504355016728614815801 4205628266262546461111851)
  ·
    refine ⟨6308442399393819691667777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4205628266262546461111851 6308442399393819691667777)
    ·
      refine ⟨4731331799545364768750833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6308442399393819691667777 4731331799545364768750833)
      ·
        refine ⟨3548498849659023576563125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731331799545364768750833 3548498849659023576563125)
        ·
          refine ⟨332671767155533460302793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3548498849659023576563125 332671767155533460302793)
          ·
            refine ⟨249503825366650095227095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332671767155533460302793 249503825366650095227095)
            ·
              refine ⟨374255738049975142840643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249503825366650095227095 374255738049975142840643)
              ·
                refine ⟨561383607074962714260965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374255738049975142840643 561383607074962714260965)
                ·
                  refine ⟨105259426326555508923931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561383607074962714260965 105259426326555508923931)
                  ·
                    rfl

theorem cell20_230616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_230616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230616 prefixEnd_230616 := by exact prefixLift 230616
  have htrace : WordTrace (prefixWord ++ tailWord_230616) baseStart_230616 baseEnd_230616 := by
    simpa [prefixWord, tailWord_230616, baseEnd_230616] using wordTrace_append hprefix tailTrace_230616
  have hstable : (prefixWord ++ tailWord_230616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230616).length < 2 ^ (prefixWord ++ tailWord_230616).sum := by decide
  have hdescent : baseEnd_230616 < baseStart_230616 := by decide
  rcases family_descends (prefixWord ++ tailWord_230616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230668 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_230668 : Nat := 118140960795 + 230668 * 2 ^ 59
def prefixEnd_230668 : Nat := 4983230072969 + 3 ^ 40 * 230668 * 2
def baseEnd_230668 : Nat := 105283160543474439190385

theorem tailTrace_230668 : CollatzResearch.WordTrace tailWord_230668 prefixEnd_230668 105283160543474439190385 := by
  unfold tailWord_230668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206576564168352901558329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5608768752224470535411105 4206576564168352901558329)
  ·
    refine ⟨3154932423126264676168747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4206576564168352901558329 3154932423126264676168747)
    ·
      refine ⟨4732398634689397014253121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154932423126264676168747 4732398634689397014253121)
      ·
        refine ⟨3549298976017047760689841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4732398634689397014253121 3549298976017047760689841)
        ·
          refine ⟨2661974232012785820517381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3549298976017047760689841 2661974232012785820517381)
          ·
            refine ⟨499120168502397341347009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2661974232012785820517381 499120168502397341347009)
            ·
              refine ⟨374340126376798006010257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499120168502397341347009 374340126376798006010257)
              ·
                refine ⟨280755094782598504507693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374340126376798006010257 280755094782598504507693)
                ·
                  refine ⟨105283160543474439190385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280755094782598504507693 105283160543474439190385)
                  ·
                    rfl

theorem cell20_230668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_230668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230668 prefixEnd_230668 := by exact prefixLift 230668
  have htrace : WordTrace (prefixWord ++ tailWord_230668) baseStart_230668 baseEnd_230668 := by
    simpa [prefixWord, tailWord_230668, baseEnd_230668] using wordTrace_append hprefix tailTrace_230668
  have hstable : (prefixWord ++ tailWord_230668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230668).length < 2 ^ (prefixWord ++ tailWord_230668).sum := by decide
  have hdescent : baseEnd_230668 < baseStart_230668 := by decide
  rcases family_descends (prefixWord ++ tailWord_230668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230672 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_230672 : Nat := 118140960795 + 230672 * 2 ^ 59
def prefixEnd_230672 : Nat := 4983230072969 + 3 ^ 40 * 230672 * 2
def baseEnd_230672 : Nat := 105284986252468203057035

theorem tailTrace_230672 : CollatzResearch.WordTrace tailWord_230672 prefixEnd_230672 105284986252468203057035 := by
  unfold tailWord_230672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206649510161107243131135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5608866013548142990841513 4206649510161107243131135)
  ·
    refine ⟨6309974265241660864696703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206649510161107243131135 6309974265241660864696703)
    ·
      refine ⟨9464961397862491297045055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309974265241660864696703 9464961397862491297045055)
      ·
        refine ⟨14197442096793736945567583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9464961397862491297045055 14197442096793736945567583)
        ·
          refine ⟨21296163145190605418351375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197442096793736945567583 21296163145190605418351375)
          ·
            refine ⟨31944244717785908127527063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21296163145190605418351375 31944244717785908127527063)
            ·
              refine ⟨47916367076678862191290595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31944244717785908127527063 47916367076678862191290595)
              ·
                refine ⟨71874550615018293286935893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47916367076678862191290595 71874550615018293286935893)
                ·
                  refine ⟨105284986252468203057035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 71874550615018293286935893 105284986252468203057035)
                  ·
                    rfl

theorem cell20_230672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_230672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230672 prefixEnd_230672 := by exact prefixLift 230672
  have htrace : WordTrace (prefixWord ++ tailWord_230672) baseStart_230672 baseEnd_230672 := by
    simpa [prefixWord, tailWord_230672, baseEnd_230672] using wordTrace_append hprefix tailTrace_230672
  have hstable : (prefixWord ++ tailWord_230672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230672).length < 2 ^ (prefixWord ++ tailWord_230672).sum := by decide
  have hdescent : baseEnd_230672 < baseStart_230672 := by decide
  rcases family_descends (prefixWord ++ tailWord_230672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230682 : List Nat := [3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_230682 : Nat := 118140960795 + 230682 * 2 ^ 59
def prefixEnd_230682 : Nat := 4983230072969 + 3 ^ 40 * 230682 * 2
def baseEnd_230682 : Nat := 35096516841650870907887

theorem tailTrace_230682 : CollatzResearch.WordTrace tailWord_230682 prefixEnd_230682 35096516841650870907887 := by
  unfold tailWord_230682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2103415937571496548531575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5609109166857324129417533 2103415937571496548531575)
  ·
    refine ⟨3155123906357244822797363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2103415937571496548531575 3155123906357244822797363)
    ·
      refine ⟨4732685859535867234196045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155123906357244822797363 4732685859535867234196045)
      ·
        refine ⟨1774757197325950212823517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4732685859535867234196045 1774757197325950212823517)
        ·
          refine ⟨665533948997231329808819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1774757197325950212823517 665533948997231329808819)
          ·
            refine ⟨998300923495846994713229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665533948997231329808819 998300923495846994713229)
            ·
              refine ⟨374362846310942623017461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998300923495846994713229 374362846310942623017461)
              ·
                refine ⟨35096516841650870907887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374362846310942623017461 35096516841650870907887)
                ·
                  rfl

theorem cell20_230682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_230682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230682 prefixEnd_230682 := by exact prefixLift 230682
  have htrace : WordTrace (prefixWord ++ tailWord_230682) baseStart_230682 baseEnd_230682 := by
    simpa [prefixWord, tailWord_230682, baseEnd_230682] using wordTrace_append hprefix tailTrace_230682
  have hstable : (prefixWord ++ tailWord_230682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230682).length < 2 ^ (prefixWord ++ tailWord_230682).sum := by decide
  have hdescent : baseEnd_230682 < baseStart_230682 := by decide
  rcases family_descends (prefixWord ++ tailWord_230682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230726 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_230726 : Nat := 118140960795 + 230726 * 2 ^ 59
def prefixEnd_230726 : Nat := 4983230072969 + 3 ^ 40 * 230726 * 2
def baseEnd_230726 : Nat := 105309633323884015256815

theorem tailTrace_230726 : CollatzResearch.WordTrace tailWord_230726 prefixEnd_230726 105309633323884015256815 := by
  unfold tailWord_230726
  simp only [CollatzResearch.WordTrace]
  refine ⟨262977142566455678397751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5610179041417721139152021 262977142566455678397751)
  ·
    refine ⟨394465713849683517596627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262977142566455678397751 394465713849683517596627)
    ·
      refine ⟨591698570774525276394941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394465713849683517596627 591698570774525276394941)
      ·
        refine ⟨221886964040446978648103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 591698570774525276394941 221886964040446978648103)
        ·
          refine ⟨332830446060670467972155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221886964040446978648103 332830446060670467972155)
          ·
            refine ⟨499245669091005701958233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332830446060670467972155 499245669091005701958233)
            ·
              refine ⟨374434251818254276468675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499245669091005701958233 374434251818254276468675)
              ·
                refine ⟨561651377727381414703013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374434251818254276468675 561651377727381414703013)
                ·
                  refine ⟨105309633323884015256815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561651377727381414703013 105309633323884015256815)
                  ·
                    rfl

theorem cell20_230726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_230726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230726 prefixEnd_230726 := by exact prefixLift 230726
  have htrace : WordTrace (prefixWord ++ tailWord_230726) baseStart_230726 baseEnd_230726 := by
    simpa [prefixWord, tailWord_230726, baseEnd_230726] using wordTrace_append hprefix tailTrace_230726
  have hstable : (prefixWord ++ tailWord_230726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230726).length < 2 ^ (prefixWord ++ tailWord_230726).sum := by decide
  have hdescent : baseEnd_230726 < baseStart_230726 := by decide
  rcases family_descends (prefixWord ++ tailWord_230726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230727 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_230727 : Nat := 118140960795 + 230727 * 2 ^ 59
def prefixEnd_230727 : Nat := 4983230072969 + 3 ^ 40 * 230727 * 2
def baseEnd_230727 : Nat := 105310089751132456223477

theorem tailTrace_230727 : CollatzResearch.WordTrace tailWord_230727 prefixEnd_230727 105310089751132456223477 := by
  unfold tailWord_230727
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415305035122958879514435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5610203356748639253009623 8415305035122958879514435)
  ·
    refine ⟨12622957552684438319271653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415305035122958879514435 12622957552684438319271653)
    ·
      refine ⟨2366804541128332184863435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12622957552684438319271653 2366804541128332184863435)
      ·
        refine ⟨3550206811692498277295153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366804541128332184863435 3550206811692498277295153)
        ·
          refine ⟨2662655108769373707971365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3550206811692498277295153 2662655108769373707971365)
          ·
            refine ⟨499247832894257570244631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2662655108769373707971365 499247832894257570244631)
            ·
              refine ⟨748871749341386355366947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499247832894257570244631 748871749341386355366947)
              ·
                refine ⟨1123307624012079533050421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748871749341386355366947 1123307624012079533050421)
                ·
                  refine ⟨105310089751132456223477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1123307624012079533050421 105310089751132456223477)
                  ·
                    rfl

theorem cell20_230727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_230727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230727 prefixEnd_230727 := by exact prefixLift 230727
  have htrace : WordTrace (prefixWord ++ tailWord_230727) baseStart_230727 baseEnd_230727 := by
    simpa [prefixWord, tailWord_230727, baseEnd_230727] using wordTrace_append hprefix tailTrace_230727
  have hstable : (prefixWord ++ tailWord_230727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230727).length < 2 ^ (prefixWord ++ tailWord_230727).sum := by decide
  have hdescent : baseEnd_230727 < baseStart_230727 := by decide
  rcases family_descends (prefixWord ++ tailWord_230727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230744 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_230744 : Nat := 118140960795 + 230744 * 2 ^ 59
def prefixEnd_230744 : Nat := 4983230072969 + 3 ^ 40 * 230744 * 2
def baseEnd_230744 : Nat := 105317849014355952656741

theorem tailTrace_230744 : CollatzResearch.WordTrace tailWord_230744 prefixEnd_230744 105317849014355952656741 := by
  unfold tailWord_230744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207962538030685391441643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5610616717374247188588857 4207962538030685391441643)
  ·
    refine ⟨6311943807046028087162465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4207962538030685391441643 6311943807046028087162465)
    ·
      refine ⟨4733957855284521065371849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6311943807046028087162465 4733957855284521065371849)
      ·
        refine ⟨3550468391463390799028887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4733957855284521065371849 3550468391463390799028887)
        ·
          refine ⟨5325702587195086198543331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550468391463390799028887 5325702587195086198543331)
          ·
            refine ⟨7988553880792629297814997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325702587195086198543331 7988553880792629297814997)
            ·
              refine ⟨187231731581077249167539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7988553880792629297814997 187231731581077249167539)
              ·
                refine ⟨280847597371615873751309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187231731581077249167539 280847597371615873751309)
                ·
                  refine ⟨105317849014355952656741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280847597371615873751309 105317849014355952656741)
                  ·
                    rfl

theorem cell20_230744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_230744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230744 prefixEnd_230744 := by exact prefixLift 230744
  have htrace : WordTrace (prefixWord ++ tailWord_230744) baseStart_230744 baseEnd_230744 := by
    simpa [prefixWord, tailWord_230744, baseEnd_230744] using wordTrace_append hprefix tailTrace_230744
  have hstable : (prefixWord ++ tailWord_230744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230744).length < 2 ^ (prefixWord ++ tailWord_230744).sum := by decide
  have hdescent : baseEnd_230744 < baseStart_230744 := by decide
  rcases family_descends (prefixWord ++ tailWord_230744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230765 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_230765 : Nat := 118140960795 + 230765 * 2 ^ 59
def prefixEnd_230765 : Nat := 4983230072969 + 3 ^ 40 * 230765 * 2
def baseEnd_230765 : Nat := 105327433986573212956655

theorem tailTrace_230765 : CollatzResearch.WordTrace tailWord_230765 prefixEnd_230765 105327433986573212956655 := by
  unfold tailWord_230765
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416691008985291369397749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5611127339323527579598499 8416691008985291369397749)
  ·
    refine ⟨789064782092371065881039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8416691008985291369397749 789064782092371065881039)
    ·
      refine ⟨1183597173138556598821559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789064782092371065881039 1183597173138556598821559)
      ·
        refine ⟨1775395759707834898232339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183597173138556598821559 1775395759707834898232339)
        ·
          refine ⟨2663093639561752347348509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775395759707834898232339 2663093639561752347348509)
          ·
            refine ⟨998660114835657130255691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2663093639561752347348509 998660114835657130255691)
            ·
              refine ⟨1497990172253485695383537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998660114835657130255691 1497990172253485695383537)
              ·
                refine ⟨1123492629190114271537653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497990172253485695383537 1123492629190114271537653)
                ·
                  refine ⟨105327433986573212956655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1123492629190114271537653 105327433986573212956655)
                  ·
                    rfl

theorem cell20_230765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_230765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230765 prefixEnd_230765 := by exact prefixLift 230765
  have htrace : WordTrace (prefixWord ++ tailWord_230765) baseStart_230765 baseEnd_230765 := by
    simpa [prefixWord, tailWord_230765, baseEnd_230765] using wordTrace_append hprefix tailTrace_230765
  have hstable : (prefixWord ++ tailWord_230765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230765).length < 2 ^ (prefixWord ++ tailWord_230765).sum := by decide
  have hdescent : baseEnd_230765 < baseStart_230765 := by decide
  rcases family_descends (prefixWord ++ tailWord_230765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230785 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 4]
def baseStart_230785 : Nat := 118140960795 + 230785 * 2 ^ 59
def prefixEnd_230785 : Nat := 4983230072969 + 3 ^ 40 * 230785 * 2
def baseEnd_230785 : Nat := 105336562531542032289907

theorem tailTrace_230785 : CollatzResearch.WordTrace tailWord_230785 prefixEnd_230785 105336562531542032289907 := by
  unfold tailWord_230785
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417420468912834785125809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5611613645941889856750539 8417420468912834785125809)
  ·
    refine ⟨6313065351684626088844357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8417420468912834785125809 6313065351684626088844357)
    ·
      refine ⟨1183699753440867391658317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6313065351684626088844357 1183699753440867391658317)
      ·
        refine ⟨443887407540325271871869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1183699753440867391658317 443887407540325271871869)
        ·
          refine ⟨166457777827621976951951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443887407540325271871869 166457777827621976951951)
          ·
            refine ⟨249686666741432965427927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166457777827621976951951 249686666741432965427927)
            ·
              refine ⟨374530000112149448141891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249686666741432965427927 374530000112149448141891)
              ·
                refine ⟨561795000168224172212837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374530000112149448141891 561795000168224172212837)
                ·
                  refine ⟨105336562531542032289907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561795000168224172212837 105336562531542032289907)
                  ·
                    rfl

theorem cell20_230785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_230785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230785 prefixEnd_230785 := by exact prefixLift 230785
  have htrace : WordTrace (prefixWord ++ tailWord_230785) baseStart_230785 baseEnd_230785 := by
    simpa [prefixWord, tailWord_230785, baseEnd_230785] using wordTrace_append hprefix tailTrace_230785
  have hstable : (prefixWord ++ tailWord_230785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230785).length < 2 ^ (prefixWord ++ tailWord_230785).sum := by decide
  have hdescent : baseEnd_230785 < baseStart_230785 := by decide
  rcases family_descends (prefixWord ++ tailWord_230785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230789 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 2]
def baseStart_230789 : Nat := 118140960795 + 230789 * 2 ^ 59
def prefixEnd_230789 : Nat := 4983230072969 + 3 ^ 40 * 230789 * 2
def baseEnd_230789 : Nat := 105338388240535796156557

theorem tailTrace_230789 : CollatzResearch.WordTrace tailWord_230789 prefixEnd_230789 105338388240535796156557 := by
  unfold tailWord_230789
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417566360898343468271421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5611710907265562312180947 8417566360898343468271421)
  ·
    refine ⟨3156587385336878800601783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8417566360898343468271421 3156587385336878800601783)
    ·
      refine ⟨4734881078005318200902675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156587385336878800601783 4734881078005318200902675)
      ·
        refine ⟨7102321617007977301354013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734881078005318200902675 7102321617007977301354013)
        ·
          refine ⟨2663370606377991488007755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7102321617007977301354013 2663370606377991488007755)
          ·
            refine ⟨3995055909566987232011633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663370606377991488007755 3995055909566987232011633)
            ·
              refine ⟨2996291932175240424008725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3995055909566987232011633 2996291932175240424008725)
              ·
                refine ⟨140451184320714394875409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2996291932175240424008725 140451184320714394875409)
                ·
                  refine ⟨105338388240535796156557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140451184320714394875409 105338388240535796156557)
                  ·
                    rfl

theorem cell20_230789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_230789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230789 prefixEnd_230789 := by exact prefixLift 230789
  have htrace : WordTrace (prefixWord ++ tailWord_230789) baseStart_230789 baseEnd_230789 := by
    simpa [prefixWord, tailWord_230789, baseEnd_230789] using wordTrace_append hprefix tailTrace_230789
  have hstable : (prefixWord ++ tailWord_230789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230789).length < 2 ^ (prefixWord ++ tailWord_230789).sum := by decide
  have hdescent : baseEnd_230789 < baseStart_230789 := by decide
  rcases family_descends (prefixWord ++ tailWord_230789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230810 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_230810 : Nat := 118140960795 + 230810 * 2 ^ 59
def prefixEnd_230810 : Nat := 4983230072969 + 3 ^ 40 * 230810 * 2
def baseEnd_230810 : Nat := 105347973212753056456471

theorem tailTrace_230810 : CollatzResearch.WordTrace tailWord_230810 prefixEnd_230810 105347973212753056456471 := by
  unfold tailWord_230810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104583073455566013696471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5612221529214842703190589 2104583073455566013696471)
  ·
    refine ⟨3156874610183349020544707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104583073455566013696471 3156874610183349020544707)
    ·
      refine ⟨4735311915275023530817061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3156874610183349020544707 4735311915275023530817061)
      ·
        refine ⟨887870984114066912028199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4735311915275023530817061 887870984114066912028199)
        ·
          refine ⟨1331806476171100368042299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887870984114066912028199 1331806476171100368042299)
          ·
            refine ⟨1997709714256650552063449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331806476171100368042299 1997709714256650552063449)
            ·
              refine ⟨1498282285692487914047587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997709714256650552063449 1498282285692487914047587)
              ·
                refine ⟨2247423428538731871071381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498282285692487914047587 2247423428538731871071381)
                ·
                  refine ⟨105347973212753056456471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2247423428538731871071381 105347973212753056456471)
                  ·
                    rfl

theorem cell20_230810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_230810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230810 prefixEnd_230810 := by exact prefixLift 230810
  have htrace : WordTrace (prefixWord ++ tailWord_230810) baseStart_230810 baseEnd_230810 := by
    simpa [prefixWord, tailWord_230810, baseEnd_230810] using wordTrace_append hprefix tailTrace_230810
  have hstable : (prefixWord ++ tailWord_230810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230810).length < 2 ^ (prefixWord ++ tailWord_230810).sum := by decide
  have hdescent : baseEnd_230810 < baseStart_230810 := by decide
  rcases family_descends (prefixWord ++ tailWord_230810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230896 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_230896 : Nat := 118140960795 + 230896 * 2 ^ 59
def prefixEnd_230896 : Nat := 4983230072969 + 3 ^ 40 * 230896 * 2
def baseEnd_230896 : Nat := 105387225956118979589453

theorem tailTrace_230896 : CollatzResearch.WordTrace tailWord_230896 prefixEnd_230896 105387225956118979589453 := by
  unfold tailWord_230896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210734485755350371208271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5614312647673800494944361 4210734485755350371208271)
  ·
    refine ⟨6316101728633025556812407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4210734485755350371208271 6316101728633025556812407)
    ·
      refine ⟨9474152592949538335218611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6316101728633025556812407 9474152592949538335218611)
      ·
        refine ⟨14211228889424307502827917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9474152592949538335218611 14211228889424307502827917)
        ·
          refine ⟨5329210833534115313560469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14211228889424307502827917 5329210833534115313560469)
          ·
            refine ⟨249806757821911655323147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5329210833534115313560469 249806757821911655323147)
            ·
              refine ⟨374710136732867482984721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249806757821911655323147 374710136732867482984721)
              ·
                refine ⟨281032602549650612238541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374710136732867482984721 281032602549650612238541)
                ·
                  refine ⟨105387225956118979589453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281032602549650612238541 105387225956118979589453)
                  ·
                    rfl

theorem cell20_230896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_230896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230896 prefixEnd_230896 := by exact prefixLift 230896
  have htrace : WordTrace (prefixWord ++ tailWord_230896) baseStart_230896 baseEnd_230896 := by
    simpa [prefixWord, tailWord_230896, baseEnd_230896] using wordTrace_append hprefix tailTrace_230896
  have hstable : (prefixWord ++ tailWord_230896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230896).length < 2 ^ (prefixWord ++ tailWord_230896).sum := by decide
  have hdescent : baseEnd_230896 < baseStart_230896 := by decide
  rcases family_descends (prefixWord ++ tailWord_230896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230907 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_230907 : Nat := 118140960795 + 230907 * 2 ^ 59
def prefixEnd_230907 : Nat := 4983230072969 + 3 ^ 40 * 230907 * 2
def baseEnd_230907 : Nat := 105392246655851830222741

theorem tailTrace_230907 : CollatzResearch.WordTrace tailWord_230907 prefixEnd_230907 105392246655851830222741 := by
  unfold tailWord_230907
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421870174470849621066975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5614580116313899747377983 8421870174470849621066975)
  ·
    refine ⟨12632805261706274431600463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421870174470849621066975 12632805261706274431600463)
    ·
      refine ⟨18949207892559411647400695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632805261706274431600463 18949207892559411647400695)
      ·
        refine ⟨28423811838839117471101043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18949207892559411647400695 28423811838839117471101043)
        ·
          refine ⟨42635717758258676206651565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28423811838839117471101043 42635717758258676206651565)
          ·
            refine ⟨15988394159347003577494337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42635717758258676206651565 15988394159347003577494337)
            ·
              refine ⟨11991295619510252683120753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15988394159347003577494337 11991295619510252683120753)
              ·
                refine ⟨8993471714632689512340565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11991295619510252683120753 8993471714632689512340565)
                ·
                  refine ⟨105392246655851830222741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8993471714632689512340565 105392246655851830222741)
                  ·
                    rfl

theorem cell20_230907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_230907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230907 prefixEnd_230907 := by exact prefixLift 230907
  have htrace : WordTrace (prefixWord ++ tailWord_230907) baseStart_230907 baseEnd_230907 := by
    simpa [prefixWord, tailWord_230907, baseEnd_230907] using wordTrace_append hprefix tailTrace_230907
  have hstable : (prefixWord ++ tailWord_230907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230907).length < 2 ^ (prefixWord ++ tailWord_230907).sum := by decide
  have hdescent : baseEnd_230907 < baseStart_230907 := by decide
  rcases family_descends (prefixWord ++ tailWord_230907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230913 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 3]
def baseStart_230913 : Nat := 118140960795 + 230913 * 2 ^ 59
def prefixEnd_230913 : Nat := 4983230072969 + 3 ^ 40 * 230913 * 2
def baseEnd_230913 : Nat := 105394985219342476022717

theorem tailTrace_230913 : CollatzResearch.WordTrace tailWord_230913 prefixEnd_230913 105394985219342476022717 := by
  unfold tailWord_230913
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422089012449112645785393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5614726008299408430523595 8422089012449112645785393)
  ·
    refine ⟨6316566759336834484339045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8422089012449112645785393 6316566759336834484339045)
    ·
      refine ⟨1184356267375656465813571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6316566759336834484339045 1184356267375656465813571)
      ·
        refine ⟨1776534401063484698720357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184356267375656465813571 1776534401063484698720357)
        ·
          refine ⟨333100200199403381010067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1776534401063484698720357 333100200199403381010067)
          ·
            refine ⟨499650300299105071515101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333100200199403381010067 499650300299105071515101)
            ·
              refine ⟨187368862612164401818163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499650300299105071515101 187368862612164401818163)
              ·
                refine ⟨281053293918246602727245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187368862612164401818163 281053293918246602727245)
                ·
                  refine ⟨105394985219342476022717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281053293918246602727245 105394985219342476022717)
                  ·
                    rfl

theorem cell20_230913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_230913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230913 prefixEnd_230913 := by exact prefixLift 230913
  have htrace : WordTrace (prefixWord ++ tailWord_230913) baseStart_230913 baseEnd_230913 := by
    simpa [prefixWord, tailWord_230913, baseEnd_230913] using wordTrace_append hprefix tailTrace_230913
  have hstable : (prefixWord ++ tailWord_230913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230913).length < 2 ^ (prefixWord ++ tailWord_230913).sum := by decide
  have hdescent : baseEnd_230913 < baseStart_230913 := by decide
  rcases family_descends (prefixWord ++ tailWord_230913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230931 : List Nat := [1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_230931 : Nat := 118140960795 + 230931 * 2 ^ 59
def prefixEnd_230931 : Nat := 4983230072969 + 3 ^ 40 * 230931 * 2
def baseEnd_230931 : Nat := 35134400303271471140881

theorem tailTrace_230931 : CollatzResearch.WordTrace tailWord_230931 prefixEnd_230931 35134400303271471140881 := by
  unfold tailWord_230931
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422745526383901719940647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5615163684255934479960431 8422745526383901719940647)
  ·
    refine ⟨12634118289575852579910971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8422745526383901719940647 12634118289575852579910971)
    ·
      refine ⟨18951177434363778869866457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12634118289575852579910971 18951177434363778869866457)
      ·
        refine ⟨14213383075772834152399843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18951177434363778869866457 14213383075772834152399843)
        ·
          refine ⟨21320074613659251228599765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14213383075772834152399843 21320074613659251228599765)
          ·
            refine ⟨499689248757638700670307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21320074613659251228599765 499689248757638700670307)
            ·
              refine ⟨749533873136458051005461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499689248757638700670307 749533873136458051005461)
              ·
                refine ⟨35134400303271471140881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 749533873136458051005461 35134400303271471140881)
                ·
                  rfl

theorem cell20_230931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_230931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230931 prefixEnd_230931 := by exact prefixLift 230931
  have htrace : WordTrace (prefixWord ++ tailWord_230931) baseStart_230931 baseEnd_230931 := by
    simpa [prefixWord, tailWord_230931, baseEnd_230931] using wordTrace_append hprefix tailTrace_230931
  have hstable : (prefixWord ++ tailWord_230931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230931).length < 2 ^ (prefixWord ++ tailWord_230931).sum := by decide
  have hdescent : baseEnd_230931 < baseStart_230931 := by decide
  rcases family_descends (prefixWord ++ tailWord_230931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230958 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_230958 : Nat := 118140960795 + 230958 * 2 ^ 59
def prefixEnd_230958 : Nat := 4983230072969 + 3 ^ 40 * 230958 * 2
def baseEnd_230958 : Nat := 105415524445522319522533

theorem tailTrace_230958 : CollatzResearch.WordTrace tailWord_230958 prefixEnd_230958 105415524445522319522533 := by
  unfold tailWord_230958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052966287160760666396691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5615820198190723554115685 1052966287160760666396691)
  ·
    refine ⟨1579449430741140999595037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1052966287160760666396691 1579449430741140999595037)
    ·
      refine ⟨592293536527927874848139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1579449430741140999595037 592293536527927874848139)
      ·
        refine ⟨888440304791891812272209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592293536527927874848139 888440304791891812272209)
        ·
          refine ⟨666330228593918859204157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888440304791891812272209 666330228593918859204157)
          ·
            refine ⟨249873835722719572201559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666330228593918859204157 249873835722719572201559)
            ·
              refine ⟨374810753584079358302339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249873835722719572201559 374810753584079358302339)
              ·
                refine ⟨562216130376119037453509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374810753584079358302339 562216130376119037453509)
                ·
                  refine ⟨105415524445522319522533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562216130376119037453509 105415524445522319522533)
                  ·
                    rfl

theorem cell20_230958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_230958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230958 prefixEnd_230958 := by exact prefixLift 230958
  have htrace : WordTrace (prefixWord ++ tailWord_230958) baseStart_230958 baseEnd_230958 := by
    simpa [prefixWord, tailWord_230958, baseEnd_230958] using wordTrace_append hprefix tailTrace_230958
  have hstable : (prefixWord ++ tailWord_230958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230958).length < 2 ^ (prefixWord ++ tailWord_230958).sum := by decide
  have hdescent : baseEnd_230958 < baseStart_230958 := by decide
  rcases family_descends (prefixWord ++ tailWord_230958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230969 : List Nat := [1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_230969 : Nat := 118140960795 + 230969 * 2 ^ 59
def prefixEnd_230969 : Nat := 4983230072969 + 3 ^ 40 * 230969 * 2
def baseEnd_230969 : Nat := 35140181715085056718607

theorem tailTrace_230969 : CollatzResearch.WordTrace tailWord_230969 prefixEnd_230969 35140181715085056718607 := by
  unfold tailWord_230969
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424131500246234209823961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5616087666830822806549307 8424131500246234209823961)
  ·
    refine ⟨6318098625184675657367971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8424131500246234209823961 6318098625184675657367971)
    ·
      refine ⟨9477147937777013486051957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318098625184675657367971 9477147937777013486051957)
      ·
        refine ⟨888482619166595014317371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9477147937777013486051957 888482619166595014317371)
        ·
          refine ⟨1332723928749892521476057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888482619166595014317371 1332723928749892521476057)
          ·
            refine ⟨999542946562419391107043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332723928749892521476057 999542946562419391107043)
            ·
              refine ⟨1499314419843629086660565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999542946562419391107043 1499314419843629086660565)
              ·
                refine ⟨35140181715085056718607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1499314419843629086660565 35140181715085056718607)
                ·
                  rfl

theorem cell20_230969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_230969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230969 prefixEnd_230969 := by exact prefixLift 230969
  have htrace : WordTrace (prefixWord ++ tailWord_230969) baseStart_230969 baseEnd_230969 := by
    simpa [prefixWord, tailWord_230969, baseEnd_230969] using wordTrace_append hprefix tailTrace_230969
  have hstable : (prefixWord ++ tailWord_230969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230969).length < 2 ^ (prefixWord ++ tailWord_230969).sum := by decide
  have hdescent : baseEnd_230969 < baseStart_230969 := by decide
  rcases family_descends (prefixWord ++ tailWord_230969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230972 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_230972 : Nat := 118140960795 + 230972 * 2 ^ 59
def prefixEnd_230972 : Nat := 4983230072969 + 3 ^ 40 * 230972 * 2
def baseEnd_230972 : Nat := 105421914427000493055809

theorem tailTrace_230972 : CollatzResearch.WordTrace tailWord_230972 prefixEnd_230972 105421914427000493055809 := by
  unfold tailWord_230972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212120459617682861091585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5616160612823577148122113 4212120459617682861091585)
  ·
    refine ⟨3159090344713262145818689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4212120459617682861091585 3159090344713262145818689)
    ·
      refine ⟨2369317758534946609364017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3159090344713262145818689 2369317758534946609364017)
      ·
        refine ⟨1776988318901209957023013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2369317758534946609364017 1776988318901209957023013)
        ·
          refine ⟨333185309793976866941815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1776988318901209957023013 333185309793976866941815)
          ·
            refine ⟨499777964690965300412723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333185309793976866941815 499777964690965300412723)
            ·
              refine ⟨749666947036447950619085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499777964690965300412723 749666947036447950619085)
              ·
                refine ⟨281125105138667981482157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 749666947036447950619085 281125105138667981482157)
                ·
                  refine ⟨105421914427000493055809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281125105138667981482157 105421914427000493055809)
                  ·
                    rfl

theorem cell20_230972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_230972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_230972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_230972 prefixEnd_230972 := by exact prefixLift 230972
  have htrace : WordTrace (prefixWord ++ tailWord_230972) baseStart_230972 baseEnd_230972 := by
    simpa [prefixWord, tailWord_230972, baseEnd_230972] using wordTrace_append hprefix tailTrace_230972
  have hstable : (prefixWord ++ tailWord_230972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230972).length < 2 ^ (prefixWord ++ tailWord_230972).sum := by decide
  have hdescent : baseEnd_230972 < baseStart_230972 := by decide
  rcases family_descends (prefixWord ++ tailWord_230972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231013 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 2]
def baseStart_231013 : Nat := 118140960795 + 231013 * 2 ^ 59
def prefixEnd_231013 : Nat := 4983230072969 + 3 ^ 40 * 231013 * 2
def baseEnd_231013 : Nat := 105440627944186572688975

theorem tailTrace_231013 : CollatzResearch.WordTrace tailWord_231013 prefixEnd_231013 105440627944186572688975 := by
  unfold tailWord_231013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425736312086829724425693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5617157541391219816283795 8425736312086829724425693)
  ·
    refine ⟨3159651117032561146659635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8425736312086829724425693 3159651117032561146659635)
    ·
      refine ⟨4739476675548841719989453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159651117032561146659635 4739476675548841719989453)
      ·
        refine ⟨1777303753330815644996045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4739476675548841719989453 1777303753330815644996045)
        ·
          refine ⟨666488907499055866873517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1777303753330815644996045 666488907499055866873517)
          ·
            refine ⟨249933340312145950077569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666488907499055866873517 249933340312145950077569)
            ·
              refine ⟨187450005234109462558177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249933340312145950077569 187450005234109462558177)
              ·
                refine ⟨140587503925582096918633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187450005234109462558177 140587503925582096918633)
                ·
                  refine ⟨105440627944186572688975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140587503925582096918633 105440627944186572688975)
                  ·
                    rfl

theorem cell20_231013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_231013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231013 prefixEnd_231013 := by exact prefixLift 231013
  have htrace : WordTrace (prefixWord ++ tailWord_231013) baseStart_231013 baseEnd_231013 := by
    simpa [prefixWord, tailWord_231013, baseEnd_231013] using wordTrace_append hprefix tailTrace_231013
  have hstable : (prefixWord ++ tailWord_231013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231013).length < 2 ^ (prefixWord ++ tailWord_231013).sum := by decide
  have hdescent : baseEnd_231013 < baseStart_231013 := by decide
  rcases family_descends (prefixWord ++ tailWord_231013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231024 : List Nat := [2, 1, 1, 1, 6, 3, 1, 5]
def baseStart_231024 : Nat := 118140960795 + 231024 * 2 ^ 59
def prefixEnd_231024 : Nat := 4983230072969 + 3 ^ 40 * 231024 * 2
def baseEnd_231024 : Nat := 35148549547973141107421

theorem tailTrace_231024 : CollatzResearch.WordTrace tailWord_231024 prefixEnd_231024 35148549547973141107421 := by
  unfold tailWord_231024
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213068757523489301538063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5617425010031319068717417 4213068757523489301538063)
  ·
    refine ⟨6319603136285233952307095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4213068757523489301538063 6319603136285233952307095)
    ·
      refine ⟨9479404704427850928460643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6319603136285233952307095 9479404704427850928460643)
      ·
        refine ⟨14219107056641776392690965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479404704427850928460643 14219107056641776392690965)
        ·
          refine ⟨666520643280083268407389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14219107056641776392690965 666520643280083268407389)
          ·
            refine ⟨249945241230031225652771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666520643280083268407389 249945241230031225652771)
            ·
              refine ⟨374917861845046838479157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249945241230031225652771 374917861845046838479157)
              ·
                refine ⟨35148549547973141107421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374917861845046838479157 35148549547973141107421)
                ·
                  rfl

theorem cell20_231024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_231024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231024 prefixEnd_231024 := by exact prefixLift 231024
  have htrace : WordTrace (prefixWord ++ tailWord_231024) baseStart_231024 baseEnd_231024 := by
    simpa [prefixWord, tailWord_231024, baseEnd_231024] using wordTrace_append hprefix tailTrace_231024
  have hstable : (prefixWord ++ tailWord_231024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231024).length < 2 ^ (prefixWord ++ tailWord_231024).sum := by decide
  have hdescent : baseEnd_231024 < baseStart_231024 := by decide
  rcases family_descends (prefixWord ++ tailWord_231024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231052 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_231052 : Nat := 118140960795 + 231052 * 2 ^ 59
def prefixEnd_231052 : Nat := 4983230072969 + 3 ^ 40 * 231052 * 2
def baseEnd_231052 : Nat := 105458428606875770388815

theorem tailTrace_231052 : CollatzResearch.WordTrace tailWord_231052 prefixEnd_231052 105458428606875770388815 := by
  unfold tailWord_231052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213579379472769692547705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5618105839297026256730273 4213579379472769692547705)
  ·
    refine ⟨3160184534604577269410779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4213579379472769692547705 3160184534604577269410779)
    ·
      refine ⟨4740276801906865904116169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3160184534604577269410779 4740276801906865904116169)
      ·
        refine ⟨3555207601430149428087127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4740276801906865904116169 3555207601430149428087127)
        ·
          refine ⟨5332811402145224142130691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555207601430149428087127 5332811402145224142130691)
          ·
            refine ⟨7999217103217836213196037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332811402145224142130691 7999217103217836213196037)
            ·
              refine ⟨1499853206853344289974257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7999217103217836213196037 1499853206853344289974257)
              ·
                refine ⟨1124889905140008217480693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499853206853344289974257 1124889905140008217480693)
                ·
                  refine ⟨105458428606875770388815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1124889905140008217480693 105458428606875770388815)
                  ·
                    rfl

theorem cell20_231052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_231052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231052 prefixEnd_231052 := by exact prefixLift 231052
  have htrace : WordTrace (prefixWord ++ tailWord_231052) baseStart_231052 baseEnd_231052 := by
    simpa [prefixWord, tailWord_231052, baseEnd_231052] using wordTrace_append hprefix tailTrace_231052
  have hstable : (prefixWord ++ tailWord_231052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231052).length < 2 ^ (prefixWord ++ tailWord_231052).sum := by decide
  have hdescent : baseEnd_231052 < baseStart_231052 := by decide
  rcases family_descends (prefixWord ++ tailWord_231052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231076 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_231076 : Nat := 118140960795 + 231076 * 2 ^ 59
def prefixEnd_231076 : Nat := 4983230072969 + 3 ^ 40 * 231076 * 2
def baseEnd_231076 : Nat := 105469382860838353588717

theorem tailTrace_231076 : CollatzResearch.WordTrace tailWord_231076 prefixEnd_231076 105469382860838353588717 := by
  unfold tailWord_231076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214017055429295741984541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5618689407239060989312721 4214017055429295741984541)
  ·
    refine ⟨1580256395785985903244203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4214017055429295741984541 1580256395785985903244203)
    ·
      refine ⟨2370384593678978854866305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580256395785985903244203 2370384593678978854866305)
      ·
        refine ⟨1777788445259234141149729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2370384593678978854866305 1777788445259234141149729)
        ·
          refine ⟨1333341333944425605862297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777788445259234141149729 1333341333944425605862297)
          ·
            refine ⟨1000006000458319204396723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333341333944425605862297 1000006000458319204396723)
            ·
              refine ⟨1500009000687478806595085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000006000458319204396723 1500009000687478806595085)
              ·
                refine ⟨562503375257804552473157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1500009000687478806595085 562503375257804552473157)
                ·
                  refine ⟨105469382860838353588717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562503375257804552473157 105469382860838353588717)
                  ·
                    rfl

theorem cell20_231076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_231076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231076 prefixEnd_231076 := by exact prefixLift 231076
  have htrace : WordTrace (prefixWord ++ tailWord_231076) baseStart_231076 baseEnd_231076 := by
    simpa [prefixWord, tailWord_231076, baseEnd_231076] using wordTrace_append hprefix tailTrace_231076
  have hstable : (prefixWord ++ tailWord_231076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231076).length < 2 ^ (prefixWord ++ tailWord_231076).sum := by decide
  have hdescent : baseEnd_231076 < baseStart_231076 := by decide
  rcases family_descends (prefixWord ++ tailWord_231076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231100 : List Nat := [2, 2, 2, 3, 1, 2, 4, 4]
def baseStart_231100 : Nat := 118140960795 + 231100 * 2 ^ 59
def prefixEnd_231100 : Nat := 4983230072969 + 3 ^ 40 * 231100 * 2
def baseEnd_231100 : Nat := 35160112371600312262873

theorem tailTrace_231100 : CollatzResearch.WordTrace tailWord_231100 prefixEnd_231100 35160112371600312262873 := by
  unfold tailWord_231100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214454731385821791421377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5619272975181095721895169 4214454731385821791421377)
  ·
    refine ⟨3160841048539366343566033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4214454731385821791421377 3160841048539366343566033)
    ·
      refine ⟨2370630786404524757674525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3160841048539366343566033 2370630786404524757674525)
      ·
        refine ⟨888986544901696784127947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2370630786404524757674525 888986544901696784127947)
        ·
          refine ⟨1333479817352545176191921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888986544901696784127947 1333479817352545176191921)
          ·
            refine ⟨1000109863014408882143941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333479817352545176191921 1000109863014408882143941)
            ·
              refine ⟨187520599315201665401989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1000109863014408882143941 187520599315201665401989)
              ·
                refine ⟨35160112371600312262873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187520599315201665401989 35160112371600312262873)
                ·
                  rfl

theorem cell20_231100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_231100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231100 prefixEnd_231100 := by exact prefixLift 231100
  have htrace : WordTrace (prefixWord ++ tailWord_231100) baseStart_231100 baseEnd_231100 := by
    simpa [prefixWord, tailWord_231100, baseEnd_231100] using wordTrace_append hprefix tailTrace_231100
  have hstable : (prefixWord ++ tailWord_231100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231100).length < 2 ^ (prefixWord ++ tailWord_231100).sum := by decide
  have hdescent : baseEnd_231100 < baseStart_231100 := by decide
  rcases family_descends (prefixWord ++ tailWord_231100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231117 : List Nat := [1, 6, 2, 1, 1, 3, 6]
def baseStart_231117 : Nat := 118140960795 + 231117 * 2 ^ 59
def prefixEnd_231117 : Nat := 4983230072969 + 3 ^ 40 * 231117 * 2
def baseEnd_231117 : Nat := 11720899597558270357987

theorem tailTrace_231117 : CollatzResearch.WordTrace tailWord_231117 prefixEnd_231117 11720899597558270357987 := by
  unfold tailWord_231117
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429529503710055486211605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5619686335806703657474403 8429529503710055486211605)
  ·
    refine ⟨395134195486408850916169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8429529503710055486211605 395134195486408850916169)
    ·
      refine ⟨296350646614806638187127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395134195486408850916169 296350646614806638187127)
      ·
        refine ⟨444525969922209957280691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296350646614806638187127 444525969922209957280691)
        ·
          refine ⟨666788954883314935921037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444525969922209957280691 666788954883314935921037)
          ·
            refine ⟨250045858081243100970389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666788954883314935921037 250045858081243100970389)
            ·
              refine ⟨11720899597558270357987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250045858081243100970389 11720899597558270357987)
              ·
                rfl

theorem cell20_231117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_231117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231117 prefixEnd_231117 := by exact prefixLift 231117
  have htrace : WordTrace (prefixWord ++ tailWord_231117) baseStart_231117 baseEnd_231117 := by
    simpa [prefixWord, tailWord_231117, baseEnd_231117] using wordTrace_append hprefix tailTrace_231117
  have hstable : (prefixWord ++ tailWord_231117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231117).length < 2 ^ (prefixWord ++ tailWord_231117).sum := by decide
  have hdescent : baseEnd_231117 < baseStart_231117 := by decide
  rcases family_descends (prefixWord ++ tailWord_231117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231121 : List Nat := [1, 2, 2, 1, 2, 6, 6]
def baseStart_231121 : Nat := 118140960795 + 231121 * 2 ^ 59
def prefixEnd_231121 : Nat := 4983230072969 + 3 ^ 40 * 231121 * 2
def baseEnd_231121 : Nat := 11721102454113133009837

theorem tailTrace_231121 : CollatzResearch.WordTrace tailWord_231121 prefixEnd_231121 11721102454113133009837 := by
  unfold tailWord_231121
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429675395695564169357217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5619783597130376112904811 8429675395695564169357217)
  ·
    refine ⟨6322256546771673127017913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8429675395695564169357217 6322256546771673127017913)
    ·
      refine ⟨4741692410078754845263435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6322256546771673127017913 4741692410078754845263435)
      ·
        refine ⟨7112538615118132267895153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741692410078754845263435 7112538615118132267895153)
        ·
          refine ⟨5334403961338599200921365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112538615118132267895153 5334403961338599200921365)
          ·
            refine ⟨250050185687746837543189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5334403961338599200921365 250050185687746837543189)
            ·
              refine ⟨11721102454113133009837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250050185687746837543189 11721102454113133009837)
              ·
                rfl

theorem cell20_231121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_231121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231121 prefixEnd_231121 := by exact prefixLift 231121
  have htrace : WordTrace (prefixWord ++ tailWord_231121) baseStart_231121 baseEnd_231121 := by
    simpa [prefixWord, tailWord_231121, baseEnd_231121] using wordTrace_append hprefix tailTrace_231121
  have hstable : (prefixWord ++ tailWord_231121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231121).length < 2 ^ (prefixWord ++ tailWord_231121).sum := by decide
  have hdescent : baseEnd_231121 < baseStart_231121 := by decide
  rcases family_descends (prefixWord ++ tailWord_231121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231128 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_231128 : Nat := 118140960795 + 231128 * 2 ^ 59
def prefixEnd_231128 : Nat := 4983230072969 + 3 ^ 40 * 231128 * 2
def baseEnd_231128 : Nat := 105493117077757283855171

theorem tailTrace_231128 : CollatzResearch.WordTrace tailWord_231128 prefixEnd_231128 105493117077757283855171 := by
  unfold tailWord_231128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214965353335102182431019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5619953804446802909908025 4214965353335102182431019)
  ·
    refine ⟨6322448030002653273646529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4214965353335102182431019 6322448030002653273646529)
    ·
      refine ⟨4741836022501989955234897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6322448030002653273646529 4741836022501989955234897)
      ·
        refine ⟨3556377016876492466426173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4741836022501989955234897 3556377016876492466426173)
        ·
          refine ⟨1333641381328684674909815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3556377016876492466426173 1333641381328684674909815)
          ·
            refine ⟨2000462071993027012364723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333641381328684674909815 2000462071993027012364723)
            ·
              refine ⟨3000693107989540518547085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000462071993027012364723 3000693107989540518547085)
              ·
                refine ⟨1125259915496077694455157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3000693107989540518547085 1125259915496077694455157)
                ·
                  refine ⟨105493117077757283855171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125259915496077694455157 105493117077757283855171)
                  ·
                    rfl

theorem cell20_231128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_231128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231128 prefixEnd_231128 := by exact prefixLift 231128
  have htrace : WordTrace (prefixWord ++ tailWord_231128) baseStart_231128 baseEnd_231128 := by
    simpa [prefixWord, tailWord_231128, baseEnd_231128] using wordTrace_append hprefix tailTrace_231128
  have hstable : (prefixWord ++ tailWord_231128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231128).length < 2 ^ (prefixWord ++ tailWord_231128).sum := by decide
  have hdescent : baseEnd_231128 < baseStart_231128 := by decide
  rcases family_descends (prefixWord ++ tailWord_231128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231174 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_231174 : Nat := 118140960795 + 231174 * 2 ^ 59
def prefixEnd_231174 : Nat := 4983230072969 + 3 ^ 40 * 231174 * 2
def baseEnd_231174 : Nat := 105514112731185568321651

theorem tailTrace_231174 : CollatzResearch.WordTrace tailWord_231174 prefixEnd_231174 105514112731185568321651 := by
  unfold tailWord_231174
  simp only [CollatzResearch.WordTrace]
  refine ⟨263487764515736069407393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5621072309669036147357717 263487764515736069407393)
  ·
    refine ⟨197615823386802052055545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263487764515736069407393 197615823386802052055545)
    ·
      refine ⟨148211867540101539041659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197615823386802052055545 148211867540101539041659)
      ·
        refine ⟨222317801310152308562489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148211867540101539041659 222317801310152308562489)
        ·
          refine ⟨166738350982614231421867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222317801310152308562489 166738350982614231421867)
          ·
            refine ⟨250107526473921347132801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166738350982614231421867 250107526473921347132801)
            ·
              refine ⟨187580644855441010349601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250107526473921347132801 187580644855441010349601)
              ·
                refine ⟨140685483641580757762201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187580644855441010349601 140685483641580757762201)
                ·
                  refine ⟨105514112731185568321651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140685483641580757762201 105514112731185568321651)
                  ·
                    rfl

theorem cell20_231174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_231174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231174 prefixEnd_231174 := by exact prefixLift 231174
  have htrace : WordTrace (prefixWord ++ tailWord_231174) baseStart_231174 baseEnd_231174 := by
    simpa [prefixWord, tailWord_231174, baseEnd_231174] using wordTrace_append hprefix tailTrace_231174
  have hstable : (prefixWord ++ tailWord_231174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231174).length < 2 ^ (prefixWord ++ tailWord_231174).sum := by decide
  have hdescent : baseEnd_231174 < baseStart_231174 := by decide
  rcases family_descends (prefixWord ++ tailWord_231174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231242 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_231242 : Nat := 118140960795 + 231242 * 2 ^ 59
def prefixEnd_231242 : Nat := 4983230072969 + 3 ^ 40 * 231242 * 2
def baseEnd_231242 : Nat := 105545149784079554054705

theorem tailTrace_231242 : CollatzResearch.WordTrace tailWord_231242 prefixEnd_231242 105545149784079554054705 := by
  unfold tailWord_231242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108522157064300458627995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5622725752171467889674653 2108522157064300458627995)
  ·
    refine ⟨3162783235596450687941993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2108522157064300458627995 3162783235596450687941993)
    ·
      refine ⟨2372087426697338015956495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3162783235596450687941993 2372087426697338015956495)
      ·
        refine ⟨3558131140046007023934743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372087426697338015956495 3558131140046007023934743)
        ·
          refine ⟨5337196710069010535902115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558131140046007023934743 5337196710069010535902115)
          ·
            refine ⟨8005795065103515803853173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337196710069010535902115 8005795065103515803853173)
            ·
              refine ⟨750543287353454606611235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8005795065103515803853173 750543287353454606611235)
              ·
                refine ⟨1125814931030181909916853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750543287353454606611235 1125814931030181909916853)
                ·
                  refine ⟨105545149784079554054705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125814931030181909916853 105545149784079554054705)
                  ·
                    rfl

theorem cell20_231242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_231242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231242 prefixEnd_231242 := by exact prefixLift 231242
  have htrace : WordTrace (prefixWord ++ tailWord_231242) baseStart_231242 baseEnd_231242 := by
    simpa [prefixWord, tailWord_231242, baseEnd_231242] using wordTrace_append hprefix tailTrace_231242
  have hstable : (prefixWord ++ tailWord_231242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231242).length < 2 ^ (prefixWord ++ tailWord_231242).sum := by decide
  have hdescent : baseEnd_231242 < baseStart_231242 := by decide
  rcases family_descends (prefixWord ++ tailWord_231242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231245 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_231245 : Nat := 118140960795 + 231245 * 2 ^ 59
def prefixEnd_231245 : Nat := 4983230072969 + 3 ^ 40 * 231245 * 2
def baseEnd_231245 : Nat := 105546519065824876954693

theorem tailTrace_231245 : CollatzResearch.WordTrace tailWord_231245 prefixEnd_231245 105546519065824876954693 := by
  unfold tailWord_231245
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434198047246333346871189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5622798698164222231247459 8434198047246333346871189)
  ·
    refine ⟨395353033464671875634587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8434198047246333346871189 395353033464671875634587)
    ·
      refine ⟨593029550197007813451881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395353033464671875634587 593029550197007813451881)
      ·
        refine ⟨444772162647755860088911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593029550197007813451881 444772162647755860088911)
        ·
          refine ⟨667158243971633790133367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444772162647755860088911 667158243971633790133367)
          ·
            refine ⟨1000737365957450685200051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667158243971633790133367 1000737365957450685200051)
            ·
              refine ⟨1501106048936176027800077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000737365957450685200051 1501106048936176027800077)
              ·
                refine ⟨562914768351066010425029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1501106048936176027800077 562914768351066010425029)
                ·
                  refine ⟨105546519065824876954693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562914768351066010425029 105546519065824876954693)
                  ·
                    rfl

theorem cell20_231245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_231245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231245 prefixEnd_231245 := by exact prefixLift 231245
  have htrace : WordTrace (prefixWord ++ tailWord_231245) baseStart_231245 baseEnd_231245 := by
    simpa [prefixWord, tailWord_231245, baseEnd_231245] using wordTrace_append hprefix tailTrace_231245
  have hstable : (prefixWord ++ tailWord_231245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231245).length < 2 ^ (prefixWord ++ tailWord_231245).sum := by decide
  have hdescent : baseEnd_231245 < baseStart_231245 := by decide
  rcases family_descends (prefixWord ++ tailWord_231245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231310 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_231310 : Nat := 118140960795 + 231310 * 2 ^ 59
def prefixEnd_231310 : Nat := 4983230072969 + 3 ^ 40 * 231310 * 2
def baseEnd_231310 : Nat := 105576186836973539787761

theorem tailTrace_231310 : CollatzResearch.WordTrace tailWord_231310 prefixEnd_231310 105576186836973539787761 := by
  unfold tailWord_231310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054571099001356180998423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5624379194673899631991589 1054571099001356180998423)
  ·
    refine ⟨1581856648502034271497635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054571099001356180998423 1581856648502034271497635)
    ·
      refine ⟨2372784972753051407246453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581856648502034271497635 2372784972753051407246453)
      ·
        refine ⟨222448591195598569429355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2372784972753051407246453 222448591195598569429355)
        ·
          refine ⟨333672886793397854144033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222448591195598569429355 333672886793397854144033)
          ·
            refine ⟨250254665095048390608025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333672886793397854144033 250254665095048390608025)
            ·
              refine ⟨187690998821286292956019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250254665095048390608025 187690998821286292956019)
              ·
                refine ⟨281536498231929439434029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187690998821286292956019 281536498231929439434029)
                ·
                  refine ⟨105576186836973539787761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281536498231929439434029 105576186836973539787761)
                  ·
                    rfl

theorem cell20_231310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_231310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231310 prefixEnd_231310 := by exact prefixLift 231310
  have htrace : WordTrace (prefixWord ++ tailWord_231310) baseStart_231310 baseEnd_231310 := by
    simpa [prefixWord, tailWord_231310, baseEnd_231310] using wordTrace_append hprefix tailTrace_231310
  have hstable : (prefixWord ++ tailWord_231310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231310).length < 2 ^ (prefixWord ++ tailWord_231310).sum := by decide
  have hdescent : baseEnd_231310 < baseStart_231310 := by decide
  rcases family_descends (prefixWord ++ tailWord_231310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231314 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_231314 : Nat := 118140960795 + 231314 * 2 ^ 59
def prefixEnd_231314 : Nat := 4983230072969 + 3 ^ 40 * 231314 * 2
def baseEnd_231314 : Nat := 105578012545967303654411

theorem tailTrace_231314 : CollatzResearch.WordTrace tailWord_231314 prefixEnd_231314 105578012545967303654411 := by
  unfold tailWord_231314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109178670999089532783249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5624476455997572087421997 2109178670999089532783249)
  ·
    refine ⟨1581884003249317149587437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2109178670999089532783249 1581884003249317149587437)
    ·
      refine ⟨593206501218493931095289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1581884003249317149587437 593206501218493931095289)
      ·
        refine ⟨444904875913870448321467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593206501218493931095289 444904875913870448321467)
        ·
          refine ⟨667357313870805672482201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444904875913870448321467 667357313870805672482201)
          ·
            refine ⟨500517985403104254361651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667357313870805672482201 500517985403104254361651)
            ·
              refine ⟨750776978104656381542477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500517985403104254361651 750776978104656381542477)
              ·
                refine ⟨281541366789246143078429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750776978104656381542477 281541366789246143078429)
                ·
                  refine ⟨105578012545967303654411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281541366789246143078429 105578012545967303654411)
                  ·
                    rfl

theorem cell20_231314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_231314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231314 prefixEnd_231314 := by exact prefixLift 231314
  have htrace : WordTrace (prefixWord ++ tailWord_231314) baseStart_231314 baseEnd_231314 := by
    simpa [prefixWord, tailWord_231314, baseEnd_231314] using wordTrace_append hprefix tailTrace_231314
  have hstable : (prefixWord ++ tailWord_231314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231314).length < 2 ^ (prefixWord ++ tailWord_231314).sum := by decide
  have hdescent : baseEnd_231314 < baseStart_231314 := by decide
  rcases family_descends (prefixWord ++ tailWord_231314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231380 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_231380 : Nat := 118140960795 + 231380 * 2 ^ 59
def prefixEnd_231380 : Nat := 4983230072969 + 3 ^ 40 * 231380 * 2
def baseEnd_231380 : Nat := 105608136744364407454141

theorem tailTrace_231380 : CollatzResearch.WordTrace tailWord_231380 prefixEnd_231380 105608136744364407454141 := by
  unfold tailWord_231380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219560950878625701517797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5626081267838167602023729 4219560950878625701517797)
  ·
    refine ⟨791167678289742319034587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4219560950878625701517797 791167678289742319034587)
    ·
      refine ⟨1186751517434613478551881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791167678289742319034587 1186751517434613478551881)
      ·
        refine ⟨890063638075960108913911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1186751517434613478551881 890063638075960108913911)
        ·
          refine ⟨1335095457113940163370867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890063638075960108913911 1335095457113940163370867)
          ·
            refine ⟨2002643185670910245056301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335095457113940163370867 2002643185670910245056301)
            ·
              refine ⟨750991194626591341896113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2002643185670910245056301 750991194626591341896113)
              ·
                refine ⟨563243395969943506422085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750991194626591341896113 563243395969943506422085)
                ·
                  refine ⟨105608136744364407454141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563243395969943506422085 105608136744364407454141)
                  ·
                    rfl

theorem cell20_231380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_231380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231380 prefixEnd_231380 := by exact prefixLift 231380
  have htrace : WordTrace (prefixWord ++ tailWord_231380) baseStart_231380 baseEnd_231380 := by
    simpa [prefixWord, tailWord_231380, baseEnd_231380] using wordTrace_append hprefix tailTrace_231380
  have hstable : (prefixWord ++ tailWord_231380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231380).length < 2 ^ (prefixWord ++ tailWord_231380).sum := by decide
  have hdescent : baseEnd_231380 < baseStart_231380 := by decide
  rcases family_descends (prefixWord ++ tailWord_231380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231452 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 2]
def baseStart_231452 : Nat := 118140960795 + 231452 * 2 ^ 59
def prefixEnd_231452 : Nat := 4983230072969 + 3 ^ 40 * 231452 * 2
def baseEnd_231452 : Nat := 105640999506252157053847

theorem tailTrace_231452 : CollatzResearch.WordTrace tailWord_231452 prefixEnd_231452 105640999506252157053847 := by
  unfold tailWord_231452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220873978748203849828305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5627831971664271799771073 4220873978748203849828305)
  ·
    refine ⟨3165655484061152887371229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4220873978748203849828305 3165655484061152887371229)
    ·
      refine ⟨1187120806522932332764211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3165655484061152887371229 1187120806522932332764211)
      ·
        refine ⟨1780681209784398499146317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187120806522932332764211 1780681209784398499146317)
        ·
          refine ⟨667755453669149437179869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1780681209784398499146317 667755453669149437179869)
          ·
            refine ⟨250408295125931038942451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667755453669149437179869 250408295125931038942451)
            ·
              refine ⟨375612442688896558413677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250408295125931038942451 375612442688896558413677)
              ·
                refine ⟨140854666008336209405129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375612442688896558413677 140854666008336209405129)
                ·
                  refine ⟨105640999506252157053847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140854666008336209405129 105640999506252157053847)
                  ·
                    rfl

theorem cell20_231452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_231452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231452 prefixEnd_231452 := by exact prefixLift 231452
  have htrace : WordTrace (prefixWord ++ tailWord_231452) baseStart_231452 baseEnd_231452 := by
    simpa [prefixWord, tailWord_231452, baseEnd_231452] using wordTrace_append hprefix tailTrace_231452
  have hstable : (prefixWord ++ tailWord_231452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231452).length < 2 ^ (prefixWord ++ tailWord_231452).sum := by decide
  have hdescent : baseEnd_231452 < baseStart_231452 := by decide
  rcases family_descends (prefixWord ++ tailWord_231452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231487 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 3]
def baseStart_231487 : Nat := 118140960795 + 231487 * 2 ^ 59
def prefixEnd_231487 : Nat := 4983230072969 + 3 ^ 40 * 231487 * 2
def baseEnd_231487 : Nat := 105656974459947590887037

theorem tailTrace_231487 : CollatzResearch.WordTrace tailWord_231487 prefixEnd_231487 105656974459947590887037 := by
  unfold tailWord_231487
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443024512369608677180715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5628683008246405784787143 8443024512369608677180715)
  ·
    refine ⟨12664536768554413015771073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443024512369608677180715 12664536768554413015771073)
    ·
      refine ⟨9498402576415809761828305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12664536768554413015771073 9498402576415809761828305)
      ·
        refine ⟨7123801932311857321371229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9498402576415809761828305 7123801932311857321371229)
        ·
          refine ⟨2671425724616946495514211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7123801932311857321371229 2671425724616946495514211)
          ·
            refine ⟨4007138586925419743271317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671425724616946495514211 4007138586925419743271317)
            ·
              refine ⟨187834621262129050465843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4007138586925419743271317 187834621262129050465843)
              ·
                refine ⟨281751931893193575698765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187834621262129050465843 281751931893193575698765)
                ·
                  refine ⟨105656974459947590887037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281751931893193575698765 105656974459947590887037)
                  ·
                    rfl

theorem cell20_231487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_231487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231487 prefixEnd_231487 := by exact prefixLift 231487
  have htrace : WordTrace (prefixWord ++ tailWord_231487) baseStart_231487 baseEnd_231487 := by
    simpa [prefixWord, tailWord_231487, baseEnd_231487] using wordTrace_append hprefix tailTrace_231487
  have hstable : (prefixWord ++ tailWord_231487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231487).length < 2 ^ (prefixWord ++ tailWord_231487).sum := by decide
  have hdescent : baseEnd_231487 < baseStart_231487 := by decide
  rcases family_descends (prefixWord ++ tailWord_231487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231491 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_231491 : Nat := 118140960795 + 231491 * 2 ^ 59
def prefixEnd_231491 : Nat := 4983230072969 + 3 ^ 40 * 231491 * 2
def baseEnd_231491 : Nat := 105658800168941354753687

theorem tailTrace_231491 : CollatzResearch.WordTrace tailWord_231491 prefixEnd_231491 105658800168941354753687 := by
  unfold tailWord_231491
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443170404355117360326327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5628780269570078240217551 8443170404355117360326327)
  ·
    refine ⟨12664755606532676040489491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443170404355117360326327 12664755606532676040489491)
    ·
      refine ⟨18997133409799014060734237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12664755606532676040489491 18997133409799014060734237)
      ·
        refine ⟨7123925028674630272775339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18997133409799014060734237 7123925028674630272775339)
        ·
          refine ⟨10685887543011945409163009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123925028674630272775339 10685887543011945409163009)
          ·
            refine ⟨8014415657258959056872257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10685887543011945409163009 8014415657258959056872257)
            ·
              refine ⟨6010811742944219292654193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014415657258959056872257 6010811742944219292654193)
              ·
                refine ⟨4508108807208164469490645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010811742944219292654193 4508108807208164469490645)
                ·
                  refine ⟨105658800168941354753687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4508108807208164469490645 105658800168941354753687)
                  ·
                    rfl

theorem cell20_231491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_231491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231491 prefixEnd_231491 := by exact prefixLift 231491
  have htrace : WordTrace (prefixWord ++ tailWord_231491) baseStart_231491 baseEnd_231491 := by
    simpa [prefixWord, tailWord_231491, baseEnd_231491] using wordTrace_append hprefix tailTrace_231491
  have hstable : (prefixWord ++ tailWord_231491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231491).length < 2 ^ (prefixWord ++ tailWord_231491).sum := by decide
  have hdescent : baseEnd_231491 < baseStart_231491 := by decide
  rcases family_descends (prefixWord ++ tailWord_231491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231501 : List Nat := [1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_231501 : Nat := 118140960795 + 231501 * 2 ^ 59
def prefixEnd_231501 : Nat := 4983230072969 + 3 ^ 40 * 231501 * 2
def baseEnd_231501 : Nat := 35221121480475254806771

theorem tailTrace_231501 : CollatzResearch.WordTrace tailWord_231501 prefixEnd_231501 35221121480475254806771 := by
  unfold tailWord_231501
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443535134318889068190357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5629023422879259378793571 8443535134318889068190357)
  ·
    refine ⟨395790709421197925071423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8443535134318889068190357 395790709421197925071423)
    ·
      refine ⟨593686064131796887607135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395790709421197925071423 593686064131796887607135)
      ·
        refine ⟨890529096197695331410703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593686064131796887607135 890529096197695331410703)
        ·
          refine ⟨1335793644296542997116055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890529096197695331410703 1335793644296542997116055)
          ·
            refine ⟨2003690466444814495674083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335793644296542997116055 2003690466444814495674083)
            ·
              refine ⟨3005535699667221743511125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003690466444814495674083 3005535699667221743511125)
              ·
                refine ⟨35221121480475254806771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3005535699667221743511125 35221121480475254806771)
                ·
                  rfl

theorem cell20_231501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_231501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231501 prefixEnd_231501 := by exact prefixLift 231501
  have htrace : WordTrace (prefixWord ++ tailWord_231501) baseStart_231501 baseEnd_231501 := by
    simpa [prefixWord, tailWord_231501, baseEnd_231501] using wordTrace_append hprefix tailTrace_231501
  have hstable : (prefixWord ++ tailWord_231501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231501).length < 2 ^ (prefixWord ++ tailWord_231501).sum := by decide
  have hdescent : baseEnd_231501 < baseStart_231501 := by decide
  rcases family_descends (prefixWord ++ tailWord_231501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231518 : List Nat := [4, 4, 1, 1, 10]
def baseStart_231518 : Nat := 118140960795 + 231518 * 2 ^ 59
def prefixEnd_231518 : Nat := 4983230072969 + 3 ^ 40 * 231518 * 2
def baseEnd_231518 : Nat := 1304581774131472356217

theorem tailTrace_231518 : CollatzResearch.WordTrace tailWord_231518 prefixEnd_231518 1304581774131472356217 := by
  unfold tailWord_231518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055519396907162621444901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5629436783504867314372805 1055519396907162621444901)
  ·
    refine ⟨197909886920092991520919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1055519396907162621444901 197909886920092991520919)
    ·
      refine ⟨296864830380139487281379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197909886920092991520919 296864830380139487281379)
      ·
        refine ⟨445297245570209230922069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296864830380139487281379 445297245570209230922069)
        ·
          refine ⟨1304581774131472356217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 445297245570209230922069 1304581774131472356217)
          ·
            rfl

theorem cell20_231518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 10].length) (baseStart_231518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231518 prefixEnd_231518 := by exact prefixLift 231518
  have htrace : WordTrace (prefixWord ++ tailWord_231518) baseStart_231518 baseEnd_231518 := by
    simpa [prefixWord, tailWord_231518, baseEnd_231518] using wordTrace_append hprefix tailTrace_231518
  have hstable : (prefixWord ++ tailWord_231518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231518).length < 2 ^ (prefixWord ++ tailWord_231518).sum := by decide
  have hdescent : baseEnd_231518 < baseStart_231518 := by decide
  rcases family_descends (prefixWord ++ tailWord_231518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231525 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_231525 : Nat := 118140960795 + 231525 * 2 ^ 59
def prefixEnd_231525 : Nat := 4983230072969 + 3 ^ 40 * 231525 * 2
def baseEnd_231525 : Nat := 105674318695388347620215

theorem tailTrace_231525 : CollatzResearch.WordTrace tailWord_231525 prefixEnd_231525 105674318695388347620215 := by
  unfold tailWord_231525
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444410486231941167064029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5629606990821294111376019 8444410486231941167064029)
  ·
    refine ⟨3166653932336977937649011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8444410486231941167064029 3166653932336977937649011)
    ·
      refine ⟨4749980898505466906473517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166653932336977937649011 4749980898505466906473517)
      ·
        refine ⟨1781242836939550089927569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4749980898505466906473517 1781242836939550089927569)
        ·
          refine ⟨1335932127704662567445677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781242836939550089927569 1335932127704662567445677)
          ·
            refine ⟨500974547889248462792129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1335932127704662567445677 500974547889248462792129)
            ·
              refine ⟨375730910916936347094097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500974547889248462792129 375730910916936347094097)
              ·
                refine ⟨281798183187702260320573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375730910916936347094097 281798183187702260320573)
                ·
                  refine ⟨105674318695388347620215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281798183187702260320573 105674318695388347620215)
                  ·
                    rfl

theorem cell20_231525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_231525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231525 prefixEnd_231525 := by exact prefixLift 231525
  have htrace : WordTrace (prefixWord ++ tailWord_231525) baseStart_231525 baseEnd_231525 := by
    simpa [prefixWord, tailWord_231525, baseEnd_231525] using wordTrace_append hprefix tailTrace_231525
  have hstable : (prefixWord ++ tailWord_231525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231525).length < 2 ^ (prefixWord ++ tailWord_231525).sum := by decide
  have hdescent : baseEnd_231525 < baseStart_231525 := by decide
  rcases family_descends (prefixWord ++ tailWord_231525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231566 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_231566 : Nat := 118140960795 + 231566 * 2 ^ 59
def prefixEnd_231566 : Nat := 4983230072969 + 3 ^ 40 * 231566 * 2
def baseEnd_231566 : Nat := 105693032212574427253381

theorem tailTrace_231566 : CollatzResearch.WordTrace tailWord_231566 prefixEnd_231566 105693032212574427253381 := by
  unfold tailWord_231566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055738234885425646163319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5630603919388936779537701 1055738234885425646163319)
  ·
    refine ⟨1583607352328138469244979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055738234885425646163319 1583607352328138469244979)
    ·
      refine ⟨2375411028492207703867469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583607352328138469244979 2375411028492207703867469)
      ·
        refine ⟨890779135684577888950301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2375411028492207703867469 890779135684577888950301)
        ·
          refine ⟨334042175881716708356363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890779135684577888950301 334042175881716708356363)
          ·
            refine ⟨501063263822575062534545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334042175881716708356363 501063263822575062534545)
            ·
              refine ⟨375797447866931296900909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501063263822575062534545 375797447866931296900909)
              ·
                refine ⟨140924042950099236337841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375797447866931296900909 140924042950099236337841)
                ·
                  refine ⟨105693032212574427253381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140924042950099236337841 105693032212574427253381)
                  ·
                    rfl

theorem cell20_231566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_231566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231566 prefixEnd_231566 := by exact prefixLift 231566
  have htrace : WordTrace (prefixWord ++ tailWord_231566) baseStart_231566 baseEnd_231566 := by
    simpa [prefixWord, tailWord_231566, baseEnd_231566] using wordTrace_append hprefix tailTrace_231566
  have hstable : (prefixWord ++ tailWord_231566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231566).length < 2 ^ (prefixWord ++ tailWord_231566).sum := by decide
  have hdescent : baseEnd_231566 < baseStart_231566 := by decide
  rcases family_descends (prefixWord ++ tailWord_231566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231584 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_231584 : Nat := 118140960795 + 231584 * 2 ^ 59
def prefixEnd_231584 : Nat := 4983230072969 + 3 ^ 40 * 231584 * 2
def baseEnd_231584 : Nat := 105701247903046364653307

theorem tailTrace_231584 : CollatzResearch.WordTrace tailWord_231584 prefixEnd_231584 105701247903046364653307 := by
  unfold tailWord_231584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223281196509097121730903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5631041595345462828974537 4223281196509097121730903)
  ·
    refine ⟨6334921794763645682596355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223281196509097121730903 6334921794763645682596355)
    ·
      refine ⟨9502382692145468523894533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6334921794763645682596355 9502382692145468523894533)
      ·
        refine ⟨1781696754777275348230225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9502382692145468523894533 1781696754777275348230225)
        ·
          refine ⟨1336272566082956511172669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781696754777275348230225 1336272566082956511172669)
          ·
            refine ⟨501102212281108691689751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1336272566082956511172669 501102212281108691689751)
            ·
              refine ⟨751653318421663037534627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501102212281108691689751 751653318421663037534627)
              ·
                refine ⟨1127479977632494556301941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751653318421663037534627 1127479977632494556301941)
                ·
                  refine ⟨105701247903046364653307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127479977632494556301941 105701247903046364653307)
                  ·
                    rfl

theorem cell20_231584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_231584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231584 prefixEnd_231584 := by exact prefixLift 231584
  have htrace : WordTrace (prefixWord ++ tailWord_231584) baseStart_231584 baseEnd_231584 := by
    simpa [prefixWord, tailWord_231584, baseEnd_231584] using wordTrace_append hprefix tailTrace_231584
  have hstable : (prefixWord ++ tailWord_231584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231584).length < 2 ^ (prefixWord ++ tailWord_231584).sum := by decide
  have hdescent : baseEnd_231584 < baseStart_231584 := by decide
  rcases family_descends (prefixWord ++ tailWord_231584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231618 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_231618 : Nat := 118140960795 + 231618 * 2 ^ 59
def prefixEnd_231618 : Nat := 4983230072969 + 3 ^ 40 * 231618 * 2
def baseEnd_231618 : Nat := 105716766429493357519835

theorem tailTrace_231618 : CollatzResearch.WordTrace tailWord_231618 prefixEnd_231618 105716766429493357519835 := by
  unfold tailWord_231618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111950618723754512549877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5631868316596678700133005 2111950618723754512549877)
  ·
    refine ⟨197995370505351985551551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2111950618723754512549877 197995370505351985551551)
    ·
      refine ⟨296993055758027978327327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197995370505351985551551 296993055758027978327327)
      ·
        refine ⟨445489583637041967490991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296993055758027978327327 445489583637041967490991)
        ·
          refine ⟨668234375455562951236487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445489583637041967490991 668234375455562951236487)
          ·
            refine ⟨1002351563183344426854731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668234375455562951236487 1002351563183344426854731)
            ·
              refine ⟨1503527344775016640282097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002351563183344426854731 1503527344775016640282097)
              ·
                refine ⟨1127645508581262480211573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1503527344775016640282097 1127645508581262480211573)
                ·
                  refine ⟨105716766429493357519835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127645508581262480211573 105716766429493357519835)
                  ·
                    rfl

theorem cell20_231618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_231618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231618 prefixEnd_231618 := by exact prefixLift 231618
  have htrace : WordTrace (prefixWord ++ tailWord_231618) baseStart_231618 baseEnd_231618 := by
    simpa [prefixWord, tailWord_231618, baseEnd_231618] using wordTrace_append hprefix tailTrace_231618
  have hstable : (prefixWord ++ tailWord_231618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231618).length < 2 ^ (prefixWord ++ tailWord_231618).sum := by decide
  have hdescent : baseEnd_231618 < baseStart_231618 := by decide
  rcases family_descends (prefixWord ++ tailWord_231618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231653 : List Nat := [1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_231653 : Nat := 118140960795 + 231653 * 2 ^ 59
def prefixEnd_231653 : Nat := 4983230072969 + 3 ^ 40 * 231653 * 2
def baseEnd_231653 : Nat := 35244247127729597117675

theorem tailTrace_231653 : CollatzResearch.WordTrace tailWord_231653 prefixEnd_231653 35244247127729597117675 := by
  unfold tailWord_231653
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449079029768219027723613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5632719353178812685149075 8449079029768219027723613)
  ·
    refine ⟨3168404636163082135396355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8449079029768219027723613 3168404636163082135396355)
    ·
      refine ⟨4752606954244623203094533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3168404636163082135396355 4752606954244623203094533)
      ·
        refine ⟨891113803920866850580225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4752606954244623203094533 891113803920866850580225)
        ·
          refine ⟨668335352940650137935169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891113803920866850580225 668335352940650137935169)
          ·
            refine ⟨501251514705487603451377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668335352940650137935169 501251514705487603451377)
            ·
              refine ⟨375938636029115702588533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501251514705487603451377 375938636029115702588533)
              ·
                refine ⟨35244247127729597117675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375938636029115702588533 35244247127729597117675)
                ·
                  rfl

theorem cell20_231653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_231653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231653 prefixEnd_231653 := by exact prefixLift 231653
  have htrace : WordTrace (prefixWord ++ tailWord_231653) baseStart_231653 baseEnd_231653 := by
    simpa [prefixWord, tailWord_231653, baseEnd_231653] using wordTrace_append hprefix tailTrace_231653
  have hstable : (prefixWord ++ tailWord_231653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231653).length < 2 ^ (prefixWord ++ tailWord_231653).sum := by decide
  have hdescent : baseEnd_231653 < baseStart_231653 := by decide
  rcases family_descends (prefixWord ++ tailWord_231653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231656 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_231656 : Nat := 118140960795 + 231656 * 2 ^ 59
def prefixEnd_231656 : Nat := 4983230072969 + 3 ^ 40 * 231656 * 2
def baseEnd_231656 : Nat := 105734110664934114253013

theorem tailTrace_231656 : CollatzResearch.WordTrace tailWord_231656 prefixEnd_231656 105734110664934114253013 := by
  unfold tailWord_231656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224594224378675270041411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5632792299171567026721881 4224594224378675270041411)
  ·
    refine ⟨6336891336568012905062117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4224594224378675270041411 6336891336568012905062117)
    ·
      refine ⟨1188167125606502419699147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6336891336568012905062117 1188167125606502419699147)
      ·
        refine ⟨1782250688409753629548721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188167125606502419699147 1782250688409753629548721)
        ·
          refine ⟨1336688016307315222161541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782250688409753629548721 1336688016307315222161541)
          ·
            refine ⟨250629003057621604155289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1336688016307315222161541 250629003057621604155289)
            ·
              refine ⟨187971752293216203116467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250629003057621604155289 187971752293216203116467)
              ·
                refine ⟨281957628439824304674701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187971752293216203116467 281957628439824304674701)
                ·
                  refine ⟨105734110664934114253013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281957628439824304674701 105734110664934114253013)
                  ·
                    rfl

theorem cell20_231656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_231656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231656 prefixEnd_231656 := by exact prefixLift 231656
  have htrace : WordTrace (prefixWord ++ tailWord_231656) baseStart_231656 baseEnd_231656 := by
    simpa [prefixWord, tailWord_231656, baseEnd_231656] using wordTrace_append hprefix tailTrace_231656
  have hstable : (prefixWord ++ tailWord_231656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231656).length < 2 ^ (prefixWord ++ tailWord_231656).sum := by decide
  have hdescent : baseEnd_231656 < baseStart_231656 := by decide
  rcases family_descends (prefixWord ++ tailWord_231656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231660 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_231660 : Nat := 118140960795 + 231660 * 2 ^ 59
def prefixEnd_231660 : Nat := 4983230072969 + 3 ^ 40 * 231660 * 2
def baseEnd_231660 : Nat := 105735936373927878119663

theorem tailTrace_231660 : CollatzResearch.WordTrace tailWord_231660 prefixEnd_231660 105735936373927878119663 := by
  unfold tailWord_231660
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224667170371429611614217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5632889560495239482152289 4224667170371429611614217)
  ·
    refine ⟨3168500377778572208710663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4224667170371429611614217 3168500377778572208710663)
    ·
      refine ⟨4752750566667858313065995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3168500377778572208710663 4752750566667858313065995)
      ·
        refine ⟨7129125850001787469598993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752750566667858313065995 7129125850001787469598993)
        ·
          refine ⟨5346844387501340602199245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7129125850001787469598993 5346844387501340602199245)
          ·
            refine ⟨2005066645313002725824717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5346844387501340602199245 2005066645313002725824717)
            ·
              refine ⟨751899991992376022184269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2005066645313002725824717 751899991992376022184269)
              ·
                refine ⟨281962496997141008319101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751899991992376022184269 281962496997141008319101)
                ·
                  refine ⟨105735936373927878119663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281962496997141008319101 105735936373927878119663)
                  ·
                    rfl

theorem cell20_231660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_231660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231660 prefixEnd_231660 := by exact prefixLift 231660
  have htrace : WordTrace (prefixWord ++ tailWord_231660) baseStart_231660 baseEnd_231660 := by
    simpa [prefixWord, tailWord_231660, baseEnd_231660] using wordTrace_append hprefix tailTrace_231660
  have hstable : (prefixWord ++ tailWord_231660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231660).length < 2 ^ (prefixWord ++ tailWord_231660).sum := by decide
  have hdescent : baseEnd_231660 < baseStart_231660 := by decide
  rcases family_descends (prefixWord ++ tailWord_231660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231674 : List Nat := [3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_231674 : Nat := 118140960795 + 231674 * 2 ^ 59
def prefixEnd_231674 : Nat := 4983230072969 + 3 ^ 40 * 231674 * 2
def baseEnd_231674 : Nat := 35247442118468683884313

theorem tailTrace_231674 : CollatzResearch.WordTrace tailWord_231674 prefixEnd_231674 35247442118468683884313 := by
  unfold tailWord_231674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112461240673034903559519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5633229975128093076158717 2112461240673034903559519)
  ·
    refine ⟨3168691861009552355339279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2112461240673034903559519 3168691861009552355339279)
    ·
      refine ⟨4753037791514328533008919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3168691861009552355339279 4753037791514328533008919)
      ·
        refine ⟨7129556687271492799513379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753037791514328533008919 7129556687271492799513379)
        ·
          refine ⟨10694335030907239199270069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129556687271492799513379 10694335030907239199270069)
          ·
            refine ⟨1002593909147553674931569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10694335030907239199270069 1002593909147553674931569)
            ·
              refine ⟨751945431860665256198677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002593909147553674931569 751945431860665256198677)
              ·
                refine ⟨35247442118468683884313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 751945431860665256198677 35247442118468683884313)
                ·
                  rfl

theorem cell20_231674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_231674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231674 prefixEnd_231674 := by exact prefixLift 231674
  have htrace : WordTrace (prefixWord ++ tailWord_231674) baseStart_231674 baseEnd_231674 := by
    simpa [prefixWord, tailWord_231674, baseEnd_231674] using wordTrace_append hprefix tailTrace_231674
  have hstable : (prefixWord ++ tailWord_231674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231674).length < 2 ^ (prefixWord ++ tailWord_231674).sum := by decide
  have hdescent : baseEnd_231674 < baseStart_231674 := by decide
  rcases family_descends (prefixWord ++ tailWord_231674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231701 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 2]
def baseStart_231701 : Nat := 118140960795 + 231701 * 2 ^ 59
def prefixEnd_231701 : Nat := 4983230072969 + 3 ^ 40 * 231701 * 2
def baseEnd_231701 : Nat := 105754649891113957752829

theorem tailTrace_231701 : CollatzResearch.WordTrace tailWord_231701 prefixEnd_231701 105754649891113957752829 := by
  unfold tailWord_231701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8450829733594323225470957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5633886489062882150313971 8450829733594323225470957)
  ·
    refine ⟨3169061150097871209551609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8450829733594323225470957 3169061150097871209551609)
    ·
      refine ⟨2376795862573403407163707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3169061150097871209551609 2376795862573403407163707)
      ·
        refine ⟨3565193793860105110745561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376795862573403407163707 3565193793860105110745561)
        ·
          refine ⟨2673895345395078833059171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565193793860105110745561 2673895345395078833059171)
          ·
            refine ⟨4010843018092618249588757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673895345395078833059171 4010843018092618249588757)
            ·
              refine ⟨188008266473091480449473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4010843018092618249588757 188008266473091480449473)
              ·
                refine ⟨141006199854818610337105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188008266473091480449473 141006199854818610337105)
                ·
                  refine ⟨105754649891113957752829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141006199854818610337105 105754649891113957752829)
                  ·
                    rfl

theorem cell20_231701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_231701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231701 prefixEnd_231701 := by exact prefixLift 231701
  have htrace : WordTrace (prefixWord ++ tailWord_231701) baseStart_231701 baseEnd_231701 := by
    simpa [prefixWord, tailWord_231701, baseEnd_231701] using wordTrace_append hprefix tailTrace_231701
  have hstable : (prefixWord ++ tailWord_231701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231701).length < 2 ^ (prefixWord ++ tailWord_231701).sum := by decide
  have hdescent : baseEnd_231701 < baseStart_231701 := by decide
  rcases family_descends (prefixWord ++ tailWord_231701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231725 : List Nat := [1, 5, 3, 1, 2, 1, 3, 4]
def baseStart_231725 : Nat := 118140960795 + 231725 * 2 ^ 59
def prefixEnd_231725 : Nat := 4983230072969 + 3 ^ 40 * 231725 * 2
def baseEnd_231725 : Nat := 35255201381692180317577

theorem tailTrace_231725 : CollatzResearch.WordTrace tailWord_231725 prefixEnd_231725 35255201381692180317577 := by
  unfold tailWord_231725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451705085507375324344629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5634470057004916882896419 8451705085507375324344629)
  ·
    refine ⟨792347351766316436657309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8451705085507375324344629 792347351766316436657309)
    ·
      refine ⟨297130256912368663746491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 792347351766316436657309 297130256912368663746491)
      ·
        refine ⟨445695385368552995619737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297130256912368663746491 445695385368552995619737)
        ·
          refine ⟨334271539026414746714803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445695385368552995619737 334271539026414746714803)
          ·
            refine ⟨501407308539622120072205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334271539026414746714803 501407308539622120072205)
            ·
              refine ⟨188027740702358295027077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501407308539622120072205 188027740702358295027077)
              ·
                refine ⟨35255201381692180317577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188027740702358295027077 35255201381692180317577)
                ·
                  rfl

theorem cell20_231725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_231725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231725 prefixEnd_231725 := by exact prefixLift 231725
  have htrace : WordTrace (prefixWord ++ tailWord_231725) baseStart_231725 baseEnd_231725 := by
    simpa [prefixWord, tailWord_231725, baseEnd_231725] using wordTrace_append hprefix tailTrace_231725
  have hstable : (prefixWord ++ tailWord_231725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231725).length < 2 ^ (prefixWord ++ tailWord_231725).sum := by decide
  have hdescent : baseEnd_231725 < baseStart_231725 := by decide
  rcases family_descends (prefixWord ++ tailWord_231725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231760 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 2]
def baseStart_231760 : Nat := 118140960795 + 231760 * 2 ^ 59
def prefixEnd_231760 : Nat := 4983230072969 + 3 ^ 40 * 231760 * 2
def baseEnd_231760 : Nat := 105781579098771974785921

theorem tailTrace_231760 : CollatzResearch.WordTrace tailWord_231760 prefixEnd_231760 105781579098771974785921 := by
  unfold tailWord_231760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226490820190288150934367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5635321093587050867912489 4226490820190288150934367)
  ·
    refine ⟨6339736230285432226401551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4226490820190288150934367 6339736230285432226401551)
    ·
      refine ⟨9509604345428148339602327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6339736230285432226401551 9509604345428148339602327)
      ·
        refine ⟨14264406518142222509403491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509604345428148339602327 14264406518142222509403491)
        ·
          refine ⟨21396609777213333764105237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14264406518142222509403491 21396609777213333764105237)
          ·
            refine ⟨1002966083306875020192433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21396609777213333764105237 1002966083306875020192433)
            ·
              refine ⟨752224562480156265144325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002966083306875020192433 752224562480156265144325)
              ·
                refine ⟨141042105465029299714561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 752224562480156265144325 141042105465029299714561)
                ·
                  refine ⟨105781579098771974785921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141042105465029299714561 105781579098771974785921)
                  ·
                    rfl

theorem cell20_231760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_231760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231760 prefixEnd_231760 := by exact prefixLift 231760
  have htrace : WordTrace (prefixWord ++ tailWord_231760) baseStart_231760 baseEnd_231760 := by
    simpa [prefixWord, tailWord_231760, baseEnd_231760] using wordTrace_append hprefix tailTrace_231760
  have hstable : (prefixWord ++ tailWord_231760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231760).length < 2 ^ (prefixWord ++ tailWord_231760).sum := by decide
  have hdescent : baseEnd_231760 < baseStart_231760 := by decide
  rcases family_descends (prefixWord ++ tailWord_231760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231781 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_231781 : Nat := 118140960795 + 231781 * 2 ^ 59
def prefixEnd_231781 : Nat := 4983230072969 + 3 ^ 40 * 231781 * 2
def baseEnd_231781 : Nat := 105791164070989235085835

theorem tailTrace_231781 : CollatzResearch.WordTrace tailWord_231781 prefixEnd_231781 105791164070989235085835 := by
  unfold tailWord_231781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453747573304496888383197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5635831715536331258922131 8453747573304496888383197)
  ·
    refine ⟨3170155339989186333143699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8453747573304496888383197 3170155339989186333143699)
    ·
      refine ⟨4755233009983779499715549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170155339989186333143699 4755233009983779499715549)
      ·
        refine ⟨1783212378743917312393331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4755233009983779499715549 1783212378743917312393331)
        ·
          refine ⟨2674818568115875968589997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783212378743917312393331 2674818568115875968589997)
          ·
            refine ⟨1003056963043453488221249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2674818568115875968589997 1003056963043453488221249)
            ·
              refine ⟨752292722282590116165937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003056963043453488221249 752292722282590116165937)
              ·
                refine ⟨564219541711942587124453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752292722282590116165937 564219541711942587124453)
                ·
                  refine ⟨105791164070989235085835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564219541711942587124453 105791164070989235085835)
                  ·
                    rfl

theorem cell20_231781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_231781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231781 prefixEnd_231781 := by exact prefixLift 231781
  have htrace : WordTrace (prefixWord ++ tailWord_231781) baseStart_231781 baseEnd_231781 := by
    simpa [prefixWord, tailWord_231781, baseEnd_231781] using wordTrace_append hprefix tailTrace_231781
  have hstable : (prefixWord ++ tailWord_231781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231781).length < 2 ^ (prefixWord ++ tailWord_231781).sum := by decide
  have hdescent : baseEnd_231781 < baseStart_231781 := by decide
  rcases family_descends (prefixWord ++ tailWord_231781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231784 : List Nat := [2, 1, 4, 2, 2, 3, 2, 4]
def baseStart_231784 : Nat := 118140960795 + 231784 * 2 ^ 59
def prefixEnd_231784 : Nat := 4983230072969 + 3 ^ 40 * 231784 * 2
def baseEnd_231784 : Nat := 35264177784244852661941

theorem tailTrace_231784 : CollatzResearch.WordTrace tailWord_231784 prefixEnd_231784 35264177784244852661941 := by
  unfold tailWord_231784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226928496146814200371203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5635904661529085600494937 4226928496146814200371203)
  ·
    refine ⟨6340392744220221300556805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4226928496146814200371203 6340392744220221300556805)
    ·
      refine ⟨1188823639541291493854401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6340392744220221300556805 1188823639541291493854401)
      ·
        refine ⟨891617729655968620390801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1188823639541291493854401 891617729655968620390801)
        ·
          refine ⟨668713297241976465293101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891617729655968620390801 668713297241976465293101)
          ·
            refine ⟨250767486465741174484913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668713297241976465293101 250767486465741174484913)
            ·
              refine ⟨188075614849305880863685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250767486465741174484913 188075614849305880863685)
              ·
                refine ⟨35264177784244852661941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188075614849305880863685 35264177784244852661941)
                ·
                  rfl

theorem cell20_231784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_231784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231784 prefixEnd_231784 := by exact prefixLift 231784
  have htrace : WordTrace (prefixWord ++ tailWord_231784) baseStart_231784 baseEnd_231784 := by
    simpa [prefixWord, tailWord_231784, baseEnd_231784] using wordTrace_append hprefix tailTrace_231784
  have hstable : (prefixWord ++ tailWord_231784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231784).length < 2 ^ (prefixWord ++ tailWord_231784).sum := by decide
  have hdescent : baseEnd_231784 < baseStart_231784 := by decide
  rcases family_descends (prefixWord ++ tailWord_231784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231812 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_231812 : Nat := 118140960795 + 231812 * 2 ^ 59
def prefixEnd_231812 : Nat := 4983230072969 + 3 ^ 40 * 231812 * 2
def baseEnd_231812 : Nat := 105805313315690905052375

theorem tailTrace_231812 : CollatzResearch.WordTrace tailWord_231812 prefixEnd_231812 105805313315690905052375 := by
  unfold tailWord_231812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4227439118096094591380845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5636585490794792788507793 4227439118096094591380845)
  ·
    refine ⟨1585289669286035471767817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4227439118096094591380845 1585289669286035471767817)
    ·
      refine ⟨1188967251964526603825863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1585289669286035471767817 1188967251964526603825863)
      ·
        refine ⟨1783450877946789905738795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188967251964526603825863 1783450877946789905738795)
        ·
          refine ⟨2675176316920184858608193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783450877946789905738795 2675176316920184858608193)
          ·
            refine ⟨2006382237690138643956145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675176316920184858608193 2006382237690138643956145)
            ·
              refine ⟨1504786678267603982967109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006382237690138643956145 1504786678267603982967109)
              ·
                refine ⟨282147502175175746806333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1504786678267603982967109 282147502175175746806333)
                ·
                  refine ⟨105805313315690905052375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282147502175175746806333 105805313315690905052375)
                  ·
                    rfl

theorem cell20_231812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_231812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231812 prefixEnd_231812 := by exact prefixLift 231812
  have htrace : WordTrace (prefixWord ++ tailWord_231812) baseStart_231812 baseEnd_231812 := by
    simpa [prefixWord, tailWord_231812, baseEnd_231812] using wordTrace_append hprefix tailTrace_231812
  have hstable : (prefixWord ++ tailWord_231812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231812).length < 2 ^ (prefixWord ++ tailWord_231812).sum := by decide
  have hdescent : baseEnd_231812 < baseStart_231812 := by decide
  rcases family_descends (prefixWord ++ tailWord_231812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231815 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 2]
def baseStart_231815 : Nat := 118140960795 + 231815 * 2 ^ 59
def prefixEnd_231815 : Nat := 4983230072969 + 3 ^ 40 * 231815 * 2
def baseEnd_231815 : Nat := 105806682597436227952363

theorem tailTrace_231815 : CollatzResearch.WordTrace tailWord_231815 prefixEnd_231815 105806682597436227952363 := by
  unfold tailWord_231815
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454987655181320695120899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5636658436787547130080599 8454987655181320695120899)
  ·
    refine ⟨12682481482771981042681349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8454987655181320695120899 12682481482771981042681349)
    ·
      refine ⟨2377965278019746445502753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12682481482771981042681349 2377965278019746445502753)
      ·
        refine ⟨1783473958514809834127065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2377965278019746445502753 1783473958514809834127065)
        ·
          refine ⟨1337605468886107375595299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783473958514809834127065 1337605468886107375595299)
          ·
            refine ⟨2006408203329161063392949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337605468886107375595299 2006408203329161063392949)
            ·
              refine ⟨188100769062108849693089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2006408203329161063392949 188100769062108849693089)
              ·
                refine ⟨141075576796581637269817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188100769062108849693089 141075576796581637269817)
                ·
                  refine ⟨105806682597436227952363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141075576796581637269817 105806682597436227952363)
                  ·
                    rfl

theorem cell20_231815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 2].length) (baseStart_231815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231815 prefixEnd_231815 := by exact prefixLift 231815
  have htrace : WordTrace (prefixWord ++ tailWord_231815) baseStart_231815 baseEnd_231815 := by
    simpa [prefixWord, tailWord_231815, baseEnd_231815] using wordTrace_append hprefix tailTrace_231815
  have hstable : (prefixWord ++ tailWord_231815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231815).length < 2 ^ (prefixWord ++ tailWord_231815).sum := by decide
  have hdescent : baseEnd_231815 < baseStart_231815 := by decide
  rcases family_descends (prefixWord ++ tailWord_231815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231819 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_231819 : Nat := 118140960795 + 231819 * 2 ^ 59
def prefixEnd_231819 : Nat := 4983230072969 + 3 ^ 40 * 231819 * 2
def baseEnd_231819 : Nat := 105808508306429991819013

theorem tailTrace_231819 : CollatzResearch.WordTrace tailWord_231819 prefixEnd_231819 105808508306429991819013 := by
  unfold tailWord_231819
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455133547166829378266511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5636755698111219585511007 8455133547166829378266511)
  ·
    refine ⟨12682700320750244067399767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8455133547166829378266511 12682700320750244067399767)
    ·
      refine ⟨19024050481125366101099651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12682700320750244067399767 19024050481125366101099651)
      ·
        refine ⟨28536075721688049151649477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19024050481125366101099651 28536075721688049151649477)
        ·
          refine ⟨5350514197816509215934277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28536075721688049151649477 5350514197816509215934277)
          ·
            refine ⟨1003221412090595477987677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5350514197816509215934277 1003221412090595477987677)
            ·
              refine ⟨376208029533973304245379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1003221412090595477987677 376208029533973304245379)
              ·
                refine ⟨564312044300959956368069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376208029533973304245379 564312044300959956368069)
                ·
                  refine ⟨105808508306429991819013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564312044300959956368069 105808508306429991819013)
                  ·
                    rfl

theorem cell20_231819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_231819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231819 prefixEnd_231819 := by exact prefixLift 231819
  have htrace : WordTrace (prefixWord ++ tailWord_231819) baseStart_231819 baseEnd_231819 := by
    simpa [prefixWord, tailWord_231819, baseEnd_231819] using wordTrace_append hprefix tailTrace_231819
  have hstable : (prefixWord ++ tailWord_231819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231819).length < 2 ^ (prefixWord ++ tailWord_231819).sum := by decide
  have hdescent : baseEnd_231819 < baseStart_231819 := by decide
  rcases family_descends (prefixWord ++ tailWord_231819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231860 : List Nat := [2, 5, 2, 2, 1, 8]
def baseStart_231860 : Nat := 118140960795 + 231860 * 2 ^ 59
def prefixEnd_231860 : Nat := 4983230072969 + 3 ^ 40 * 231860 * 2
def baseEnd_231860 : Nat := 3919526734208002646377

theorem tailTrace_231860 : CollatzResearch.WordTrace tailWord_231860 prefixEnd_231860 3919526734208002646377 := by
  unfold tailWord_231860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228314470009146690254517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5637752626678862253672689 4228314470009146690254517)
  ·
    refine ⟨396404481563357502211361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4228314470009146690254517 396404481563357502211361)
    ·
      refine ⟨297303361172518126658521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396404481563357502211361 297303361172518126658521)
      ·
        refine ⟨222977520879388594993891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297303361172518126658521 222977520879388594993891)
        ·
          refine ⟨334466281319082892490837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222977520879388594993891 334466281319082892490837)
          ·
            refine ⟨3919526734208002646377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 334466281319082892490837 3919526734208002646377)
            ·
              rfl

theorem cell20_231860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 8].length) (baseStart_231860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231860 prefixEnd_231860 := by exact prefixLift 231860
  have htrace : WordTrace (prefixWord ++ tailWord_231860) baseStart_231860 baseEnd_231860 := by
    simpa [prefixWord, tailWord_231860, baseEnd_231860] using wordTrace_append hprefix tailTrace_231860
  have hstable : (prefixWord ++ tailWord_231860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231860).length < 2 ^ (prefixWord ++ tailWord_231860).sum := by decide
  have hdescent : baseEnd_231860 < baseStart_231860 := by decide
  rcases family_descends (prefixWord ++ tailWord_231860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231912 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 2]
def baseStart_231912 : Nat := 118140960795 + 231912 * 2 ^ 59
def prefixEnd_231912 : Nat := 4983230072969 + 3 ^ 40 * 231912 * 2
def baseEnd_231912 : Nat := 105850956040535001718633

theorem tailTrace_231912 : CollatzResearch.WordTrace tailWord_231912 prefixEnd_231912 105850956040535001718633 := by
  unfold tailWord_231912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229262767914953130700995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5639017023886604174267993 4229262767914953130700995)
  ·
    refine ⟨6343894151872429696051493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229262767914953130700995 6343894151872429696051493)
    ·
      refine ⟨1189480153476080568009655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6343894151872429696051493 1189480153476080568009655)
      ·
        refine ⟨1784220230214120852014483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189480153476080568009655 1784220230214120852014483)
        ·
          refine ⟨2676330345321181278021725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784220230214120852014483 2676330345321181278021725)
          ·
            refine ⟨1003623879495442979258147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2676330345321181278021725 1003623879495442979258147)
            ·
              refine ⟨1505435819243164468887221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003623879495442979258147 1505435819243164468887221)
              ·
                refine ⟨141134608054046668958177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1505435819243164468887221 141134608054046668958177)
                ·
                  refine ⟨105850956040535001718633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141134608054046668958177 105850956040535001718633)
                  ·
                    rfl

theorem cell20_231912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_231912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231912 prefixEnd_231912 := by exact prefixLift 231912
  have htrace : WordTrace (prefixWord ++ tailWord_231912) baseStart_231912 baseEnd_231912 := by
    simpa [prefixWord, tailWord_231912, baseEnd_231912] using wordTrace_append hprefix tailTrace_231912
  have hstable : (prefixWord ++ tailWord_231912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231912).length < 2 ^ (prefixWord ++ tailWord_231912).sum := by decide
  have hdescent : baseEnd_231912 < baseStart_231912 := by decide
  rcases family_descends (prefixWord ++ tailWord_231912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231916 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_231916 : Nat := 118140960795 + 231916 * 2 ^ 59
def prefixEnd_231916 : Nat := 4983230072969 + 3 ^ 40 * 231916 * 2
def baseEnd_231916 : Nat := 105852781749528765585283

theorem tailTrace_231916 : CollatzResearch.WordTrace tailWord_231916 prefixEnd_231916 105852781749528765585283 := by
  unfold tailWord_231916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229335713907707472273801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5639114285210276629698401 4229335713907707472273801)
  ·
    refine ⟨3172001785430780604205351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4229335713907707472273801 3172001785430780604205351)
    ·
      refine ⟨4758002678146170906308027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3172001785430780604205351 4758002678146170906308027)
      ·
        refine ⟨7137004017219256359462041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758002678146170906308027 7137004017219256359462041)
        ·
          refine ⟨5352753012914442269596531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7137004017219256359462041 5352753012914442269596531)
          ·
            refine ⟨8029129519371663404394797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352753012914442269596531 8029129519371663404394797)
            ·
              refine ⟨3010923569764373776648049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8029129519371663404394797 3010923569764373776648049)
              ·
                refine ⟨2258192677323280332486037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010923569764373776648049 2258192677323280332486037)
                ·
                  refine ⟨105852781749528765585283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2258192677323280332486037 105852781749528765585283)
                  ·
                    rfl

theorem cell20_231916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_231916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231916 prefixEnd_231916 := by exact prefixLift 231916
  have htrace : WordTrace (prefixWord ++ tailWord_231916) baseStart_231916 baseEnd_231916 := by
    simpa [prefixWord, tailWord_231916, baseEnd_231916] using wordTrace_append hprefix tailTrace_231916
  have hstable : (prefixWord ++ tailWord_231916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231916).length < 2 ^ (prefixWord ++ tailWord_231916).sum := by decide
  have hdescent : baseEnd_231916 < baseStart_231916 := by decide
  rcases family_descends (prefixWord ++ tailWord_231916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231922 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_231922 : Nat := 118140960795 + 231922 * 2 ^ 59
def prefixEnd_231922 : Nat := 4983230072969 + 3 ^ 40 * 231922 * 2
def baseEnd_231922 : Nat := 105855520313019411385259

theorem tailTrace_231922 : CollatzResearch.WordTrace tailWord_231922 prefixEnd_231922 105855520313019411385259 := by
  unfold tailWord_231922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114722566448419492316505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5639260177195785312844013 2114722566448419492316505)
  ·
    refine ⟨1586041924836314619237379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2114722566448419492316505 1586041924836314619237379)
    ·
      refine ⟨2379062887254471928856069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586041924836314619237379 2379062887254471928856069)
      ·
        refine ⟨446074291360213486660513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2379062887254471928856069 446074291360213486660513)
        ·
          refine ⟨334555718520160114995385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446074291360213486660513 334555718520160114995385)
          ·
            refine ⟨250916788890120086246539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334555718520160114995385 250916788890120086246539)
            ·
              refine ⟨376375183335180129369809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250916788890120086246539 376375183335180129369809)
              ·
                refine ⟨282281387501385097027357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376375183335180129369809 282281387501385097027357)
                ·
                  refine ⟨105855520313019411385259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282281387501385097027357 105855520313019411385259)
                  ·
                    rfl

theorem cell20_231922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_231922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231922 prefixEnd_231922 := by exact prefixLift 231922
  have htrace : WordTrace (prefixWord ++ tailWord_231922) baseStart_231922 baseEnd_231922 := by
    simpa [prefixWord, tailWord_231922, baseEnd_231922] using wordTrace_append hprefix tailTrace_231922
  have hstable : (prefixWord ++ tailWord_231922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231922).length < 2 ^ (prefixWord ++ tailWord_231922).sum := by decide
  have hdescent : baseEnd_231922 < baseStart_231922 := by decide
  rcases family_descends (prefixWord ++ tailWord_231922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231923 : List Nat := [1, 1, 1, 2, 2, 2, 11]
def baseStart_231923 : Nat := 118140960795 + 231923 * 2 ^ 59
def prefixEnd_231923 : Nat := 4983230072969 + 3 ^ 40 * 231923 * 2
def baseEnd_231923 : Nat := 11761775193363094705769

theorem tailTrace_231923 : CollatzResearch.WordTrace tailWord_231923 prefixEnd_231923 11761775193363094705769 := by
  unfold tailWord_231923
  simp only [CollatzResearch.WordTrace]
  refine ⟨8458926738790055140052423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5639284492526703426701615 8458926738790055140052423)
  ·
    refine ⟨12688390108185082710078635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8458926738790055140052423 12688390108185082710078635)
    ·
      refine ⟨19032585162277624065117953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12688390108185082710078635 19032585162277624065117953)
      ·
        refine ⟨14274438871708218048838465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19032585162277624065117953 14274438871708218048838465)
        ·
          refine ⟨10705829153781163536628849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14274438871708218048838465 10705829153781163536628849)
          ·
            refine ⟨8029371865335872652471637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10705829153781163536628849 8029371865335872652471637)
            ·
              refine ⟨11761775193363094705769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8029371865335872652471637 11761775193363094705769)
              ·
                rfl

theorem cell20_231923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_231923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231923 prefixEnd_231923 := by exact prefixLift 231923
  have htrace : WordTrace (prefixWord ++ tailWord_231923) baseStart_231923 baseEnd_231923 := by
    simpa [prefixWord, tailWord_231923, baseEnd_231923] using wordTrace_append hprefix tailTrace_231923
  have hstable : (prefixWord ++ tailWord_231923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231923).length < 2 ^ (prefixWord ++ tailWord_231923).sum := by decide
  have hdescent : baseEnd_231923 < baseStart_231923 := by decide
  rcases family_descends (prefixWord ++ tailWord_231923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231926 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_231926 : Nat := 118140960795 + 231926 * 2 ^ 59
def prefixEnd_231926 : Nat := 4983230072969 + 3 ^ 40 * 231926 * 2
def baseEnd_231926 : Nat := 105857346022013175251909

theorem tailTrace_231926 : CollatzResearch.WordTrace tailWord_231926 prefixEnd_231926 105857346022013175251909 := by
  unfold tailWord_231926
  simp only [CollatzResearch.WordTrace]
  refine ⟨528689759861199165775727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5639357438519457768274421 528689759861199165775727)
  ·
    refine ⟨793034639791798748663591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 528689759861199165775727 793034639791798748663591)
    ·
      refine ⟨1189551959687698122995387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793034639791798748663591 1189551959687698122995387)
      ·
        refine ⟨1784327939531547184493081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189551959687698122995387 1784327939531547184493081)
        ·
          refine ⟨1338245954648660388369811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1784327939531547184493081 1338245954648660388369811)
          ·
            refine ⟨2007368931972990582554717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338245954648660388369811 2007368931972990582554717)
            ·
              refine ⟨752763349489871468458019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2007368931972990582554717 752763349489871468458019)
              ·
                refine ⟨1129145024234807202687029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752763349489871468458019 1129145024234807202687029)
                ·
                  refine ⟨105857346022013175251909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129145024234807202687029 105857346022013175251909)
                  ·
                    rfl

theorem cell20_231926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_231926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231926 prefixEnd_231926 := by exact prefixLift 231926
  have htrace : WordTrace (prefixWord ++ tailWord_231926) baseStart_231926 baseEnd_231926 := by
    simpa [prefixWord, tailWord_231926, baseEnd_231926] using wordTrace_append hprefix tailTrace_231926
  have hstable : (prefixWord ++ tailWord_231926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231926).length < 2 ^ (prefixWord ++ tailWord_231926).sum := by decide
  have hdescent : baseEnd_231926 < baseStart_231926 := by decide
  rcases family_descends (prefixWord ++ tailWord_231926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231933 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_231933 : Nat := 118140960795 + 231933 * 2 ^ 59
def prefixEnd_231933 : Nat := 4983230072969 + 3 ^ 40 * 231933 * 2
def baseEnd_231933 : Nat := 105860541012752262018547

theorem tailTrace_231933 : CollatzResearch.WordTrace tailWord_231933 prefixEnd_231933 105860541012752262018547 := by
  unfold tailWord_231933
  simp only [CollatzResearch.WordTrace]
  refine ⟨8459291468753826847916453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5639527645835884565277635 8459291468753826847916453)
  ·
    refine ⟨1586117150391342533984335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8459291468753826847916453 1586117150391342533984335)
    ·
      refine ⟨2379175725587013800976503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586117150391342533984335 2379175725587013800976503)
      ·
        refine ⟨3568763588380520701464755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379175725587013800976503 3568763588380520701464755)
        ·
          refine ⟨5353145382570781052197133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568763588380520701464755 5353145382570781052197133)
          ·
            refine ⟨2007429518464042894573925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5353145382570781052197133 2007429518464042894573925)
            ·
              refine ⟨376393034712008042732611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2007429518464042894573925 376393034712008042732611)
              ·
                refine ⟨564589552068012064098917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376393034712008042732611 564589552068012064098917)
                ·
                  refine ⟨105860541012752262018547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564589552068012064098917 105860541012752262018547)
                  ·
                    rfl

theorem cell20_231933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_231933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231933 prefixEnd_231933 := by exact prefixLift 231933
  have htrace : WordTrace (prefixWord ++ tailWord_231933) baseStart_231933 baseEnd_231933 := by
    simpa [prefixWord, tailWord_231933, baseEnd_231933] using wordTrace_append hprefix tailTrace_231933
  have hstable : (prefixWord ++ tailWord_231933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231933).length < 2 ^ (prefixWord ++ tailWord_231933).sum := by decide
  have hdescent : baseEnd_231933 < baseStart_231933 := by decide
  rcases family_descends (prefixWord ++ tailWord_231933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231961 : List Nat := [1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_231961 : Nat := 118140960795 + 231961 * 2 ^ 59
def prefixEnd_231961 : Nat := 4983230072969 + 3 ^ 40 * 231961 * 2
def baseEnd_231961 : Nat := 35291106991902869695033

theorem tailTrace_231961 : CollatzResearch.WordTrace tailWord_231961 prefixEnd_231961 35291106991902869695033 := by
  unfold tailWord_231961
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460312712652387629935737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5640208475101591753290491 8460312712652387629935737)
  ·
    refine ⟨6345234534489290722451803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8460312712652387629935737 6345234534489290722451803)
    ·
      refine ⟨9517851801733936083677705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345234534489290722451803 9517851801733936083677705)
      ·
        refine ⟨7138388851300452062758279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9517851801733936083677705 7138388851300452062758279)
        ·
          refine ⟨10707583276950678094137419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138388851300452062758279 10707583276950678094137419)
          ·
            refine ⟨16061374915426017141206129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707583276950678094137419 16061374915426017141206129)
            ·
              refine ⟨12046031186569512855904597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16061374915426017141206129 12046031186569512855904597)
              ·
                refine ⟨35291106991902869695033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12046031186569512855904597 35291106991902869695033)
                ·
                  rfl

theorem cell20_231961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_231961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231961 prefixEnd_231961 := by exact prefixLift 231961
  have htrace : WordTrace (prefixWord ++ tailWord_231961) baseStart_231961 baseEnd_231961 := by
    simpa [prefixWord, tailWord_231961, baseEnd_231961] using wordTrace_append hprefix tailTrace_231961
  have hstable : (prefixWord ++ tailWord_231961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231961).length < 2 ^ (prefixWord ++ tailWord_231961).sum := by decide
  have hdescent : baseEnd_231961 < baseStart_231961 := by decide
  rcases family_descends (prefixWord ++ tailWord_231961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
