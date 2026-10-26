import V185TrunkScan20Chunk154

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_943722 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_943722 : Nat := 118140960795 + 943722 * 2 ^ 59
def prefixEnd_943722 : Nat := 4983230072969 + 3 ^ 40 * 943722 * 2
def baseEnd_943722 : Nat := 430740435753299481808807

theorem tailTrace_943722 : CollatzResearch.WordTrace tailWord_943722 prefixEnd_943722 430740435753299481808807 := by
  unfold tailWord_943722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605092271765960932730355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22946912724709229153947613 8605092271765960932730355)
  ·
    refine ⟨12907638407648941399095533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8605092271765960932730355 12907638407648941399095533)
    ·
      refine ⟨4840364402868353024660825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12907638407648941399095533 4840364402868353024660825)
      ·
        refine ⟨3630273302151264768495619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4840364402868353024660825 3630273302151264768495619)
        ·
          refine ⟨5445409953226897152743429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630273302151264768495619 5445409953226897152743429)
          ·
            refine ⟨1021014366230043216139393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5445409953226897152743429 1021014366230043216139393)
            ·
              refine ⟨765760774672532412104545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021014366230043216139393 765760774672532412104545)
              ·
                refine ⟨574320581004399309078409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765760774672532412104545 574320581004399309078409)
                ·
                  refine ⟨430740435753299481808807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574320581004399309078409 430740435753299481808807)
                  ·
                    rfl

theorem cell20_943722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_943722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943722 prefixEnd_943722 := by exact prefixLift 943722
  have htrace : WordTrace (prefixWord ++ tailWord_943722) baseStart_943722 baseEnd_943722 := by
    simpa [prefixWord, tailWord_943722, baseEnd_943722] using wordTrace_append hprefix tailTrace_943722
  have hstable : (prefixWord ++ tailWord_943722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943722).length < 2 ^ (prefixWord ++ tailWord_943722).sum := by decide
  have hdescent : baseEnd_943722 < baseStart_943722 := by decide
  rcases family_descends (prefixWord ++ tailWord_943722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943733 : List Nat := [1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_943733 : Nat := 118140960795 + 943733 * 2 ^ 59
def prefixEnd_943733 : Nat := 4983230072969 + 3 ^ 40 * 943733 * 2
def baseEnd_943733 : Nat := 143581818817677444147365

theorem tailTrace_943733 : CollatzResearch.WordTrace tailWord_943733 prefixEnd_943733 143581818817677444147365 := by
  unfold tailWord_943733
  simp only [CollatzResearch.WordTrace]
  refine ⟨34420770290023992609571853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22947180193349328406381235 34420770290023992609571853)
  ·
    refine ⟨12907788858758997228589445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34420770290023992609571853 12907788858758997228589445)
    ·
      refine ⟨2420210411017311980360521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12907788858758997228589445 2420210411017311980360521)
      ·
        refine ⟨1815157808262983985270391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2420210411017311980360521 1815157808262983985270391)
        ·
          refine ⟨2722736712394475977905587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815157808262983985270391 2722736712394475977905587)
          ·
            refine ⟨4084105068591713966858381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722736712394475977905587 4084105068591713966858381)
            ·
              refine ⟨1531539400721892737571893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4084105068591713966858381 1531539400721892737571893)
              ·
                refine ⟨143581818817677444147365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1531539400721892737571893 143581818817677444147365)
                ·
                  rfl

theorem cell20_943733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_943733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943733 prefixEnd_943733 := by exact prefixLift 943733
  have htrace : WordTrace (prefixWord ++ tailWord_943733) baseStart_943733 baseEnd_943733 := by
    simpa [prefixWord, tailWord_943733, baseEnd_943733] using wordTrace_append hprefix tailTrace_943733
  have hstable : (prefixWord ++ tailWord_943733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943733).length < 2 ^ (prefixWord ++ tailWord_943733).sum := by decide
  have hdescent : baseEnd_943733 < baseStart_943733 := by decide
  rcases family_descends (prefixWord ++ tailWord_943733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943774 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_943774 : Nat := 118140960795 + 943774 * 2 ^ 59
def prefixEnd_943774 : Nat := 4983230072969 + 3 ^ 40 * 943774 * 2
def baseEnd_943774 : Nat := 430764169970218412075261

theorem tailTrace_943774 : CollatzResearch.WordTrace tailWord_943774 prefixEnd_943774 430764169970218412075261 := by
  unfold tailWord_943774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302783210359432076476797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22948177121916971074542917 4302783210359432076476797)
  ·
    refine ⟨1613543703884787028678799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4302783210359432076476797 1613543703884787028678799)
    ·
      refine ⟨2420315555827180543018199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613543703884787028678799 2420315555827180543018199)
      ·
        refine ⟨3630473333740770814527299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420315555827180543018199 3630473333740770814527299)
        ·
          refine ⟨5445710000611156221790949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630473333740770814527299 5445710000611156221790949)
          ·
            refine ⟨1021070625114591791585803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5445710000611156221790949 1021070625114591791585803)
            ·
              refine ⟨1531605937671887687378705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021070625114591791585803 1531605937671887687378705)
              ·
                refine ⟨1148704453253915765534029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531605937671887687378705 1148704453253915765534029)
                ·
                  refine ⟨430764169970218412075261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148704453253915765534029 430764169970218412075261)
                  ·
                    rfl

theorem cell20_943774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_943774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943774 prefixEnd_943774 := by exact prefixLift 943774
  have htrace : WordTrace (prefixWord ++ tailWord_943774) baseStart_943774 baseEnd_943774 := by
    simpa [prefixWord, tailWord_943774, baseEnd_943774] using wordTrace_append hprefix tailTrace_943774
  have hstable : (prefixWord ++ tailWord_943774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943774).length < 2 ^ (prefixWord ++ tailWord_943774).sum := by decide
  have hdescent : baseEnd_943774 < baseStart_943774 := by decide
  rcases family_descends (prefixWord ++ tailWord_943774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943813 : List Nat := [1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_943813 : Nat := 118140960795 + 943813 * 2 ^ 59
def prefixEnd_943813 : Nat := 4983230072969 + 3 ^ 40 * 943813 * 2
def baseEnd_943813 : Nat := 143593990210969203258367

theorem tailTrace_943813 : CollatzResearch.WordTrace tailWord_943813 prefixEnd_943813 143593990210969203258367 := by
  unfold tailWord_943813
  simp only [CollatzResearch.WordTrace]
  refine ⟨34423688129734166272484093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22949125419822777514989395 34423688129734166272484093)
  ·
    refine ⟨12908883048650312352181535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34423688129734166272484093 12908883048650312352181535)
    ·
      refine ⟨19363324572975468528272303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12908883048650312352181535 19363324572975468528272303)
      ·
        refine ⟨29044986859463202792408455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19363324572975468528272303 29044986859463202792408455)
        ·
          refine ⟨43567480289194804188612683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29044986859463202792408455 43567480289194804188612683)
          ·
            refine ⟨65351220433792206282919025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43567480289194804188612683 65351220433792206282919025)
            ·
              refine ⟨49013415325344154712189269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65351220433792206282919025 49013415325344154712189269)
              ·
                refine ⟨143593990210969203258367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49013415325344154712189269 143593990210969203258367)
                ·
                  rfl

theorem cell20_943813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_943813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943813 prefixEnd_943813 := by exact prefixLift 943813
  have htrace : WordTrace (prefixWord ++ tailWord_943813) baseStart_943813 baseEnd_943813 := by
    simpa [prefixWord, tailWord_943813, baseEnd_943813] using wordTrace_append hprefix tailTrace_943813
  have hstable : (prefixWord ++ tailWord_943813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943813).length < 2 ^ (prefixWord ++ tailWord_943813).sum := by decide
  have hdescent : baseEnd_943813 < baseStart_943813 := by decide
  rcases family_descends (prefixWord ++ tailWord_943813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943836 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 4]
def baseStart_943836 : Nat := 118140960795 + 943836 * 2 ^ 59
def prefixEnd_943836 : Nat := 4983230072969 + 3 ^ 40 * 943836 * 2
def baseEnd_943836 : Nat := 430792468459621752008341

theorem tailTrace_943836 : CollatzResearch.WordTrace tailWord_943836 prefixEnd_943836 430792468459621752008341 := by
  unfold tailWord_943836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17212263504325420600285681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22949684672433894133714241 17212263504325420600285681)
  ·
    refine ⟨12909197628244065450214261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17212263504325420600285681 12909197628244065450214261)
    ·
      refine ⟨1210237277647881135957587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12909197628244065450214261 1210237277647881135957587)
      ·
        refine ⟨1815355916471821703936381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210237277647881135957587 1815355916471821703936381)
        ·
          refine ⟨680758468676933138976143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1815355916471821703936381 680758468676933138976143)
          ·
            refine ⟨1021137703015399708464215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680758468676933138976143 1021137703015399708464215)
            ·
              refine ⟨1531706554523099562696323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021137703015399708464215 1531706554523099562696323)
              ·
                refine ⟨2297559831784649344044485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531706554523099562696323 2297559831784649344044485)
                ·
                  refine ⟨430792468459621752008341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2297559831784649344044485 430792468459621752008341)
                  ·
                    rfl

theorem cell20_943836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_943836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943836 prefixEnd_943836 := by exact prefixLift 943836
  have htrace : WordTrace (prefixWord ++ tailWord_943836) baseStart_943836 baseEnd_943836 := by
    simpa [prefixWord, tailWord_943836, baseEnd_943836] using wordTrace_append hprefix tailTrace_943836
  have hstable : (prefixWord ++ tailWord_943836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943836).length < 2 ^ (prefixWord ++ tailWord_943836).sum := by decide
  have hdescent : baseEnd_943836 < baseStart_943836 := by decide
  rcases family_descends (prefixWord ++ tailWord_943836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943851 : List Nat := [1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_943851 : Nat := 118140960795 + 943851 * 2 ^ 59
def prefixEnd_943851 : Nat := 4983230072969 + 3 ^ 40 * 943851 * 2
def baseEnd_943851 : Nat := 143599771622782788836093

theorem tailTrace_943851 : CollatzResearch.WordTrace tailWord_943851 prefixEnd_943851 143599771622782788836093 := by
  unfold tailWord_943851
  simp only [CollatzResearch.WordTrace]
  refine ⟨34425074103596498762367407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22950049402397665841578271 34425074103596498762367407)
  ·
    refine ⟨51637611155394748143551111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34425074103596498762367407 51637611155394748143551111)
    ·
      refine ⟨77456416733092122215326667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51637611155394748143551111 77456416733092122215326667)
      ·
        refine ⟨116184625099638183322990001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77456416733092122215326667 116184625099638183322990001)
        ·
          refine ⟨87138468824728637492242501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116184625099638183322990001 87138468824728637492242501)
          ·
            refine ⟨16338462904636619529795469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87138468824728637492242501 16338462904636619529795469)
            ·
              refine ⟨6126923589238732323673301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16338462904636619529795469 6126923589238732323673301)
              ·
                refine ⟨143599771622782788836093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6126923589238732323673301 143599771622782788836093)
                ·
                  rfl

theorem cell20_943851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_943851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943851 prefixEnd_943851 := by exact prefixLift 943851
  have htrace : WordTrace (prefixWord ++ tailWord_943851) baseStart_943851 baseEnd_943851 := by
    simpa [prefixWord, tailWord_943851, baseEnd_943851] using wordTrace_append hprefix tailTrace_943851
  have hstable : (prefixWord ++ tailWord_943851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943851).length < 2 ^ (prefixWord ++ tailWord_943851).sum := by decide
  have hdescent : baseEnd_943851 < baseStart_943851 := by decide
  rcases family_descends (prefixWord ++ tailWord_943851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943854 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_943854 : Nat := 118140960795 + 943854 * 2 ^ 59
def prefixEnd_943854 : Nat := 4983230072969 + 3 ^ 40 * 943854 * 2
def baseEnd_943854 : Nat := 430800684150093689408267

theorem tailTrace_943854 : CollatzResearch.WordTrace tailWord_943854 prefixEnd_943854 430800684150093689408267 := by
  unfold tailWord_943854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303147940323203784340827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22950122348390420183151077 4303147940323203784340827)
  ·
    refine ⟨6454721910484805676511241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4303147940323203784340827 6454721910484805676511241)
    ·
      refine ⟨4841041432863604257383431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6454721910484805676511241 4841041432863604257383431)
      ·
        refine ⟨7261562149295406386075147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841041432863604257383431 7261562149295406386075147)
        ·
          refine ⟨10892343223943109579112721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261562149295406386075147 10892343223943109579112721)
          ·
            refine ⟨8169257417957332184334541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10892343223943109579112721 8169257417957332184334541)
            ·
              refine ⟨3063471531733999569125453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8169257417957332184334541 3063471531733999569125453)
              ·
                refine ⟨1148801824400249838422045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3063471531733999569125453 1148801824400249838422045)
                ·
                  refine ⟨430800684150093689408267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148801824400249838422045 430800684150093689408267)
                  ·
                    rfl

theorem cell20_943854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_943854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943854 prefixEnd_943854 := by exact prefixLift 943854
  have htrace : WordTrace (prefixWord ++ tailWord_943854) baseStart_943854 baseEnd_943854 := by
    simpa [prefixWord, tailWord_943854, baseEnd_943854] using wordTrace_append hprefix tailTrace_943854
  have hstable : (prefixWord ++ tailWord_943854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943854).length < 2 ^ (prefixWord ++ tailWord_943854).sum := by decide
  have hdescent : baseEnd_943854 < baseStart_943854 := by decide
  rcases family_descends (prefixWord ++ tailWord_943854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943895 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 2]
def baseStart_943895 : Nat := 118140960795 + 943895 * 2 ^ 59
def prefixEnd_943895 : Nat := 4983230072969 + 3 ^ 40 * 943895 * 2
def baseEnd_943895 : Nat := 430819397667279769041433

theorem tailTrace_943895 : CollatzResearch.WordTrace tailWord_943895 prefixEnd_943895 430819397667279769041433 := by
  unfold tailWord_943895
  simp only [CollatzResearch.WordTrace]
  refine ⟨34426678915437094276969139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22951119276958062851312759 34426678915437094276969139)
  ·
    refine ⟨51640018373155641415453709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34426678915437094276969139 51640018373155641415453709)
    ·
      refine ⟨19365006889933365530795141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51640018373155641415453709 19365006889933365530795141)
      ·
        refine ⟨3630938791862506037024089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19365006889933365530795141 3630938791862506037024089)
        ·
          refine ⟨2723204093896879527768067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630938791862506037024089 2723204093896879527768067)
          ·
            refine ⟨4084806140845319291652101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723204093896879527768067 4084806140845319291652101)
            ·
              refine ⟨765901151408497367184769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4084806140845319291652101 765901151408497367184769)
              ·
                refine ⟨574425863556373025388577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765901151408497367184769 574425863556373025388577)
                ·
                  refine ⟨430819397667279769041433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574425863556373025388577 430819397667279769041433)
                  ·
                    rfl

theorem cell20_943895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 2].length) (baseStart_943895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943895 prefixEnd_943895 := by exact prefixLift 943895
  have htrace : WordTrace (prefixWord ++ tailWord_943895) baseStart_943895 baseEnd_943895 := by
    simpa [prefixWord, tailWord_943895, baseEnd_943895] using wordTrace_append hprefix tailTrace_943895
  have hstable : (prefixWord ++ tailWord_943895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943895).length < 2 ^ (prefixWord ++ tailWord_943895).sum := by decide
  have hdescent : baseEnd_943895 < baseStart_943895 := by decide
  rcases family_descends (prefixWord ++ tailWord_943895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943899 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 2]
def baseStart_943899 : Nat := 118140960795 + 943899 * 2 ^ 59
def prefixEnd_943899 : Nat := 4983230072969 + 3 ^ 40 * 943899 * 2
def baseEnd_943899 : Nat := 430821223376273532908083

theorem tailTrace_943899 : CollatzResearch.WordTrace tailWord_943899 prefixEnd_943899 430821223376273532908083 := by
  unfold tailWord_943899
  simp only [CollatzResearch.WordTrace]
  refine ⟨34426824807422602960114751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22951216538281735306743167 34426824807422602960114751)
  ·
    refine ⟨51640237211133904440172127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34426824807422602960114751 51640237211133904440172127)
    ·
      refine ⟨77460355816700856660258191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51640237211133904440172127 77460355816700856660258191)
      ·
        refine ⟨116190533725051284990387287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77460355816700856660258191 116190533725051284990387287)
        ·
          refine ⟨174285800587576927485580931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116190533725051284990387287 174285800587576927485580931)
          ·
            refine ⟨261428700881365391228371397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174285800587576927485580931 261428700881365391228371397)
            ·
              refine ⟨49017881415256010855319637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261428700881365391228371397 49017881415256010855319637)
              ·
                refine ⟨574428297835031377210777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 49017881415256010855319637 574428297835031377210777)
                ·
                  refine ⟨430821223376273532908083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574428297835031377210777 430821223376273532908083)
                  ·
                    rfl

theorem cell20_943899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 2].length) (baseStart_943899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943899 prefixEnd_943899 := by exact prefixLift 943899
  have htrace : WordTrace (prefixWord ++ tailWord_943899) baseStart_943899 baseEnd_943899 := by
    simpa [prefixWord, tailWord_943899, baseEnd_943899] using wordTrace_append hprefix tailTrace_943899
  have hstable : (prefixWord ++ tailWord_943899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943899).length < 2 ^ (prefixWord ++ tailWord_943899).sum := by decide
  have hdescent : baseEnd_943899 < baseStart_943899 := by decide
  rcases family_descends (prefixWord ++ tailWord_943899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943923 : List Nat := [1, 1, 1, 2, 7, 1, 3, 4]
def baseStart_943923 : Nat := 118140960795 + 943923 * 2 ^ 59
def prefixEnd_943923 : Nat := 4983230072969 + 3 ^ 40 * 943923 * 2
def baseEnd_943923 : Nat := 143610725876745372035995

theorem tailTrace_943923 : CollatzResearch.WordTrace tailWord_943923 prefixEnd_943923 143610725876745372035995 := by
  unfold tailWord_943923
  simp only [CollatzResearch.WordTrace]
  refine ⟨34427700159335655058988423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22951800106223770039325615 34427700159335655058988423)
  ·
    refine ⟨51641550239003482588482635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34427700159335655058988423 51641550239003482588482635)
    ·
      refine ⟨77462325358505223882723953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51641550239003482588482635 77462325358505223882723953)
      ·
        refine ⟨58096744018878917912042965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77462325358505223882723953 58096744018878917912042965)
        ·
          refine ⟨1361642437942474638563507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58096744018878917912042965 1361642437942474638563507)
          ·
            refine ⟨2042463656913711957845261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361642437942474638563507 2042463656913711957845261)
            ·
              refine ⟨765923871342641984191973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2042463656913711957845261 765923871342641984191973)
              ·
                refine ⟨143610725876745372035995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765923871342641984191973 143610725876745372035995)
                ·
                  rfl

theorem cell20_943923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_943923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943923 prefixEnd_943923 := by exact prefixLift 943923
  have htrace : WordTrace (prefixWord ++ tailWord_943923) baseStart_943923 baseEnd_943923 := by
    simpa [prefixWord, tailWord_943923, baseEnd_943923] using wordTrace_append hprefix tailTrace_943923
  have hstable : (prefixWord ++ tailWord_943923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943923).length < 2 ^ (prefixWord ++ tailWord_943923).sum := by decide
  have hdescent : baseEnd_943923 < baseStart_943923 := by decide
  rcases family_descends (prefixWord ++ tailWord_943923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943933 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 2]
def baseStart_943933 : Nat := 118140960795 + 943933 * 2 ^ 59
def prefixEnd_943933 : Nat := 4983230072969 + 3 ^ 40 * 943933 * 2
def baseEnd_943933 : Nat := 430836741902720525774611

theorem tailTrace_943933 : CollatzResearch.WordTrace tailWord_943933 prefixEnd_943933 430836741902720525774611 := by
  unfold tailWord_943933
  simp only [CollatzResearch.WordTrace]
  refine ⟨34428064889299426766852453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22952043259532951177901635 34428064889299426766852453)
  ·
    refine ⟨6455262166743642518784835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34428064889299426766852453 6455262166743642518784835)
    ·
      refine ⟨9682893250115463778177253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6455262166743642518784835 9682893250115463778177253)
      ·
        refine ⟨1815542484396649458408235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9682893250115463778177253 1815542484396649458408235)
        ·
          refine ⟨2723313726594974187612353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815542484396649458408235 2723313726594974187612353)
          ·
            refine ⟨2042485294946230640709265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2723313726594974187612353 2042485294946230640709265)
            ·
              refine ⟨1531863971209672980531949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042485294946230640709265 1531863971209672980531949)
              ·
                refine ⟨574448989203627367699481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1531863971209672980531949 574448989203627367699481)
                ·
                  refine ⟨430836741902720525774611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574448989203627367699481 430836741902720525774611)
                  ·
                    rfl

theorem cell20_943933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_943933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943933 prefixEnd_943933 := by exact prefixLift 943933
  have htrace : WordTrace (prefixWord ++ tailWord_943933) baseStart_943933 baseEnd_943933 := by
    simpa [prefixWord, tailWord_943933, baseEnd_943933] using wordTrace_append hprefix tailTrace_943933
  have hstable : (prefixWord ++ tailWord_943933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943933).length < 2 ^ (prefixWord ++ tailWord_943933).sum := by decide
  have hdescent : baseEnd_943933 < baseStart_943933 := by decide
  rcases family_descends (prefixWord ++ tailWord_943933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943954 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_943954 : Nat := 118140960795 + 943954 * 2 ^ 59
def prefixEnd_943954 : Nat := 4983230072969 + 3 ^ 40 * 943954 * 2
def baseEnd_943954 : Nat := 430846326874937786074525

theorem tailTrace_943954 : CollatzResearch.WordTrace tailWord_943954 prefixEnd_943954 430846326874937786074525 := by
  unfold tailWord_943954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607207705555836838341729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22952553881482231568911277 8607207705555836838341729)
  ·
    refine ⟨6455405779166877628756297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8607207705555836838341729 6455405779166877628756297)
    ·
      refine ⟨4841554334375158221567223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6455405779166877628756297 4841554334375158221567223)
      ·
        refine ⟨7262331501562737332350835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841554334375158221567223 7262331501562737332350835)
        ·
          refine ⟨10893497252344105998526253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262331501562737332350835 10893497252344105998526253)
          ·
            refine ⟨4085061469629039749447345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10893497252344105998526253 4085061469629039749447345)
            ·
              refine ⟨3063796102221779812085509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085061469629039749447345 3063796102221779812085509)
              ·
                refine ⟨574461769166583714766033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3063796102221779812085509 574461769166583714766033)
                ·
                  refine ⟨430846326874937786074525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574461769166583714766033 430846326874937786074525)
                  ·
                    rfl

theorem cell20_943954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_943954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943954 prefixEnd_943954 := by exact prefixLift 943954
  have htrace : WordTrace (prefixWord ++ tailWord_943954) baseStart_943954 baseEnd_943954 := by
    simpa [prefixWord, tailWord_943954, baseEnd_943954] using wordTrace_append hprefix tailTrace_943954
  have hstable : (prefixWord ++ tailWord_943954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943954).length < 2 ^ (prefixWord ++ tailWord_943954).sum := by decide
  have hdescent : baseEnd_943954 < baseStart_943954 := by decide
  rcases family_descends (prefixWord ++ tailWord_943954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943964 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_943964 : Nat := 118140960795 + 943964 * 2 ^ 59
def prefixEnd_943964 : Nat := 4983230072969 + 3 ^ 40 * 943964 * 2
def baseEnd_943964 : Nat := 430850891147422195741151

theorem tailTrace_943964 : CollatzResearch.WordTrace tailWord_943964 prefixEnd_943964 430850891147422195741151 := by
  unfold tailWord_943964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214597776093559530615473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22952797034791412707487297 17214597776093559530615473)
  ·
    refine ⟨12910948332070169647961605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17214597776093559530615473 12910948332070169647961605)
    ·
      refine ⟨2420802812263156808992801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12910948332070169647961605 2420802812263156808992801)
      ·
        refine ⟨1815602109197367606744601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2420802812263156808992801 1815602109197367606744601)
        ·
          refine ⟨1361701581898025705058451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1815602109197367606744601 1361701581898025705058451)
          ·
            refine ⟨2042552372847038557587677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361701581898025705058451 2042552372847038557587677)
            ·
              refine ⟨765957139817639459095379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2042552372847038557587677 765957139817639459095379)
              ·
                refine ⟨1148935709726459188643069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765957139817639459095379 1148935709726459188643069)
                ·
                  refine ⟨430850891147422195741151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148935709726459188643069 430850891147422195741151)
                  ·
                    rfl

theorem cell20_943964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_943964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943964 prefixEnd_943964 := by exact prefixLift 943964
  have htrace : WordTrace (prefixWord ++ tailWord_943964) baseStart_943964 baseEnd_943964 := by
    simpa [prefixWord, tailWord_943964, baseEnd_943964] using wordTrace_append hprefix tailTrace_943964
  have hstable : (prefixWord ++ tailWord_943964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943964).length < 2 ^ (prefixWord ++ tailWord_943964).sum := by decide
  have hdescent : baseEnd_943964 < baseStart_943964 := by decide
  rcases family_descends (prefixWord ++ tailWord_943964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943989 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_943989 : Nat := 118140960795 + 943989 * 2 ^ 59
def prefixEnd_943989 : Nat := 4983230072969 + 3 ^ 40 * 943989 * 2
def baseEnd_943989 : Nat := 430862301828633219907715

theorem tailTrace_943989 : CollatzResearch.WordTrace tailWord_943989 prefixEnd_943989 430862301828633219907715 := by
  unfold tailWord_943989
  simp only [CollatzResearch.WordTrace]
  refine ⟨34430107377096548330891021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22953404918064365553927347 34430107377096548330891021)
  ·
    refine ⟨12911290266411205624084133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34430107377096548330891021 12911290266411205624084133)
    ·
      refine ⟨2420866924952101054515775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12911290266411205624084133 2420866924952101054515775)
      ·
        refine ⟨3631300387428151581773663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420866924952101054515775 3631300387428151581773663)
        ·
          refine ⟨5446950581142227372660495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3631300387428151581773663 5446950581142227372660495)
          ·
            refine ⟨8170425871713341058990743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5446950581142227372660495 8170425871713341058990743)
            ·
              refine ⟨12255638807570011588486115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170425871713341058990743 12255638807570011588486115)
              ·
                refine ⟨18383458211355017382729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12255638807570011588486115 18383458211355017382729173)
                ·
                  refine ⟨430862301828633219907715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18383458211355017382729173 430862301828633219907715)
                  ·
                    rfl

theorem cell20_943989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_943989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943989 prefixEnd_943989 := by exact prefixLift 943989
  have htrace : WordTrace (prefixWord ++ tailWord_943989) baseStart_943989 baseEnd_943989 := by
    simpa [prefixWord, tailWord_943989, baseEnd_943989] using wordTrace_append hprefix tailTrace_943989
  have hstable : (prefixWord ++ tailWord_943989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943989).length < 2 ^ (prefixWord ++ tailWord_943989).sum := by decide
  have hdescent : baseEnd_943989 < baseStart_943989 := by decide
  rcases family_descends (prefixWord ++ tailWord_943989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944003 : List Nat := [1, 1, 1, 3, 4, 2, 8]
def baseStart_944003 : Nat := 118140960795 + 944003 * 2 ^ 59
def prefixEnd_944003 : Nat := 4983230072969 + 3 ^ 40 * 944003 * 2
def baseEnd_944003 : Nat := 47874299090012377048999

theorem tailTrace_944003 : CollatzResearch.WordTrace tailWord_944003 prefixEnd_944003 47874299090012377048999 := by
  unfold tailWord_944003
  simp only [CollatzResearch.WordTrace]
  refine ⟨34430617999045828721900663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22953745332697219147933775 34430617999045828721900663)
  ·
    refine ⟨51645926998568743082850995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34430617999045828721900663 51645926998568743082850995)
    ·
      refine ⟨77468890497853114624276493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51645926998568743082850995 77468890497853114624276493)
      ·
        refine ⟨29050833936694917984103685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77468890497853114624276493 29050833936694917984103685)
        ·
          refine ⟨5447031363130297122019441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29050833936694917984103685 5447031363130297122019441)
          ·
            refine ⟨4085273522347722841514581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5447031363130297122019441 4085273522347722841514581)
            ·
              refine ⟨47874299090012377048999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4085273522347722841514581 47874299090012377048999)
              ·
                rfl

theorem cell20_944003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_944003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944003 prefixEnd_944003 := by exact prefixLift 944003
  have htrace : WordTrace (prefixWord ++ tailWord_944003) baseStart_944003 baseEnd_944003 := by
    simpa [prefixWord, tailWord_944003, baseEnd_944003] using wordTrace_append hprefix tailTrace_944003
  have hstable : (prefixWord ++ tailWord_944003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944003).length < 2 ^ (prefixWord ++ tailWord_944003).sum := by decide
  have hdescent : baseEnd_944003 < baseStart_944003 := by decide
  rcases family_descends (prefixWord ++ tailWord_944003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944020 : List Nat := [2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_944020 : Nat := 118140960795 + 944020 * 2 ^ 59
def prefixEnd_944020 : Nat := 4983230072969 + 3 ^ 40 * 944020 * 2
def baseEnd_944020 : Nat := 143625483691111629958085

theorem tailTrace_944020 : CollatzResearch.WordTrace tailWord_944020 prefixEnd_944020 143625483691111629958085 := by
  unfold tailWord_944020
  simp only [CollatzResearch.WordTrace]
  refine ⟨17215619019992120312634757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22954158693322827083513009 17215619019992120312634757)
  ·
    refine ⟨3227928566248522558619017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17215619019992120312634757 3227928566248522558619017)
    ·
      refine ⟨2420946424686391918964263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3227928566248522558619017 2420946424686391918964263)
      ·
        refine ⟨3631419637029587878446395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420946424686391918964263 3631419637029587878446395)
        ·
          refine ⟨5447129455544381817669593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3631419637029587878446395 5447129455544381817669593)
          ·
            refine ⟨4085347091658286363252195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5447129455544381817669593 4085347091658286363252195)
            ·
              refine ⟨6128020637487429544878293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085347091658286363252195 6128020637487429544878293)
              ·
                refine ⟨143625483691111629958085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6128020637487429544878293 143625483691111629958085)
                ·
                  rfl

theorem cell20_944020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_944020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944020 prefixEnd_944020 := by exact prefixLift 944020
  have htrace : WordTrace (prefixWord ++ tailWord_944020) baseStart_944020 baseEnd_944020 := by
    simpa [prefixWord, tailWord_944020, baseEnd_944020] using wordTrace_append hprefix tailTrace_944020
  have hstable : (prefixWord ++ tailWord_944020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944020).length < 2 ^ (prefixWord ++ tailWord_944020).sum := by decide
  have hdescent : baseEnd_944020 < baseStart_944020 := by decide
  rcases family_descends (prefixWord ++ tailWord_944020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944023 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 3]
def baseStart_944023 : Nat := 118140960795 + 944023 * 2 ^ 59
def prefixEnd_944023 : Nat := 4983230072969 + 3 ^ 40 * 944023 * 2
def baseEnd_944023 : Nat := 430877820355080212774243

theorem tailTrace_944023 : CollatzResearch.WordTrace tailWord_944023 prefixEnd_944023 430877820355080212774243 := by
  unfold tailWord_944023
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431347458973372137628723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22954231639315581425085815 34431347458973372137628723)
  ·
    refine ⟨51647021188460058206443085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34431347458973372137628723 51647021188460058206443085)
    ·
      refine ⟨19367632945672521827416157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51647021188460058206443085 19367632945672521827416157)
      ·
        refine ⟨7262862354627195685281059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19367632945672521827416157 7262862354627195685281059)
        ·
          refine ⟨10894293531940793527921589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262862354627195685281059 10894293531940793527921589)
          ·
            refine ⟨1021340018619449393242649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10894293531940793527921589 1021340018619449393242649)
            ·
              refine ⟨766005013964587044931987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021340018619449393242649 766005013964587044931987)
              ·
                refine ⟨1149007520946880567397981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766005013964587044931987 1149007520946880567397981)
                ·
                  refine ⟨430877820355080212774243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149007520946880567397981 430877820355080212774243)
                  ·
                    rfl

theorem cell20_944023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_944023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944023 prefixEnd_944023 := by exact prefixLift 944023
  have htrace : WordTrace (prefixWord ++ tailWord_944023) baseStart_944023 baseEnd_944023 := by
    simpa [prefixWord, tailWord_944023, baseEnd_944023] using wordTrace_append hprefix tailTrace_944023
  have hstable : (prefixWord ++ tailWord_944023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944023).length < 2 ^ (prefixWord ++ tailWord_944023).sum := by decide
  have hdescent : baseEnd_944023 < baseStart_944023 := by decide
  rcases family_descends (prefixWord ++ tailWord_944023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944051 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 2]
def baseStart_944051 : Nat := 118140960795 + 944051 * 2 ^ 59
def prefixEnd_944051 : Nat := 4983230072969 + 3 ^ 40 * 944051 * 2
def baseEnd_944051 : Nat := 430890600318036559840795

theorem tailTrace_944051 : CollatzResearch.WordTrace tailWord_944051 prefixEnd_944051 430890600318036559840795 := by
  unfold tailWord_944051
  simp only [CollatzResearch.WordTrace]
  refine ⟨34432368702871932919648007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22954912468581288613098671 34432368702871932919648007)
  ·
    refine ⟨51648553054307899379472011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34432368702871932919648007 51648553054307899379472011)
    ·
      refine ⟨77472829581461849069208017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51648553054307899379472011 77472829581461849069208017)
      ·
        refine ⟨58104622186096386801906013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77472829581461849069208017 58104622186096386801906013)
        ·
          refine ⟨21789233319786145050714755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58104622186096386801906013 21789233319786145050714755)
          ·
            refine ⟨32683849979679217576072133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21789233319786145050714755 32683849979679217576072133)
            ·
              refine ⟨6128221871189853295513525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32683849979679217576072133 6128221871189853295513525)
              ·
                refine ⟨574520800424048746454393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6128221871189853295513525 574520800424048746454393)
                ·
                  refine ⟨430890600318036559840795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574520800424048746454393 430890600318036559840795)
                  ·
                    rfl

theorem cell20_944051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 2].length) (baseStart_944051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944051 prefixEnd_944051 := by exact prefixLift 944051
  have htrace : WordTrace (prefixWord ++ tailWord_944051) baseStart_944051 baseEnd_944051 := by
    simpa [prefixWord, tailWord_944051, baseEnd_944051] using wordTrace_append hprefix tailTrace_944051
  have hstable : (prefixWord ++ tailWord_944051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944051).length < 2 ^ (prefixWord ++ tailWord_944051).sum := by decide
  have hdescent : baseEnd_944051 < baseStart_944051 := by decide
  rcases family_descends (prefixWord ++ tailWord_944051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944089 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_944089 : Nat := 118140960795 + 944089 * 2 ^ 59
def prefixEnd_944089 : Nat := 4983230072969 + 3 ^ 40 * 944089 * 2
def baseEnd_944089 : Nat := 430907944553477316573973

theorem tailTrace_944089 : CollatzResearch.WordTrace tailWord_944089 prefixEnd_944089 430907944553477316573973 := by
  unfold tailWord_944089
  simp only [CollatzResearch.WordTrace]
  refine ⟨34433754676734265409531321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22955836451156176939687547 34433754676734265409531321)
  ·
    refine ⟨25825316007550699057148491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34433754676734265409531321 25825316007550699057148491)
    ·
      refine ⟨38737974011326048585722737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25825316007550699057148491 38737974011326048585722737)
      ·
        refine ⟨29053480508494536439292053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38737974011326048585722737 29053480508494536439292053)
        ·
          refine ⟨1361881898835681395591815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29053480508494536439292053 1361881898835681395591815)
          ·
            refine ⟨2042822848253522093387723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361881898835681395591815 2042822848253522093387723)
            ·
              refine ⟨3064234272380283140081585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042822848253522093387723 3064234272380283140081585)
              ·
                refine ⟨2298175704285212355061189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064234272380283140081585 2298175704285212355061189)
                ·
                  refine ⟨430907944553477316573973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2298175704285212355061189 430907944553477316573973)
                  ·
                    rfl

theorem cell20_944089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_944089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944089 prefixEnd_944089 := by exact prefixLift 944089
  have htrace : WordTrace (prefixWord ++ tailWord_944089) baseStart_944089 baseEnd_944089 := by
    simpa [prefixWord, tailWord_944089, baseEnd_944089] using wordTrace_append hprefix tailTrace_944089
  have hstable : (prefixWord ++ tailWord_944089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944089).length < 2 ^ (prefixWord ++ tailWord_944089).sum := by decide
  have hdescent : baseEnd_944089 < baseStart_944089 := by decide
  rcases family_descends (prefixWord ++ tailWord_944089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944106 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_944106 : Nat := 118140960795 + 944106 * 2 ^ 59
def prefixEnd_944106 : Nat := 4983230072969 + 3 ^ 40 * 944106 * 2
def baseEnd_944106 : Nat := 430915703816700813007237

theorem tailTrace_944106 : CollatzResearch.WordTrace tailWord_944106 prefixEnd_944106 430915703816700813007237 := by
  unfold tailWord_944106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8608593679418169328225043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22956249811781784875266781 8608593679418169328225043)
  ·
    refine ⟨12912890519127253992337565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8608593679418169328225043 12912890519127253992337565)
    ·
      refine ⟨4842333944672720247126587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12912890519127253992337565 4842333944672720247126587)
      ·
        refine ⟨7263500917009080370689881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4842333944672720247126587 7263500917009080370689881)
        ·
          refine ⟨5447625687756810278017411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7263500917009080370689881 5447625687756810278017411)
          ·
            refine ⟨8171438531635215417026117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447625687756810278017411 8171438531635215417026117)
            ·
              refine ⟨1532144724681602890692397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8171438531635215417026117 1532144724681602890692397)
              ·
                refine ⟨574554271755601084009649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1532144724681602890692397 574554271755601084009649)
                ·
                  refine ⟨430915703816700813007237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574554271755601084009649 430915703816700813007237)
                  ·
                    rfl

theorem cell20_944106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_944106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944106 prefixEnd_944106 := by exact prefixLift 944106
  have htrace : WordTrace (prefixWord ++ tailWord_944106) baseStart_944106 baseEnd_944106 := by
    simpa [prefixWord, tailWord_944106, baseEnd_944106] using wordTrace_append hprefix tailTrace_944106
  have hstable : (prefixWord ++ tailWord_944106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944106).length < 2 ^ (prefixWord ++ tailWord_944106).sum := by decide
  have hdescent : baseEnd_944106 < baseStart_944106 := by decide
  rcases family_descends (prefixWord ++ tailWord_944106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944161 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 2]
def baseStart_944161 : Nat := 118140960795 + 944161 * 2 ^ 59
def prefixEnd_944161 : Nat := 4983230072969 + 3 ^ 40 * 944161 * 2
def baseEnd_944161 : Nat := 430940807315365066173679

theorem tailTrace_944161 : CollatzResearch.WordTrace tailWord_944161 prefixEnd_944161 430940807315365066173679 := by
  unfold tailWord_944161
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436380732473421706152337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22957587154982281137434891 34436380732473421706152337)
  ·
    refine ⟨25827285549355066279614253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34436380732473421706152337 25827285549355066279614253)
    ·
      refine ⟨9685232081008149854855345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25827285549355066279614253 9685232081008149854855345)
      ·
        refine ⟨7263924060756112391141509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9685232081008149854855345 7263924060756112391141509)
        ·
          refine ⟨1361985761391771073339033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7263924060756112391141509 1361985761391771073339033)
          ·
            refine ⟨1021489321043828305004275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361985761391771073339033 1021489321043828305004275)
            ·
              refine ⟨1532233981565742457506413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021489321043828305004275 1532233981565742457506413)
              ·
                refine ⟨574587743087153421564905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1532233981565742457506413 574587743087153421564905)
                ·
                  refine ⟨430940807315365066173679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574587743087153421564905 430940807315365066173679)
                  ·
                    rfl

theorem cell20_944161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_944161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944161 prefixEnd_944161 := by exact prefixLift 944161
  have htrace : WordTrace (prefixWord ++ tailWord_944161) baseStart_944161 baseEnd_944161 := by
    simpa [prefixWord, tailWord_944161, baseEnd_944161] using wordTrace_append hprefix tailTrace_944161
  have hstable : (prefixWord ++ tailWord_944161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944161).length < 2 ^ (prefixWord ++ tailWord_944161).sum := by decide
  have hdescent : baseEnd_944161 < baseStart_944161 := by decide
  rcases family_descends (prefixWord ++ tailWord_944161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944168 : List Nat := [2, 1, 5, 3, 2, 1, 6]
def baseStart_944168 : Nat := 118140960795 + 944168 * 2 ^ 59
def prefixEnd_944168 : Nat := 4983230072969 + 3 ^ 40 * 944168 * 2
def baseEnd_944168 : Nat := 47882666922900461437813

theorem tailTrace_944168 : CollatzResearch.WordTrace tailWord_944168 prefixEnd_944168 47882666922900461437813 := by
  unfold tailWord_944168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218318021724030950828579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22957757362298707934438105 17218318021724030950828579)
  ·
    refine ⟨25827477032586046426242869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17218318021724030950828579 25827477032586046426242869)
    ·
      refine ⟨2421325971804941852460269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25827477032586046426242869 2421325971804941852460269)
      ·
        refine ⟨907997239426853194672601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2421325971804941852460269 907997239426853194672601)
        ·
          refine ⟨680997929570139896004451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907997239426853194672601 680997929570139896004451)
          ·
            refine ⟨1021496894355209844006677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680997929570139896004451 1021496894355209844006677)
            ·
              refine ⟨47882666922900461437813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1021496894355209844006677 47882666922900461437813)
              ·
                rfl

theorem cell20_944168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 6].length) (baseStart_944168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944168 prefixEnd_944168 := by exact prefixLift 944168
  have htrace : WordTrace (prefixWord ++ tailWord_944168) baseStart_944168 baseEnd_944168 := by
    simpa [prefixWord, tailWord_944168, baseEnd_944168] using wordTrace_append hprefix tailTrace_944168
  have hstable : (prefixWord ++ tailWord_944168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944168).length < 2 ^ (prefixWord ++ tailWord_944168).sum := by decide
  have hdescent : baseEnd_944168 < baseStart_944168 := by decide
  rcases family_descends (prefixWord ++ tailWord_944168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944200 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_944200 : Nat := 118140960795 + 944200 * 2 ^ 59
def prefixEnd_944200 : Nat := 4983230072969 + 3 ^ 40 * 944200 * 2
def baseEnd_944200 : Nat := 430958607978054263873519

theorem tailTrace_944200 : CollatzResearch.WordTrace tailWord_944200 prefixEnd_944200 430958607978054263873519 := by
  unfold tailWord_944200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218901589666065683411027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22958535452888087577881369 17218901589666065683411027)
  ·
    refine ⟨25828352384499098525116541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17218901589666065683411027 25828352384499098525116541)
    ·
      refine ⟨9685632144187161946918703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25828352384499098525116541 9685632144187161946918703)
      ·
        refine ⟨14528448216280742920378055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685632144187161946918703 14528448216280742920378055)
        ·
          refine ⟨21792672324421114380567083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528448216280742920378055 21792672324421114380567083)
          ·
            refine ⟨32689008486631671570850625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21792672324421114380567083 32689008486631671570850625)
            ·
              refine ⟨24516756364973753678137969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32689008486631671570850625 24516756364973753678137969)
              ·
                refine ⟨18387567273730315258603477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24516756364973753678137969 18387567273730315258603477)
                ·
                  refine ⟨430958607978054263873519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18387567273730315258603477 430958607978054263873519)
                  ·
                    rfl

theorem cell20_944200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_944200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944200 prefixEnd_944200 := by exact prefixLift 944200
  have htrace : WordTrace (prefixWord ++ tailWord_944200) baseStart_944200 baseEnd_944200 := by
    simpa [prefixWord, tailWord_944200, baseEnd_944200] using wordTrace_append hprefix tailTrace_944200
  have hstable : (prefixWord ++ tailWord_944200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944200).length < 2 ^ (prefixWord ++ tailWord_944200).sum := by decide
  have hdescent : baseEnd_944200 < baseStart_944200 := by decide
  rcases family_descends (prefixWord ++ tailWord_944200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944241 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 2]
def baseStart_944241 : Nat := 118140960795 + 944241 * 2 ^ 59
def prefixEnd_944241 : Nat := 4983230072969 + 3 ^ 40 * 944241 * 2
def baseEnd_944241 : Nat := 430977321495240343506685

theorem tailTrace_944241 : CollatzResearch.WordTrace tailWord_944241 prefixEnd_944241 430977321495240343506685 := by
  unfold tailWord_944241
  simp only [CollatzResearch.WordTrace]
  refine ⟨34439298572183595369064577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22959532381455730246043051 34439298572183595369064577)
  ·
    refine ⟨25829473929137696526798433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34439298572183595369064577 25829473929137696526798433)
    ·
      refine ⟨19372105446853272395098825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25829473929137696526798433 19372105446853272395098825)
      ·
        refine ⟨14529079085139954296324119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19372105446853272395098825 14529079085139954296324119)
        ·
          refine ⟨21793618627709931444486179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14529079085139954296324119 21793618627709931444486179)
          ·
            refine ⟨32690427941564897166729269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21793618627709931444486179 32690427941564897166729269)
            ·
              refine ⟨3064727619521709109380869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32690427941564897166729269 3064727619521709109380869)
              ·
                refine ⟨574636428660320458008913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3064727619521709109380869 574636428660320458008913)
                ·
                  refine ⟨430977321495240343506685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574636428660320458008913 430977321495240343506685)
                  ·
                    rfl

theorem cell20_944241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_944241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944241 prefixEnd_944241 := by exact prefixLift 944241
  have htrace : WordTrace (prefixWord ++ tailWord_944241) baseStart_944241 baseEnd_944241 := by
    simpa [prefixWord, tailWord_944241, baseEnd_944241] using wordTrace_append hprefix tailTrace_944241
  have hstable : (prefixWord ++ tailWord_944241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944241).length < 2 ^ (prefixWord ++ tailWord_944241).sum := by decide
  have hdescent : baseEnd_944241 < baseStart_944241 := by decide
  rcases family_descends (prefixWord ++ tailWord_944241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944283 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_944283 : Nat := 118140960795 + 944283 * 2 ^ 59
def prefixEnd_944283 : Nat := 4983230072969 + 3 ^ 40 * 944283 * 2
def baseEnd_944283 : Nat := 430996491439674864106513

theorem tailTrace_944283 : CollatzResearch.WordTrace tailWord_944283 prefixEnd_944283 430996491439674864106513 := by
  unfold tailWord_944283
  simp only [CollatzResearch.WordTrace]
  refine ⟨34440830438031436542093503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22960553625354291028062335 34440830438031436542093503)
  ·
    refine ⟨51661245657047154813140255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34440830438031436542093503 51661245657047154813140255)
    ·
      refine ⟨77491868485570732219710383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51661245657047154813140255 77491868485570732219710383)
      ·
        refine ⟨116237802728356098329565575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77491868485570732219710383 116237802728356098329565575)
        ·
          refine ⟨174356704092534147494348363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116237802728356098329565575 174356704092534147494348363)
          ·
            refine ⟨261535056138801221241522545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174356704092534147494348363 261535056138801221241522545)
            ·
              refine ⟨196151292104100915931141909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261535056138801221241522545 196151292104100915931141909)
              ·
                refine ⟨9194591817379730434272277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196151292104100915931141909 9194591817379730434272277)
                ·
                  refine ⟨430996491439674864106513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9194591817379730434272277 430996491439674864106513)
                  ·
                    rfl

theorem cell20_944283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_944283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944283 prefixEnd_944283 := by exact prefixLift 944283
  have htrace : WordTrace (prefixWord ++ tailWord_944283) baseStart_944283 baseEnd_944283 := by
    simpa [prefixWord, tailWord_944283, baseEnd_944283] using wordTrace_append hprefix tailTrace_944283
  have hstable : (prefixWord ++ tailWord_944283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944283).length < 2 ^ (prefixWord ++ tailWord_944283).sum := by decide
  have hdescent : baseEnd_944283 < baseStart_944283 := by decide
  rcases family_descends (prefixWord ++ tailWord_944283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944324 : List Nat := [2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_944324 : Nat := 118140960795 + 944324 * 2 ^ 59
def prefixEnd_944324 : Nat := 4983230072969 + 3 ^ 40 * 944324 * 2
def baseEnd_944324 : Nat := 143671734985620314579893

theorem tailTrace_944324 : CollatzResearch.WordTrace tailWord_944324 prefixEnd_944324 143671734985620314579893 := by
  unfold tailWord_944324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221162915441450272168013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22961550553921933696224017 17221162915441450272168013)
  ·
    refine ⟨6457936093290543852063005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17221162915441450272168013 6457936093290543852063005)
    ·
      refine ⟨2421726034983953944523627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6457936093290543852063005 2421726034983953944523627)
      ·
        refine ⟨3632589052475930916785441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421726034983953944523627 3632589052475930916785441)
        ·
          refine ⟨2724441789356948187589081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632589052475930916785441 2724441789356948187589081)
          ·
            refine ⟨2043331342017711140691811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2724441789356948187589081 2043331342017711140691811)
            ·
              refine ⟨3064997013026566711037717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043331342017711140691811 3064997013026566711037717)
              ·
                refine ⟨143671734985620314579893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3064997013026566711037717 143671734985620314579893)
                ·
                  rfl

theorem cell20_944324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_944324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944324 prefixEnd_944324 := by exact prefixLift 944324
  have htrace : WordTrace (prefixWord ++ tailWord_944324) baseStart_944324 baseEnd_944324 := by
    simpa [prefixWord, tailWord_944324, baseEnd_944324] using wordTrace_append hprefix tailTrace_944324
  have hstable : (prefixWord ++ tailWord_944324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944324).length < 2 ^ (prefixWord ++ tailWord_944324).sum := by decide
  have hdescent : baseEnd_944324 < baseStart_944324 := by decide
  rcases family_descends (prefixWord ++ tailWord_944324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944334 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_944334 : Nat := 118140960795 + 944334 * 2 ^ 59
def prefixEnd_944334 : Nat := 4983230072969 + 3 ^ 40 * 944334 * 2
def baseEnd_944334 : Nat := 431019769229345353406305

theorem tailTrace_944334 : CollatzResearch.WordTrace tailWord_944334 prefixEnd_944334 431019769229345353406305 := by
  unfold tailWord_944334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305336320105834031525007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22961793707231114834800037 4305336320105834031525007)
  ·
    refine ⟨6458004480158751047287511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4305336320105834031525007 6458004480158751047287511)
    ·
      refine ⟨9687006720238126570931267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6458004480158751047287511 9687006720238126570931267)
      ·
        refine ⟨14530510080357189856396901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687006720238126570931267 14530510080357189856396901)
        ·
          refine ⟨2724470640066973098074419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14530510080357189856396901 2724470640066973098074419)
          ·
            refine ⟨4086705960100459647111629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724470640066973098074419 4086705960100459647111629)
            ·
              refine ⟨1532514735037672367666861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4086705960100459647111629 1532514735037672367666861)
              ·
                refine ⟨574693025639127137875073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1532514735037672367666861 574693025639127137875073)
                ·
                  refine ⟨431019769229345353406305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574693025639127137875073 431019769229345353406305)
                  ·
                    rfl

theorem cell20_944334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_944334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944334 prefixEnd_944334 := by exact prefixLift 944334
  have htrace : WordTrace (prefixWord ++ tailWord_944334) baseStart_944334 baseEnd_944334 := by
    simpa [prefixWord, tailWord_944334, baseEnd_944334] using wordTrace_append hprefix tailTrace_944334
  have hstable : (prefixWord ++ tailWord_944334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944334).length < 2 ^ (prefixWord ++ tailWord_944334).sum := by decide
  have hdescent : baseEnd_944334 < baseStart_944334 := by decide
  rcases family_descends (prefixWord ++ tailWord_944334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944341 : List Nat := [1, 3, 2, 4, 3, 1, 6]
def baseStart_944341 : Nat := 118140960795 + 944341 * 2 ^ 59
def prefixEnd_944341 : Nat := 4983230072969 + 3 ^ 40 * 944341 * 2
def baseEnd_944341 : Nat := 47891440468898271130327

theorem tailTrace_944341 : CollatzResearch.WordTrace tailWord_944341 prefixEnd_944341 47891440468898271130327 := by
  unfold tailWord_944341
  simp only [CollatzResearch.WordTrace]
  refine ⟨34442945871821312447704877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22961963914547541631803251 34442945871821312447704877)
  ·
    refine ⟨12916104701932992167889329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34442945871821312447704877 12916104701932992167889329)
    ·
      refine ⟨9687078526449744125916997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12916104701932992167889329 9687078526449744125916997)
      ·
        refine ⟨1816327223709327023609437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9687078526449744125916997 1816327223709327023609437)
        ·
          refine ⟨681122708890997633853539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1816327223709327023609437 681122708890997633853539)
          ·
            refine ⟨1021684063336496450780309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681122708890997633853539 1021684063336496450780309)
            ·
              refine ⟨47891440468898271130327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1021684063336496450780309 47891440468898271130327)
              ·
                rfl

theorem cell20_944341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 6].length) (baseStart_944341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944341 prefixEnd_944341 := by exact prefixLift 944341
  have htrace : WordTrace (prefixWord ++ tailWord_944341) baseStart_944341 baseEnd_944341 := by
    simpa [prefixWord, tailWord_944341, baseEnd_944341] using wordTrace_append hprefix tailTrace_944341
  have hstable : (prefixWord ++ tailWord_944341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944341).length < 2 ^ (prefixWord ++ tailWord_944341).sum := by decide
  have hdescent : baseEnd_944341 < baseStart_944341 := by decide
  rcases family_descends (prefixWord ++ tailWord_944341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944352 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_944352 : Nat := 118140960795 + 944352 * 2 ^ 59
def prefixEnd_944352 : Nat := 4983230072969 + 3 ^ 40 * 944352 * 2
def baseEnd_944352 : Nat := 431027984919817290806231

theorem tailTrace_944352 : CollatzResearch.WordTrace tailWord_944352 prefixEnd_944352 431027984919817290806231 := by
  unfold tailWord_944352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221673537390730663177655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22962231383187640884236873 17221673537390730663177655)
  ·
    refine ⟨25832510306086095994766483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17221673537390730663177655 25832510306086095994766483)
    ·
      refine ⟨38748765459129143992149725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25832510306086095994766483 38748765459129143992149725)
      ·
        refine ⟨14530787047173428997056147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38748765459129143992149725 14530787047173428997056147)
        ·
          refine ⟨21796180570760143495584221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14530787047173428997056147 21796180570760143495584221)
          ·
            refine ⟨8173567714035053810844083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21796180570760143495584221 8173567714035053810844083)
            ·
              refine ⟨12260351571052580716266125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173567714035053810844083 12260351571052580716266125)
              ·
                refine ⟨4597631839144717768599797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12260351571052580716266125 4597631839144717768599797)
                ·
                  refine ⟨431027984919817290806231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4597631839144717768599797 431027984919817290806231)
                  ·
                    rfl

theorem cell20_944352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_944352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944352 prefixEnd_944352 := by exact prefixLift 944352
  have htrace : WordTrace (prefixWord ++ tailWord_944352) baseStart_944352 baseEnd_944352 := by
    simpa [prefixWord, tailWord_944352, baseEnd_944352] using wordTrace_append hprefix tailTrace_944352
  have hstable : (prefixWord ++ tailWord_944352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944352).length < 2 ^ (prefixWord ++ tailWord_944352).sum := by decide
  have hdescent : baseEnd_944352 < baseStart_944352 := by decide
  rcases family_descends (prefixWord ++ tailWord_944352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944407 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_944407 : Nat := 118140960795 + 944407 * 2 ^ 59
def prefixEnd_944407 : Nat := 4983230072969 + 3 ^ 40 * 944407 * 2
def baseEnd_944407 : Nat := 431053088418481543972673

theorem tailTrace_944407 : CollatzResearch.WordTrace tailWord_944407 prefixEnd_944407 431053088418481543972673 := by
  unfold tailWord_944407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34445353089582205719607475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22963568726388137146404983 34445353089582205719607475)
  ·
    refine ⟨51668029634373308579411213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34445353089582205719607475 51668029634373308579411213)
    ·
      refine ⟨19375511112889990717279205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51668029634373308579411213 19375511112889990717279205)
      ·
        refine ⟨3632908333666873259489851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19375511112889990717279205 3632908333666873259489851)
        ·
          refine ⟨5449362500500309889234777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632908333666873259489851 5449362500500309889234777)
          ·
            refine ⟨4087021875375232416926083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5449362500500309889234777 4087021875375232416926083)
            ·
              refine ⟨6130532813062848625389125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087021875375232416926083 6130532813062848625389125)
              ·
                refine ⟨1149474902449284117260461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6130532813062848625389125 1149474902449284117260461)
                ·
                  refine ⟨431053088418481543972673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149474902449284117260461 431053088418481543972673)
                  ·
                    rfl

theorem cell20_944407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_944407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944407 prefixEnd_944407 := by exact prefixLift 944407
  have htrace : WordTrace (prefixWord ++ tailWord_944407) baseStart_944407 baseEnd_944407 := by
    simpa [prefixWord, tailWord_944407, baseEnd_944407] using wordTrace_append hprefix tailTrace_944407
  have hstable : (prefixWord ++ tailWord_944407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944407).length < 2 ^ (prefixWord ++ tailWord_944407).sum := by decide
  have hdescent : baseEnd_944407 < baseStart_944407 := by decide
  rcases family_descends (prefixWord ++ tailWord_944407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944410 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_944410 : Nat := 118140960795 + 944410 * 2 ^ 59
def prefixEnd_944410 : Nat := 4983230072969 + 3 ^ 40 * 944410 * 2
def baseEnd_944410 : Nat := 431054457700226866872661

theorem tailTrace_944410 : CollatzResearch.WordTrace tailWord_944410 prefixEnd_944410 431054457700226866872661 := by
  unfold tailWord_944410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611365627142834307991671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22963641672380891487977789 8611365627142834307991671)
  ·
    refine ⟨12917048440714251461987507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8611365627142834307991671 12917048440714251461987507)
    ·
      refine ⟨19375572661071377192981261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12917048440714251461987507 19375572661071377192981261)
      ·
        refine ⟨7265839747901766447367973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19375572661071377192981261 7265839747901766447367973)
        ·
          refine ⟨1362344952731581208881495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7265839747901766447367973 1362344952731581208881495)
          ·
            refine ⟨2043517429097371813322243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362344952731581208881495 2043517429097371813322243)
            ·
              refine ⟨3065276143646057719983365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043517429097371813322243 3065276143646057719983365)
              ·
                refine ⟨574739276933635822496881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3065276143646057719983365 574739276933635822496881)
                ·
                  refine ⟨431054457700226866872661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574739276933635822496881 431054457700226866872661)
                  ·
                    rfl

theorem cell20_944410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_944410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944410 prefixEnd_944410 := by exact prefixLift 944410
  have htrace : WordTrace (prefixWord ++ tailWord_944410) baseStart_944410 baseEnd_944410 := by
    simpa [prefixWord, tailWord_944410, baseEnd_944410] using wordTrace_append hprefix tailTrace_944410
  have hstable : (prefixWord ++ tailWord_944410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944410).length < 2 ^ (prefixWord ++ tailWord_944410).sum := by decide
  have hdescent : baseEnd_944410 < baseStart_944410 := by decide
  rcases family_descends (prefixWord ++ tailWord_944410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944469 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_944469 : Nat := 118140960795 + 944469 * 2 ^ 59
def prefixEnd_944469 : Nat := 4983230072969 + 3 ^ 40 * 944469 * 2
def baseEnd_944469 : Nat := 431081386907884883905753

theorem tailTrace_944469 : CollatzResearch.WordTrace tailWord_944469 prefixEnd_944469 431081386907884883905753 := by
  unfold tailWord_944469
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447614415357590308364461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22965076276905060205576307 34447614415357590308364461)
  ·
    refine ⟨12917855405759096365636673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34447614415357590308364461 12917855405759096365636673)
    ·
      refine ⟨9688391554319322274227505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12917855405759096365636673 9688391554319322274227505)
      ·
        refine ⟨7266293665739491705670629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9688391554319322274227505 7266293665739491705670629)
        ·
          refine ⟨1362430062326154694813243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7266293665739491705670629 1362430062326154694813243)
          ·
            refine ⟨2043645093489232042219865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362430062326154694813243 2043645093489232042219865)
            ·
              refine ⟨1532733820116924031664899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043645093489232042219865 1532733820116924031664899)
              ·
                refine ⟨2299100730175386047497349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532733820116924031664899 2299100730175386047497349)
                ·
                  refine ⟨431081386907884883905753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299100730175386047497349 431081386907884883905753)
                  ·
                    rfl

theorem cell20_944469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_944469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944469 prefixEnd_944469 := by exact prefixLift 944469
  have htrace : WordTrace (prefixWord ++ tailWord_944469) baseStart_944469 baseEnd_944469 := by
    simpa [prefixWord, tailWord_944469, baseEnd_944469] using wordTrace_append hprefix tailTrace_944469
  have hstable : (prefixWord ++ tailWord_944469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944469).length < 2 ^ (prefixWord ++ tailWord_944469).sum := by decide
  have hdescent : baseEnd_944469 < baseStart_944469 := by decide
  rcases family_descends (prefixWord ++ tailWord_944469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944507 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 2]
def baseStart_944507 : Nat := 118140960795 + 944507 * 2 ^ 59
def prefixEnd_944507 : Nat := 4983230072969 + 3 ^ 40 * 944507 * 2
def baseEnd_944507 : Nat := 431098731143325640638931

theorem tailTrace_944507 : CollatzResearch.WordTrace tailWord_944507 prefixEnd_944507 431098731143325640638931 := by
  unfold tailWord_944507
  simp only [CollatzResearch.WordTrace]
  refine ⟨34449000389219922798247775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22966000259479948532165183 34449000389219922798247775)
  ·
    refine ⟨51673500583829884197371663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34449000389219922798247775 51673500583829884197371663)
    ·
      refine ⟨77510250875744826296057495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51673500583829884197371663 77510250875744826296057495)
      ·
        refine ⟨116265376313617239444086243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77510250875744826296057495 116265376313617239444086243)
        ·
          refine ⟨174398064470425859166129365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116265376313617239444086243 174398064470425859166129365)
          ·
            refine ⟨4087454636025606074206157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 174398064470425859166129365 4087454636025606074206157)
            ·
              refine ⟨1532795488509602277827309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4087454636025606074206157 1532795488509602277827309)
              ·
                refine ⟨574798308191100854185241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1532795488509602277827309 574798308191100854185241)
                ·
                  refine ⟨431098731143325640638931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574798308191100854185241 431098731143325640638931)
                  ·
                    rfl

theorem cell20_944507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 2].length) (baseStart_944507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944507 prefixEnd_944507 := by exact prefixLift 944507
  have htrace : WordTrace (prefixWord ++ tailWord_944507) baseStart_944507 baseEnd_944507 := by
    simpa [prefixWord, tailWord_944507, baseEnd_944507] using wordTrace_append hprefix tailTrace_944507
  have hstable : (prefixWord ++ tailWord_944507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944507).length < 2 ^ (prefixWord ++ tailWord_944507).sum := by decide
  have hdescent : baseEnd_944507 < baseStart_944507 := by decide
  rcases family_descends (prefixWord ++ tailWord_944507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944524 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 2]
def baseStart_944524 : Nat := 118140960795 + 944524 * 2 ^ 59
def prefixEnd_944524 : Nat := 4983230072969 + 3 ^ 40 * 944524 * 2
def baseEnd_944524 : Nat := 431106490406549137072195

theorem tailTrace_944524 : CollatzResearch.WordTrace tailWord_944524 prefixEnd_944524 431106490406549137072195 := by
  unfold tailWord_944524
  simp only [CollatzResearch.WordTrace]
  refine ⟨17224810215079167350808313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22966413620105556467744417 17224810215079167350808313)
  ·
    refine ⟨12918607661309375513106235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17224810215079167350808313 12918607661309375513106235)
    ·
      refine ⟨19377911491964063269659353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12918607661309375513106235 19377911491964063269659353)
      ·
        refine ⟨14533433618973047452244515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19377911491964063269659353 14533433618973047452244515)
        ·
          refine ⟨21800150428459571178366773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14533433618973047452244515 21800150428459571178366773)
          ·
            refine ⟨2043764102668084797971885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21800150428459571178366773 2043764102668084797971885)
            ·
              refine ⟨766411538500531799239457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2043764102668084797971885 766411538500531799239457)
              ·
                refine ⟨574808653875398849429593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766411538500531799239457 574808653875398849429593)
                ·
                  refine ⟨431106490406549137072195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574808653875398849429593 431106490406549137072195)
                  ·
                    rfl

theorem cell20_944524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_944524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944524 prefixEnd_944524 := by exact prefixLift 944524
  have htrace : WordTrace (prefixWord ++ tailWord_944524) baseStart_944524 baseEnd_944524 := by
    simpa [prefixWord, tailWord_944524, baseEnd_944524] using wordTrace_append hprefix tailTrace_944524
  have hstable : (prefixWord ++ tailWord_944524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944524).length < 2 ^ (prefixWord ++ tailWord_944524).sum := by decide
  have hdescent : baseEnd_944524 < baseStart_944524 := by decide
  rcases family_descends (prefixWord ++ tailWord_944524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944538 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_944538 : Nat := 118140960795 + 944538 * 2 ^ 59
def prefixEnd_944538 : Nat := 4983230072969 + 3 ^ 40 * 944538 * 2
def baseEnd_944538 : Nat := 431112880388027310605471

theorem tailTrace_944538 : CollatzResearch.WordTrace tailWord_944538 prefixEnd_944538 431112880388027310605471 := by
  unfold tailWord_944538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612532763026903773156567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22966754034738410061750845 8612532763026903773156567)
  ·
    refine ⟨12918799144540355659734851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8612532763026903773156567 12918799144540355659734851)
    ·
      refine ⟨19378198716810533489602277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12918799144540355659734851 19378198716810533489602277)
      ·
        refine ⟨3633412259401975029300427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19378198716810533489602277 3633412259401975029300427)
        ·
          refine ⟨5450118389102962543950641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633412259401975029300427 5450118389102962543950641)
          ·
            refine ⟨4087588791827221907962981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450118389102962543950641 4087588791827221907962981)
            ·
              refine ⟨766422898467604107743059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4087588791827221907962981 766422898467604107743059)
              ·
                refine ⟨1149634347701406161614589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766422898467604107743059 1149634347701406161614589)
                ·
                  refine ⟨431112880388027310605471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149634347701406161614589 431112880388027310605471)
                  ·
                    rfl

theorem cell20_944538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_944538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944538 prefixEnd_944538 := by exact prefixLift 944538
  have htrace : WordTrace (prefixWord ++ tailWord_944538) baseStart_944538 baseEnd_944538 := by
    simpa [prefixWord, tailWord_944538, baseEnd_944538] using wordTrace_append hprefix tailTrace_944538
  have hstable : (prefixWord ++ tailWord_944538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944538).length < 2 ^ (prefixWord ++ tailWord_944538).sum := by decide
  have hdescent : baseEnd_944538 < baseStart_944538 := by decide
  rcases family_descends (prefixWord ++ tailWord_944538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944549 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_944549 : Nat := 118140960795 + 944549 * 2 ^ 59
def prefixEnd_944549 : Nat := 4983230072969 + 3 ^ 40 * 944549 * 2
def baseEnd_944549 : Nat := 431117901087760161238759

theorem tailTrace_944549 : CollatzResearch.WordTrace tailWord_944549 prefixEnd_944549 431117901087760161238759 := by
  unfold tailWord_944549
  simp only [CollatzResearch.WordTrace]
  refine ⟨34450532255067763971276701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22967021503378509314184467 34450532255067763971276701)
  ·
    refine ⟨12918949595650411489228763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34450532255067763971276701 12918949595650411489228763)
    ·
      refine ⟨19378424393475617233843145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12918949595650411489228763 19378424393475617233843145)
      ·
        refine ⟨14533818295106712925382359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19378424393475617233843145 14533818295106712925382359)
        ·
          refine ⟨21800727442660069388073539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14533818295106712925382359 21800727442660069388073539)
          ·
            refine ⟨32701091163990104082110309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21800727442660069388073539 32701091163990104082110309)
            ·
              refine ⟨6131454593248144515395683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32701091163990104082110309 6131454593248144515395683)
              ·
                refine ⟨9197181889872216773093525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131454593248144515395683 9197181889872216773093525)
                ·
                  refine ⟨431117901087760161238759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9197181889872216773093525 431117901087760161238759)
                  ·
                    rfl

theorem cell20_944549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_944549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944549 prefixEnd_944549 := by exact prefixLift 944549
  have htrace : WordTrace (prefixWord ++ tailWord_944549) baseStart_944549 baseEnd_944549 := by
    simpa [prefixWord, tailWord_944549, baseEnd_944549] using wordTrace_append hprefix tailTrace_944549
  have hstable : (prefixWord ++ tailWord_944549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944549).length < 2 ^ (prefixWord ++ tailWord_944549).sum := by decide
  have hdescent : baseEnd_944549 < baseStart_944549 := by decide
  rcases family_descends (prefixWord ++ tailWord_944549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944552 : List Nat := [2, 1, 6, 1, 1, 1, 2, 6]
def baseStart_944552 : Nat := 118140960795 + 944552 * 2 ^ 59
def prefixEnd_944552 : Nat := 4983230072969 + 3 ^ 40 * 944552 * 2
def baseEnd_944552 : Nat := 143706423456501828046249

theorem tailTrace_944552 : CollatzResearch.WordTrace tailWord_944552 prefixEnd_944552 143706423456501828046249 := by
  unfold tailWord_944552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17225320837028447741817955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22967094449371263655757273 17225320837028447741817955)
  ·
    refine ⟨25837981255542671612726933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17225320837028447741817955 25837981255542671612726933)
    ·
      refine ⟨1211155371353562731846575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25837981255542671612726933 1211155371353562731846575)
      ·
        refine ⟨1816733057030344097769863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211155371353562731846575 1816733057030344097769863)
        ·
          refine ⟨2725099585545516146654795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816733057030344097769863 2725099585545516146654795)
          ·
            refine ⟨4087649378318274219982193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725099585545516146654795 4087649378318274219982193)
            ·
              refine ⟨3065737033738705664986645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087649378318274219982193 3065737033738705664986645)
              ·
                refine ⟨143706423456501828046249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3065737033738705664986645 143706423456501828046249)
                ·
                  rfl

theorem cell20_944552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_944552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944552 prefixEnd_944552 := by exact prefixLift 944552
  have htrace : WordTrace (prefixWord ++ tailWord_944552) baseStart_944552 baseEnd_944552 := by
    simpa [prefixWord, tailWord_944552, baseEnd_944552] using wordTrace_append hprefix tailTrace_944552
  have hstable : (prefixWord ++ tailWord_944552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944552).length < 2 ^ (prefixWord ++ tailWord_944552).sum := by decide
  have hdescent : baseEnd_944552 < baseStart_944552 := by decide
  rcases family_descends (prefixWord ++ tailWord_944552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944583 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 2]
def baseStart_944583 : Nat := 118140960795 + 944583 * 2 ^ 59
def prefixEnd_944583 : Nat := 4983230072969 + 3 ^ 40 * 944583 * 2
def baseEnd_944583 : Nat := 431133419614207154105287

theorem tailTrace_944583 : CollatzResearch.WordTrace tailWord_944583 prefixEnd_944583 431133419614207154105287 := by
  unfold tailWord_944583
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451772336944587778014403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22967848224629725185342935 34451772336944587778014403)
  ·
    refine ⟨51677658505416881667021605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34451772336944587778014403 51677658505416881667021605)
    ·
      refine ⟨9689560969765665312566551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51677658505416881667021605 9689560969765665312566551)
      ·
        refine ⟨14534341454648497968849827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9689560969765665312566551 14534341454648497968849827)
        ·
          refine ⟨21801512181972746953274741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14534341454648497968849827 21801512181972746953274741)
          ·
            refine ⟨2043891767059945026869507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21801512181972746953274741 2043891767059945026869507)
            ·
              refine ⟨3065837650589917540304261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043891767059945026869507 3065837650589917540304261)
              ·
                refine ⟨574844559485609538807049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3065837650589917540304261 574844559485609538807049)
                ·
                  refine ⟨431133419614207154105287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574844559485609538807049 431133419614207154105287)
                  ·
                    rfl

theorem cell20_944583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 2].length) (baseStart_944583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944583 prefixEnd_944583 := by exact prefixLift 944583
  have htrace : WordTrace (prefixWord ++ tailWord_944583) baseStart_944583 baseEnd_944583 := by
    simpa [prefixWord, tailWord_944583, baseEnd_944583] using wordTrace_append hprefix tailTrace_944583
  have hstable : (prefixWord ++ tailWord_944583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944583).length < 2 ^ (prefixWord ++ tailWord_944583).sum := by decide
  have hdescent : baseEnd_944583 < baseStart_944583 := by decide
  rcases family_descends (prefixWord ++ tailWord_944583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944587 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_944587 : Nat := 118140960795 + 944587 * 2 ^ 59
def prefixEnd_944587 : Nat := 4983230072969 + 3 ^ 40 * 944587 * 2
def baseEnd_944587 : Nat := 431135245323200917971937

theorem tailTrace_944587 : CollatzResearch.WordTrace tailWord_944587 prefixEnd_944587 431135245323200917971937 := by
  unfold tailWord_944587
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451918228930096461160015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22967945485953397640773343 34451918228930096461160015)
  ·
    refine ⟨51677877343395144691740023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34451918228930096461160015 51677877343395144691740023)
    ·
      refine ⟨77516816015092717037610035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51677877343395144691740023 77516816015092717037610035)
      ·
        refine ⟨116275224022639075556415053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77516816015092717037610035 116275224022639075556415053)
        ·
          refine ⟨43603209008489653333655645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116275224022639075556415053 43603209008489653333655645)
          ·
            refine ⟨16351203378183620000120867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43603209008489653333655645 16351203378183620000120867)
            ·
              refine ⟨24526805067275430000181301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16351203378183620000120867 24526805067275430000181301)
              ·
                refine ⟨2299387975057071562516997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24526805067275430000181301 2299387975057071562516997)
                ·
                  refine ⟨431135245323200917971937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299387975057071562516997 431135245323200917971937)
                  ·
                    rfl

theorem cell20_944587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_944587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944587 prefixEnd_944587 := by exact prefixLift 944587
  have htrace : WordTrace (prefixWord ++ tailWord_944587) baseStart_944587 baseEnd_944587 := by
    simpa [prefixWord, tailWord_944587, baseEnd_944587] using wordTrace_append hprefix tailTrace_944587
  have hstable : (prefixWord ++ tailWord_944587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944587).length < 2 ^ (prefixWord ++ tailWord_944587).sum := by decide
  have hdescent : baseEnd_944587 < baseStart_944587 := by decide
  rcases family_descends (prefixWord ++ tailWord_944587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944597 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_944597 : Nat := 118140960795 + 944597 * 2 ^ 59
def prefixEnd_944597 : Nat := 4983230072969 + 3 ^ 40 * 944597 * 2
def baseEnd_944597 : Nat := 431139809595685327638563

theorem tailTrace_944597 : CollatzResearch.WordTrace tailWord_944597 prefixEnd_944597 431139809595685327638563 := by
  unfold tailWord_944597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34452282958893868169024045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22968188639262578779349363 34452282958893868169024045)
  ·
    refine ⟨12919606109585200563384017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34452282958893868169024045 12919606109585200563384017)
    ·
      refine ⟨9689704582188900422538013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12919606109585200563384017 9689704582188900422538013)
      ·
        refine ⟨3633639218320837658451755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9689704582188900422538013 3633639218320837658451755)
        ·
          refine ⟨5450458827481256487677633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633639218320837658451755 5450458827481256487677633)
          ·
            refine ⟨4087844120610942365758225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450458827481256487677633 4087844120610942365758225)
            ·
              refine ⟨3065883090458206774318669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087844120610942365758225 3065883090458206774318669)
              ·
                refine ⟨1149706158921827540369501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3065883090458206774318669 1149706158921827540369501)
                ·
                  refine ⟨431139809595685327638563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149706158921827540369501 431139809595685327638563)
                  ·
                    rfl

theorem cell20_944597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_944597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944597 prefixEnd_944597 := by exact prefixLift 944597
  have htrace : WordTrace (prefixWord ++ tailWord_944597) baseStart_944597 baseEnd_944597 := by
    simpa [prefixWord, tailWord_944597, baseEnd_944597] using wordTrace_append hprefix tailTrace_944597
  have hstable : (prefixWord ++ tailWord_944597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944597).length < 2 ^ (prefixWord ++ tailWord_944597).sum := by decide
  have hdescent : baseEnd_944597 < baseStart_944597 := by decide
  rcases family_descends (prefixWord ++ tailWord_944597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944625 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_944625 : Nat := 118140960795 + 944625 * 2 ^ 59
def prefixEnd_944625 : Nat := 4983230072969 + 3 ^ 40 * 944625 * 2
def baseEnd_944625 : Nat := 431152589558641674705115

theorem tailTrace_944625 : CollatzResearch.WordTrace tailWord_944625 prefixEnd_944625 431152589558641674705115 := by
  unfold tailWord_944625
  simp only [CollatzResearch.WordTrace]
  refine ⟨34453304202792428951043329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22968869468528285967362219 34453304202792428951043329)
  ·
    refine ⟨25839978152094321713282497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34453304202792428951043329 25839978152094321713282497)
    ·
      refine ⟨19379983614070741284961873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25839978152094321713282497 19379983614070741284961873)
      ·
        refine ⟨14534987710553055963721405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19379983614070741284961873 14534987710553055963721405)
        ·
          refine ⟨5450620391457395986395527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14534987710553055963721405 5450620391457395986395527)
          ·
            refine ⟨8175930587186093979593291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450620391457395986395527 8175930587186093979593291)
            ·
              refine ⟨12263895880779140969389937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8175930587186093979593291 12263895880779140969389937)
              ·
                refine ⟨9197921910584355727042453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12263895880779140969389937 9197921910584355727042453)
                ·
                  refine ⟨431152589558641674705115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9197921910584355727042453 431152589558641674705115)
                  ·
                    rfl

theorem cell20_944625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_944625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944625 prefixEnd_944625 := by exact prefixLift 944625
  have htrace : WordTrace (prefixWord ++ tailWord_944625) baseStart_944625 baseEnd_944625 := by
    simpa [prefixWord, tailWord_944625, baseEnd_944625] using wordTrace_append hprefix tailTrace_944625
  have hstable : (prefixWord ++ tailWord_944625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944625).length < 2 ^ (prefixWord ++ tailWord_944625).sum := by decide
  have hdescent : baseEnd_944625 < baseStart_944625 := by decide
  rcases family_descends (prefixWord ++ tailWord_944625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944632 : List Nat := [2, 1, 2, 1, 1, 4, 9]
def baseStart_944632 : Nat := 118140960795 + 944632 * 2 ^ 59
def prefixEnd_944632 : Nat := 4983230072969 + 3 ^ 40 * 944632 * 2
def baseEnd_944632 : Nat := 47906198283264529052417

theorem tailTrace_944632 : CollatzResearch.WordTrace tailWord_944632 prefixEnd_944632 47906198283264529052417 := by
  unfold tailWord_944632
  simp only [CollatzResearch.WordTrace]
  refine ⟨17226779756883534573274075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22969039675844712764365433 17226779756883534573274075)
  ·
    refine ⟨25840169635325301859911113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17226779756883534573274075 25840169635325301859911113)
    ·
      refine ⟨19380127226493976394933335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25840169635325301859911113 19380127226493976394933335)
      ·
        refine ⟨29070190839740964592400003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19380127226493976394933335 29070190839740964592400003)
        ·
          refine ⟨43605286259611446888600005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29070190839740964592400003 43605286259611446888600005)
          ·
            refine ⟨8175991173677146291612501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43605286259611446888600005 8175991173677146291612501)
            ·
              refine ⟨47906198283264529052417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8175991173677146291612501 47906198283264529052417)
              ·
                rfl

theorem cell20_944632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_944632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944632 prefixEnd_944632 := by exact prefixLift 944632
  have htrace : WordTrace (prefixWord ++ tailWord_944632) baseStart_944632 baseEnd_944632 := by
    simpa [prefixWord, tailWord_944632, baseEnd_944632] using wordTrace_append hprefix tailTrace_944632
  have hstable : (prefixWord ++ tailWord_944632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944632).length < 2 ^ (prefixWord ++ tailWord_944632).sum := by decide
  have hdescent : baseEnd_944632 < baseStart_944632 := by decide
  rcases family_descends (prefixWord ++ tailWord_944632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944652 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_944652 : Nat := 118140960795 + 944652 * 2 ^ 59
def prefixEnd_944652 : Nat := 4983230072969 + 3 ^ 40 * 944652 * 2
def baseEnd_944652 : Nat := 431164913094349580805005

theorem tailTrace_944652 : CollatzResearch.WordTrace tailWord_944652 prefixEnd_944652 431164913094349580805005 := by
  unfold tailWord_944652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227144486847306281138105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22969525982463075041517473 17227144486847306281138105)
  ·
    refine ⟨12920358365135479710853579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17227144486847306281138105 12920358365135479710853579)
    ·
      refine ⟨19380537547703219566280369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12920358365135479710853579 19380537547703219566280369)
      ·
        refine ⟨14535403160777414674710277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19380537547703219566280369 14535403160777414674710277)
        ·
          refine ⟨2725388092645765251508177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14535403160777414674710277 2725388092645765251508177)
          ·
            refine ⟨2044041069484323938631133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725388092645765251508177 2044041069484323938631133)
            ·
              refine ⟨766515401056621476986675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2044041069484323938631133 766515401056621476986675)
              ·
                refine ⟨1149773101584932215480013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766515401056621476986675 1149773101584932215480013)
                ·
                  refine ⟨431164913094349580805005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149773101584932215480013 431164913094349580805005)
                  ·
                    rfl

theorem cell20_944652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_944652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944652 prefixEnd_944652 := by exact prefixLift 944652
  have htrace : WordTrace (prefixWord ++ tailWord_944652) baseStart_944652 baseEnd_944652 := by
    simpa [prefixWord, tailWord_944652, baseEnd_944652] using wordTrace_append hprefix tailTrace_944652
  have hstable : (prefixWord ++ tailWord_944652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944652).length < 2 ^ (prefixWord ++ tailWord_944652).sum := by decide
  have hdescent : baseEnd_944652 < baseStart_944652 := by decide
  rcases family_descends (prefixWord ++ tailWord_944652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944711 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_944711 : Nat := 118140960795 + 944711 * 2 ^ 59
def prefixEnd_944711 : Nat := 4983230072969 + 3 ^ 40 * 944711 * 2
def baseEnd_944711 : Nat := 431191842302007597838097

theorem tailTrace_944711 : CollatzResearch.WordTrace tailWord_944711 prefixEnd_944711 431191842302007597838097 := by
  unfold tailWord_944711
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456440880480865638673987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22970960586987243759115991 34456440880480865638673987)
  ·
    refine ⟨51684661320721298458010981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34456440880480865638673987 51684661320721298458010981)
    ·
      refine ⟨9690873997635243460877059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51684661320721298458010981 9690873997635243460877059)
      ·
        refine ⟨14536310996452865191315589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690873997635243460877059 14536310996452865191315589)
        ·
          refine ⟨2725558311834912223371673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14536310996452865191315589 2725558311834912223371673)
          ·
            refine ⟨2044168733876184167528755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725558311834912223371673 2044168733876184167528755)
            ·
              refine ⟨3066253100814276251293133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044168733876184167528755 3066253100814276251293133)
              ·
                refine ⟨1149844912805353594234925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3066253100814276251293133 1149844912805353594234925)
                ·
                  refine ⟨431191842302007597838097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149844912805353594234925 431191842302007597838097)
                  ·
                    rfl

theorem cell20_944711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_944711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944711 prefixEnd_944711 := by exact prefixLift 944711
  have htrace : WordTrace (prefixWord ++ tailWord_944711) baseStart_944711 baseEnd_944711 := by
    simpa [prefixWord, tailWord_944711, baseEnd_944711] using wordTrace_append hprefix tailTrace_944711
  have hstable : (prefixWord ++ tailWord_944711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944711).length < 2 ^ (prefixWord ++ tailWord_944711).sum := by decide
  have hdescent : baseEnd_944711 < baseStart_944711 := by decide
  rcases family_descends (prefixWord ++ tailWord_944711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944749 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_944749 : Nat := 118140960795 + 944749 * 2 ^ 59
def prefixEnd_944749 : Nat := 4983230072969 + 3 ^ 40 * 944749 * 2
def baseEnd_944749 : Nat := 431209186537448354571275

theorem tailTrace_944749 : CollatzResearch.WordTrace tailWord_944749 prefixEnd_944749 431209186537448354571275 := by
  unfold tailWord_944749
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457826854343198128557301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22971884569562132085704867 34457826854343198128557301)
  ·
    refine ⟨3230421267594674824552247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34457826854343198128557301 3230421267594674824552247)
    ·
      refine ⟨4845631901392012236828371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230421267594674824552247 4845631901392012236828371)
      ·
        refine ⟨7268447852088018355242557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845631901392012236828371 7268447852088018355242557)
        ·
          refine ⟨2725667944533006883215959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7268447852088018355242557 2725667944533006883215959)
          ·
            refine ⟨4088501916799510324823939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725667944533006883215959 4088501916799510324823939)
            ·
              refine ⟨6132752875199265487235909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088501916799510324823939 6132752875199265487235909)
              ·
                refine ⟨1149891164099862278856733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6132752875199265487235909 1149891164099862278856733)
                ·
                  refine ⟨431209186537448354571275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149891164099862278856733 431209186537448354571275)
                  ·
                    rfl

theorem cell20_944749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_944749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944749 prefixEnd_944749 := by exact prefixLift 944749
  have htrace : WordTrace (prefixWord ++ tailWord_944749) baseStart_944749 baseEnd_944749 := by
    simpa [prefixWord, tailWord_944749, baseEnd_944749] using wordTrace_append hprefix tailTrace_944749
  have hstable : (prefixWord ++ tailWord_944749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944749).length < 2 ^ (prefixWord ++ tailWord_944749).sum := by decide
  have hdescent : baseEnd_944749 < baseStart_944749 := by decide
  rcases family_descends (prefixWord ++ tailWord_944749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944801 : List Nat := [1, 2, 3, 3, 3, 1, 7]
def baseStart_944801 : Nat := 118140960795 + 944801 * 2 ^ 59
def prefixEnd_944801 : Nat := 4983230072969 + 3 ^ 40 * 944801 * 2
def baseEnd_944801 : Nat := 47914768972707476093081

theorem tailTrace_944801 : CollatzResearch.WordTrace tailWord_944801 prefixEnd_944801 47914768972707476093081 := by
  unfold tailWord_944801
  simp only [CollatzResearch.WordTrace]
  refine ⟨34459723450154811009450257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22973148966769874006300171 34459723450154811009450257)
  ·
    refine ⟨25844792587616108257087693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34459723450154811009450257 25844792587616108257087693)
    ·
      refine ⟨9691797220356040596407885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25844792587616108257087693 9691797220356040596407885)
      ·
        refine ⟨3634423957633515223652957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9691797220356040596407885 3634423957633515223652957)
        ·
          refine ⟨1362908984112568208869859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3634423957633515223652957 1362908984112568208869859)
          ·
            refine ⟨2044363476168852313304789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362908984112568208869859 2044363476168852313304789)
            ·
              refine ⟨47914768972707476093081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2044363476168852313304789 47914768972707476093081)
              ·
                rfl

theorem cell20_944801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_944801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944801 prefixEnd_944801 := by exact prefixLift 944801
  have htrace : WordTrace (prefixWord ++ tailWord_944801) baseStart_944801 baseEnd_944801 := by
    simpa [prefixWord, tailWord_944801, baseEnd_944801] using wordTrace_append hprefix tailTrace_944801
  have hstable : (prefixWord ++ tailWord_944801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944801).length < 2 ^ (prefixWord ++ tailWord_944801).sum := by decide
  have hdescent : baseEnd_944801 < baseStart_944801 := by decide
  rcases family_descends (prefixWord ++ tailWord_944801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944815 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_944815 : Nat := 118140960795 + 944815 * 2 ^ 59
def prefixEnd_944815 : Nat := 4983230072969 + 3 ^ 40 * 944815 * 2
def baseEnd_944815 : Nat := 431239310735845458371005

theorem tailTrace_944815 : CollatzResearch.WordTrace tailWord_944815 prefixEnd_944815 431239310735845458371005 := by
  unfold tailWord_944815
  simp only [CollatzResearch.WordTrace]
  refine ⟨34460234072104091400459899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22973489381402727600306599 34460234072104091400459899)
  ·
    refine ⟨51690351108156137100689849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34460234072104091400459899 51690351108156137100689849)
    ·
      refine ⟨38767763331117102825517387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51690351108156137100689849 38767763331117102825517387)
      ·
        refine ⟨58151644996675654238276081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38767763331117102825517387 58151644996675654238276081)
        ·
          refine ⟨43613733747506740678707061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58151644996675654238276081 43613733747506740678707061)
          ·
            refine ⟨4088787538828756938628787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43613733747506740678707061 4088787538828756938628787)
            ·
              refine ⟨6133181308243135407943181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088787538828756938628787 6133181308243135407943181)
              ·
                refine ⟨2299942990591175777978693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6133181308243135407943181 2299942990591175777978693)
                ·
                  refine ⟨431239310735845458371005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299942990591175777978693 431239310735845458371005)
                  ·
                    rfl

theorem cell20_944815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_944815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944815 prefixEnd_944815 := by exact prefixLift 944815
  have htrace : WordTrace (prefixWord ++ tailWord_944815) baseStart_944815 baseEnd_944815 := by
    simpa [prefixWord, tailWord_944815, baseEnd_944815] using wordTrace_append hprefix tailTrace_944815
  have hstable : (prefixWord ++ tailWord_944815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944815).length < 2 ^ (prefixWord ++ tailWord_944815).sum := by decide
  have hdescent : baseEnd_944815 < baseStart_944815 := by decide
  rcases family_descends (prefixWord ++ tailWord_944815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944846 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_944846 : Nat := 118140960795 + 944846 * 2 ^ 59
def prefixEnd_944846 : Nat := 4983230072969 + 3 ^ 40 * 944846 * 2
def baseEnd_944846 : Nat := 431253459980547128337545

theorem tailTrace_944846 : CollatzResearch.WordTrace tailWord_944846 prefixEnd_944846 431253459980547128337545 := by
  unfold tailWord_944846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307670591873972961854799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22974243156661189129892261 4307670591873972961854799)
  ·
    refine ⟨6461505887810959442782199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4307670591873972961854799 6461505887810959442782199)
    ·
      refine ⟨9692258831716439164173299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6461505887810959442782199 9692258831716439164173299)
      ·
        refine ⟨14538388247574658746259949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692258831716439164173299 14538388247574658746259949)
        ·
          refine ⟨5451895592840497029847481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14538388247574658746259949 5451895592840497029847481)
          ·
            refine ⟨4088921694630372772385611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5451895592840497029847481 4088921694630372772385611)
            ·
              refine ⟨6133382541945559158578417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088921694630372772385611 6133382541945559158578417)
              ·
                refine ⟨4600036906459169368933813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6133382541945559158578417 4600036906459169368933813)
                ·
                  refine ⟨431253459980547128337545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600036906459169368933813 431253459980547128337545)
                  ·
                    rfl

theorem cell20_944846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_944846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944846 prefixEnd_944846 := by exact prefixLift 944846
  have htrace : WordTrace (prefixWord ++ tailWord_944846) baseStart_944846 baseEnd_944846 := by
    simpa [prefixWord, tailWord_944846, baseEnd_944846] using wordTrace_append hprefix tailTrace_944846
  have hstable : (prefixWord ++ tailWord_944846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944846).length < 2 ^ (prefixWord ++ tailWord_944846).sum := by decide
  have hdescent : baseEnd_944846 < baseStart_944846 := by decide
  rcases family_descends (prefixWord ++ tailWord_944846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944877 : List Nat := [1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_944877 : Nat := 118140960795 + 944877 * 2 ^ 59
def prefixEnd_944877 : Nat := 4983230072969 + 3 ^ 40 * 944877 * 2
def baseEnd_944877 : Nat := 143755869741749599434695

theorem tailTrace_944877 : CollatzResearch.WordTrace tailWord_944877 prefixEnd_944877 143755869741749599434695 := by
  unfold tailWord_944877
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462495397879475989216885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22974996931919650659477923 34462495397879475989216885)
  ·
    refine ⟨3230858943551200873989083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34462495397879475989216885 3230858943551200873989083)
    ·
      refine ⟨4846288415326801310983625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230858943551200873989083 4846288415326801310983625)
      ·
        refine ⟨3634716311495100983237719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4846288415326801310983625 3634716311495100983237719)
        ·
          refine ⟨5452074467242651474856579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634716311495100983237719 5452074467242651474856579)
          ·
            refine ⟨8178111700863977212284869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452074467242651474856579 8178111700863977212284869)
            ·
              refine ⟨1533395943911995727303413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8178111700863977212284869 1533395943911995727303413)
              ·
                refine ⟨143755869741749599434695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1533395943911995727303413 143755869741749599434695)
                ·
                  rfl

theorem cell20_944877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_944877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944877 prefixEnd_944877 := by exact prefixLift 944877
  have htrace : WordTrace (prefixWord ++ tailWord_944877) baseStart_944877 baseEnd_944877 := by
    simpa [prefixWord, tailWord_944877, baseEnd_944877] using wordTrace_append hprefix tailTrace_944877
  have hstable : (prefixWord ++ tailWord_944877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944877).length < 2 ^ (prefixWord ++ tailWord_944877).sum := by decide
  have hdescent : baseEnd_944877 < baseStart_944877 := by decide
  rcases family_descends (prefixWord ++ tailWord_944877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944905 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_944905 : Nat := 118140960795 + 944905 * 2 ^ 59
def prefixEnd_944905 : Nat := 4983230072969 + 3 ^ 40 * 944905 * 2
def baseEnd_944905 : Nat := 431280389188205145370637

theorem tailTrace_944905 : CollatzResearch.WordTrace tailWord_944905 prefixEnd_944905 431280389188205145370637 := by
  unfold tailWord_944905
  simp only [CollatzResearch.WordTrace]
  refine ⟨34463516641778036771236169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22975677761185357847490779 34463516641778036771236169)
  ·
    refine ⟨25847637481333527578427127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34463516641778036771236169 25847637481333527578427127)
    ·
      refine ⟨38771456222000291367640691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25847637481333527578427127 38771456222000291367640691)
      ·
        refine ⟨58157184333000437051461037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38771456222000291367640691 58157184333000437051461037)
        ·
          refine ⟨21808944124875163894297889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58157184333000437051461037 21808944124875163894297889)
          ·
            refine ⟨16356708093656372920723417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21808944124875163894297889 16356708093656372920723417)
            ·
              refine ⟨12267531070242279690542563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16356708093656372920723417 12267531070242279690542563)
              ·
                refine ⟨18401296605363419535813845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267531070242279690542563 18401296605363419535813845)
                ·
                  refine ⟨431280389188205145370637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18401296605363419535813845 431280389188205145370637)
                  ·
                    rfl

theorem cell20_944905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_944905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944905 prefixEnd_944905 := by exact prefixLift 944905
  have htrace : WordTrace (prefixWord ++ tailWord_944905) baseStart_944905 baseEnd_944905 := by
    simpa [prefixWord, tailWord_944905, baseEnd_944905] using wordTrace_append hprefix tailTrace_944905
  have hstable : (prefixWord ++ tailWord_944905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944905).length < 2 ^ (prefixWord ++ tailWord_944905).sum := by decide
  have hdescent : baseEnd_944905 < baseStart_944905 := by decide
  rcases family_descends (prefixWord ++ tailWord_944905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944908 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 2]
def baseStart_944908 : Nat := 118140960795 + 944908 * 2 ^ 59
def prefixEnd_944908 : Nat := 4983230072969 + 3 ^ 40 * 944908 * 2
def baseEnd_944908 : Nat := 431281758469950468270625

theorem tailTrace_944908 : CollatzResearch.WordTrace tailWord_944908 prefixEnd_944908 431281758469950468270625 := by
  unfold tailWord_944908
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231813030383584141797689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22975750707178112189063585 17231813030383584141797689)
  ·
    refine ⟨12923859772787688106348267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17231813030383584141797689 12923859772787688106348267)
    ·
      refine ⟨19385789659181532159522401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12923859772787688106348267 19385789659181532159522401)
      ·
        refine ⟨14539342244386149119641801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19385789659181532159522401 14539342244386149119641801)
        ·
          refine ⟨10904506683289611839731351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14539342244386149119641801 10904506683289611839731351)
          ·
            refine ⟨16356760024934417759597027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10904506683289611839731351 16356760024934417759597027)
            ·
              refine ⟨24535140037401626639395541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16356760024934417759597027 24535140037401626639395541)
              ·
                refine ⟨575042344626600624360833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24535140037401626639395541 575042344626600624360833)
                ·
                  refine ⟨431281758469950468270625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575042344626600624360833 431281758469950468270625)
                  ·
                    rfl

theorem cell20_944908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_944908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944908 prefixEnd_944908 := by exact prefixLift 944908
  have htrace : WordTrace (prefixWord ++ tailWord_944908) baseStart_944908 baseEnd_944908 := by
    simpa [prefixWord, tailWord_944908, baseEnd_944908] using wordTrace_append hprefix tailTrace_944908
  have hstable : (prefixWord ++ tailWord_944908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944908).length < 2 ^ (prefixWord ++ tailWord_944908).sum := by decide
  have hdescent : baseEnd_944908 < baseStart_944908 := by decide
  rcases family_descends (prefixWord ++ tailWord_944908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944929 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_944929 : Nat := 118140960795 + 944929 * 2 ^ 59
def prefixEnd_944929 : Nat := 4983230072969 + 3 ^ 40 * 944929 * 2
def baseEnd_944929 : Nat := 431291343442167728570539

theorem tailTrace_944929 : CollatzResearch.WordTrace tailWord_944929 prefixEnd_944929 431291343442167728570539 := by
  unfold tailWord_944929
  simp only [CollatzResearch.WordTrace]
  refine ⟨34464391993691088870109841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22976261329127392580073227 34464391993691088870109841)
  ·
    refine ⟨25848293995268316652582381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34464391993691088870109841 25848293995268316652582381)
    ·
      refine ⟨9693110248225618744718393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25848293995268316652582381 9693110248225618744718393)
      ·
        refine ⟨7269832686169214058538795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9693110248225618744718393 7269832686169214058538795)
        ·
          refine ⟨10904749029253821087808193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7269832686169214058538795 10904749029253821087808193)
          ·
            refine ⟨8178561771940365815856145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10904749029253821087808193 8178561771940365815856145)
            ·
              refine ⟨6133921328955274361892109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8178561771940365815856145 6133921328955274361892109)
              ·
                refine ⟨2300220498358227885709541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6133921328955274361892109 2300220498358227885709541)
                ·
                  refine ⟨431291343442167728570539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300220498358227885709541 431291343442167728570539)
                  ·
                    rfl

theorem cell20_944929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_944929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944929 prefixEnd_944929 := by exact prefixLift 944929
  have htrace : WordTrace (prefixWord ++ tailWord_944929) baseStart_944929 baseEnd_944929 := by
    simpa [prefixWord, tailWord_944929, baseEnd_944929] using wordTrace_append hprefix tailTrace_944929
  have hstable : (prefixWord ++ tailWord_944929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944929).length < 2 ^ (prefixWord ++ tailWord_944929).sum := by decide
  have hdescent : baseEnd_944929 < baseStart_944929 := by decide
  rcases family_descends (prefixWord ++ tailWord_944929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944932 : List Nat := [2, 3, 1, 3, 3, 2, 1, 5]
def baseStart_944932 : Nat := 118140960795 + 944932 * 2 ^ 59
def prefixEnd_944932 : Nat := 4983230072969 + 3 ^ 40 * 944932 * 2
def baseEnd_944932 : Nat := 143764237574637683823509

theorem tailTrace_944932 : CollatzResearch.WordTrace tailWord_944932 prefixEnd_944932 143764237574637683823509 := by
  unfold tailWord_944932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17232250706340110191234525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22976334275120146921646033 17232250706340110191234525)
  ·
    refine ⟨6462094014877541321712947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17232250706340110191234525 6462094014877541321712947)
    ·
      refine ⟨9693141022316311982569421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6462094014877541321712947 9693141022316311982569421)
      ·
        refine ⟨3634927883368616993463533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9693141022316311982569421 3634927883368616993463533)
        ·
          refine ⟨1363097956263231372548825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3634927883368616993463533 1363097956263231372548825)
          ·
            refine ⟨1022323467197423529411619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363097956263231372548825 1022323467197423529411619)
            ·
              refine ⟨1533485200796135294117429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022323467197423529411619 1533485200796135294117429)
              ·
                refine ⟨143764237574637683823509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1533485200796135294117429 143764237574637683823509)
                ·
                  rfl

theorem cell20_944932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_944932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944932 prefixEnd_944932 := by exact prefixLift 944932
  have htrace : WordTrace (prefixWord ++ tailWord_944932) baseStart_944932 baseEnd_944932 := by
    simpa [prefixWord, tailWord_944932, baseEnd_944932] using wordTrace_append hprefix tailTrace_944932
  have hstable : (prefixWord ++ tailWord_944932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944932).length < 2 ^ (prefixWord ++ tailWord_944932).sum := by decide
  have hdescent : baseEnd_944932 < baseStart_944932 := by decide
  rcases family_descends (prefixWord ++ tailWord_944932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944973 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 3]
def baseStart_944973 : Nat := 118140960795 + 944973 * 2 ^ 59
def prefixEnd_944973 : Nat := 4983230072969 + 3 ^ 40 * 944973 * 2
def baseEnd_944973 : Nat := 431311426241099131103693

theorem tailTrace_944973 : CollatzResearch.WordTrace tailWord_944973 prefixEnd_944973 431311426241099131103693 := by
  unfold tailWord_944973
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465996805531684384711573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22977331203687789589807715 34465996805531684384711573)
  ·
    refine ⟨1615593600259297705533355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34465996805531684384711573 1615593600259297705533355)
    ·
      refine ⟨2423390400388946558300033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1615593600259297705533355 2423390400388946558300033)
      ·
        refine ⟨1817542800291709918725025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2423390400388946558300033 1817542800291709918725025)
        ·
          refine ⟨1363157100218782439043769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1817542800291709918725025 1363157100218782439043769)
          ·
            refine ⟨1022367825164086829282827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363157100218782439043769 1022367825164086829282827)
            ·
              refine ⟨1533551737746130243924241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022367825164086829282827 1533551737746130243924241)
              ·
                refine ⟨1150163803309597682943181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533551737746130243924241 1150163803309597682943181)
                ·
                  refine ⟨431311426241099131103693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150163803309597682943181 431311426241099131103693)
                  ·
                    rfl

theorem cell20_944973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_944973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_944973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_944973 prefixEnd_944973 := by exact prefixLift 944973
  have htrace : WordTrace (prefixWord ++ tailWord_944973) baseStart_944973 baseEnd_944973 := by
    simpa [prefixWord, tailWord_944973, baseEnd_944973] using wordTrace_append hprefix tailTrace_944973
  have hstable : (prefixWord ++ tailWord_944973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944973).length < 2 ^ (prefixWord ++ tailWord_944973).sum := by decide
  have hdescent : baseEnd_944973 < baseStart_944973 := by decide
  rcases family_descends (prefixWord ++ tailWord_944973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945019 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_945019 : Nat := 118140960795 + 945019 * 2 ^ 59
def prefixEnd_945019 : Nat := 4983230072969 + 3 ^ 40 * 945019 * 2
def baseEnd_945019 : Nat := 431332421894527415570171

theorem tailTrace_945019 : CollatzResearch.WordTrace tailWord_945019 prefixEnd_945019 431332421894527415570171 := by
  unfold tailWord_945019
  simp only [CollatzResearch.WordTrace]
  refine ⟨34467674563365034240886111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22978449708910022827257407 34467674563365034240886111)
  ·
    refine ⟨51701511845047551361329167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34467674563365034240886111 51701511845047551361329167)
    ·
      refine ⟨77552267767571327041993751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51701511845047551361329167 77552267767571327041993751)
      ·
        refine ⟨116328401651356990562990627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77552267767571327041993751 116328401651356990562990627)
        ·
          refine ⟨174492602477035485844485941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116328401651356990562990627 174492602477035485844485941)
          ·
            refine ⟨16358681482222076797920557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174492602477035485844485941 16358681482222076797920557)
            ·
              refine ⟨6134505555833278799220209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16358681482222076797920557 6134505555833278799220209)
              ·
                refine ⟨4600879166874959099415157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6134505555833278799220209 4600879166874959099415157)
                ·
                  refine ⟨431332421894527415570171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600879166874959099415157 431332421894527415570171)
                  ·
                    rfl

theorem cell20_945019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_945019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945019 prefixEnd_945019 := by exact prefixLift 945019
  have htrace : WordTrace (prefixWord ++ tailWord_945019) baseStart_945019 baseEnd_945019 := by
    simpa [prefixWord, tailWord_945019, baseEnd_945019] using wordTrace_append hprefix tailTrace_945019
  have hstable : (prefixWord ++ tailWord_945019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945019).length < 2 ^ (prefixWord ++ tailWord_945019).sum := by decide
  have hdescent : baseEnd_945019 < baseStart_945019 := by decide
  rcases family_descends (prefixWord ++ tailWord_945019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945095 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_945095 : Nat := 118140960795 + 945095 * 2 ^ 59
def prefixEnd_945095 : Nat := 4983230072969 + 3 ^ 40 * 945095 * 2
def baseEnd_945095 : Nat := 431367110365408929036527

theorem tailTrace_945095 : CollatzResearch.WordTrace tailWord_945095 prefixEnd_945095 431367110365408929036527 := by
  unfold tailWord_945095
  simp only [CollatzResearch.WordTrace]
  refine ⟨34470446511089699220652739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22980297674059799480435159 34470446511089699220652739)
  ·
    refine ⟨51705669766634548830979109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34470446511089699220652739 51705669766634548830979109)
    ·
      refine ⟨9694813081243977905808583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51705669766634548830979109 9694813081243977905808583)
      ·
        refine ⟨14542219621865966858712875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694813081243977905808583 14542219621865966858712875)
        ·
          refine ⟨21813329432798950288069313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14542219621865966858712875 21813329432798950288069313)
          ·
            refine ⟨16359997074599212716051985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21813329432798950288069313 16359997074599212716051985)
            ·
              refine ⟨12269997805949409537038989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16359997074599212716051985 12269997805949409537038989)
              ·
                refine ⟨4601249177231028576389621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12269997805949409537038989 4601249177231028576389621)
                ·
                  refine ⟨431367110365408929036527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601249177231028576389621 431367110365408929036527)
                  ·
                    rfl

theorem cell20_945095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_945095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945095 prefixEnd_945095 := by exact prefixLift 945095
  have htrace : WordTrace (prefixWord ++ tailWord_945095) baseStart_945095 baseEnd_945095 := by
    simpa [prefixWord, tailWord_945095, baseEnd_945095] using wordTrace_append hprefix tailTrace_945095
  have hstable : (prefixWord ++ tailWord_945095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945095).length < 2 ^ (prefixWord ++ tailWord_945095).sum := by decide
  have hdescent : baseEnd_945095 < baseStart_945095 := by decide
  rcases family_descends (prefixWord ++ tailWord_945095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945112 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_945112 : Nat := 118140960795 + 945112 * 2 ^ 59
def prefixEnd_945112 : Nat := 4983230072969 + 3 ^ 40 * 945112 * 2
def baseEnd_945112 : Nat := 431374869628632425469791

theorem tailTrace_945112 : CollatzResearch.WordTrace tailWord_945112 prefixEnd_945112 431374869628632425469791 := by
  unfold tailWord_945112
  simp only [CollatzResearch.WordTrace]
  refine ⟨17235533276014055562010795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22980711034685407416014393 17235533276014055562010795)
  ·
    refine ⟨25853299914021083343016193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17235533276014055562010795 25853299914021083343016193)
    ·
      refine ⟨19389974935515812507262145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25853299914021083343016193 19389974935515812507262145)
      ·
        refine ⟨14542481201636859380446609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19389974935515812507262145 14542481201636859380446609)
        ·
          refine ⟨10906860901227644535334957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14542481201636859380446609 10906860901227644535334957)
          ·
            refine ⟨4090072837960366700750609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10906860901227644535334957 4090072837960366700750609)
            ·
              refine ⟨3067554628470275025562957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090072837960366700750609 3067554628470275025562957)
              ·
                refine ⟨1150332985676353134586109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3067554628470275025562957 1150332985676353134586109)
                ·
                  refine ⟨431374869628632425469791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150332985676353134586109 431374869628632425469791)
                  ·
                    rfl

theorem cell20_945112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_945112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945112 prefixEnd_945112 := by exact prefixLift 945112
  have htrace : WordTrace (prefixWord ++ tailWord_945112) baseStart_945112 baseEnd_945112 := by
    simpa [prefixWord, tailWord_945112, baseEnd_945112] using wordTrace_append hprefix tailTrace_945112
  have hstable : (prefixWord ++ tailWord_945112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945112).length < 2 ^ (prefixWord ++ tailWord_945112).sum := by decide
  have hdescent : baseEnd_945112 < baseStart_945112 := by decide
  rcases family_descends (prefixWord ++ tailWord_945112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945157 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_945157 : Nat := 118140960795 + 945157 * 2 ^ 59
def prefixEnd_945157 : Nat := 4983230072969 + 3 ^ 40 * 945157 * 2
def baseEnd_945157 : Nat := 431395408854812268969607

theorem tailTrace_945157 : CollatzResearch.WordTrace tailWord_945157 prefixEnd_945157 431395408854812268969607 := by
  unfold tailWord_945157
  simp only [CollatzResearch.WordTrace]
  refine ⟨34472707836865083809409725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22981805224576722539606483 34472707836865083809409725)
  ·
    refine ⟨12927265438824406428528647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34472707836865083809409725 12927265438824406428528647)
    ·
      refine ⟨19390898158236609642792971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12927265438824406428528647 19390898158236609642792971)
      ·
        refine ⟨29086347237354914464189457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19390898158236609642792971 29086347237354914464189457)
        ·
          refine ⟨21814760428016185848142093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29086347237354914464189457 21814760428016185848142093)
          ·
            refine ⟨8180535160506069693053285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21814760428016185848142093 8180535160506069693053285)
            ·
              refine ⟨1533850342594888067447491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8180535160506069693053285 1533850342594888067447491)
              ·
                refine ⟨2300775513892332101171237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533850342594888067447491 2300775513892332101171237)
                ·
                  refine ⟨431395408854812268969607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300775513892332101171237 431395408854812268969607)
                  ·
                    rfl

theorem cell20_945157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_945157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945157 prefixEnd_945157 := by exact prefixLift 945157
  have htrace : WordTrace (prefixWord ++ tailWord_945157) baseStart_945157 baseEnd_945157 := by
    simpa [prefixWord, tailWord_945157, baseEnd_945157] using wordTrace_append hprefix tailTrace_945157
  have hstable : (prefixWord ++ tailWord_945157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945157).length < 2 ^ (prefixWord ++ tailWord_945157).sum := by decide
  have hdescent : baseEnd_945157 < baseStart_945157 := by decide
  rcases family_descends (prefixWord ++ tailWord_945157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945181 : List Nat := [1, 4, 2, 2, 3, 1, 1, 6]
def baseStart_945181 : Nat := 118140960795 + 945181 * 2 ^ 59
def prefixEnd_945181 : Nat := 4983230072969 + 3 ^ 40 * 945181 * 2
def baseEnd_945181 : Nat := 143802121036258284056503

theorem tailTrace_945181 : CollatzResearch.WordTrace tailWord_945181 prefixEnd_945181 143802121036258284056503 := by
  unfold tailWord_945181
  simp only [CollatzResearch.WordTrace]
  refine ⟨34473583188778135908283397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22982388792518757272188931 34473583188778135908283397)
  ·
    refine ⟨6463796847895900482803137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34473583188778135908283397 6463796847895900482803137)
    ·
      refine ⟨4847847635921925362102353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6463796847895900482803137 4847847635921925362102353)
      ·
        refine ⟨3635885726941444021576765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4847847635921925362102353 3635885726941444021576765)
        ·
          refine ⟨1363457147603041508091287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3635885726941444021576765 1363457147603041508091287)
          ·
            refine ⟨2045185721404562262136931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363457147603041508091287 2045185721404562262136931)
            ·
              refine ⟨3067778582106843393205397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045185721404562262136931 3067778582106843393205397)
              ·
                refine ⟨143802121036258284056503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3067778582106843393205397 143802121036258284056503)
                ·
                  rfl

theorem cell20_945181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_945181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945181 prefixEnd_945181 := by exact prefixLift 945181
  have htrace : WordTrace (prefixWord ++ tailWord_945181) baseStart_945181 baseEnd_945181 := by
    simpa [prefixWord, tailWord_945181, baseEnd_945181] using wordTrace_append hprefix tailTrace_945181
  have hstable : (prefixWord ++ tailWord_945181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945181).length < 2 ^ (prefixWord ++ tailWord_945181).sum := by decide
  have hdescent : baseEnd_945181 < baseStart_945181 := by decide
  rcases family_descends (prefixWord ++ tailWord_945181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945188 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_945188 : Nat := 118140960795 + 945188 * 2 ^ 59
def prefixEnd_945188 : Nat := 4983230072969 + 3 ^ 40 * 945188 * 2
def baseEnd_945188 : Nat := 431409558099513938936147

theorem tailTrace_945188 : CollatzResearch.WordTrace tailWord_945188 prefixEnd_945188 431409558099513938936147 := by
  unfold tailWord_945188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236919249876388051894109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22982558999835184069192145 17236919249876388051894109)
  ·
    refine ⟨6463844718703645519460291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17236919249876388051894109 6463844718703645519460291)
    ·
      refine ⟨9695767078055468279190437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6463844718703645519460291 9695767078055468279190437)
      ·
        refine ⟨1817956327135400302348207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9695767078055468279190437 1817956327135400302348207)
        ·
          refine ⟨2726934490703100453522311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817956327135400302348207 2726934490703100453522311)
          ·
            refine ⟨4090401736054650680283467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726934490703100453522311 4090401736054650680283467)
            ·
              refine ⟨6135602604081976020425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090401736054650680283467 6135602604081976020425201)
              ·
                refine ⟨4601701953061482015318901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6135602604081976020425201 4601701953061482015318901)
                ·
                  refine ⟨431409558099513938936147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601701953061482015318901 431409558099513938936147)
                  ·
                    rfl

theorem cell20_945188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_945188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945188 prefixEnd_945188 := by exact prefixLift 945188
  have htrace : WordTrace (prefixWord ++ tailWord_945188) baseStart_945188 baseEnd_945188 := by
    simpa [prefixWord, tailWord_945188, baseEnd_945188] using wordTrace_append hprefix tailTrace_945188
  have hstable : (prefixWord ++ tailWord_945188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945188).length < 2 ^ (prefixWord ++ tailWord_945188).sum := by decide
  have hdescent : baseEnd_945188 < baseStart_945188 := by decide
  rcases family_descends (prefixWord ++ tailWord_945188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945212 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_945212 : Nat := 118140960795 + 945212 * 2 ^ 59
def prefixEnd_945212 : Nat := 4983230072969 + 3 ^ 40 * 945212 * 2
def baseEnd_945212 : Nat := 431420512353476522136049

theorem tailTrace_945212 : CollatzResearch.WordTrace tailWord_945212 prefixEnd_945212 431420512353476522136049 := by
  unfold tailWord_945212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17237356925832914101330945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22983142567777218801774593 17237356925832914101330945)
  ·
    refine ⟨12928017694374685575998209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17237356925832914101330945 12928017694374685575998209)
    ·
      refine ⟨9696013270781014181998657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12928017694374685575998209 9696013270781014181998657)
      ·
        refine ⟨7272009953085760636498993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9696013270781014181998657 7272009953085760636498993)
        ·
          refine ⟨5454007464814320477374245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7272009953085760636498993 5454007464814320477374245)
          ·
            refine ⟨1022626399652685089507671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5454007464814320477374245 1022626399652685089507671)
            ·
              refine ⟨1533939599479027634261507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022626399652685089507671 1533939599479027634261507)
              ·
                refine ⟨2300909399218541451392261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533939599479027634261507 2300909399218541451392261)
                ·
                  refine ⟨431420512353476522136049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300909399218541451392261 431420512353476522136049)
                  ·
                    rfl

theorem cell20_945212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_945212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945212 prefixEnd_945212 := by exact prefixLift 945212
  have htrace : WordTrace (prefixWord ++ tailWord_945212) baseStart_945212 baseEnd_945212 := by
    simpa [prefixWord, tailWord_945212, baseEnd_945212] using wordTrace_append hprefix tailTrace_945212
  have hstable : (prefixWord ++ tailWord_945212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945212).length < 2 ^ (prefixWord ++ tailWord_945212).sum := by decide
  have hdescent : baseEnd_945212 < baseStart_945212 := by decide
  rcases family_descends (prefixWord ++ tailWord_945212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945222 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_945222 : Nat := 118140960795 + 945222 * 2 ^ 59
def prefixEnd_945222 : Nat := 4983230072969 + 3 ^ 40 * 945222 * 2
def baseEnd_945222 : Nat := 431425076625960931802675

theorem tailTrace_945222 : CollatzResearch.WordTrace tailWord_945222 prefixEnd_945222 431425076625960931802675 := by
  unfold tailWord_945222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077346205675924997203935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22983385721086399940350613 1077346205675924997203935)
  ·
    refine ⟨1616019308513887495805903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1077346205675924997203935 1616019308513887495805903)
    ·
      refine ⟨2424028962770831243708855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616019308513887495805903 2424028962770831243708855)
      ·
        refine ⟨3636043444156246865563283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424028962770831243708855 3636043444156246865563283)
        ·
          refine ⟨5454065166234370298344925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636043444156246865563283 5454065166234370298344925)
          ·
            refine ⟨2045274437337888861879347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5454065166234370298344925 2045274437337888861879347)
            ·
              refine ⟨3067911656006833292819021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045274437337888861879347 3067911656006833292819021)
              ·
                refine ⟨1150466871002562484807133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3067911656006833292819021 1150466871002562484807133)
                ·
                  refine ⟨431425076625960931802675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150466871002562484807133 431425076625960931802675)
                  ·
                    rfl

theorem cell20_945222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_945222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945222 prefixEnd_945222 := by exact prefixLift 945222
  have htrace : WordTrace (prefixWord ++ tailWord_945222) baseStart_945222 baseEnd_945222 := by
    simpa [prefixWord, tailWord_945222, baseEnd_945222] using wordTrace_append hprefix tailTrace_945222
  have hstable : (prefixWord ++ tailWord_945222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945222).length < 2 ^ (prefixWord ++ tailWord_945222).sum := by decide
  have hdescent : baseEnd_945222 < baseStart_945222 := by decide
  rcases family_descends (prefixWord ++ tailWord_945222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945264 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_945264 : Nat := 118140960795 + 945264 * 2 ^ 59
def prefixEnd_945264 : Nat := 4983230072969 + 3 ^ 40 * 945264 * 2
def baseEnd_945264 : Nat := 431444246570395452402503

theorem tailTrace_945264 : CollatzResearch.WordTrace tailWord_945264 prefixEnd_945264 431444246570395452402503 := by
  unfold tailWord_945264
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238305223738720541777423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22984406964984960722369897 17238305223738720541777423)
  ·
    refine ⟨25857457835608080812666135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17238305223738720541777423 25857457835608080812666135)
    ·
      refine ⟨38786186753412121218999203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25857457835608080812666135 38786186753412121218999203)
      ·
        refine ⟨58179280130118181828498805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38786186753412121218999203 58179280130118181828498805)
        ·
          refine ⟨5454307512198579546421763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58179280130118181828498805 5454307512198579546421763)
          ·
            refine ⟨8181461268297869319632645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454307512198579546421763 8181461268297869319632645)
            ·
              refine ⟨1534023987805850497431121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8181461268297869319632645 1534023987805850497431121)
              ·
                refine ⟨1150517990854387873073341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534023987805850497431121 1150517990854387873073341)
                ·
                  refine ⟨431444246570395452402503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150517990854387873073341 431444246570395452402503)
                  ·
                    rfl

theorem cell20_945264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_945264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945264 prefixEnd_945264 := by exact prefixLift 945264
  have htrace : WordTrace (prefixWord ++ tailWord_945264) baseStart_945264 baseEnd_945264 := by
    simpa [prefixWord, tailWord_945264, baseEnd_945264] using wordTrace_append hprefix tailTrace_945264
  have hstable : (prefixWord ++ tailWord_945264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945264).length < 2 ^ (prefixWord ++ tailWord_945264).sum := by decide
  have hdescent : baseEnd_945264 < baseStart_945264 := by decide
  rcases family_descends (prefixWord ++ tailWord_945264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945288 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_945288 : Nat := 118140960795 + 945288 * 2 ^ 59
def prefixEnd_945288 : Nat := 4983230072969 + 3 ^ 40 * 945288 * 2
def baseEnd_945288 : Nat := 431455200824358035602405

theorem tailTrace_945288 : CollatzResearch.WordTrace tailWord_945288 prefixEnd_945288 431455200824358035602405 := by
  unfold tailWord_945288
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238742899695246591214259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22984990532926995454952345 17238742899695246591214259)
  ·
    refine ⟨25858114349542869886821389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17238742899695246591214259 25858114349542869886821389)
    ·
      refine ⟨9696792881078576207558021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25858114349542869886821389 9696792881078576207558021)
      ·
        refine ⟨1818148665202233038917129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9696792881078576207558021 1818148665202233038917129)
        ·
          refine ⟨1363611498901674779187847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818148665202233038917129 1363611498901674779187847)
          ·
            refine ⟨2045417248352512168781771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363611498901674779187847 2045417248352512168781771)
            ·
              refine ⟨3068125872528768253172657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045417248352512168781771 3068125872528768253172657)
              ·
                refine ⟨2301094404396576189879493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068125872528768253172657 2301094404396576189879493)
                ·
                  refine ⟨431455200824358035602405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301094404396576189879493 431455200824358035602405)
                  ·
                    rfl

theorem cell20_945288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_945288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945288 prefixEnd_945288 := by exact prefixLift 945288
  have htrace : WordTrace (prefixWord ++ tailWord_945288) baseStart_945288 baseEnd_945288 := by
    simpa [prefixWord, tailWord_945288, baseEnd_945288] using wordTrace_append hprefix tailTrace_945288
  have hstable : (prefixWord ++ tailWord_945288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945288).length < 2 ^ (prefixWord ++ tailWord_945288).sum := by decide
  have hdescent : baseEnd_945288 < baseStart_945288 := by decide
  rcases family_descends (prefixWord ++ tailWord_945288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945299 : List Nat := [1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_945299 : Nat := 118140960795 + 945299 * 2 ^ 59
def prefixEnd_945299 : Nat := 4983230072969 + 3 ^ 40 * 945299 * 2
def baseEnd_945299 : Nat := 143820073841363628745231

theorem tailTrace_945299 : CollatzResearch.WordTrace tailWord_945299 prefixEnd_945299 143820073841363628745231 := by
  unfold tailWord_945299
  simp only [CollatzResearch.WordTrace]
  refine ⟨34477887002350642061078951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22985258001567094707385967 34477887002350642061078951)
  ·
    refine ⟨51716830503525963091618427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34477887002350642061078951 51716830503525963091618427)
    ·
      refine ⟨77575245755288944637427641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51716830503525963091618427 77575245755288944637427641)
      ·
        refine ⟨58181434316466708478070731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77575245755288944637427641 58181434316466708478070731)
        ·
          refine ⟨87272151474700062717106097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58181434316466708478070731 87272151474700062717106097)
          ·
            refine ⟨65454113606025047037829573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87272151474700062717106097 65454113606025047037829573)
            ·
              refine ⟨12272646301129696319593045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65454113606025047037829573 12272646301129696319593045)
              ·
                refine ⟨143820073841363628745231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12272646301129696319593045 143820073841363628745231)
                ·
                  rfl

theorem cell20_945299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_945299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945299 prefixEnd_945299 := by exact prefixLift 945299
  have htrace : WordTrace (prefixWord ++ tailWord_945299) baseStart_945299 baseEnd_945299 := by
    simpa [prefixWord, tailWord_945299, baseEnd_945299] using wordTrace_append hprefix tailTrace_945299
  have hstable : (prefixWord ++ tailWord_945299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945299).length < 2 ^ (prefixWord ++ tailWord_945299).sum := by decide
  have hdescent : baseEnd_945299 < baseStart_945299 := by decide
  rcases family_descends (prefixWord ++ tailWord_945299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945316 : List Nat := [2, 3, 1, 2, 3, 2, 7]
def baseStart_945316 : Nat := 118140960795 + 945316 * 2 ^ 59
def prefixEnd_945316 : Nat := 4983230072969 + 3 ^ 40 * 945316 * 2
def baseEnd_945316 : Nat := 47940886754146042518773

theorem tailTrace_945316 : CollatzResearch.WordTrace tailWord_945316 prefixEnd_945316 47940886754146042518773 := by
  unfold tailWord_945316
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239253521644526982223901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22985671362192702642965201 17239253521644526982223901)
  ·
    refine ⟨6464720070616697618333963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17239253521644526982223901 6464720070616697618333963)
    ·
      refine ⟨9697080105925046427500945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464720070616697618333963 9697080105925046427500945)
      ·
        refine ⟨7272810079443784820625709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9697080105925046427500945 7272810079443784820625709)
        ·
          refine ⟨2727303779791419307734641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7272810079443784820625709 2727303779791419307734641)
          ·
            refine ⟨2045477834843564480800981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727303779791419307734641 2045477834843564480800981)
            ·
              refine ⟨47940886754146042518773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2045477834843564480800981 47940886754146042518773)
              ·
                rfl

theorem cell20_945316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_945316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945316 prefixEnd_945316 := by exact prefixLift 945316
  have htrace : WordTrace (prefixWord ++ tailWord_945316) baseStart_945316 baseEnd_945316 := by
    simpa [prefixWord, tailWord_945316, baseEnd_945316] using wordTrace_append hprefix tailTrace_945316
  have hstable : (prefixWord ++ tailWord_945316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945316).length < 2 ^ (prefixWord ++ tailWord_945316).sum := by decide
  have hdescent : baseEnd_945316 < baseStart_945316 := by decide
  rcases family_descends (prefixWord ++ tailWord_945316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945319 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_945319 : Nat := 118140960795 + 945319 * 2 ^ 59
def prefixEnd_945319 : Nat := 4983230072969 + 3 ^ 40 * 945319 * 2
def baseEnd_945319 : Nat := 431469350069059705568945

theorem tailTrace_945319 : CollatzResearch.WordTrace tailWord_945319 prefixEnd_945319 431469350069059705568945 := by
  unfold tailWord_945319
  simp only [CollatzResearch.WordTrace]
  refine ⟨34478616462278185476807011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22985744308185456984538007 34478616462278185476807011)
  ·
    refine ⟨51717924693417278215210517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34478616462278185476807011 51717924693417278215210517)
    ·
      refine ⟨2424277720003934916337993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51717924693417278215210517 2424277720003934916337993)
      ·
        refine ⟨1818208290002951187253495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424277720003934916337993 1818208290002951187253495)
        ·
          refine ⟨2727312435004426780880243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818208290002951187253495 2727312435004426780880243)
          ·
            refine ⟨4090968652506640171320365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727312435004426780880243 4090968652506640171320365)
            ·
              refine ⟨1534113244689990064245137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4090968652506640171320365 1534113244689990064245137)
              ·
                refine ⟨1150584933517492548183853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534113244689990064245137 1150584933517492548183853)
                ·
                  refine ⟨431469350069059705568945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150584933517492548183853 431469350069059705568945)
                  ·
                    rfl

theorem cell20_945319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_945319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945319 prefixEnd_945319 := by exact prefixLift 945319
  have htrace : WordTrace (prefixWord ++ tailWord_945319) baseStart_945319 baseEnd_945319 := by
    simpa [prefixWord, tailWord_945319, baseEnd_945319] using wordTrace_append hprefix tailTrace_945319
  have hstable : (prefixWord ++ tailWord_945319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945319).length < 2 ^ (prefixWord ++ tailWord_945319).sum := by decide
  have hdescent : baseEnd_945319 < baseStart_945319 := by decide
  rcases family_descends (prefixWord ++ tailWord_945319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945346 : List Nat := [3, 5, 1, 1, 2, 2, 2, 4]
def baseStart_945346 : Nat := 118140960795 + 945346 * 2 ^ 59
def prefixEnd_945346 : Nat := 4983230072969 + 3 ^ 40 * 945346 * 2
def baseEnd_945346 : Nat := 143827224534922537222945

theorem tailTrace_945346 : CollatzResearch.WordTrace tailWord_945346 prefixEnd_945346 143827224534922537222945 := by
  unfold tailWord_945346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619900308295092272009973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22986400822120246058693261 8619900308295092272009973)
  ·
    refine ⟨808115653902664900500935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8619900308295092272009973 808115653902664900500935)
    ·
      refine ⟨1212173480853997350751403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808115653902664900500935 1212173480853997350751403)
      ·
        refine ⟨1818260221280996026127105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212173480853997350751403 1818260221280996026127105)
        ·
          refine ⟨1363695165960747019595329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818260221280996026127105 1363695165960747019595329)
          ·
            refine ⟨1022771374470560264696497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363695165960747019595329 1022771374470560264696497)
            ·
              refine ⟨767078530852920198522373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022771374470560264696497 767078530852920198522373)
              ·
                refine ⟨143827224534922537222945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767078530852920198522373 143827224534922537222945)
                ·
                  rfl

theorem cell20_945346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_945346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945346 prefixEnd_945346 := by exact prefixLift 945346
  have htrace : WordTrace (prefixWord ++ tailWord_945346) baseStart_945346 baseEnd_945346 := by
    simpa [prefixWord, tailWord_945346, baseEnd_945346] using wordTrace_append hprefix tailTrace_945346
  have hstable : (prefixWord ++ tailWord_945346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945346).length < 2 ^ (prefixWord ++ tailWord_945346).sum := by decide
  have hdescent : baseEnd_945346 < baseStart_945346 := by decide
  rcases family_descends (prefixWord ++ tailWord_945346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945354 : List Nat := [3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_945354 : Nat := 118140960795 + 945354 * 2 ^ 59
def prefixEnd_945354 : Nat := 4983230072969 + 3 ^ 40 * 945354 * 2
def baseEnd_945354 : Nat := 143828441674251713134045

theorem tailTrace_945354 : CollatzResearch.WordTrace tailWord_945354 prefixEnd_945354 143828441674251713134045 := by
  unfold tailWord_945354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619973254287846613582779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22986595344767590969554077 8619973254287846613582779)
  ·
    refine ⟨12929959881431769920374169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8619973254287846613582779 12929959881431769920374169)
    ·
      refine ⟨9697469911073827440280627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12929959881431769920374169 9697469911073827440280627)
      ·
        refine ⟨14546204866610741160420941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697469911073827440280627 14546204866610741160420941)
        ·
          refine ⟨5454826824979027935157853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14546204866610741160420941 5454826824979027935157853)
          ·
            refine ⟨2045560059367135475684195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5454826824979027935157853 2045560059367135475684195)
            ·
              refine ⟨3068340089050703213526293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045560059367135475684195 3068340089050703213526293)
              ·
                refine ⟨143828441674251713134045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3068340089050703213526293 143828441674251713134045)
                ·
                  rfl

theorem cell20_945354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_945354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945354 prefixEnd_945354 := by exact prefixLift 945354
  have htrace : WordTrace (prefixWord ++ tailWord_945354) baseStart_945354 baseEnd_945354 := by
    simpa [prefixWord, tailWord_945354, baseEnd_945354] using wordTrace_append hprefix tailTrace_945354
  have hstable : (prefixWord ++ tailWord_945354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945354).length < 2 ^ (prefixWord ++ tailWord_945354).sum := by decide
  have hdescent : baseEnd_945354 < baseStart_945354 := by decide
  rcases family_descends (prefixWord ++ tailWord_945354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945375 : List Nat := [1, 1, 2, 3, 2, 1, 10]
def baseStart_945375 : Nat := 118140960795 + 945375 * 2 ^ 59
def prefixEnd_945375 : Nat := 4983230072969 + 3 ^ 40 * 945375 * 2
def baseEnd_945375 : Nat := 47943878888330266633561

theorem tailTrace_945375 : CollatzResearch.WordTrace tailWord_945375 prefixEnd_945375 47943878888330266633561 := by
  unfold tailWord_945375
  simp only [CollatzResearch.WordTrace]
  refine ⟨34480658950075307040845579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22987105966716871360563719 34480658950075307040845579)
  ·
    refine ⟨51720988425112960561268369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34480658950075307040845579 51720988425112960561268369)
    ·
      refine ⟨38790741318834720420951277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51720988425112960561268369 38790741318834720420951277)
      ·
        refine ⟨14546527994563020157856729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38790741318834720420951277 14546527994563020157856729)
        ·
          refine ⟨10909895995922265118392547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14546527994563020157856729 10909895995922265118392547)
          ·
            refine ⟨16364843993883397677588821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10909895995922265118392547 16364843993883397677588821)
            ·
              refine ⟨47943878888330266633561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16364843993883397677588821 47943878888330266633561)
              ·
                rfl

theorem cell20_945375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_945375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945375 prefixEnd_945375 := by exact prefixLift 945375
  have htrace : WordTrace (prefixWord ++ tailWord_945375) baseStart_945375 baseEnd_945375 := by
    simpa [prefixWord, tailWord_945375, baseEnd_945375] using wordTrace_append hprefix tailTrace_945375
  have hstable : (prefixWord ++ tailWord_945375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945375).length < 2 ^ (prefixWord ++ tailWord_945375).sum := by decide
  have hdescent : baseEnd_945375 < baseStart_945375 := by decide
  rcases family_descends (prefixWord ++ tailWord_945375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945381 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 4]
def baseStart_945381 : Nat := 118140960795 + 945381 * 2 ^ 59
def prefixEnd_945381 : Nat := 4983230072969 + 3 ^ 40 * 945381 * 2
def baseEnd_945381 : Nat := 431497648558463045502025

theorem tailTrace_945381 : CollatzResearch.WordTrace tailWord_945381 prefixEnd_945381 431497648558463045502025 := by
  unfold tailWord_945381
  simp only [CollatzResearch.WordTrace]
  refine ⟨34480877788053570065563997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22987251858702380043709331 34480877788053570065563997)
  ·
    refine ⟨12930329170520088774586499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34480877788053570065563997 12930329170520088774586499)
    ·
      refine ⟨19395493755780133161879749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12930329170520088774586499 19395493755780133161879749)
      ·
        refine ⟨3636655079208774967852453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19395493755780133161879749 3636655079208774967852453)
        ·
          refine ⟨681872827351645306472335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3636655079208774967852453 681872827351645306472335)
          ·
            refine ⟨1022809241027467959708503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681872827351645306472335 1022809241027467959708503)
            ·
              refine ⟨1534213861541201939562755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022809241027467959708503 1534213861541201939562755)
              ·
                refine ⟨2301320792311802909344133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534213861541201939562755 2301320792311802909344133)
                ·
                  refine ⟨431497648558463045502025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301320792311802909344133 431497648558463045502025)
                  ·
                    rfl

theorem cell20_945381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_945381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945381 prefixEnd_945381 := by exact prefixLift 945381
  have htrace : WordTrace (prefixWord ++ tailWord_945381) baseStart_945381 baseEnd_945381 := by
    simpa [prefixWord, tailWord_945381, baseEnd_945381] using wordTrace_append hprefix tailTrace_945381
  have hstable : (prefixWord ++ tailWord_945381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945381).length < 2 ^ (prefixWord ++ tailWord_945381).sum := by decide
  have hdescent : baseEnd_945381 < baseStart_945381 := by decide
  rcases family_descends (prefixWord ++ tailWord_945381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945395 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 3]
def baseStart_945395 : Nat := 118140960795 + 945395 * 2 ^ 59
def prefixEnd_945395 : Nat := 4983230072969 + 3 ^ 40 * 945395 * 2
def baseEnd_945395 : Nat := 431504038539941219035301

theorem tailTrace_945395 : CollatzResearch.WordTrace tailWord_945395 prefixEnd_945395 431504038539941219035301 := by
  unfold tailWord_945395
  simp only [CollatzResearch.WordTrace]
  refine ⟨34481388410002850456573639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22987592273335233637715759 34481388410002850456573639)
  ·
    refine ⟨51722082615004275684860459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34481388410002850456573639 51722082615004275684860459)
    ·
      refine ⟨77583123922506413527290689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51722082615004275684860459 77583123922506413527290689)
      ·
        refine ⟨58187342941879810145468017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77583123922506413527290689 58187342941879810145468017)
        ·
          refine ⟨43640507206409857609101013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58187342941879810145468017 43640507206409857609101013)
          ·
            refine ⟨1022824387650231037713305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43640507206409857609101013 1022824387650231037713305)
            ·
              refine ⟨767118290737673278284979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022824387650231037713305 767118290737673278284979)
              ·
                refine ⟨1150677436106509917427469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767118290737673278284979 1150677436106509917427469)
                ·
                  refine ⟨431504038539941219035301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150677436106509917427469 431504038539941219035301)
                  ·
                    rfl

theorem cell20_945395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_945395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945395 prefixEnd_945395 := by exact prefixLift 945395
  have htrace : WordTrace (prefixWord ++ tailWord_945395) baseStart_945395 baseEnd_945395 := by
    simpa [prefixWord, tailWord_945395, baseEnd_945395] using wordTrace_append hprefix tailTrace_945395
  have hstable : (prefixWord ++ tailWord_945395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945395).length < 2 ^ (prefixWord ++ tailWord_945395).sum := by decide
  have hdescent : baseEnd_945395 < baseStart_945395 := by decide
  rcases family_descends (prefixWord ++ tailWord_945395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945399 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_945399 : Nat := 118140960795 + 945399 * 2 ^ 59
def prefixEnd_945399 : Nat := 4983230072969 + 3 ^ 40 * 945399 * 2
def baseEnd_945399 : Nat := 431505864248934982901951

theorem tailTrace_945399 : CollatzResearch.WordTrace tailWord_945399 prefixEnd_945399 431505864248934982901951 := by
  unfold tailWord_945399
  simp only [CollatzResearch.WordTrace]
  refine ⟨34481534301988359139719251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22987689534658906093146167 34481534301988359139719251)
  ·
    refine ⟨51722301452982538709578877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34481534301988359139719251 51722301452982538709578877)
    ·
      refine ⟨19395863044868452016092079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51722301452982538709578877 19395863044868452016092079)
      ·
        refine ⟨29093794567302678024138119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19395863044868452016092079 29093794567302678024138119)
        ·
          refine ⟨43640691850954017036207179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29093794567302678024138119 43640691850954017036207179)
          ·
            refine ⟨65461037776431025554310769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43640691850954017036207179 65461037776431025554310769)
            ·
              refine ⟨49095778332323269165733077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65461037776431025554310769 49095778332323269165733077)
              ·
                refine ⟨1150682304663826621071869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49095778332323269165733077 1150682304663826621071869)
                ·
                  refine ⟨431505864248934982901951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150682304663826621071869 431505864248934982901951)
                  ·
                    rfl

theorem cell20_945399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_945399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945399 prefixEnd_945399 := by exact prefixLift 945399
  have htrace : WordTrace (prefixWord ++ tailWord_945399) baseStart_945399 baseEnd_945399 := by
    simpa [prefixWord, tailWord_945399, baseEnd_945399] using wordTrace_append hprefix tailTrace_945399
  have hstable : (prefixWord ++ tailWord_945399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945399).length < 2 ^ (prefixWord ++ tailWord_945399).sum := by decide
  have hdescent : baseEnd_945399 < baseStart_945399 := by decide
  rcases family_descends (prefixWord ++ tailWord_945399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945413 : List Nat := [1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_945413 : Nat := 118140960795 + 945413 * 2 ^ 59
def prefixEnd_945413 : Nat := 4983230072969 + 3 ^ 40 * 945413 * 2
def baseEnd_945413 : Nat := 143837418076804385478409

theorem tailTrace_945413 : CollatzResearch.WordTrace tailWord_945413 prefixEnd_945413 143837418076804385478409 := by
  unfold tailWord_945413
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482044923937639530728893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22988029949291759687152595 34482044923937639530728893)
  ·
    refine ⟨12930766846476614824023335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34482044923937639530728893 12930766846476614824023335)
    ·
      refine ⟨19396150269714922236035003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12930766846476614824023335 19396150269714922236035003)
      ·
        refine ⟨29094225404572383354052505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19396150269714922236035003 29094225404572383354052505)
        ·
          refine ⟨21820669053429287515539379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29094225404572383354052505 21820669053429287515539379)
          ·
            refine ⟨32731003580143931273309069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21820669053429287515539379 32731003580143931273309069)
            ·
              refine ⟨12274126342553974227490901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32731003580143931273309069 12274126342553974227490901)
              ·
                refine ⟨143837418076804385478409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12274126342553974227490901 143837418076804385478409)
                ·
                  rfl

theorem cell20_945413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_945413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945413 prefixEnd_945413 := by exact prefixLift 945413
  have htrace : WordTrace (prefixWord ++ tailWord_945413) baseStart_945413 baseEnd_945413 := by
    simpa [prefixWord, tailWord_945413, baseEnd_945413] using wordTrace_append hprefix tailTrace_945413
  have hstable : (prefixWord ++ tailWord_945413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945413).length < 2 ^ (prefixWord ++ tailWord_945413).sum := by decide
  have hdescent : baseEnd_945413 < baseStart_945413 := by decide
  rcases family_descends (prefixWord ++ tailWord_945413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945426 : List Nat := [3, 2, 4, 2, 2, 7]
def baseStart_945426 : Nat := 118140960795 + 945426 * 2 ^ 59
def prefixEnd_945426 : Nat := 4983230072969 + 3 ^ 40 * 945426 * 2
def baseEnd_945426 : Nat := 15982155103134921814883

theorem tailTrace_945426 : CollatzResearch.WordTrace tailWord_945426 prefixEnd_945426 15982155103134921814883 := by
  unfold tailWord_945426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620629768222635687738033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22988346048593695167301421 8620629768222635687738033)
  ·
    refine ⟨6465472326166976765803525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8620629768222635687738033 6465472326166976765803525)
    ·
      refine ⟨1212276061156308143588161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6465472326166976765803525 1212276061156308143588161)
      ·
        refine ⟨909207045867231107691121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1212276061156308143588161 909207045867231107691121)
        ·
          refine ⟨681905284400423330768341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909207045867231107691121 681905284400423330768341)
          ·
            refine ⟨15982155103134921814883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 681905284400423330768341 15982155103134921814883)
            ·
              rfl

theorem cell20_945426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 7].length) (baseStart_945426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945426 prefixEnd_945426 := by exact prefixLift 945426
  have htrace : WordTrace (prefixWord ++ tailWord_945426) baseStart_945426 baseEnd_945426 := by
    simpa [prefixWord, tailWord_945426, baseEnd_945426] using wordTrace_append hprefix tailTrace_945426
  have hstable : (prefixWord ++ tailWord_945426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945426).length < 2 ^ (prefixWord ++ tailWord_945426).sum := by decide
  have hdescent : baseEnd_945426 < baseStart_945426 := by decide
  rcases family_descends (prefixWord ++ tailWord_945426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945461 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_945461 : Nat := 118140960795 + 945461 * 2 ^ 59
def prefixEnd_945461 : Nat := 4983230072969 + 3 ^ 40 * 945461 * 2
def baseEnd_945461 : Nat := 431534162738338322835031

theorem tailTrace_945461 : CollatzResearch.WordTrace tailWord_945461 prefixEnd_945461 431534162738338322835031 := by
  unfold tailWord_945461
  simp only [CollatzResearch.WordTrace]
  refine ⟨34483795627763743728476237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22989197085175829152317491 34483795627763743728476237)
  ·
    refine ⟨12931423360411403898178589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34483795627763743728476237 12931423360411403898178589)
    ·
      refine ⟨4849283760154276461816971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12931423360411403898178589 4849283760154276461816971)
      ·
        refine ⟨7273925640231414692725457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4849283760154276461816971 7273925640231414692725457)
        ·
          refine ⟨5455444230173561019544093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7273925640231414692725457 5455444230173561019544093)
          ·
            refine ⟨2045791586315085382329035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5455444230173561019544093 2045791586315085382329035)
            ·
              refine ⟨3068687379472628073493553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045791586315085382329035 3068687379472628073493553)
              ·
                refine ⟨2301515534604471055120165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068687379472628073493553 2301515534604471055120165)
                ·
                  refine ⟨431534162738338322835031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301515534604471055120165 431534162738338322835031)
                  ·
                    rfl

theorem cell20_945461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_945461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945461 prefixEnd_945461 := by exact prefixLift 945461
  have htrace : WordTrace (prefixWord ++ tailWord_945461) baseStart_945461 baseEnd_945461 := by
    simpa [prefixWord, tailWord_945461, baseEnd_945461] using wordTrace_append hprefix tailTrace_945461
  have hstable : (prefixWord ++ tailWord_945461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945461).length < 2 ^ (prefixWord ++ tailWord_945461).sum := by decide
  have hdescent : baseEnd_945461 < baseStart_945461 := by decide
  rcases family_descends (prefixWord ++ tailWord_945461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945489 : List Nat := [1, 2, 2, 1, 4, 1, 9]
def baseStart_945489 : Nat := 118140960795 + 945489 * 2 ^ 59
def prefixEnd_945489 : Nat := 4983230072969 + 3 ^ 40 * 945489 * 2
def baseEnd_945489 : Nat := 47949660300143852211287

theorem tailTrace_945489 : CollatzResearch.WordTrace tailWord_945489 prefixEnd_945489 47949660300143852211287 := by
  unfold tailWord_945489
  simp only [CollatzResearch.WordTrace]
  refine ⟨34484816871662304510495521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22989877914441536340330347 34484816871662304510495521)
  ·
    refine ⟨25863612653746728382871641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34484816871662304510495521 25863612653746728382871641)
    ·
      refine ⟨19397709490310046287153731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25863612653746728382871641 19397709490310046287153731)
      ·
        refine ⟨29096564235465069430730597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19397709490310046287153731 29096564235465069430730597)
        ·
          refine ⟨5455605794149700518261987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29096564235465069430730597 5455605794149700518261987)
          ·
            refine ⟨8183408691224550777392981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455605794149700518261987 8183408691224550777392981)
            ·
              refine ⟨47949660300143852211287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8183408691224550777392981 47949660300143852211287)
              ·
                rfl

theorem cell20_945489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_945489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945489 prefixEnd_945489 := by exact prefixLift 945489
  have htrace : WordTrace (prefixWord ++ tailWord_945489) baseStart_945489 baseEnd_945489 := by
    simpa [prefixWord, tailWord_945489, baseEnd_945489] using wordTrace_append hprefix tailTrace_945489
  have hstable : (prefixWord ++ tailWord_945489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945489).length < 2 ^ (prefixWord ++ tailWord_945489).sum := by decide
  have hdescent : baseEnd_945489 < baseStart_945489 := by decide
  rcases family_descends (prefixWord ++ tailWord_945489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945506 : List Nat := [3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_945506 : Nat := 118140960795 + 945506 * 2 ^ 59
def prefixEnd_945506 : Nat := 4983230072969 + 3 ^ 40 * 945506 * 2
def baseEnd_945506 : Nat := 143851567321506055444949

theorem tailTrace_945506 : CollatzResearch.WordTrace tailWord_945506 prefixEnd_945506 143851567321506055444949 := by
  unfold tailWord_945506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621359228150179103466093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22990291275067144275909581 8621359228150179103466093)
  ·
    refine ⟨3233009710556317163799785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8621359228150179103466093 3233009710556317163799785)
    ·
      refine ⟨2424757282917237872849839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233009710556317163799785 2424757282917237872849839)
      ·
        refine ⟨3637135924375856809274759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424757282917237872849839 3637135924375856809274759)
        ·
          refine ⟨5455703886563785213912139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637135924375856809274759 5455703886563785213912139)
          ·
            refine ⟨8183555829845677820868209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455703886563785213912139 8183555829845677820868209)
            ·
              refine ⟨6137666872384258365651157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8183555829845677820868209 6137666872384258365651157)
              ·
                refine ⟨143851567321506055444949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6137666872384258365651157 143851567321506055444949)
                ·
                  rfl

theorem cell20_945506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_945506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945506 prefixEnd_945506 := by exact prefixLift 945506
  have htrace : WordTrace (prefixWord ++ tailWord_945506) baseStart_945506 baseEnd_945506 := by
    simpa [prefixWord, tailWord_945506, baseEnd_945506] using wordTrace_append hprefix tailTrace_945506
  have hstable : (prefixWord ++ tailWord_945506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945506).length < 2 ^ (prefixWord ++ tailWord_945506).sum := by decide
  have hdescent : baseEnd_945506 < baseStart_945506 := by decide
  rcases family_descends (prefixWord ++ tailWord_945506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945520 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_945520 : Nat := 118140960795 + 945520 * 2 ^ 59
def prefixEnd_945520 : Nat := 4983230072969 + 3 ^ 40 * 945520 * 2
def baseEnd_945520 : Nat := 431561091945996339868123

theorem tailTrace_945520 : CollatzResearch.WordTrace tailWord_945520 prefixEnd_945520 431561091945996339868123 := by
  unfold tailWord_945520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17242973767274998402437007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22990631689699997869916009 17242973767274998402437007)
  ·
    refine ⟨25864460650912497603655511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17242973767274998402437007 25864460650912497603655511)
    ·
      refine ⟨38796690976368746405483267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864460650912497603655511 38796690976368746405483267)
      ·
        refine ⟨58195036464553119608224901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38796690976368746405483267 58195036464553119608224901)
        ·
          refine ⟨10911569337103709926542169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58195036464553119608224901 10911569337103709926542169)
          ·
            refine ⟨8183677002827782444906627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10911569337103709926542169 8183677002827782444906627)
            ·
              refine ⟨12275515504241673667359941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183677002827782444906627 12275515504241673667359941)
              ·
                refine ⟨2301659157045313812629989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12275515504241673667359941 2301659157045313812629989)
                ·
                  refine ⟨431561091945996339868123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301659157045313812629989 431561091945996339868123)
                  ·
                    rfl

theorem cell20_945520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_945520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945520 prefixEnd_945520 := by exact prefixLift 945520
  have htrace : WordTrace (prefixWord ++ tailWord_945520) baseStart_945520 baseEnd_945520 := by
    simpa [prefixWord, tailWord_945520, baseEnd_945520] using wordTrace_append hprefix tailTrace_945520
  have hstable : (prefixWord ++ tailWord_945520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945520).length < 2 ^ (prefixWord ++ tailWord_945520).sum := by decide
  have hdescent : baseEnd_945520 < baseStart_945520 := by decide
  rcases family_descends (prefixWord ++ tailWord_945520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945527 : List Nat := [1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_945527 : Nat := 118140960795 + 945527 * 2 ^ 59
def prefixEnd_945527 : Nat := 4983230072969 + 3 ^ 40 * 945527 * 2
def baseEnd_945527 : Nat := 143854762312245142211587

theorem tailTrace_945527 : CollatzResearch.WordTrace tailWord_945527 prefixEnd_945527 143854762312245142211587 := by
  unfold tailWord_945527
  simp only [CollatzResearch.WordTrace]
  refine ⟨34486202845524637000378835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22990801897016424666919223 34486202845524637000378835)
  ·
    refine ⟨51729304268286955500568253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34486202845524637000378835 51729304268286955500568253)
    ·
      refine ⟨19398489100607608312713095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51729304268286955500568253 19398489100607608312713095)
      ·
        refine ⟨29097733650911412469069643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19398489100607608312713095 29097733650911412469069643)
        ·
          refine ⟨43646600476367118703604465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29097733650911412469069643 43646600476367118703604465)
          ·
            refine ⟨32734950357275339027703349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43646600476367118703604465 32734950357275339027703349)
            ·
              refine ⟨3068901595994563033847189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32734950357275339027703349 3068901595994563033847189)
              ·
                refine ⟨143854762312245142211587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3068901595994563033847189 143854762312245142211587)
                ·
                  rfl

theorem cell20_945527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_945527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945527 prefixEnd_945527 := by exact prefixLift 945527
  have htrace : WordTrace (prefixWord ++ tailWord_945527) baseStart_945527 baseEnd_945527 := by
    simpa [prefixWord, tailWord_945527, baseEnd_945527] using wordTrace_append hprefix tailTrace_945527
  have hstable : (prefixWord ++ tailWord_945527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945527).length < 2 ^ (prefixWord ++ tailWord_945527).sum := by decide
  have hdescent : baseEnd_945527 < baseStart_945527 := by decide
  rcases family_descends (prefixWord ++ tailWord_945527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945544 : List Nat := [2, 1, 3, 3, 1, 4, 6]
def baseStart_945544 : Nat := 118140960795 + 945544 * 2 ^ 59
def prefixEnd_945544 : Nat := 4983230072969 + 3 ^ 40 * 945544 * 2
def baseEnd_945544 : Nat := 47952449577773213674225

theorem tailTrace_945544 : CollatzResearch.WordTrace tailWord_945544 prefixEnd_945544 47952449577773213674225 := by
  unfold tailWord_945544
  simp only [CollatzResearch.WordTrace]
  refine ⟨17243411443231524451873843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22991215257642032602498457 17243411443231524451873843)
  ·
    refine ⟨25865117164847286677810765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17243411443231524451873843 25865117164847286677810765)
    ·
      refine ⟨9699418936817732504179037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25865117164847286677810765 9699418936817732504179037)
      ·
        refine ⟨3637282101306649689067139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9699418936817732504179037 3637282101306649689067139)
        ·
          refine ⟨5455923151959974533600709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637282101306649689067139 5455923151959974533600709)
          ·
            refine ⟨1022985590992495225050133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5455923151959974533600709 1022985590992495225050133)
            ·
              refine ⟨47952449577773213674225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1022985590992495225050133 47952449577773213674225)
              ·
                rfl

theorem cell20_945544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 6].length) (baseStart_945544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945544 prefixEnd_945544 := by exact prefixLift 945544
  have htrace : WordTrace (prefixWord ++ tailWord_945544) baseStart_945544 baseEnd_945544 := by
    simpa [prefixWord, tailWord_945544, baseEnd_945544] using wordTrace_append hprefix tailTrace_945544
  have hstable : (prefixWord ++ tailWord_945544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945544).length < 2 ^ (prefixWord ++ tailWord_945544).sum := by decide
  have hdescent : baseEnd_945544 < baseStart_945544 := by decide
  rcases family_descends (prefixWord ++ tailWord_945544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945550 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_945550 : Nat := 118140960795 + 945550 * 2 ^ 59
def prefixEnd_945550 : Nat := 4983230072969 + 3 ^ 40 * 945550 * 2
def baseEnd_945550 : Nat := 431574784763449568868001

theorem tailTrace_945550 : CollatzResearch.WordTrace tailWord_945550 prefixEnd_945550 431574784763449568868001 := by
  unfold tailWord_945550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310880215555163991058263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22991361149627541285644069 4310880215555163991058263)
  ·
    refine ⟨6466320323332745986587395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4310880215555163991058263 6466320323332745986587395)
    ·
      refine ⟨9699480484999118979881093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6466320323332745986587395 9699480484999118979881093)
      ·
        refine ⟨1818652590937334808727705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9699480484999118979881093 1818652590937334808727705)
        ·
          refine ⟨1363989443203001106545779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818652590937334808727705 1363989443203001106545779)
          ·
            refine ⟨2045984164804501659818669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363989443203001106545779 2045984164804501659818669)
            ·
              refine ⟨767244061801688122432001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2045984164804501659818669 767244061801688122432001)
              ·
                refine ⟨575433046351266091824001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767244061801688122432001 575433046351266091824001)
                ·
                  refine ⟨431574784763449568868001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575433046351266091824001 431574784763449568868001)
                  ·
                    rfl

theorem cell20_945550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_945550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945550 prefixEnd_945550 := by exact prefixLift 945550
  have htrace : WordTrace (prefixWord ++ tailWord_945550) baseStart_945550 baseEnd_945550 := by
    simpa [prefixWord, tailWord_945550, baseEnd_945550] using wordTrace_append hprefix tailTrace_945550
  have hstable : (prefixWord ++ tailWord_945550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945550).length < 2 ^ (prefixWord ++ tailWord_945550).sum := by decide
  have hdescent : baseEnd_945550 < baseStart_945550 := by decide
  rcases family_descends (prefixWord ++ tailWord_945550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945637 : List Nat := [1, 3, 1, 5, 1, 2, 3, 4]
def baseStart_945637 : Nat := 118140960795 + 945637 * 2 ^ 59
def prefixEnd_945637 : Nat := 4983230072969 + 3 ^ 40 * 945637 * 2
def baseEnd_945637 : Nat := 143871497978021310989215

theorem tailTrace_945637 : CollatzResearch.WordTrace tailWord_945637 prefixEnd_945637 143871497978021310989215 := by
  unfold tailWord_945637
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490214875126125786883165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22993476583417417191255443 34490214875126125786883165)
  ·
    refine ⟨12933830578172297170081187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34490214875126125786883165 12933830578172297170081187)
    ·
      refine ⟨19400745867258445755121781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12933830578172297170081187 19400745867258445755121781)
      ·
        refine ⟨1818819925055479289542667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19400745867258445755121781 1818819925055479289542667)
        ·
          refine ⟨2728229887583218934314001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818819925055479289542667 2728229887583218934314001)
          ·
            refine ⟨2046172415687414200735501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728229887583218934314001 2046172415687414200735501)
            ·
              refine ⟨767314655882780325275813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2046172415687414200735501 767314655882780325275813)
              ·
                refine ⟨143871497978021310989215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767314655882780325275813 143871497978021310989215)
                ·
                  rfl

theorem cell20_945637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_945637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945637 prefixEnd_945637 := by exact prefixLift 945637
  have htrace : WordTrace (prefixWord ++ tailWord_945637) baseStart_945637 baseEnd_945637 := by
    simpa [prefixWord, tailWord_945637, baseEnd_945637] using wordTrace_append hprefix tailTrace_945637
  have hstable : (prefixWord ++ tailWord_945637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945637).length < 2 ^ (prefixWord ++ tailWord_945637).sum := by decide
  have hdescent : baseEnd_945637 < baseStart_945637 := by decide
  rcases family_descends (prefixWord ++ tailWord_945637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945668 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_945668 : Nat := 118140960795 + 945668 * 2 ^ 59
def prefixEnd_945668 : Nat := 4983230072969 + 3 ^ 40 * 945668 * 2
def baseEnd_945668 : Nat := 431628643178765602934185

theorem tailTrace_945668 : CollatzResearch.WordTrace tailWord_945668 prefixEnd_945668 431628643178765602934185 := by
  unfold tailWord_945668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245672769006909040630829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22994230358675878720841105 17245672769006909040630829)
  ·
    refine ⟨6467127288377590890236561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17245672769006909040630829 6467127288377590890236561)
    ·
      refine ⟨4850345466283193167677421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6467127288377590890236561 4850345466283193167677421)
      ·
        refine ⟨1818879549856197437879033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4850345466283193167677421 1818879549856197437879033)
        ·
          refine ⟨1364159662392148078409275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818879549856197437879033 1364159662392148078409275)
          ·
            refine ⟨2046239493588222117613913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364159662392148078409275 2046239493588222117613913)
            ·
              refine ⟨1534679620191166588210435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046239493588222117613913 1534679620191166588210435)
              ·
                refine ⟨2302019430286749882315653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534679620191166588210435 2302019430286749882315653)
                ·
                  refine ⟨431628643178765602934185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302019430286749882315653 431628643178765602934185)
                  ·
                    rfl

theorem cell20_945668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_945668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945668 prefixEnd_945668 := by exact prefixLift 945668
  have htrace : WordTrace (prefixWord ++ tailWord_945668) baseStart_945668 baseEnd_945668 := by
    simpa [prefixWord, tailWord_945668, baseEnd_945668] using wordTrace_append hprefix tailTrace_945668
  have hstable : (prefixWord ++ tailWord_945668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945668).length < 2 ^ (prefixWord ++ tailWord_945668).sum := by decide
  have hdescent : baseEnd_945668 < baseStart_945668 := by decide
  rcases family_descends (prefixWord ++ tailWord_945668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945672 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_945672 : Nat := 118140960795 + 945672 * 2 ^ 59
def prefixEnd_945672 : Nat := 4983230072969 + 3 ^ 40 * 945672 * 2
def baseEnd_945672 : Nat := 431630468887759366800835

theorem tailTrace_945672 : CollatzResearch.WordTrace tailWord_945672 prefixEnd_945672 431630468887759366800835 := by
  unfold tailWord_945672
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245745714999663382203635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22994327619999551176271513 17245745714999663382203635)
  ·
    refine ⟨25868618572499495073305453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17245745714999663382203635 25868618572499495073305453)
    ·
      refine ⟨9700731964687310652489545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25868618572499495073305453 9700731964687310652489545)
      ·
        refine ⟨7275548973515482989367159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9700731964687310652489545 7275548973515482989367159)
        ·
          refine ⟨10913323460273224484050739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275548973515482989367159 10913323460273224484050739)
          ·
            refine ⟨16369985190409836726076109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10913323460273224484050739 16369985190409836726076109)
            ·
              refine ⟨6138744446403688772278541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16369985190409836726076109 6138744446403688772278541)
              ·
                refine ⟨2302029167401383289604453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6138744446403688772278541 2302029167401383289604453)
                ·
                  refine ⟨431630468887759366800835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302029167401383289604453 431630468887759366800835)
                  ·
                    rfl

theorem cell20_945672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_945672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945672 prefixEnd_945672 := by exact prefixLift 945672
  have htrace : WordTrace (prefixWord ++ tailWord_945672) baseStart_945672 baseEnd_945672 := by
    simpa [prefixWord, tailWord_945672, baseEnd_945672] using wordTrace_append hprefix tailTrace_945672
  have hstable : (prefixWord ++ tailWord_945672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945672).length < 2 ^ (prefixWord ++ tailWord_945672).sum := by decide
  have hdescent : baseEnd_945672 < baseStart_945672 := by decide
  rcases family_descends (prefixWord ++ tailWord_945672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945696 : List Nat := [2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_945696 : Nat := 118140960795 + 945696 * 2 ^ 59
def prefixEnd_945696 : Nat := 4983230072969 + 3 ^ 40 * 945696 * 2
def baseEnd_945696 : Nat := 143880474380573983333579

theorem tailTrace_945696 : CollatzResearch.WordTrace tailWord_945696 prefixEnd_945696 143880474380573983333579 := by
  unfold tailWord_945696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246183390956189431640471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22994911187941585908853961 17246183390956189431640471)
  ·
    refine ⟨25869275086434284147460707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17246183390956189431640471 25869275086434284147460707)
    ·
      refine ⟨38803912629651426221191061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25869275086434284147460707 38803912629651426221191061)
      ·
        refine ⟨1818933404514910604118331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38803912629651426221191061 1818933404514910604118331)
        ·
          refine ⟨2728400106772365906177497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818933404514910604118331 2728400106772365906177497)
          ·
            refine ⟨2046300080079274429633123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728400106772365906177497 2046300080079274429633123)
            ·
              refine ⟨3069450120118911644449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046300080079274429633123 3069450120118911644449685)
              ·
                refine ⟨143880474380573983333579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3069450120118911644449685 143880474380573983333579)
                ·
                  rfl

theorem cell20_945696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_945696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945696 prefixEnd_945696 := by exact prefixLift 945696
  have htrace : WordTrace (prefixWord ++ tailWord_945696) baseStart_945696 baseEnd_945696 := by
    simpa [prefixWord, tailWord_945696, baseEnd_945696] using wordTrace_append hprefix tailTrace_945696
  have hstable : (prefixWord ++ tailWord_945696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945696).length < 2 ^ (prefixWord ++ tailWord_945696).sum := by decide
  have hdescent : baseEnd_945696 < baseStart_945696 := by decide
  rcases family_descends (prefixWord ++ tailWord_945696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945717 : List Nat := [1, 3, 3, 1, 1, 3, 8]
def baseStart_945717 : Nat := 118140960795 + 945717 * 2 ^ 59
def prefixEnd_945717 : Nat := 4983230072969 + 3 ^ 40 * 945717 * 2
def baseEnd_945717 : Nat := 47961223123771023366739

theorem tailTrace_945717 : CollatzResearch.WordTrace tailWord_945717 prefixEnd_945717 47961223123771023366739 := by
  unfold tailWord_945717
  simp only [CollatzResearch.WordTrace]
  refine ⟨34493132714836299449795405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22995421809890866299863603 34493132714836299449795405)
  ·
    refine ⟨12934924768063612293673277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34493132714836299449795405 12934924768063612293673277)
    ·
      refine ⟨4850596788023854610127479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12934924768063612293673277 4850596788023854610127479)
      ·
        refine ⟨7275895182035781915191219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850596788023854610127479 7275895182035781915191219)
        ·
          refine ⟨10913842773053672872786829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275895182035781915191219 10913842773053672872786829)
          ·
            refine ⟨4092691039895127327295061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10913842773053672872786829 4092691039895127327295061)
            ·
              refine ⟨47961223123771023366739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4092691039895127327295061 47961223123771023366739)
              ·
                rfl

theorem cell20_945717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_945717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945717 prefixEnd_945717 := by exact prefixLift 945717
  have htrace : WordTrace (prefixWord ++ tailWord_945717) baseStart_945717 baseEnd_945717 := by
    simpa [prefixWord, tailWord_945717, baseEnd_945717] using wordTrace_append hprefix tailTrace_945717
  have hstable : (prefixWord ++ tailWord_945717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945717).length < 2 ^ (prefixWord ++ tailWord_945717).sum := by decide
  have hdescent : baseEnd_945717 < baseStart_945717 := by decide
  rcases family_descends (prefixWord ++ tailWord_945717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945727 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 4]
def baseStart_945727 : Nat := 118140960795 + 945727 * 2 ^ 59
def prefixEnd_945727 : Nat := 4983230072969 + 3 ^ 40 * 945727 * 2
def baseEnd_945727 : Nat := 431655572386423619967277

theorem tailTrace_945727 : CollatzResearch.WordTrace tailWord_945727 prefixEnd_945727 431655572386423619967277 := by
  unfold tailWord_945727
  simp only [CollatzResearch.WordTrace]
  refine ⟨34493497444800071157659435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22995664963200047438439623 34493497444800071157659435)
  ·
    refine ⟨51740246167200106736489153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34493497444800071157659435 51740246167200106736489153)
    ·
      refine ⟨38805184625400080052366865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51740246167200106736489153 38805184625400080052366865)
      ·
        refine ⟨29103888469050060039275149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38805184625400080052366865 29103888469050060039275149)
        ·
          refine ⟨10913958175893772514728181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29103888469050060039275149 10913958175893772514728181)
          ·
            refine ⟨1023183578990041173255767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10913958175893772514728181 1023183578990041173255767)
            ·
              refine ⟨1534775368485061759883651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023183578990041173255767 1534775368485061759883651)
              ·
                refine ⟨2302163052727592639825477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534775368485061759883651 2302163052727592639825477)
                ·
                  refine ⟨431655572386423619967277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302163052727592639825477 431655572386423619967277)
                  ·
                    rfl

theorem cell20_945727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_945727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945727 prefixEnd_945727 := by exact prefixLift 945727
  have htrace : WordTrace (prefixWord ++ tailWord_945727) baseStart_945727 baseEnd_945727 := by
    simpa [prefixWord, tailWord_945727, baseEnd_945727] using wordTrace_append hprefix tailTrace_945727
  have hstable : (prefixWord ++ tailWord_945727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945727).length < 2 ^ (prefixWord ++ tailWord_945727).sum := by decide
  have hdescent : baseEnd_945727 < baseStart_945727 := by decide
  rcases family_descends (prefixWord ++ tailWord_945727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945748 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_945748 : Nat := 118140960795 + 945748 * 2 ^ 59
def prefixEnd_945748 : Nat := 4983230072969 + 3 ^ 40 * 945748 * 2
def baseEnd_945748 : Nat := 431665157358640880267191

theorem tailTrace_945748 : CollatzResearch.WordTrace tailWord_945748 prefixEnd_945748 431665157358640880267191 := by
  unfold tailWord_945748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247131688861995872086949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22996175585149327829449265 17247131688861995872086949)
  ·
    refine ⟨3233837191661624226016303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17247131688861995872086949 3233837191661624226016303)
    ·
      refine ⟨4850755787492436339024455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233837191661624226016303 4850755787492436339024455)
      ·
        refine ⟨7276133681238654508536683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850755787492436339024455 7276133681238654508536683)
        ·
          refine ⟨10914200521857981762805025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276133681238654508536683 10914200521857981762805025)
          ·
            refine ⟨8185650391393486322103769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10914200521857981762805025 8185650391393486322103769)
            ·
              refine ⟨6139237793545114741577827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185650391393486322103769 6139237793545114741577827)
              ·
                refine ⟨9208856690317672112366741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139237793545114741577827 9208856690317672112366741)
                ·
                  refine ⟨431665157358640880267191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9208856690317672112366741 431665157358640880267191)
                  ·
                    rfl

theorem cell20_945748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_945748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945748 prefixEnd_945748 := by exact prefixLift 945748
  have htrace : WordTrace (prefixWord ++ tailWord_945748) baseStart_945748 baseEnd_945748 := by
    simpa [prefixWord, tailWord_945748, baseEnd_945748] using wordTrace_append hprefix tailTrace_945748
  have hstable : (prefixWord ++ tailWord_945748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945748).length < 2 ^ (prefixWord ++ tailWord_945748).sum := by decide
  have hdescent : baseEnd_945748 < baseStart_945748 := by decide
  rcases family_descends (prefixWord ++ tailWord_945748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945893 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_945893 : Nat := 118140960795 + 945893 * 2 ^ 59
def prefixEnd_945893 : Nat := 4983230072969 + 3 ^ 40 * 945893 * 2
def baseEnd_945893 : Nat := 431731339309664820433265

theorem tailTrace_945893 : CollatzResearch.WordTrace tailWord_945893 prefixEnd_945893 431731339309664820433265 := by
  unfold tailWord_945893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34499551962198681508202333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22999701308132454338801555 34499551962198681508202333)
  ·
    refine ⟨12937331985824505565575875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34499551962198681508202333 12937331985824505565575875)
    ·
      refine ⟨19405997978736758348363813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12937331985824505565575875 19405997978736758348363813)
      ·
        refine ⟨3638624621013142190318215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19405997978736758348363813 3638624621013142190318215)
        ·
          refine ⟨5457936931519713285477323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638624621013142190318215 5457936931519713285477323)
          ·
            refine ⟨8186905397279569928215985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457936931519713285477323 8186905397279569928215985)
            ·
              refine ⟨6140179047959677446161989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186905397279569928215985 6140179047959677446161989)
              ·
                refine ⟨1151283571492439521155373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6140179047959677446161989 1151283571492439521155373)
                ·
                  refine ⟨431731339309664820433265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151283571492439521155373 431731339309664820433265)
                  ·
                    rfl

theorem cell20_945893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_945893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945893 prefixEnd_945893 := by exact prefixLift 945893
  have htrace : WordTrace (prefixWord ++ tailWord_945893) baseStart_945893 baseEnd_945893 := by
    simpa [prefixWord, tailWord_945893, baseEnd_945893] using wordTrace_append hprefix tailTrace_945893
  have hstable : (prefixWord ++ tailWord_945893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945893).length < 2 ^ (prefixWord ++ tailWord_945893).sum := by decide
  have hdescent : baseEnd_945893 < baseStart_945893 := by decide
  rcases family_descends (prefixWord ++ tailWord_945893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945900 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_945900 : Nat := 118140960795 + 945900 * 2 ^ 59
def prefixEnd_945900 : Nat := 4983230072969 + 3 ^ 40 * 945900 * 2
def baseEnd_945900 : Nat := 431734534300403907199903

theorem tailTrace_945900 : CollatzResearch.WordTrace tailWord_945900 prefixEnd_945900 431734534300403907199903 := by
  unfold tailWord_945900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249903636586660851853577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22999871515448881135804769 17249903636586660851853577)
  ·
    refine ⟨12937427727439995638890183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17249903636586660851853577 12937427727439995638890183)
    ·
      refine ⟨19406141591159993458335275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12937427727439995638890183 19406141591159993458335275)
      ·
        refine ⟨29109212386739990187502913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19406141591159993458335275 29109212386739990187502913)
        ·
          refine ⟨21831909290054992640627185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29109212386739990187502913 21831909290054992640627185)
          ·
            refine ⟨16373931967541244480470389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21831909290054992640627185 16373931967541244480470389)
            ·
              refine ⟨1535056121956991670044099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16373931967541244480470389 1535056121956991670044099)
              ·
                refine ⟨2302584182935487505066149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535056121956991670044099 2302584182935487505066149)
                ·
                  refine ⟨431734534300403907199903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302584182935487505066149 431734534300403907199903)
                  ·
                    rfl

theorem cell20_945900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_945900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945900 prefixEnd_945900 := by exact prefixLift 945900
  have htrace : WordTrace (prefixWord ++ tailWord_945900) baseStart_945900 baseEnd_945900 := by
    simpa [prefixWord, tailWord_945900, baseEnd_945900] using wordTrace_append hprefix tailTrace_945900
  have hstable : (prefixWord ++ tailWord_945900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945900).length < 2 ^ (prefixWord ++ tailWord_945900).sum := by decide
  have hdescent : baseEnd_945900 < baseStart_945900 := by decide
  rcases family_descends (prefixWord ++ tailWord_945900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945910 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_945910 : Nat := 118140960795 + 945910 * 2 ^ 59
def prefixEnd_945910 : Nat := 4983230072969 + 3 ^ 40 * 945910 * 2
def baseEnd_945910 : Nat := 431739098572888316866529

theorem tailTrace_945910 : CollatzResearch.WordTrace tailWord_945910 prefixEnd_945910 431739098572888316866529 := by
  unfold tailWord_945910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156260750196068338223199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23000114668758062274380789 2156260750196068338223199)
  ·
    refine ⟨3234391125294102507334799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156260750196068338223199 3234391125294102507334799)
    ·
      refine ⟨4851586687941153761002199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234391125294102507334799 4851586687941153761002199)
      ·
        refine ⟨7277380031911730641503299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851586687941153761002199 7277380031911730641503299)
        ·
          refine ⟨10916070047867595962254949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277380031911730641503299 10916070047867595962254949)
          ·
            refine ⟨2046763133975174242922803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10916070047867595962254949 2046763133975174242922803)
            ·
              refine ⟨3070144700962761364384205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046763133975174242922803 3070144700962761364384205)
              ·
                refine ⟨1151304262861035511644077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3070144700962761364384205 1151304262861035511644077)
                ·
                  refine ⟨431739098572888316866529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151304262861035511644077 431739098572888316866529)
                  ·
                    rfl

theorem cell20_945910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_945910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945910 prefixEnd_945910 := by exact prefixLift 945910
  have htrace : WordTrace (prefixWord ++ tailWord_945910) baseStart_945910 baseEnd_945910 := by
    simpa [prefixWord, tailWord_945910, baseEnd_945910] using wordTrace_append hprefix tailTrace_945910
  have hstable : (prefixWord ++ tailWord_945910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945910).length < 2 ^ (prefixWord ++ tailWord_945910).sum := by decide
  have hdescent : baseEnd_945910 < baseStart_945910 := by decide
  rcases family_descends (prefixWord ++ tailWord_945910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945969 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_945969 : Nat := 118140960795 + 945969 * 2 ^ 59
def prefixEnd_945969 : Nat := 4983230072969 + 3 ^ 40 * 945969 * 2
def baseEnd_945969 : Nat := 431766027780546333899621

theorem tailTrace_945969 : CollatzResearch.WordTrace tailWord_945969 prefixEnd_945969 431766027780546333899621 := by
  unfold tailWord_945969
  simp only [CollatzResearch.WordTrace]
  refine ⟨34502323909923346487968961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23001549273282230991979307 34502323909923346487968961)
  ·
    refine ⟨25876742932442509865976721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34502323909923346487968961 25876742932442509865976721)
    ·
      refine ⟨19407557199331882399482541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25876742932442509865976721 19407557199331882399482541)
      ·
        refine ⟨7277833949749455899805953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19407557199331882399482541 7277833949749455899805953)
        ·
          refine ⟨5458375462312091924854465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277833949749455899805953 5458375462312091924854465)
          ·
            refine ⟨4093781596734068943640849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458375462312091924854465 4093781596734068943640849)
            ·
              refine ⟨3070336197550551707730637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4093781596734068943640849 3070336197550551707730637)
              ·
                refine ⟨1151376074081456890398989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3070336197550551707730637 1151376074081456890398989)
                ·
                  refine ⟨431766027780546333899621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151376074081456890398989 431766027780546333899621)
                  ·
                    rfl

theorem cell20_945969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_945969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945969 prefixEnd_945969 := by exact prefixLift 945969
  have htrace : WordTrace (prefixWord ++ tailWord_945969) baseStart_945969 baseEnd_945969 := by
    simpa [prefixWord, tailWord_945969, baseEnd_945969] using wordTrace_append hprefix tailTrace_945969
  have hstable : (prefixWord ++ tailWord_945969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945969).length < 2 ^ (prefixWord ++ tailWord_945969).sum := by decide
  have hdescent : baseEnd_945969 < baseStart_945969 := by decide
  rcases family_descends (prefixWord ++ tailWord_945969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945976 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_945976 : Nat := 118140960795 + 945976 * 2 ^ 59
def prefixEnd_945976 : Nat := 4983230072969 + 3 ^ 40 * 945976 * 2
def baseEnd_945976 : Nat := 431769222771285420666259

theorem tailTrace_945976 : CollatzResearch.WordTrace tailWord_945976 prefixEnd_945976 431769222771285420666259 := by
  unfold tailWord_945976
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251289610448993341736891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23001719480598657788982521 17251289610448993341736891)
  ·
    refine ⟨25876934415673490012605337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17251289610448993341736891 25876934415673490012605337)
    ·
      refine ⟨19407700811755117509454003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25876934415673490012605337 19407700811755117509454003)
      ·
        refine ⟨29111551217632676264181005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19407700811755117509454003 29111551217632676264181005)
        ·
          refine ⟨10916831706612253599067877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29111551217632676264181005 10916831706612253599067877)
          ·
            refine ⟨2046905944989797549825227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10916831706612253599067877 2046905944989797549825227)
            ·
              refine ⟨3070358917484696324737841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046905944989797549825227 3070358917484696324737841)
              ·
                refine ⟨2302769188113522243553381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070358917484696324737841 2302769188113522243553381)
                ·
                  refine ⟨431769222771285420666259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302769188113522243553381 431769222771285420666259)
                  ·
                    rfl

theorem cell20_945976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_945976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945976 prefixEnd_945976 := by exact prefixLift 945976
  have htrace : WordTrace (prefixWord ++ tailWord_945976) baseStart_945976 baseEnd_945976 := by
    simpa [prefixWord, tailWord_945976, baseEnd_945976] using wordTrace_append hprefix tailTrace_945976
  have hstable : (prefixWord ++ tailWord_945976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945976).length < 2 ^ (prefixWord ++ tailWord_945976).sum := by decide
  have hdescent : baseEnd_945976 < baseStart_945976 := by decide
  rcases family_descends (prefixWord ++ tailWord_945976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945993 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 2]
def baseStart_945993 : Nat := 118140960795 + 945993 * 2 ^ 59
def prefixEnd_945993 : Nat := 4983230072969 + 3 ^ 40 * 945993 * 2
def baseEnd_945993 : Nat := 431776982034508917099523

theorem tailTrace_945993 : CollatzResearch.WordTrace tailWord_945993 prefixEnd_945993 431776982034508917099523 := by
  unfold tailWord_945993
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503199261836398586842633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23002132841224265724561755 34503199261836398586842633)
  ·
    refine ⟨25877399446377298940131975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34503199261836398586842633 25877399446377298940131975)
    ·
      refine ⟨38816099169565948410197963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25877399446377298940131975 38816099169565948410197963)
      ·
        refine ⟨58224148754348922615296945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38816099169565948410197963 58224148754348922615296945)
        ·
          refine ⟨43668111565761691961472709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58224148754348922615296945 43668111565761691961472709)
          ·
            refine ⟨8187770918580317242776133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43668111565761691961472709 8187770918580317242776133)
            ·
              refine ⟨1535207047233809483020525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8187770918580317242776133 1535207047233809483020525)
              ·
                refine ⟨575702642712678556132697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535207047233809483020525 575702642712678556132697)
                ·
                  refine ⟨431776982034508917099523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575702642712678556132697 431776982034508917099523)
                  ·
                    rfl

theorem cell20_945993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_945993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_945993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_945993 prefixEnd_945993 := by exact prefixLift 945993
  have htrace : WordTrace (prefixWord ++ tailWord_945993) baseStart_945993 baseEnd_945993 := by
    simpa [prefixWord, tailWord_945993, baseEnd_945993] using wordTrace_append hprefix tailTrace_945993
  have hstable : (prefixWord ++ tailWord_945993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945993).length < 2 ^ (prefixWord ++ tailWord_945993).sum := by decide
  have hdescent : baseEnd_945993 < baseStart_945993 := by decide
  rcases family_descends (prefixWord ++ tailWord_945993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946007 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_946007 : Nat := 118140960795 + 946007 * 2 ^ 59
def prefixEnd_946007 : Nat := 4983230072969 + 3 ^ 40 * 946007 * 2
def baseEnd_946007 : Nat := 431783372015987090632799

theorem tailTrace_946007 : CollatzResearch.WordTrace tailWord_946007 prefixEnd_946007 431783372015987090632799 := by
  unfold tailWord_946007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503709883785678977852275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23002473255857119318568183 34503709883785678977852275)
  ·
    refine ⟨51755564825678518466778413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34503709883785678977852275 51755564825678518466778413)
    ·
      refine ⟨19408336809629444425041905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51755564825678518466778413 19408336809629444425041905)
      ·
        refine ⟨14556252607222083318781429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19408336809629444425041905 14556252607222083318781429)
        ·
          refine ⟨1364648681927070311135759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14556252607222083318781429 1364648681927070311135759)
          ·
            refine ⟨2046973022890605466703639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364648681927070311135759 2046973022890605466703639)
            ·
              refine ⟨3070459534335908200055459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046973022890605466703639 3070459534335908200055459)
              ·
                refine ⟨4605689301503862300083189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070459534335908200055459 4605689301503862300083189)
                ·
                  refine ⟨431783372015987090632799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4605689301503862300083189 431783372015987090632799)
                  ·
                    rfl

theorem cell20_946007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_946007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946007 prefixEnd_946007 := by exact prefixLift 946007
  have htrace : WordTrace (prefixWord ++ tailWord_946007) baseStart_946007 baseEnd_946007 := by
    simpa [prefixWord, tailWord_946007, baseEnd_946007] using wordTrace_append hprefix tailTrace_946007
  have hstable : (prefixWord ++ tailWord_946007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946007).length < 2 ^ (prefixWord ++ tailWord_946007).sum := by decide
  have hdescent : baseEnd_946007 < baseStart_946007 := by decide
  rcases family_descends (prefixWord ++ tailWord_946007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946024 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_946024 : Nat := 118140960795 + 946024 * 2 ^ 59
def prefixEnd_946024 : Nat := 4983230072969 + 3 ^ 40 * 946024 * 2
def baseEnd_946024 : Nat := 431791131279210587066063

theorem tailTrace_946024 : CollatzResearch.WordTrace tailWord_946024 prefixEnd_946024 431791131279210587066063 := by
  unfold tailWord_946024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17252164962362045440610563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23002886616482727254147417 17252164962362045440610563)
  ·
    refine ⟨25878247443543068160915845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17252164962362045440610563 25878247443543068160915845)
    ·
      refine ⟨4852171395664325280171721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25878247443543068160915845 4852171395664325280171721)
      ·
        refine ⟨3639128546748243960128791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4852171395664325280171721 3639128546748243960128791)
        ·
          refine ⟨5458692820122365940193187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639128546748243960128791 5458692820122365940193187)
          ·
            refine ⟨8188039230183548910289781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458692820122365940193187 8188039230183548910289781)
            ·
              refine ⟨767628677829707710339667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8188039230183548910289781 767628677829707710339667)
              ·
                refine ⟨1151443016744561565509501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767628677829707710339667 1151443016744561565509501)
                ·
                  refine ⟨431791131279210587066063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151443016744561565509501 431791131279210587066063)
                  ·
                    rfl

theorem cell20_946024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_946024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946024 prefixEnd_946024 := by exact prefixLift 946024
  have htrace : WordTrace (prefixWord ++ tailWord_946024) baseStart_946024 baseEnd_946024 := by
    simpa [prefixWord, tailWord_946024, baseEnd_946024] using wordTrace_append hprefix tailTrace_946024
  have hstable : (prefixWord ++ tailWord_946024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946024).length < 2 ^ (prefixWord ++ tailWord_946024).sum := by decide
  have hdescent : baseEnd_946024 < baseStart_946024 := by decide
  rcases family_descends (prefixWord ++ tailWord_946024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946076 : List Nat := [2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_946076 : Nat := 118140960795 + 946076 * 2 ^ 59
def prefixEnd_946076 : Nat := 4983230072969 + 3 ^ 40 * 946076 * 2
def baseEnd_946076 : Nat := 143938288498709839110839

theorem tailTrace_946076 : CollatzResearch.WordTrace tailWord_946076 prefixEnd_946076 143938288498709839110839 := by
  unfold tailWord_946076
  simp only [CollatzResearch.WordTrace]
  refine ⟨17253113260267851881057041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23004151013690469174742721 17253113260267851881057041)
  ·
    refine ⟨12939834945200888910792781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17253113260267851881057041 12939834945200888910792781)
    ·
      refine ⟨4852438104450333341547293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12939834945200888910792781 4852438104450333341547293)
      ·
        refine ⟨1819664289168875003080235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4852438104450333341547293 1819664289168875003080235)
        ·
          refine ⟨2729496433753312504620353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819664289168875003080235 2729496433753312504620353)
          ·
            refine ⟨2047122325314984378465265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729496433753312504620353 2047122325314984378465265)
            ·
              refine ⟨1535341743986238283848949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047122325314984378465265 1535341743986238283848949)
              ·
                refine ⟨143938288498709839110839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1535341743986238283848949 143938288498709839110839)
                ·
                  rfl

theorem cell20_946076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_946076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946076 prefixEnd_946076 := by exact prefixLift 946076
  have htrace : WordTrace (prefixWord ++ tailWord_946076) baseStart_946076 baseEnd_946076 := by
    simpa [prefixWord, tailWord_946076, baseEnd_946076] using wordTrace_append hprefix tailTrace_946076
  have hstable : (prefixWord ++ tailWord_946076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946076).length < 2 ^ (prefixWord ++ tailWord_946076).sum := by decide
  have hdescent : baseEnd_946076 < baseStart_946076 := by decide
  rcases family_descends (prefixWord ++ tailWord_946076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946079 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 3]
def baseStart_946079 : Nat := 118140960795 + 946079 * 2 ^ 59
def prefixEnd_946079 : Nat := 4983230072969 + 3 ^ 40 * 946079 * 2
def baseEnd_946079 : Nat := 431816234777874840232505

theorem tailTrace_946079 : CollatzResearch.WordTrace tailWord_946079 prefixEnd_946079 431816234777874840232505 := by
  unfold tailWord_946079
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506335939524835274473291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23004223959683223516315527 34506335939524835274473291)
  ·
    refine ⟨51759503909287252911709937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34506335939524835274473291 51759503909287252911709937)
    ·
      refine ⟨38819627931965439683782453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51759503909287252911709937 38819627931965439683782453)
      ·
        refine ⟨3639340118621759970354605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38819627931965439683782453 3639340118621759970354605)
        ·
          refine ⟨1364752544483159988882977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3639340118621759970354605 1364752544483159988882977)
          ·
            refine ⟨1023564408362369991662233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364752544483159988882977 1023564408362369991662233)
            ·
              refine ⟨767673306271777493746675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023564408362369991662233 767673306271777493746675)
              ·
                refine ⟨1151509959407666240620013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767673306271777493746675 1151509959407666240620013)
                ·
                  refine ⟨431816234777874840232505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151509959407666240620013 431816234777874840232505)
                  ·
                    rfl

theorem cell20_946079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_946079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946079 prefixEnd_946079 := by exact prefixLift 946079
  have htrace : WordTrace (prefixWord ++ tailWord_946079) baseStart_946079 baseEnd_946079 := by
    simpa [prefixWord, tailWord_946079, baseEnd_946079] using wordTrace_append hprefix tailTrace_946079
  have hstable : (prefixWord ++ tailWord_946079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946079).length < 2 ^ (prefixWord ++ tailWord_946079).sum := by decide
  have hdescent : baseEnd_946079 < baseStart_946079 := by decide
  rcases family_descends (prefixWord ++ tailWord_946079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946097 : List Nat := [1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_946097 : Nat := 118140960795 + 946097 * 2 ^ 59
def prefixEnd_946097 : Nat := 4983230072969 + 3 ^ 40 * 946097 * 2
def baseEnd_946097 : Nat := 143941483489448925877477

theorem tailTrace_946097 : CollatzResearch.WordTrace tailWord_946097 prefixEnd_946097 143941483489448925877477 := by
  unfold tailWord_946097
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506992453459624348628545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23004661635639749565752363 34506992453459624348628545)
  ·
    refine ⟨25880244340094718261471409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34506992453459624348628545 25880244340094718261471409)
    ·
      refine ⟨19410183255071038696103557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25880244340094718261471409 19410183255071038696103557)
      ·
        refine ⟨3639409360325819755519417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19410183255071038696103557 3639409360325819755519417)
        ·
          refine ⟨2729557020244364816639563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639409360325819755519417 2729557020244364816639563)
          ·
            refine ⟨4094335530366547224959345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729557020244364816639563 4094335530366547224959345)
            ·
              refine ⟨3070751647774910418719509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094335530366547224959345 3070751647774910418719509)
              ·
                refine ⟨143941483489448925877477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3070751647774910418719509 143941483489448925877477)
                ·
                  rfl

theorem cell20_946097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_946097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946097 prefixEnd_946097 := by exact prefixLift 946097
  have htrace : WordTrace (prefixWord ++ tailWord_946097) baseStart_946097 baseEnd_946097 := by
    simpa [prefixWord, tailWord_946097, baseEnd_946097] using wordTrace_append hprefix tailTrace_946097
  have hstable : (prefixWord ++ tailWord_946097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946097).length < 2 ^ (prefixWord ++ tailWord_946097).sum := by decide
  have hdescent : baseEnd_946097 < baseStart_946097 := by decide
  rcases family_descends (prefixWord ++ tailWord_946097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946124 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 2]
def baseStart_946124 : Nat := 118140960795 + 946124 * 2 ^ 59
def prefixEnd_946124 : Nat := 4983230072969 + 3 ^ 40 * 946124 * 2
def baseEnd_946124 : Nat := 431836774004054683732321

theorem tailTrace_946124 : CollatzResearch.WordTrace tailWord_946124 prefixEnd_946124 431836774004054683732321 := by
  unfold tailWord_946124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17253988612180903979930713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23005318149574538639907617 17253988612180903979930713)
  ·
    refine ⟨12940491459135677984948035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17253988612180903979930713 12940491459135677984948035)
    ·
      refine ⟨19410737188703516977422053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12940491459135677984948035 19410737188703516977422053)
      ·
        refine ⟨3639513222881909433266635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19410737188703516977422053 3639513222881909433266635)
        ·
          refine ⟨5459269834322864149899953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639513222881909433266635 5459269834322864149899953)
          ·
            refine ⟨4094452375742148112424965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459269834322864149899953 4094452375742148112424965)
            ·
              refine ⟨767709820451652771079681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4094452375742148112424965 767709820451652771079681)
              ·
                refine ⟨575782365338739578309761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767709820451652771079681 575782365338739578309761)
                ·
                  refine ⟨431836774004054683732321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575782365338739578309761 431836774004054683732321)
                  ·
                    rfl

theorem cell20_946124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_946124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946124 prefixEnd_946124 := by exact prefixLift 946124
  have htrace : WordTrace (prefixWord ++ tailWord_946124) baseStart_946124 baseEnd_946124 := by
    simpa [prefixWord, tailWord_946124, baseEnd_946124] using wordTrace_append hprefix tailTrace_946124
  have hstable : (prefixWord ++ tailWord_946124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946124).length < 2 ^ (prefixWord ++ tailWord_946124).sum := by decide
  have hdescent : baseEnd_946124 < baseStart_946124 := by decide
  rcases family_descends (prefixWord ++ tailWord_946124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946156 : List Nat := [2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_946156 : Nat := 118140960795 + 946156 * 2 ^ 59
def prefixEnd_946156 : Nat := 4983230072969 + 3 ^ 40 * 946156 * 2
def baseEnd_946156 : Nat := 143950459892001598221841

theorem tailTrace_946156 : CollatzResearch.WordTrace tailWord_946156 prefixEnd_946156 143950459892001598221841 := by
  unfold tailWord_946156
  simp only [CollatzResearch.WordTrace]
  refine ⟨17254572180122938712513161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23006096240163918283350881 17254572180122938712513161)
  ·
    refine ⟨12940929135092204034384871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17254572180122938712513161 12940929135092204034384871)
    ·
      refine ⟨19411393702638306051577307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12940929135092204034384871 19411393702638306051577307)
      ·
        refine ⟨29117090553957459077365961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19411393702638306051577307 29117090553957459077365961)
        ·
          refine ⟨21837817915468094308024471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29117090553957459077365961 21837817915468094308024471)
          ·
            refine ⟨32756726873202141462036707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21837817915468094308024471 32756726873202141462036707)
            ·
              refine ⟨49135090309803212193055061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32756726873202141462036707 49135090309803212193055061)
              ·
                refine ⟨143950459892001598221841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49135090309803212193055061 143950459892001598221841)
                ·
                  rfl

theorem cell20_946156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_946156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946156 prefixEnd_946156 := by exact prefixLift 946156
  have htrace : WordTrace (prefixWord ++ tailWord_946156) baseStart_946156 baseEnd_946156 := by
    simpa [prefixWord, tailWord_946156, baseEnd_946156] using wordTrace_append hprefix tailTrace_946156
  have hstable : (prefixWord ++ tailWord_946156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946156).length < 2 ^ (prefixWord ++ tailWord_946156).sum := by decide
  have hdescent : baseEnd_946156 < baseStart_946156 := by decide
  rcases family_descends (prefixWord ++ tailWord_946156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946183 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 2]
def baseStart_946183 : Nat := 118140960795 + 946183 * 2 ^ 59
def prefixEnd_946183 : Nat := 4983230072969 + 3 ^ 40 * 946183 * 2
def baseEnd_946183 : Nat := 431863703211712700765413

theorem tailTrace_946183 : CollatzResearch.WordTrace tailWord_946183 prefixEnd_946183 431863703211712700765413 := by
  unfold tailWord_946183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34510129131148061036259203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23006752754098707357506135 34510129131148061036259203)
  ·
    refine ⟨51765193696722091554388805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34510129131148061036259203 51765193696722091554388805)
    ·
      refine ⟨9705973818135392166447901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51765193696722091554388805 9705973818135392166447901)
      ·
        refine ⟨3639740181800772062417963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9705973818135392166447901 3639740181800772062417963)
        ·
          refine ⟨5459610272701158093626945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639740181800772062417963 5459610272701158093626945)
          ·
            refine ⟨4094707704525868570220209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459610272701158093626945 4094707704525868570220209)
            ·
              refine ⟨3071030778394401427665157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094707704525868570220209 3071030778394401427665157)
              ·
                refine ⟨575818270948950267687217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3071030778394401427665157 575818270948950267687217)
                ·
                  refine ⟨431863703211712700765413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575818270948950267687217 431863703211712700765413)
                  ·
                    rfl

theorem cell20_946183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 2].length) (baseStart_946183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946183 prefixEnd_946183 := by exact prefixLift 946183
  have htrace : WordTrace (prefixWord ++ tailWord_946183) baseStart_946183 baseEnd_946183 := by
    simpa [prefixWord, tailWord_946183, baseEnd_946183] using wordTrace_append hprefix tailTrace_946183
  have hstable : (prefixWord ++ tailWord_946183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946183).length < 2 ^ (prefixWord ++ tailWord_946183).sum := by decide
  have hdescent : baseEnd_946183 < baseStart_946183 := by decide
  rcases family_descends (prefixWord ++ tailWord_946183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946189 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 3]
def baseStart_946189 : Nat := 118140960795 + 946189 * 2 ^ 59
def prefixEnd_946189 : Nat := 4983230072969 + 3 ^ 40 * 946189 * 2
def baseEnd_946189 : Nat := 431866441775203346565389

theorem tailTrace_946189 : CollatzResearch.WordTrace tailWord_946189 prefixEnd_946189 431866441775203346565389 := by
  unfold tailWord_946189
  simp only [CollatzResearch.WordTrace]
  refine ⟨34510347969126324060977621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23006898646084216040651747 34510347969126324060977621)
  ·
    refine ⟨808836280526398220179163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 34510347969126324060977621 808836280526398220179163)
    ·
      refine ⟨1213254420789597330268745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808836280526398220179163 1213254420789597330268745)
      ·
        refine ⟨909940815592197997701559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1213254420789597330268745 909940815592197997701559)
        ·
          refine ⟨1364911223388296996552339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909940815592197997701559 1364911223388296996552339)
          ·
            refine ⟨2047366835082445494828509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364911223388296996552339 2047366835082445494828509)
            ·
              refine ⟨767762563155917060560691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2047366835082445494828509 767762563155917060560691)
              ·
                refine ⟨1151643844733875590841037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767762563155917060560691 1151643844733875590841037)
                ·
                  refine ⟨431866441775203346565389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151643844733875590841037 431866441775203346565389)
                  ·
                    rfl

theorem cell20_946189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_946189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946189 prefixEnd_946189 := by exact prefixLift 946189
  have htrace : WordTrace (prefixWord ++ tailWord_946189) baseStart_946189 baseEnd_946189 := by
    simpa [prefixWord, tailWord_946189, baseEnd_946189] using wordTrace_append hprefix tailTrace_946189
  have hstable : (prefixWord ++ tailWord_946189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946189).length < 2 ^ (prefixWord ++ tailWord_946189).sum := by decide
  have hdescent : baseEnd_946189 < baseStart_946189 := by decide
  rcases family_descends (prefixWord ++ tailWord_946189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946204 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_946204 : Nat := 118140960795 + 946204 * 2 ^ 59
def prefixEnd_946204 : Nat := 4983230072969 + 3 ^ 40 * 946204 * 2
def baseEnd_946204 : Nat := 431873288183929961065327

theorem tailTrace_946204 : CollatzResearch.WordTrace tailWord_946204 prefixEnd_946204 431873288183929961065327 := by
  unfold tailWord_946204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255447532035990811386833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23007263376047987748515777 17255447532035990811386833)
  ·
    refine ⟨12941585649026993108540125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17255447532035990811386833 12941585649026993108540125)
    ·
      refine ⟨4853094618385122415702547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12941585649026993108540125 4853094618385122415702547)
      ·
        refine ⟨7279641927577683623553821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853094618385122415702547 7279641927577683623553821)
        ·
          refine ⟨2729865722841631358832683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7279641927577683623553821 2729865722841631358832683)
          ·
            refine ⟨4094798584262447038249025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729865722841631358832683 4094798584262447038249025)
            ·
              refine ⟨3071098938196835278686769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094798584262447038249025 3071098938196835278686769)
              ·
                refine ⟨2303324203647626459015077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3071098938196835278686769 2303324203647626459015077)
                ·
                  refine ⟨431873288183929961065327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303324203647626459015077 431873288183929961065327)
                  ·
                    rfl

theorem cell20_946204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_946204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946204 prefixEnd_946204 := by exact prefixLift 946204
  have htrace : WordTrace (prefixWord ++ tailWord_946204) baseStart_946204 baseEnd_946204 := by
    simpa [prefixWord, tailWord_946204, baseEnd_946204] using wordTrace_append hprefix tailTrace_946204
  have hstable : (prefixWord ++ tailWord_946204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946204).length < 2 ^ (prefixWord ++ tailWord_946204).sum := by decide
  have hdescent : baseEnd_946204 < baseStart_946204 := by decide
  rcases family_descends (prefixWord ++ tailWord_946204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946238 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_946238 : Nat := 118140960795 + 946238 * 2 ^ 59
def prefixEnd_946238 : Nat := 4983230072969 + 3 ^ 40 * 946238 * 2
def baseEnd_946238 : Nat := 431888806710376953931855

theorem tailTrace_946238 : CollatzResearch.WordTrace tailWord_946238 prefixEnd_946238 431888806710376953931855 := by
  unfold tailWord_946238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314016893243600678688921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23008090097299203619674245 4314016893243600678688921)
  ·
    refine ⟨3235512669932700509016691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4314016893243600678688921 3235512669932700509016691)
    ·
      refine ⟨4853269004899050763525037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235512669932700509016691 4853269004899050763525037)
      ·
        refine ⟨1819975876837144036321889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4853269004899050763525037 1819975876837144036321889)
        ·
          refine ⟨1364981907627858027241417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819975876837144036321889 1364981907627858027241417)
          ·
            refine ⟨1023736430720893520431063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364981907627858027241417 1023736430720893520431063)
            ·
              refine ⟨1535604646081340280646595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023736430720893520431063 1535604646081340280646595)
              ·
                refine ⟨2303406969122010420969893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535604646081340280646595 2303406969122010420969893)
                ·
                  refine ⟨431888806710376953931855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303406969122010420969893 431888806710376953931855)
                  ·
                    rfl

theorem cell20_946238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_946238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946238 prefixEnd_946238 := by exact prefixLift 946238
  have htrace : WordTrace (prefixWord ++ tailWord_946238) baseStart_946238 baseEnd_946238 := by
    simpa [prefixWord, tailWord_946238, baseEnd_946238] using wordTrace_append hprefix tailTrace_946238
  have hstable : (prefixWord ++ tailWord_946238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946238).length < 2 ^ (prefixWord ++ tailWord_946238).sum := by decide
  have hdescent : baseEnd_946238 < baseStart_946238 := by decide
  rcases family_descends (prefixWord ++ tailWord_946238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946263 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_946263 : Nat := 118140960795 + 946263 * 2 ^ 59
def prefixEnd_946263 : Nat := 4983230072969 + 3 ^ 40 * 946263 * 2
def baseEnd_946263 : Nat := 431900217391587978098419

theorem tailTrace_946263 : CollatzResearch.WordTrace tailWord_946263 prefixEnd_946263 431900217391587978098419 := by
  unfold tailWord_946263
  simp only [CollatzResearch.WordTrace]
  refine ⟨34513046970858234699171443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23008697980572156466114295 34513046970858234699171443)
  ·
    refine ⟨51769570456287352048757165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34513046970858234699171443 51769570456287352048757165)
    ·
      refine ⟨19413588921107757018283937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51769570456287352048757165 19413588921107757018283937)
      ·
        refine ⟨14560191690830817763712953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19413588921107757018283937 14560191690830817763712953)
        ·
          refine ⟨10920143768123113322784715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14560191690830817763712953 10920143768123113322784715)
          ·
            refine ⟨16380215652184669984177073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10920143768123113322784715 16380215652184669984177073)
            ·
              refine ⟨12285161739138502488132805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16380215652184669984177073 12285161739138502488132805)
              ·
                refine ⟨2303467826088469216524901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12285161739138502488132805 2303467826088469216524901)
                ·
                  refine ⟨431900217391587978098419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303467826088469216524901 431900217391587978098419)
                  ·
                    rfl

theorem cell20_946263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_946263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946263 prefixEnd_946263 := by exact prefixLift 946263
  have htrace : WordTrace (prefixWord ++ tailWord_946263) baseStart_946263 baseEnd_946263 := by
    simpa [prefixWord, tailWord_946263, baseEnd_946263] using wordTrace_append hprefix tailTrace_946263
  have hstable : (prefixWord ++ tailWord_946263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946263).length < 2 ^ (prefixWord ++ tailWord_946263).sum := by decide
  have hdescent : baseEnd_946263 < baseStart_946263 := by decide
  rcases family_descends (prefixWord ++ tailWord_946263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946297 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 2]
def baseStart_946297 : Nat := 118140960795 + 946297 * 2 ^ 59
def prefixEnd_946297 : Nat := 4983230072969 + 3 ^ 40 * 946297 * 2
def baseEnd_946297 : Nat := 431915735918034970964947

theorem tailTrace_946297 : CollatzResearch.WordTrace tailWord_946297 prefixEnd_946297 431915735918034970964947 := by
  unfold tailWord_946297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34514287052735058505909145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23009524701823372337272763 34514287052735058505909145)
  ·
    refine ⟨25885715289551293879431859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34514287052735058505909145 25885715289551293879431859)
    ·
      refine ⟨38828572934326940819147789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25885715289551293879431859 38828572934326940819147789)
      ·
        refine ⟨14560714850372602807180421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38828572934326940819147789 14560714850372602807180421)
        ·
          refine ⟨2730134034444863026346329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14560714850372602807180421 2730134034444863026346329)
          ·
            refine ⟨2047600525833647269759747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730134034444863026346329 2047600525833647269759747)
            ·
              refine ⟨3071400788750470904639621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047600525833647269759747 3071400788750470904639621)
              ·
                refine ⟨575887647890713294619929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3071400788750470904639621 575887647890713294619929)
                ·
                  refine ⟨431915735918034970964947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575887647890713294619929 431915735918034970964947)
                  ·
                    rfl

theorem cell20_946297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_946297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946297 prefixEnd_946297 := by exact prefixLift 946297
  have htrace : WordTrace (prefixWord ++ tailWord_946297) baseStart_946297 baseEnd_946297 := by
    simpa [prefixWord, tailWord_946297, baseEnd_946297] using wordTrace_append hprefix tailTrace_946297
  have hstable : (prefixWord ++ tailWord_946297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946297).length < 2 ^ (prefixWord ++ tailWord_946297).sum := by decide
  have hdescent : baseEnd_946297 < baseStart_946297 := by decide
  rcases family_descends (prefixWord ++ tailWord_946297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946315 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_946315 : Nat := 118140960795 + 946315 * 2 ^ 59
def prefixEnd_946315 : Nat := 4983230072969 + 3 ^ 40 * 946315 * 2
def baseEnd_946315 : Nat := 431923951608506908364873

theorem tailTrace_946315 : CollatzResearch.WordTrace tailWord_946315 prefixEnd_946315 431923951608506908364873 := by
  unfold tailWord_946315
  simp only [CollatzResearch.WordTrace]
  refine ⟨34514943566669847580064399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23009962377779898386709599 34514943566669847580064399)
  ·
    refine ⟨51772415350004771370096599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34514943566669847580064399 51772415350004771370096599)
    ·
      refine ⟨77658623025007157055144899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51772415350004771370096599 77658623025007157055144899)
      ·
        refine ⟨116487934537510735582717349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77658623025007157055144899 116487934537510735582717349)
        ·
          refine ⟨21841487725783262921759503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116487934537510735582717349 21841487725783262921759503)
          ·
            refine ⟨32762231588674894382639255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21841487725783262921759503 32762231588674894382639255)
            ·
              refine ⟨49143347383012341573958883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32762231588674894382639255 49143347383012341573958883)
              ·
                refine ⟨73715021074518512360938325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49143347383012341573958883 73715021074518512360938325)
                ·
                  refine ⟨431923951608506908364873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73715021074518512360938325 431923951608506908364873)
                  ·
                    rfl

theorem cell20_946315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_946315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946315 prefixEnd_946315 := by exact prefixLift 946315
  have htrace : WordTrace (prefixWord ++ tailWord_946315) baseStart_946315 baseEnd_946315 := by
    simpa [prefixWord, tailWord_946315, baseEnd_946315] using wordTrace_append hprefix tailTrace_946315
  have hstable : (prefixWord ++ tailWord_946315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946315).length < 2 ^ (prefixWord ++ tailWord_946315).sum := by decide
  have hdescent : baseEnd_946315 < baseStart_946315 := by decide
  rcases family_descends (prefixWord ++ tailWord_946315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946325 : List Nat := [1, 3, 2, 1, 1, 1, 7, 4]
def baseStart_946325 : Nat := 118140960795 + 946325 * 2 ^ 59
def prefixEnd_946325 : Nat := 4983230072969 + 3 ^ 40 * 946325 * 2
def baseEnd_946325 : Nat := 143976171960330439343833

theorem tailTrace_946325 : CollatzResearch.WordTrace tailWord_946325 prefixEnd_946325 143976171960330439343833 := by
  unfold tailWord_946325
  simp only [CollatzResearch.WordTrace]
  refine ⟨34515308296633619287928429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23010205531089079525285619 34515308296633619287928429)
  ·
    refine ⟨12943240611237607232973161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34515308296633619287928429 12943240611237607232973161)
    ·
      refine ⟨9707430458428205424729871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12943240611237607232973161 9707430458428205424729871)
      ·
        refine ⟨14561145687642308137094807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707430458428205424729871 14561145687642308137094807)
        ·
          refine ⟨21841718531463462205642211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561145687642308137094807 21841718531463462205642211)
          ·
            refine ⟨32762577797195193308463317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21841718531463462205642211 32762577797195193308463317)
            ·
              refine ⟨767872917121762343167109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32762577797195193308463317 767872917121762343167109)
              ·
                refine ⟨143976171960330439343833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767872917121762343167109 143976171960330439343833)
                ·
                  rfl

theorem cell20_946325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_946325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946325 prefixEnd_946325 := by exact prefixLift 946325
  have htrace : WordTrace (prefixWord ++ tailWord_946325) baseStart_946325 baseEnd_946325 := by
    simpa [prefixWord, tailWord_946325, baseEnd_946325] using wordTrace_append hprefix tailTrace_946325
  have hstable : (prefixWord ++ tailWord_946325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946325).length < 2 ^ (prefixWord ++ tailWord_946325).sum := by decide
  have hdescent : baseEnd_946325 < baseStart_946325 := by decide
  rcases family_descends (prefixWord ++ tailWord_946325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946332 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_946332 : Nat := 118140960795 + 946332 * 2 ^ 59
def prefixEnd_946332 : Nat := 4983230072969 + 3 ^ 40 * 946332 * 2
def baseEnd_946332 : Nat := 431931710871730404798137

theorem tailTrace_946332 : CollatzResearch.WordTrace tailWord_946332 prefixEnd_946332 431931710871730404798137 := by
  unfold tailWord_946332
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257781803804129741716625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23010375738405506322288833 17257781803804129741716625)
  ·
    refine ⟨12943336352853097306287469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17257781803804129741716625 12943336352853097306287469)
    ·
      refine ⟨4853751132319911489857801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12943336352853097306287469 4853751132319911489857801)
      ·
        refine ⟨3640313349239933617393351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4853751132319911489857801 3640313349239933617393351)
        ·
          refine ⟨5460470023859900426090027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640313349239933617393351 5460470023859900426090027)
          ·
            refine ⟨8190705035789850639135041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460470023859900426090027 8190705035789850639135041)
            ·
              refine ⟨6143028776842387979351281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8190705035789850639135041 6143028776842387979351281)
              ·
                refine ⟨4607271582631790984513461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6143028776842387979351281 4607271582631790984513461)
                ·
                  refine ⟨431931710871730404798137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4607271582631790984513461 431931710871730404798137)
                  ·
                    rfl

theorem cell20_946332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_946332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946332 prefixEnd_946332 := by exact prefixLift 946332
  have htrace : WordTrace (prefixWord ++ tailWord_946332) baseStart_946332 baseEnd_946332 := by
    simpa [prefixWord, tailWord_946332, baseEnd_946332] using wordTrace_append hprefix tailTrace_946332
  have hstable : (prefixWord ++ tailWord_946332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946332).length < 2 ^ (prefixWord ++ tailWord_946332).sum := by decide
  have hdescent : baseEnd_946332 < baseStart_946332 := by decide
  rcases family_descends (prefixWord ++ tailWord_946332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946335 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 2]
def baseStart_946335 : Nat := 118140960795 + 946335 * 2 ^ 59
def prefixEnd_946335 : Nat := 4983230072969 + 3 ^ 40 * 946335 * 2
def baseEnd_946335 : Nat := 431933080153475727698125

theorem tailTrace_946335 : CollatzResearch.WordTrace tailWord_946335 prefixEnd_946335 431933080153475727698125 := by
  unfold tailWord_946335
  simp only [CollatzResearch.WordTrace]
  refine ⟨34515673026597390995792459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23010448684398260663861639 34515673026597390995792459)
  ·
    refine ⟨51773509539896086493688689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34515673026597390995792459 51773509539896086493688689)
    ·
      refine ⟨38830132154922064870266517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51773509539896086493688689 38830132154922064870266517)
      ·
        refine ⟨1820162444761971790793743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38830132154922064870266517 1820162444761971790793743)
        ·
          refine ⟨2730243667142957686190615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820162444761971790793743 2730243667142957686190615)
          ·
            refine ⟨4095365500714436529285923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730243667142957686190615 4095365500714436529285923)
            ·
              refine ⟨6143048251071654793928885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095365500714436529285923 6143048251071654793928885)
              ·
                refine ⟨575910773537967636930833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6143048251071654793928885 575910773537967636930833)
                ·
                  refine ⟨431933080153475727698125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575910773537967636930833 431933080153475727698125)
                  ·
                    rfl

theorem cell20_946335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 2].length) (baseStart_946335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946335 prefixEnd_946335 := by exact prefixLift 946335
  have htrace : WordTrace (prefixWord ++ tailWord_946335) baseStart_946335 baseEnd_946335 := by
    simpa [prefixWord, tailWord_946335, baseEnd_946335] using wordTrace_append hprefix tailTrace_946335
  have hstable : (prefixWord ++ tailWord_946335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946335).length < 2 ^ (prefixWord ++ tailWord_946335).sum := by decide
  have hdescent : baseEnd_946335 < baseStart_946335 := by decide
  rcases family_descends (prefixWord ++ tailWord_946335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946349 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_946349 : Nat := 118140960795 + 946349 * 2 ^ 59
def prefixEnd_946349 : Nat := 4983230072969 + 3 ^ 40 * 946349 * 2
def baseEnd_946349 : Nat := 431939470134953901231401

theorem tailTrace_946349 : CollatzResearch.WordTrace tailWord_946349 prefixEnd_946349 431939470134953901231401 := by
  unfold tailWord_946349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34516183648546671386802101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23010789099031114257868067 34516183648546671386802101)
  ·
    refine ⟨3235892217051250442512697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34516183648546671386802101 3235892217051250442512697)
    ·
      refine ⟨2426919162788437831884523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3235892217051250442512697 2426919162788437831884523)
      ·
        refine ⟨3640378744182656747826785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426919162788437831884523 3640378744182656747826785)
        ·
          refine ⟨2730284058136992560870089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3640378744182656747826785 2730284058136992560870089)
          ·
            refine ⟨2047713043602744420652567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730284058136992560870089 2047713043602744420652567)
            ·
              refine ⟨3071569565404116630978851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047713043602744420652567 3071569565404116630978851)
              ·
                refine ⟨4607354348106174946468277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071569565404116630978851 4607354348106174946468277)
                ·
                  refine ⟨431939470134953901231401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4607354348106174946468277 431939470134953901231401)
                  ·
                    rfl

theorem cell20_946349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_946349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946349 prefixEnd_946349 := by exact prefixLift 946349
  have htrace : WordTrace (prefixWord ++ tailWord_946349) baseStart_946349 baseEnd_946349 := by
    simpa [prefixWord, tailWord_946349, baseEnd_946349] using wordTrace_append hprefix tailTrace_946349
  have hstable : (prefixWord ++ tailWord_946349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946349).length < 2 ^ (prefixWord ++ tailWord_946349).sum := by decide
  have hdescent : baseEnd_946349 < baseStart_946349 := by decide
  rcases family_descends (prefixWord ++ tailWord_946349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946380 : List Nat := [2, 2, 1, 6, 1, 1, 1, 6]
def baseStart_946380 : Nat := 118140960795 + 946380 * 2 ^ 59
def prefixEnd_946380 : Nat := 4983230072969 + 3 ^ 40 * 946380 * 2
def baseEnd_946380 : Nat := 143984539793218523732647

theorem tailTrace_946380 : CollatzResearch.WordTrace tailWord_946380 prefixEnd_946380 143984539793218523732647 := by
  unfold tailWord_946380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258657155717181840590297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23011542874289575787453729 17258657155717181840590297)
  ·
    refine ⟨12943992866787886380442723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17258657155717181840590297 12943992866787886380442723)
    ·
      refine ⟨19415989300181829570664085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12943992866787886380442723 19415989300181829570664085)
      ·
        refine ⟨910124498446023261124879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19415989300181829570664085 910124498446023261124879)
        ·
          refine ⟨1365186747669034891687319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910124498446023261124879 1365186747669034891687319)
          ·
            refine ⟨2047780121503552337530979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365186747669034891687319 2047780121503552337530979)
            ·
              refine ⟨3071670182255328506296469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047780121503552337530979 3071670182255328506296469)
              ·
                refine ⟨143984539793218523732647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3071670182255328506296469 143984539793218523732647)
                ·
                  rfl

theorem cell20_946380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_946380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946380 prefixEnd_946380 := by exact prefixLift 946380
  have htrace : WordTrace (prefixWord ++ tailWord_946380) baseStart_946380 baseEnd_946380 := by
    simpa [prefixWord, tailWord_946380, baseEnd_946380] using wordTrace_append hprefix tailTrace_946380
  have hstable : (prefixWord ++ tailWord_946380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946380).length < 2 ^ (prefixWord ++ tailWord_946380).sum := by decide
  have hdescent : baseEnd_946380 < baseStart_946380 := by decide
  rcases family_descends (prefixWord ++ tailWord_946380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946408 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_946408 : Nat := 118140960795 + 946408 * 2 ^ 59
def prefixEnd_946408 : Nat := 4983230072969 + 3 ^ 40 * 946408 * 2
def baseEnd_946408 : Nat := 431966399342611918264493

theorem tailTrace_946408 : CollatzResearch.WordTrace tailWord_946408 prefixEnd_946408 431966399342611918264493 := by
  unfold tailWord_946408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259167777666462231599939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23012223703555282975466585 17259167777666462231599939)
  ·
    refine ⟨25888751666499693347399909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17259167777666462231599939 25888751666499693347399909)
    ·
      refine ⟨4854140937468692502637483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25888751666499693347399909 4854140937468692502637483)
      ·
        refine ⟨7281211406203038753956225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854140937468692502637483 7281211406203038753956225)
        ·
          refine ⟨5460908554652279065467169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281211406203038753956225 5460908554652279065467169)
          ·
            refine ⟨4095681415989209299100377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5460908554652279065467169 4095681415989209299100377)
            ·
              refine ⟨3071761061991906974325283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095681415989209299100377 3071761061991906974325283)
              ·
                refine ⟨4607641592987860461487925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071761061991906974325283 4607641592987860461487925)
                ·
                  refine ⟨431966399342611918264493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4607641592987860461487925 431966399342611918264493)
                  ·
                    rfl

theorem cell20_946408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_946408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946408 prefixEnd_946408 := by exact prefixLift 946408
  have htrace : WordTrace (prefixWord ++ tailWord_946408) baseStart_946408 baseEnd_946408 := by
    simpa [prefixWord, tailWord_946408, baseEnd_946408] using wordTrace_append hprefix tailTrace_946408
  have hstable : (prefixWord ++ tailWord_946408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946408).length < 2 ^ (prefixWord ++ tailWord_946408).sum := by decide
  have hdescent : baseEnd_946408 < baseStart_946408 := by decide
  rcases family_descends (prefixWord ++ tailWord_946408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946411 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 2]
def baseStart_946411 : Nat := 118140960795 + 946411 * 2 ^ 59
def prefixEnd_946411 : Nat := 4983230072969 + 3 ^ 40 * 946411 * 2
def baseEnd_946411 : Nat := 431967768624357241164481

theorem tailTrace_946411 : CollatzResearch.WordTrace tailWord_946411 prefixEnd_946411 431967768624357241164481 := by
  unfold tailWord_946411
  simp only [CollatzResearch.WordTrace]
  refine ⟨34518444974322055975559087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23012296649548037317039391 34518444974322055975559087)
  ·
    refine ⟨51777667461483083963338631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34518444974322055975559087 51777667461483083963338631)
    ·
      refine ⟨77666501192224625945007947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51777667461483083963338631 77666501192224625945007947)
      ·
        refine ⟨116499751788336938917511921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77666501192224625945007947 116499751788336938917511921)
        ·
          refine ⟨87374813841252704188133941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116499751788336938917511921 87374813841252704188133941)
          ·
            refine ⟨8191388797617441017637557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87374813841252704188133941 8191388797617441017637557)
            ·
              refine ⟨767942699776635095403521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8191388797617441017637557 767942699776635095403521)
              ·
                refine ⟨575957024832476321552641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767942699776635095403521 575957024832476321552641)
                ·
                  refine ⟨431967768624357241164481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575957024832476321552641 431967768624357241164481)
                  ·
                    rfl

theorem cell20_946411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 2].length) (baseStart_946411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946411 prefixEnd_946411 := by exact prefixLift 946411
  have htrace : WordTrace (prefixWord ++ tailWord_946411) baseStart_946411 baseEnd_946411 := by
    simpa [prefixWord, tailWord_946411, baseEnd_946411] using wordTrace_append hprefix tailTrace_946411
  have hstable : (prefixWord ++ tailWord_946411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946411).length < 2 ^ (prefixWord ++ tailWord_946411).sum := by decide
  have hdescent : baseEnd_946411 < baseStart_946411 := by decide
  rcases family_descends (prefixWord ++ tailWord_946411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946462 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_946462 : Nat := 118140960795 + 946462 * 2 ^ 59
def prefixEnd_946462 : Nat := 4983230072969 + 3 ^ 40 * 946462 * 2
def baseEnd_946462 : Nat := 431991046414027730464273

theorem tailTrace_946462 : CollatzResearch.WordTrace tailWord_946462 prefixEnd_946462 431991046414027730464273 := by
  unfold tailWord_946462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315038137142161460708205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23013536731424861123777093 4315038137142161460708205)
  ·
    refine ⟨1618139301428310547765577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4315038137142161460708205 1618139301428310547765577)
    ·
      refine ⟨1213604476071232910824183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1618139301428310547765577 1213604476071232910824183)
      ·
        refine ⟨1820406714106849366236275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213604476071232910824183 1820406714106849366236275)
        ·
          refine ⟨2730610071160274049354413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820406714106849366236275 2730610071160274049354413)
          ·
            refine ⟨1023978776685102768507905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2730610071160274049354413 1023978776685102768507905)
            ·
              refine ⟨767984082513827076380929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023978776685102768507905 767984082513827076380929)
              ·
                refine ⟨575988061885370307285697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767984082513827076380929 575988061885370307285697)
                ·
                  refine ⟨431991046414027730464273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575988061885370307285697 431991046414027730464273)
                  ·
                    rfl

theorem cell20_946462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_946462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946462 prefixEnd_946462 := by exact prefixLift 946462
  have htrace : WordTrace (prefixWord ++ tailWord_946462) baseStart_946462 baseEnd_946462 := by
    simpa [prefixWord, tailWord_946462, baseEnd_946462] using wordTrace_append hprefix tailTrace_946462
  have hstable : (prefixWord ++ tailWord_946462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946462).length < 2 ^ (prefixWord ++ tailWord_946462).sum := by decide
  have hdescent : baseEnd_946462 < baseStart_946462 := by decide
  rcases family_descends (prefixWord ++ tailWord_946462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946463 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_946463 : Nat := 118140960795 + 946463 * 2 ^ 59
def prefixEnd_946463 : Nat := 4983230072969 + 3 ^ 40 * 946463 * 2
def baseEnd_946463 : Nat := 431991502841276171430935

theorem tailTrace_946463 : CollatzResearch.WordTrace tailWord_946463 prefixEnd_946463 431991502841276171430935 := by
  unfold tailWord_946463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34520341570133668856452043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23013561046755779237634695 34520341570133668856452043)
  ·
    refine ⟨51780512355200503284678065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34520341570133668856452043 51780512355200503284678065)
    ·
      refine ⟨38835384266400377463508549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51780512355200503284678065 38835384266400377463508549)
      ·
        refine ⟨7281634549950070774407853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38835384266400377463508549 7281634549950070774407853)
        ·
          refine ⟨2730612956231276540402945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7281634549950070774407853 2730612956231276540402945)
          ·
            refine ⟨2047959717173457405302209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730612956231276540402945 2047959717173457405302209)
            ·
              refine ⟨1535969787880093053976657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047959717173457405302209 1535969787880093053976657)
              ·
                refine ⟨1151977340910069790482493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535969787880093053976657 1151977340910069790482493)
                ·
                  refine ⟨431991502841276171430935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151977340910069790482493 431991502841276171430935)
                  ·
                    rfl

theorem cell20_946463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_946463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946463 prefixEnd_946463 := by exact prefixLift 946463
  have htrace : WordTrace (prefixWord ++ tailWord_946463) baseStart_946463 baseEnd_946463 := by
    simpa [prefixWord, tailWord_946463, baseEnd_946463] using wordTrace_append hprefix tailTrace_946463
  have hstable : (prefixWord ++ tailWord_946463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946463).length < 2 ^ (prefixWord ++ tailWord_946463).sum := by decide
  have hdescent : baseEnd_946463 < baseStart_946463 := by decide
  rcases family_descends (prefixWord ++ tailWord_946463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946466 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_946466 : Nat := 118140960795 + 946466 * 2 ^ 59
def prefixEnd_946466 : Nat := 4983230072969 + 3 ^ 40 * 946466 * 2
def baseEnd_946466 : Nat := 431992872123021494330923

theorem tailTrace_946466 : CollatzResearch.WordTrace tailWord_946466 prefixEnd_946466 431992872123021494330923 := by
  unfold tailWord_946466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630112747280700092202813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23013633992748533579207501 8630112747280700092202813)
  ·
    refine ⟨3236292280230262534576055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8630112747280700092202813 3236292280230262534576055)
    ·
      refine ⟨4854438420345393801864083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236292280230262534576055 4854438420345393801864083)
      ·
        refine ⟨7281657630518090702796125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854438420345393801864083 7281657630518090702796125)
        ·
          refine ⟨2730621611444284013548547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7281657630518090702796125 2730621611444284013548547)
          ·
            refine ⟨4095932417166426020322821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730621611444284013548547 4095932417166426020322821)
            ·
              refine ⟨767987328218704878810529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4095932417166426020322821 767987328218704878810529)
              ·
                refine ⟨575990496164028659107897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767987328218704878810529 575990496164028659107897)
                ·
                  refine ⟨431992872123021494330923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575990496164028659107897 431992872123021494330923)
                  ·
                    rfl

theorem cell20_946466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_946466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946466 prefixEnd_946466 := by exact prefixLift 946466
  have htrace : WordTrace (prefixWord ++ tailWord_946466) baseStart_946466 baseEnd_946466 := by
    simpa [prefixWord, tailWord_946466, baseEnd_946466] using wordTrace_append hprefix tailTrace_946466
  have hstable : (prefixWord ++ tailWord_946466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946466).length < 2 ^ (prefixWord ++ tailWord_946466).sum := by decide
  have hdescent : baseEnd_946466 < baseStart_946466 := by decide
  rcases family_descends (prefixWord ++ tailWord_946466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946494 : List Nat := [4, 2, 1, 2, 1, 3, 3, 4]
def baseStart_946494 : Nat := 118140960795 + 946494 * 2 ^ 59
def prefixEnd_946494 : Nat := 4983230072969 + 3 ^ 40 * 946494 * 2
def baseEnd_946494 : Nat := 144001884028659280465825

theorem tailTrace_946494 : CollatzResearch.WordTrace tailWord_946494 prefixEnd_946494 144001884028659280465825 := by
  unfold tailWord_946494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315184029127670143853817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23014314822014240767220357 4315184029127670143853817)
  ·
    refine ⟨3236388021845752607890363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4315184029127670143853817 3236388021845752607890363)
    ·
      refine ⟨4854582032768628911835545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236388021845752607890363 4854582032768628911835545)
      ·
        refine ⟨3640936524576471683876659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4854582032768628911835545 3640936524576471683876659)
        ·
          refine ⟨5461404786864707525814989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640936524576471683876659 5461404786864707525814989)
          ·
            refine ⟨2048026795074265322180621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5461404786864707525814989 2048026795074265322180621)
            ·
              refine ⟨768010048152849495817733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2048026795074265322180621 768010048152849495817733)
              ·
                refine ⟨144001884028659280465825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768010048152849495817733 144001884028659280465825)
                ·
                  rfl

theorem cell20_946494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_946494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946494 prefixEnd_946494 := by exact prefixLift 946494
  have htrace : WordTrace (prefixWord ++ tailWord_946494) baseStart_946494 baseEnd_946494 := by
    simpa [prefixWord, tailWord_946494, baseEnd_946494] using wordTrace_append hprefix tailTrace_946494
  have hstable : (prefixWord ++ tailWord_946494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946494).length < 2 ^ (prefixWord ++ tailWord_946494).sum := by decide
  have hdescent : baseEnd_946494 < baseStart_946494 := by decide
  rcases family_descends (prefixWord ++ tailWord_946494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946505 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_946505 : Nat := 118140960795 + 946505 * 2 ^ 59
def prefixEnd_946505 : Nat := 4983230072969 + 3 ^ 40 * 946505 * 2
def baseEnd_946505 : Nat := 432010672785710692030763

theorem tailTrace_946505 : CollatzResearch.WordTrace tailWord_946505 prefixEnd_946505 432010672785710692030763 := by
  unfold tailWord_946505
  simp only [CollatzResearch.WordTrace]
  refine ⟨34521873435981510029480969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23014582290654340019653979 34521873435981510029480969)
  ·
    refine ⟨25891405076986132522110727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34521873435981510029480969 25891405076986132522110727)
    ·
      refine ⟨38837107615479198783166091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25891405076986132522110727 38837107615479198783166091)
      ·
        refine ⟨58255661423218798174749137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38837107615479198783166091 58255661423218798174749137)
        ·
          refine ⟨43691746067414098631061853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58255661423218798174749137 43691746067414098631061853)
          ·
            refine ⟨16384404775280286986648195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43691746067414098631061853 16384404775280286986648195)
            ·
              refine ⟨24576607162920430479972293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16384404775280286986648195 24576607162920430479972293)
              ·
                refine ⟨4608113843047580714994805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24576607162920430479972293 4608113843047580714994805)
                ·
                  refine ⟨432010672785710692030763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4608113843047580714994805 432010672785710692030763)
                  ·
                    rfl

theorem cell20_946505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_946505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946505 prefixEnd_946505 := by exact prefixLift 946505
  have htrace : WordTrace (prefixWord ++ tailWord_946505) baseStart_946505 baseEnd_946505 := by
    simpa [prefixWord, tailWord_946505, baseEnd_946505] using wordTrace_append hprefix tailTrace_946505
  have hstable : (prefixWord ++ tailWord_946505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946505).length < 2 ^ (prefixWord ++ tailWord_946505).sum := by decide
  have hdescent : baseEnd_946505 < baseStart_946505 := by decide
  rcases family_descends (prefixWord ++ tailWord_946505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946570 : List Nat := [3, 1, 2, 5, 1, 2, 6]
def baseStart_946570 : Nat := 118140960795 + 946570 * 2 ^ 59
def prefixEnd_946570 : Nat := 4983230072969 + 3 ^ 40 * 946570 * 2
def baseEnd_946570 : Nat := 48004482284095483873759

theorem tailTrace_946570 : CollatzResearch.WordTrace tailWord_946570 prefixEnd_946570 48004482284095483873759 := by
  unfold tailWord_946570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631061045186506532649291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23016162787164017420398109 8631061045186506532649291)
  ·
    refine ⟨12946591567779759798973937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8631061045186506532649291 12946591567779759798973937)
    ·
      refine ⟨9709943675834819849230453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12946591567779759798973937 9709943675834819849230453)
      ·
        refine ⟨910307219609514360865355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9709943675834819849230453 910307219609514360865355)
        ·
          refine ⟨1365460829414271541298033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910307219609514360865355 1365460829414271541298033)
          ·
            refine ⟨1024095622060703655973525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365460829414271541298033 1024095622060703655973525)
            ·
              refine ⟨48004482284095483873759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1024095622060703655973525 48004482284095483873759)
              ·
                rfl

theorem cell20_946570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 6].length) (baseStart_946570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946570 prefixEnd_946570 := by exact prefixLift 946570
  have htrace : WordTrace (prefixWord ++ tailWord_946570) baseStart_946570 baseEnd_946570 := by
    simpa [prefixWord, tailWord_946570, baseEnd_946570] using wordTrace_append hprefix tailTrace_946570
  have hstable : (prefixWord ++ tailWord_946570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946570).length < 2 ^ (prefixWord ++ tailWord_946570).sum := by decide
  have hdescent : baseEnd_946570 < baseStart_946570 := by decide
  rcases family_descends (prefixWord ++ tailWord_946570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946580 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 4]
def baseStart_946580 : Nat := 118140960795 + 946580 * 2 ^ 59
def prefixEnd_946580 : Nat := 4983230072969 + 3 ^ 40 * 946580 * 2
def baseEnd_946580 : Nat := 432044904829343764530457

theorem tailTrace_946580 : CollatzResearch.WordTrace tailWord_946580 prefixEnd_946580 432044904829343764530457 := by
  unfold tailWord_946580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17262304455354898919230597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23016405940473198558974129 17262304455354898919230597)
  ·
    refine ⟨3236682085379043547355737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17262304455354898919230597 3236682085379043547355737)
    ·
      refine ⟨2427511564034282660516803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236682085379043547355737 2427511564034282660516803)
      ·
        refine ⟨3641267346051423990775205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427511564034282660516803 3641267346051423990775205)
        ·
          refine ⟨682737627384641998270351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3641267346051423990775205 682737627384641998270351)
          ·
            refine ⟨1024106441076962997405527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682737627384641998270351 1024106441076962997405527)
            ·
              refine ⟨1536159661615444496108291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024106441076962997405527 1536159661615444496108291)
              ·
                refine ⟨2304239492423166744162437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536159661615444496108291 2304239492423166744162437)
                ·
                  refine ⟨432044904829343764530457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304239492423166744162437 432044904829343764530457)
                  ·
                    rfl

theorem cell20_946580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_946580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946580 prefixEnd_946580 := by exact prefixLift 946580
  have htrace : WordTrace (prefixWord ++ tailWord_946580) baseStart_946580 baseEnd_946580 := by
    simpa [prefixWord, tailWord_946580, baseEnd_946580] using wordTrace_append hprefix tailTrace_946580
  have hstable : (prefixWord ++ tailWord_946580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946580).length < 2 ^ (prefixWord ++ tailWord_946580).sum := by decide
  have hdescent : baseEnd_946580 < baseStart_946580 := by decide
  rcases family_descends (prefixWord ++ tailWord_946580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946584 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_946584 : Nat := 118140960795 + 946584 * 2 ^ 59
def prefixEnd_946584 : Nat := 4983230072969 + 3 ^ 40 * 946584 * 2
def baseEnd_946584 : Nat := 432046730538337528397107

theorem tailTrace_946584 : CollatzResearch.WordTrace tailWord_946584 prefixEnd_946584 432046730538337528397107 := by
  unfold tailWord_946584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17262377401347653260803403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23016503201796871014404537 17262377401347653260803403)
  ·
    refine ⟨25893566102021479891205105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17262377401347653260803403 25893566102021479891205105)
    ·
      refine ⟨19420174576516109918403829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25893566102021479891205105 19420174576516109918403829)
      ·
        refine ⟨1820641366548385304850359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19420174576516109918403829 1820641366548385304850359)
        ·
          refine ⟨2730962049822577957275539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820641366548385304850359 2730962049822577957275539)
          ·
            refine ⟨4096443074733866935913309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730962049822577957275539 4096443074733866935913309)
            ·
              refine ⟨1536166153025200100967491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4096443074733866935913309 1536166153025200100967491)
              ·
                refine ⟨2304249229537800151451237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536166153025200100967491 2304249229537800151451237)
                ·
                  refine ⟨432046730538337528397107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304249229537800151451237 432046730538337528397107)
                  ·
                    rfl

theorem cell20_946584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_946584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946584 prefixEnd_946584 := by exact prefixLift 946584
  have htrace : WordTrace (prefixWord ++ tailWord_946584) baseStart_946584 baseEnd_946584 := by
    simpa [prefixWord, tailWord_946584, baseEnd_946584] using wordTrace_append hprefix tailTrace_946584
  have hstable : (prefixWord ++ tailWord_946584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946584).length < 2 ^ (prefixWord ++ tailWord_946584).sum := by decide
  have hdescent : baseEnd_946584 < baseStart_946584 := by decide
  rcases family_descends (prefixWord ++ tailWord_946584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946625 : List Nat := [1, 2, 7, 1, 2, 7]
def baseStart_946625 : Nat := 118140960795 + 946625 * 2 ^ 59
def prefixEnd_946625 : Nat := 4983230072969 + 3 ^ 40 * 946625 * 2
def baseEnd_946625 : Nat := 16002423853908281778899

theorem tailTrace_946625 : CollatzResearch.WordTrace tailWord_946625 prefixEnd_946625 16002423853908281778899 := by
  unfold tailWord_946625
  simp only [CollatzResearch.WordTrace]
  refine ⟨34526250195546770523849329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23017500130364513682566219 34526250195546770523849329)
  ·
    refine ⟨25894687646660077892886997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34526250195546770523849329 25894687646660077892886997)
    ·
      refine ⟨606906741718595575614539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25894687646660077892886997 606906741718595575614539)
      ·
        refine ⟨910360112577893363421809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606906741718595575614539 910360112577893363421809)
        ·
          refine ⟨682770084433420022566357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910360112577893363421809 682770084433420022566357)
          ·
            refine ⟨16002423853908281778899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 682770084433420022566357 16002423853908281778899)
            ·
              rfl

theorem cell20_946625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 7].length) (baseStart_946625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946625 prefixEnd_946625 := by exact prefixLift 946625
  have htrace : WordTrace (prefixWord ++ tailWord_946625) baseStart_946625 baseEnd_946625 := by
    simpa [prefixWord, tailWord_946625, baseEnd_946625] using wordTrace_append hprefix tailTrace_946625
  have hstable : (prefixWord ++ tailWord_946625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946625).length < 2 ^ (prefixWord ++ tailWord_946625).sum := by decide
  have hdescent : baseEnd_946625 < baseStart_946625 := by decide
  rcases family_descends (prefixWord ++ tailWord_946625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946694 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_946694 : Nat := 118140960795 + 946694 * 2 ^ 59
def prefixEnd_946694 : Nat := 4983230072969 + 3 ^ 40 * 946694 * 2
def baseEnd_946694 : Nat := 432096937535666034729991

theorem tailTrace_946694 : CollatzResearch.WordTrace tailWord_946694 prefixEnd_946694 432096937535666034729991 := by
  unfold tailWord_946694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079023963509274853378473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23019177888197863538740757 1079023963509274853378473)
  ·
    refine ⟨809267972631956140033855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1079023963509274853378473 809267972631956140033855)
    ·
      refine ⟨1213901958947934210050783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809267972631956140033855 1213901958947934210050783)
      ·
        refine ⟨1820852938421901315076175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213901958947934210050783 1820852938421901315076175)
        ·
          refine ⟨2731279407632851972614263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820852938421901315076175 2731279407632851972614263)
          ·
            refine ⟨4096919111449277958921395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731279407632851972614263 4096919111449277958921395)
            ·
              refine ⟨6145378667173916938382093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096919111449277958921395 6145378667173916938382093)
              ·
                refine ⟨2304517000190218851893285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6145378667173916938382093 2304517000190218851893285)
                ·
                  refine ⟨432096937535666034729991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304517000190218851893285 432096937535666034729991)
                  ·
                    rfl

theorem cell20_946694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_946694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946694 prefixEnd_946694 := by exact prefixLift 946694
  have htrace : WordTrace (prefixWord ++ tailWord_946694) baseStart_946694 baseEnd_946694 := by
    simpa [prefixWord, tailWord_946694, baseEnd_946694] using wordTrace_append hprefix tailTrace_946694
  have hstable : (prefixWord ++ tailWord_946694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946694).length < 2 ^ (prefixWord ++ tailWord_946694).sum := by decide
  have hdescent : baseEnd_946694 < baseStart_946694 := by decide
  rcases family_descends (prefixWord ++ tailWord_946694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946698 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_946698 : Nat := 118140960795 + 946698 * 2 ^ 59
def prefixEnd_946698 : Nat := 4983230072969 + 3 ^ 40 * 946698 * 2
def baseEnd_946698 : Nat := 432098763244659798596641

theorem tailTrace_946698 : CollatzResearch.WordTrace tailWord_946698 prefixEnd_946698 432098763244659798596641 := by
  unfold tailWord_946698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632228181070575997814187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23019275149521535994171165 8632228181070575997814187)
  ·
    refine ⟨12948342271605863996721281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8632228181070575997814187 12948342271605863996721281)
    ·
      refine ⟨9711256703704397997540961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12948342271605863996721281 9711256703704397997540961)
      ·
        refine ⟨7283442527778298498155721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9711256703704397997540961 7283442527778298498155721)
        ·
          refine ⟨5462581895833723873616791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7283442527778298498155721 5462581895833723873616791)
          ·
            refine ⟨8193872843750585810425187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462581895833723873616791 8193872843750585810425187)
            ·
              refine ⟨12290809265625878715637781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193872843750585810425187 12290809265625878715637781)
              ·
                refine ⟨576131684326213064795521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12290809265625878715637781 576131684326213064795521)
                ·
                  refine ⟨432098763244659798596641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576131684326213064795521 432098763244659798596641)
                  ·
                    rfl

theorem cell20_946698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_946698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946698 prefixEnd_946698 := by exact prefixLift 946698
  have htrace : WordTrace (prefixWord ++ tailWord_946698) baseStart_946698 baseEnd_946698 := by
    simpa [prefixWord, tailWord_946698, baseEnd_946698] using wordTrace_append hprefix tailTrace_946698
  have hstable : (prefixWord ++ tailWord_946698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946698).length < 2 ^ (prefixWord ++ tailWord_946698).sum := by decide
  have hdescent : baseEnd_946698 < baseStart_946698 := by decide
  rcases family_descends (prefixWord ++ tailWord_946698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946736 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 2]
def baseStart_946736 : Nat := 118140960795 + 946736 * 2 ^ 59
def prefixEnd_946736 : Nat := 4983230072969 + 3 ^ 40 * 946736 * 2
def baseEnd_946736 : Nat := 432116107480100555329819

theorem tailTrace_946736 : CollatzResearch.WordTrace tailWord_946736 prefixEnd_946736 432116107480100555329819 := by
  unfold tailWord_946736
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265149349072318240570031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23020199132096424320760041 17265149349072318240570031)
  ·
    refine ⟨25897724023608477360855047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17265149349072318240570031 25897724023608477360855047)
    ·
      refine ⟨38846586035412716041282571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25897724023608477360855047 38846586035412716041282571)
      ·
        refine ⟨58269879053119074061923857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38846586035412716041282571 58269879053119074061923857)
        ·
          refine ⟨43702409289839305546442893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58269879053119074061923857 43702409289839305546442893)
          ·
            refine ⟨16388403483689739579916085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43702409289839305546442893 16388403483689739579916085)
            ·
              refine ⟨1536412826595913085617133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16388403483689739579916085 1536412826595913085617133)
              ·
                refine ⟨576154809973467407106425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536412826595913085617133 576154809973467407106425)
                ·
                  refine ⟨432116107480100555329819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576154809973467407106425 432116107480100555329819)
                  ·
                    rfl

theorem cell20_946736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_946736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946736 prefixEnd_946736 := by exact prefixLift 946736
  have htrace : WordTrace (prefixWord ++ tailWord_946736) baseStart_946736 baseEnd_946736 := by
    simpa [prefixWord, tailWord_946736, baseEnd_946736] using wordTrace_append hprefix tailTrace_946736
  have hstable : (prefixWord ++ tailWord_946736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946736).length < 2 ^ (prefixWord ++ tailWord_946736).sum := by decide
  have hdescent : baseEnd_946736 < baseStart_946736 := by decide
  rcases family_descends (prefixWord ++ tailWord_946736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946757 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_946757 : Nat := 118140960795 + 946757 * 2 ^ 59
def prefixEnd_946757 : Nat := 4983230072969 + 3 ^ 40 * 946757 * 2
def baseEnd_946757 : Nat := 432125692452317815629733

theorem tailTrace_946757 : CollatzResearch.WordTrace tailWord_946757 prefixEnd_946757 432125692452317815629733 := by
  unfold tailWord_946757
  simp only [CollatzResearch.WordTrace]
  refine ⟨34531064631068557067654525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23020709754045704711769683 34531064631068557067654525)
  ·
    refine ⟨12949149236650708900370447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34531064631068557067654525 12949149236650708900370447)
    ·
      refine ⟨19423723854976063350555671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949149236650708900370447 19423723854976063350555671)
      ·
        refine ⟨29135585782464095025833507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19423723854976063350555671 29135585782464095025833507)
        ·
          refine ⟨43703378673696142538750261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29135585782464095025833507 43703378673696142538750261)
          ·
            refine ⟨4097191750659013363007837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43703378673696142538750261 4097191750659013363007837)
            ·
              refine ⟨1536446906497130011127939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4097191750659013363007837 1536446906497130011127939)
              ·
                refine ⟨2304670359745695016691909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536446906497130011127939 2304670359745695016691909)
                ·
                  refine ⟨432125692452317815629733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304670359745695016691909 432125692452317815629733)
                  ·
                    rfl

theorem cell20_946757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_946757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946757 prefixEnd_946757 := by exact prefixLift 946757
  have htrace : WordTrace (prefixWord ++ tailWord_946757) baseStart_946757 baseEnd_946757 := by
    simpa [prefixWord, tailWord_946757, baseEnd_946757] using wordTrace_append hprefix tailTrace_946757
  have hstable : (prefixWord ++ tailWord_946757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946757).length < 2 ^ (prefixWord ++ tailWord_946757).sum := by decide
  have hdescent : baseEnd_946757 < baseStart_946757 := by decide
  rcases family_descends (prefixWord ++ tailWord_946757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946764 : List Nat := [2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_946764 : Nat := 118140960795 + 946764 * 2 ^ 59
def prefixEnd_946764 : Nat := 4983230072969 + 3 ^ 40 * 946764 * 2
def baseEnd_946764 : Nat := 144042962481018967465457

theorem tailTrace_946764 : CollatzResearch.WordTrace tailWord_946764 prefixEnd_946764 144042962481018967465457 := by
  unfold tailWord_946764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265659971021598631579673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23020879961362131508772897 17265659971021598631579673)
  ·
    refine ⟨12949244978266198973684755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17265659971021598631579673 12949244978266198973684755)
    ·
      refine ⟨19423867467399298460527133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949244978266198973684755 19423867467399298460527133)
      ·
        refine ⟨7283950300274736922697675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19423867467399298460527133 7283950300274736922697675)
        ·
          refine ⟨10925925450412105384046513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283950300274736922697675 10925925450412105384046513)
          ·
            refine ⟨8194444087809079038034885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10925925450412105384046513 8194444087809079038034885)
            ·
              refine ⟨1536458266464202319631541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8194444087809079038034885 1536458266464202319631541)
              ·
                refine ⟨144042962481018967465457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1536458266464202319631541 144042962481018967465457)
                ·
                  rfl

theorem cell20_946764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_946764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946764 prefixEnd_946764 := by exact prefixLift 946764
  have htrace : WordTrace (prefixWord ++ tailWord_946764) baseStart_946764 baseEnd_946764 := by
    simpa [prefixWord, tailWord_946764, baseEnd_946764] using wordTrace_append hprefix tailTrace_946764
  have hstable : (prefixWord ++ tailWord_946764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946764).length < 2 ^ (prefixWord ++ tailWord_946764).sum := by decide
  have hdescent : baseEnd_946764 < baseStart_946764 := by decide
  rcases family_descends (prefixWord ++ tailWord_946764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946802 : List Nat := [3, 2, 1, 2, 4, 8]
def baseStart_946802 : Nat := 118140960795 + 946802 * 2 ^ 59
def prefixEnd_946802 : Nat := 4983230072969 + 3 ^ 40 * 946802 * 2
def baseEnd_946802 : Nat := 16005415988092505893687

theorem tailTrace_946802 : CollatzResearch.WordTrace tailWord_946802 prefixEnd_946802 16005415988092505893687 := by
  unfold tailWord_946802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633176478976382438260665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23021803943937019835361773 8633176478976382438260665)
  ·
    refine ⟨6474882359232286828695499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8633176478976382438260665 6474882359232286828695499)
    ·
      refine ⟨9712323538848430243043249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6474882359232286828695499 9712323538848430243043249)
      ·
        refine ⟨7284242654136322682282437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9712323538848430243043249 7284242654136322682282437)
        ·
          refine ⟨1365795497650560502927957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7284242654136322682282437 1365795497650560502927957)
          ·
            refine ⟨16005415988092505893687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1365795497650560502927957 16005415988092505893687)
            ·
              rfl

theorem cell20_946802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 8].length) (baseStart_946802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946802 prefixEnd_946802 := by exact prefixLift 946802
  have htrace : WordTrace (prefixWord ++ tailWord_946802) baseStart_946802 baseEnd_946802 := by
    simpa [prefixWord, tailWord_946802, baseEnd_946802] using wordTrace_append hprefix tailTrace_946802
  have hstable : (prefixWord ++ tailWord_946802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946802).length < 2 ^ (prefixWord ++ tailWord_946802).sum := by decide
  have hdescent : baseEnd_946802 < baseStart_946802 := by decide
  rcases family_descends (prefixWord ++ tailWord_946802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946836 : List Nat := [2, 4, 2, 2, 1, 2, 3, 4]
def baseStart_946836 : Nat := 118140960795 + 946836 * 2 ^ 59
def prefixEnd_946836 : Nat := 4983230072969 + 3 ^ 40 * 946836 * 2
def baseEnd_946836 : Nat := 144053916734981550665359

theorem tailTrace_946836 : CollatzResearch.WordTrace tailWord_946836 prefixEnd_946836 144053916734981550665359 := by
  unfold tailWord_946836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266972998891176779890181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23022630665188235706520241 17266972998891176779890181)
  ·
    refine ⟨3237557437292095646229409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17266972998891176779890181 3237557437292095646229409)
    ·
      refine ⟨2428168077969071734672057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3237557437292095646229409 2428168077969071734672057)
      ·
        refine ⟨1821126058476803801004043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2428168077969071734672057 1821126058476803801004043)
        ·
          refine ⟨2731689087715205701506065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821126058476803801004043 2731689087715205701506065)
          ·
            refine ⟨2048766815786404276129549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731689087715205701506065 2048766815786404276129549)
            ·
              refine ⟨768287555919901603548581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2048766815786404276129549 768287555919901603548581)
              ·
                refine ⟨144053916734981550665359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768287555919901603548581 144053916734981550665359)
                ·
                  rfl

theorem cell20_946836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_946836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946836 prefixEnd_946836 := by exact prefixLift 946836
  have htrace : WordTrace (prefixWord ++ tailWord_946836) baseStart_946836 baseEnd_946836 := by
    simpa [prefixWord, tailWord_946836, baseEnd_946836] using wordTrace_append hprefix tailTrace_946836
  have hstable : (prefixWord ++ tailWord_946836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946836).length < 2 ^ (prefixWord ++ tailWord_946836).sum := by decide
  have hdescent : baseEnd_946836 < baseStart_946836 := by decide
  rcases family_descends (prefixWord ++ tailWord_946836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946878 : List Nat := [4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_946878 : Nat := 118140960795 + 946878 * 2 ^ 59
def prefixEnd_946878 : Nat := 4983230072969 + 3 ^ 40 * 946878 * 2
def baseEnd_946878 : Nat := 144060306716459724198635

theorem tailTrace_946878 : CollatzResearch.WordTrace tailWord_946878 prefixEnd_946878 144060306716459724198635 := by
  unfold tailWord_946878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316934732953774341601161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23023651909086796488539525 4316934732953774341601161)
  ·
    refine ⟨3237701049715330756200871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4316934732953774341601161 3237701049715330756200871)
    ·
      refine ⟨4856551574572996134301307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237701049715330756200871 4856551574572996134301307)
      ·
        refine ⟨7284827361859494201451961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856551574572996134301307 7284827361859494201451961)
        ·
          refine ⟨5463620521394620651088971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7284827361859494201451961 5463620521394620651088971)
          ·
            refine ⟨8195430782091930976633457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463620521394620651088971 8195430782091930976633457)
            ·
              refine ⟨6146573086568948232475093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195430782091930976633457 6146573086568948232475093)
              ·
                refine ⟨144060306716459724198635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6146573086568948232475093 144060306716459724198635)
                ·
                  rfl

theorem cell20_946878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_946878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946878 prefixEnd_946878 := by exact prefixLift 946878
  have htrace : WordTrace (prefixWord ++ tailWord_946878) baseStart_946878 baseEnd_946878 := by
    simpa [prefixWord, tailWord_946878, baseEnd_946878] using wordTrace_append hprefix tailTrace_946878
  have hstable : (prefixWord ++ tailWord_946878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946878).length < 2 ^ (prefixWord ++ tailWord_946878).sum := by decide
  have hdescent : baseEnd_946878 < baseStart_946878 := by decide
  rcases family_descends (prefixWord ++ tailWord_946878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946901 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 2]
def baseStart_946901 : Nat := 118140960795 + 946901 * 2 ^ 59
def prefixEnd_946901 : Nat := 4983230072969 + 3 ^ 40 * 946901 * 2
def baseEnd_946901 : Nat := 432191417976093314829145

theorem tailTrace_946901 : CollatzResearch.WordTrace tailWord_946901 prefixEnd_946901 432191417976093314829145 := by
  unfold tailWord_946901
  simp only [CollatzResearch.WordTrace]
  refine ⟨34536316742546869660896557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23024211161697913107264371 34536316742546869660896557)
  ·
    refine ⟨12951118778455076122836209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34536316742546869660896557 12951118778455076122836209)
    ·
      refine ⟨9713339083841307092127157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12951118778455076122836209 9713339083841307092127157)
      ·
        refine ⟨910625539110122539886921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9713339083841307092127157 910625539110122539886921)
        ·
          refine ⟨682969154332591904915191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910625539110122539886921 682969154332591904915191)
          ·
            refine ⟨1024453731498887857372787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682969154332591904915191 1024453731498887857372787)
            ·
              refine ⟨1536680597248331786059181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024453731498887857372787 1536680597248331786059181)
              ·
                refine ⟨576255223968124419772193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536680597248331786059181 576255223968124419772193)
                ·
                  refine ⟨432191417976093314829145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576255223968124419772193 432191417976093314829145)
                  ·
                    rfl

theorem cell20_946901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_946901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946901 prefixEnd_946901 := by exact prefixLift 946901
  have htrace : WordTrace (prefixWord ++ tailWord_946901) baseStart_946901 baseEnd_946901 := by
    simpa [prefixWord, tailWord_946901, baseEnd_946901] using wordTrace_append hprefix tailTrace_946901
  have hstable : (prefixWord ++ tailWord_946901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946901).length < 2 ^ (prefixWord ++ tailWord_946901).sum := by decide
  have hdescent : baseEnd_946901 < baseStart_946901 := by decide
  rcases family_descends (prefixWord ++ tailWord_946901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946916 : List Nat := [2, 3, 1, 1, 1, 6, 6]
def baseStart_946916 : Nat := 118140960795 + 946916 * 2 ^ 59
def prefixEnd_946916 : Nat := 4983230072969 + 3 ^ 40 * 946916 * 2
def baseEnd_946916 : Nat := 48022029376091103258787

theorem tailTrace_946916 : CollatzResearch.WordTrace tailWord_946916 prefixEnd_946916 48022029376091103258787 := by
  unfold tailWord_946916
  simp only [CollatzResearch.WordTrace]
  refine ⟨17268431918746263611346301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23024575891661684815128401 17268431918746263611346301)
  ·
    refine ⟨6475661969529848854254863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17268431918746263611346301 6475661969529848854254863)
    ·
      refine ⟨9713492954294773281382295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6475661969529848854254863 9713492954294773281382295)
      ·
        refine ⟨14570239431442159922073443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9713492954294773281382295 14570239431442159922073443)
        ·
          refine ⟨21855359147163239883110165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14570239431442159922073443 21855359147163239883110165)
          ·
            refine ⟨1024469960023276869520789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21855359147163239883110165 1024469960023276869520789)
            ·
              refine ⟨48022029376091103258787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1024469960023276869520789 48022029376091103258787)
              ·
                rfl

theorem cell20_946916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 6].length) (baseStart_946916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946916 prefixEnd_946916 := by exact prefixLift 946916
  have htrace : WordTrace (prefixWord ++ tailWord_946916) baseStart_946916 baseEnd_946916 := by
    simpa [prefixWord, tailWord_946916, baseEnd_946916] using wordTrace_append hprefix tailTrace_946916
  have hstable : (prefixWord ++ tailWord_946916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946916).length < 2 ^ (prefixWord ++ tailWord_946916).sum := by decide
  have hdescent : baseEnd_946916 < baseStart_946916 := by decide
  rcases family_descends (prefixWord ++ tailWord_946916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946923 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_946923 : Nat := 118140960795 + 946923 * 2 ^ 59
def prefixEnd_946923 : Nat := 4983230072969 + 3 ^ 40 * 946923 * 2
def baseEnd_946923 : Nat := 432201459375559016095721

theorem tailTrace_946923 : CollatzResearch.WordTrace tailWord_946923 prefixEnd_946923 432201459375559016095721 := by
  unfold tailWord_946923
  simp only [CollatzResearch.WordTrace]
  refine ⟨34537119148467167418197423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23024746098978111612131615 34537119148467167418197423)
  ·
    refine ⟨51805678722700751127296135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34537119148467167418197423 51805678722700751127296135)
    ·
      refine ⟨77708518084051126690944203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51805678722700751127296135 77708518084051126690944203)
      ·
        refine ⟨116562777126076690036416305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77708518084051126690944203 116562777126076690036416305)
        ·
          refine ⟨87422082844557517527312229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116562777126076690036416305 87422082844557517527312229)
          ·
            refine ⟨16391640533354534536371043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87422082844557517527312229 16391640533354534536371043)
            ·
              refine ⟨24587460800031801804556565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16391640533354534536371043 24587460800031801804556565)
              ·
                refine ⟨1152537225001490709588589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24587460800031801804556565 1152537225001490709588589)
                ·
                  refine ⟨432201459375559016095721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152537225001490709588589 432201459375559016095721)
                  ·
                    rfl

theorem cell20_946923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_946923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946923 prefixEnd_946923 := by exact prefixLift 946923
  have htrace : WordTrace (prefixWord ++ tailWord_946923) baseStart_946923 baseEnd_946923 := by
    simpa [prefixWord, tailWord_946923, baseEnd_946923] using wordTrace_append hprefix tailTrace_946923
  have hstable : (prefixWord ++ tailWord_946923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946923).length < 2 ^ (prefixWord ++ tailWord_946923).sum := by decide
  have hdescent : baseEnd_946923 < baseStart_946923 := by decide
  rcases family_descends (prefixWord ++ tailWord_946923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946926 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_946926 : Nat := 118140960795 + 946926 * 2 ^ 59
def prefixEnd_946926 : Nat := 4983230072969 + 3 ^ 40 * 946926 * 2
def baseEnd_946926 : Nat := 432202828657304338995709

theorem tailTrace_946926 : CollatzResearch.WordTrace tailWord_946926 prefixEnd_946926 432202828657304338995709 := by
  unfold tailWord_946926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317153570932037366319579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23024819044970865953704421 4317153570932037366319579)
  ·
    refine ⟨6475730356398056049479369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317153570932037366319579 6475730356398056049479369)
    ·
      refine ⟨4856797767298542037109527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6475730356398056049479369 4856797767298542037109527)
      ·
        refine ⟨7285196650947813055664291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856797767298542037109527 7285196650947813055664291)
        ·
          refine ⟨10927794976421719583496437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285196650947813055664291 10927794976421719583496437)
          ·
            refine ⟨1024480779039536210952791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10927794976421719583496437 1024480779039536210952791)
            ·
              refine ⟨1536721168559304316429187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024480779039536210952791 1536721168559304316429187)
              ·
                refine ⟨2305081752838956474643781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536721168559304316429187 2305081752838956474643781)
                ·
                  refine ⟨432202828657304338995709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305081752838956474643781 432202828657304338995709)
                  ·
                    rfl

theorem cell20_946926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_946926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946926 prefixEnd_946926 := by exact prefixLift 946926
  have htrace : WordTrace (prefixWord ++ tailWord_946926) baseStart_946926 baseEnd_946926 := by
    simpa [prefixWord, tailWord_946926, baseEnd_946926] using wordTrace_append hprefix tailTrace_946926
  have hstable : (prefixWord ++ tailWord_946926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946926).length < 2 ^ (prefixWord ++ tailWord_946926).sum := by decide
  have hdescent : baseEnd_946926 < baseStart_946926 := by decide
  rcases family_descends (prefixWord ++ tailWord_946926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946932 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_946932 : Nat := 118140960795 + 946932 * 2 ^ 59
def prefixEnd_946932 : Nat := 4983230072969 + 3 ^ 40 * 946932 * 2
def baseEnd_946932 : Nat := 432205567220794984795685

theorem tailTrace_946932 : CollatzResearch.WordTrace tailWord_946932 prefixEnd_946932 432205567220794984795685 := by
  unfold tailWord_946932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17268723702717280977637525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23024964936956374636850033 17268723702717280977637525)
  ·
    refine ⟨809471423564872545826759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17268723702717280977637525 809471423564872545826759)
    ·
      refine ⟨1214207135347308818740139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809471423564872545826759 1214207135347308818740139)
      ·
        refine ⟨1821310703020963228110209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214207135347308818740139 1821310703020963228110209)
        ·
          refine ⟨1365983027265722421082657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1821310703020963228110209 1365983027265722421082657)
          ·
            refine ⟨1024487270449291815811993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365983027265722421082657 1024487270449291815811993)
            ·
              refine ⟨768365452836968861858995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024487270449291815811993 768365452836968861858995)
              ·
                refine ⟨1152548179255453292788493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768365452836968861858995 1152548179255453292788493)
                ·
                  refine ⟨432205567220794984795685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152548179255453292788493 432205567220794984795685)
                  ·
                    rfl

theorem cell20_946932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_946932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946932 prefixEnd_946932 := by exact prefixLift 946932
  have htrace : WordTrace (prefixWord ++ tailWord_946932) baseStart_946932 baseEnd_946932 := by
    simpa [prefixWord, tailWord_946932, baseEnd_946932] using wordTrace_append hprefix tailTrace_946932
  have hstable : (prefixWord ++ tailWord_946932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946932).length < 2 ^ (prefixWord ++ tailWord_946932).sum := by decide
  have hdescent : baseEnd_946932 < baseStart_946932 := by decide
  rcases family_descends (prefixWord ++ tailWord_946932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946940 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_946940 : Nat := 118140960795 + 946940 * 2 ^ 59
def prefixEnd_946940 : Nat := 4983230072969 + 3 ^ 40 * 946940 * 2
def baseEnd_946940 : Nat := 432209218638782512528985

theorem tailTrace_946940 : CollatzResearch.WordTrace tailWord_946940 prefixEnd_946940 432209218638782512528985 := by
  unfold tailWord_946940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17268869594702789660783137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23025159459603719547710849 17268869594702789660783137)
  ·
    refine ⟨12951652196027092245587353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17268869594702789660783137 12951652196027092245587353)
    ·
      refine ⟨9713739147020319184190515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12951652196027092245587353 9713739147020319184190515)
      ·
        refine ⟨14570608720530478776285773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9713739147020319184190515 14570608720530478776285773)
        ·
          refine ⟨5463978270198929541107165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14570608720530478776285773 5463978270198929541107165)
          ·
            refine ⟨2048991851324598577915187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5463978270198929541107165 2048991851324598577915187)
            ·
              refine ⟨3073487776986897866872781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048991851324598577915187 3073487776986897866872781)
              ·
                refine ⟨1152557916370086700077293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3073487776986897866872781 1152557916370086700077293)
                ·
                  refine ⟨432209218638782512528985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152557916370086700077293 432209218638782512528985)
                  ·
                    rfl

theorem cell20_946940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_946940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946940 prefixEnd_946940 := by exact prefixLift 946940
  have htrace : WordTrace (prefixWord ++ tailWord_946940) baseStart_946940 baseEnd_946940 := by
    simpa [prefixWord, tailWord_946940, baseEnd_946940] using wordTrace_append hprefix tailTrace_946940
  have hstable : (prefixWord ++ tailWord_946940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946940).length < 2 ^ (prefixWord ++ tailWord_946940).sum := by decide
  have hdescent : baseEnd_946940 < baseStart_946940 := by decide
  rcases family_descends (prefixWord ++ tailWord_946940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946975 : List Nat := [1, 1, 2, 4, 2, 10]
def baseStart_946975 : Nat := 118140960795 + 946975 * 2 ^ 59
def prefixEnd_946975 : Nat := 4983230072969 + 3 ^ 40 * 946975 * 2
def baseEnd_946975 : Nat := 16008340503425109124525

theorem tailTrace_946975 : CollatzResearch.WordTrace tailWord_946975 prefixEnd_946975 16008340503425109124525 := by
  unfold tailWord_946975
  simp only [CollatzResearch.WordTrace]
  refine ⟨34539015744278780299090379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23026010496185853532726919 34539015744278780299090379)
  ·
    refine ⟨51808523616418170448635569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34539015744278780299090379 51808523616418170448635569)
    ·
      refine ⟨38856392712313627836476677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51808523616418170448635569 38856392712313627836476677)
      ·
        refine ⟨7285573633558805219339377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38856392712313627836476677 7285573633558805219339377)
        ·
          refine ⟨5464180225169103914504533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285573633558805219339377 5464180225169103914504533)
          ·
            refine ⟨16008340503425109124525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5464180225169103914504533 16008340503425109124525)
            ·
              rfl

theorem cell20_946975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 10].length) (baseStart_946975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946975 prefixEnd_946975 := by exact prefixLift 946975
  have htrace : WordTrace (prefixWord ++ tailWord_946975) baseStart_946975 baseEnd_946975 := by
    simpa [prefixWord, tailWord_946975, baseEnd_946975] using wordTrace_append hprefix tailTrace_946975
  have hstable : (prefixWord ++ tailWord_946975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946975).length < 2 ^ (prefixWord ++ tailWord_946975).sum := by decide
  have hdescent : baseEnd_946975 < baseStart_946975 := by decide
  rcases family_descends (prefixWord ++ tailWord_946975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946978 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_946978 : Nat := 118140960795 + 946978 * 2 ^ 59
def prefixEnd_946978 : Nat := 4983230072969 + 3 ^ 40 * 946978 * 2
def baseEnd_946978 : Nat := 432226562874223269262163

theorem tailTrace_946978 : CollatzResearch.WordTrace tailWord_946978 prefixEnd_946978 432226562874223269262163 := by
  unfold tailWord_946978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634781290816977952862397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23026083442178607874299725 8634781290816977952862397)
  ·
    refine ⟨3238042984056366732323399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8634781290816977952862397 3238042984056366732323399)
    ·
      refine ⟨4857064476084550098485099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238042984056366732323399 4857064476084550098485099)
      ·
        refine ⟨7285596714126825147727649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857064476084550098485099 7285596714126825147727649)
        ·
          refine ⟨5464197535595118860795737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285596714126825147727649 5464197535595118860795737)
          ·
            refine ⟨4098148151696339145596803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464197535595118860795737 4098148151696339145596803)
            ·
              refine ⟨6147222227544508718395205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098148151696339145596803 6147222227544508718395205)
              ·
                refine ⟨1152604167664595384699101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6147222227544508718395205 1152604167664595384699101)
                ·
                  refine ⟨432226562874223269262163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152604167664595384699101 432226562874223269262163)
                  ·
                    rfl

theorem cell20_946978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_946978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946978 prefixEnd_946978 := by exact prefixLift 946978
  have htrace : WordTrace (prefixWord ++ tailWord_946978) baseStart_946978 baseEnd_946978 := by
    simpa [prefixWord, tailWord_946978, baseEnd_946978] using wordTrace_append hprefix tailTrace_946978
  have hstable : (prefixWord ++ tailWord_946978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946978).length < 2 ^ (prefixWord ++ tailWord_946978).sum := by decide
  have hdescent : baseEnd_946978 < baseStart_946978 := by decide
  rcases family_descends (prefixWord ++ tailWord_946978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946985 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 2]
def baseStart_946985 : Nat := 118140960795 + 946985 * 2 ^ 59
def prefixEnd_946985 : Nat := 4983230072969 + 3 ^ 40 * 946985 * 2
def baseEnd_946985 : Nat := 432229757864962356028801

theorem tailTrace_946985 : CollatzResearch.WordTrace tailWord_946985 prefixEnd_946985 432229757864962356028801 := by
  unfold tailWord_946985
  simp only [CollatzResearch.WordTrace]
  refine ⟨34539380474242552006954409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23026253649495034671302939 34539380474242552006954409)
  ·
    refine ⟨25904535355681914005215807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34539380474242552006954409 25904535355681914005215807)
    ·
      refine ⟨38856803033522871007823711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25904535355681914005215807 38856803033522871007823711)
      ·
        refine ⟨58285204550284306511735567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38856803033522871007823711 58285204550284306511735567)
        ·
          refine ⟨87427806825426459767603351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58285204550284306511735567 87427806825426459767603351)
          ·
            refine ⟨131141710238139689651405027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87427806825426459767603351 131141710238139689651405027)
            ·
              refine ⟨196712565357209534477107541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131141710238139689651405027 196712565357209534477107541)
              ·
                refine ⟨576306343819949808038401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 196712565357209534477107541 576306343819949808038401)
                ·
                  refine ⟨432229757864962356028801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576306343819949808038401 432229757864962356028801)
                  ·
                    rfl

theorem cell20_946985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_946985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946985 prefixEnd_946985 := by exact prefixLift 946985
  have htrace : WordTrace (prefixWord ++ tailWord_946985) baseStart_946985 baseEnd_946985 := by
    simpa [prefixWord, tailWord_946985, baseEnd_946985] using wordTrace_append hprefix tailTrace_946985
  have hstable : (prefixWord ++ tailWord_946985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946985).length < 2 ^ (prefixWord ++ tailWord_946985).sum := by decide
  have hdescent : baseEnd_946985 < baseStart_946985 := by decide
  rcases family_descends (prefixWord ++ tailWord_946985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946999 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_946999 : Nat := 118140960795 + 946999 * 2 ^ 59
def prefixEnd_946999 : Nat := 4983230072969 + 3 ^ 40 * 946999 * 2
def baseEnd_946999 : Nat := 432236147846440529562077

theorem tailTrace_946999 : CollatzResearch.WordTrace tailWord_946999 prefixEnd_946999 432236147846440529562077 := by
  unfold tailWord_946999
  simp only [CollatzResearch.WordTrace]
  refine ⟨34539891096191832397964051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23026594064127888265309367 34539891096191832397964051)
  ·
    refine ⟨51809836644287748596946077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34539891096191832397964051 51809836644287748596946077)
    ·
      refine ⟨19428688741607905723854779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51809836644287748596946077 19428688741607905723854779)
      ·
        refine ⟨29143033112411858585782169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19428688741607905723854779 29143033112411858585782169)
        ·
          refine ⟨21857274834308893939336627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29143033112411858585782169 21857274834308893939336627)
          ·
            refine ⟨32785912251463340909004941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21857274834308893939336627 32785912251463340909004941)
            ·
              refine ⟨12294717094298752840876853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32785912251463340909004941 12294717094298752840876853)
              ·
                refine ⟨1152629727590508078832205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12294717094298752840876853 1152629727590508078832205)
                ·
                  refine ⟨432236147846440529562077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152629727590508078832205 432236147846440529562077)
                  ·
                    rfl

theorem cell20_946999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_946999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_946999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_946999 prefixEnd_946999 := by exact prefixLift 946999
  have htrace : WordTrace (prefixWord ++ tailWord_946999) baseStart_946999 baseEnd_946999 := by
    simpa [prefixWord, tailWord_946999, baseEnd_946999] using wordTrace_append hprefix tailTrace_946999
  have hstable : (prefixWord ++ tailWord_946999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946999).length < 2 ^ (prefixWord ++ tailWord_946999).sum := by decide
  have hdescent : baseEnd_946999 < baseStart_946999 := by decide
  rcases family_descends (prefixWord ++ tailWord_946999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947061 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_947061 : Nat := 118140960795 + 947061 * 2 ^ 59
def prefixEnd_947061 : Nat := 4983230072969 + 3 ^ 40 * 947061 * 2
def baseEnd_947061 : Nat := 432264446335843869495157

theorem tailTrace_947061 : CollatzResearch.WordTrace tailWord_947061 prefixEnd_947061 432264446335843869495157 := by
  unfold tailWord_947061
  simp only [CollatzResearch.WordTrace]
  refine ⟨34542152421967216986721037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23028101614644811324480691 34542152421967216986721037)
  ·
    refine ⟨12953307158237706370020389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34542152421967216986721037 12953307158237706370020389)
    ·
      refine ⟨2428745092169569944378823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12953307158237706370020389 2428745092169569944378823)
      ·
        refine ⟨3643117638254354916568235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428745092169569944378823 3643117638254354916568235)
        ·
          refine ⟨5464676457381532374852353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643117638254354916568235 5464676457381532374852353)
          ·
            refine ⟨4098507343036149281139265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464676457381532374852353 4098507343036149281139265)
            ·
              refine ⟨3073880507277111960854449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4098507343036149281139265 3073880507277111960854449)
              ·
                refine ⟨2305410380457833970640837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073880507277111960854449 2305410380457833970640837)
                ·
                  refine ⟨432264446335843869495157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305410380457833970640837 432264446335843869495157)
                  ·
                    rfl

theorem cell20_947061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_947061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947061 prefixEnd_947061 := by exact prefixLift 947061
  have htrace : WordTrace (prefixWord ++ tailWord_947061) baseStart_947061 baseEnd_947061 := by
    simpa [prefixWord, tailWord_947061, baseEnd_947061] using wordTrace_append hprefix tailTrace_947061
  have hstable : (prefixWord ++ tailWord_947061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947061).length < 2 ^ (prefixWord ++ tailWord_947061).sum := by decide
  have hdescent : baseEnd_947061 < baseStart_947061 := by decide
  rcases family_descends (prefixWord ++ tailWord_947061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947092 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_947092 : Nat := 118140960795 + 947092 * 2 ^ 59
def prefixEnd_947092 : Nat := 4983230072969 + 3 ^ 40 * 947092 * 2
def baseEnd_947092 : Nat := 432278595580545539461697

theorem tailTrace_947092 : CollatzResearch.WordTrace tailWord_947092 prefixEnd_947092 432278595580545539461697 := by
  unfold tailWord_947092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17271641542427454640549765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23028855389903272854066353 17271641542427454640549765)
  ·
    refine ⟨3238432789205147745103081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17271641542427454640549765 3238432789205147745103081)
    ·
      refine ⟨2428824591903860808827311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3238432789205147745103081 2428824591903860808827311)
      ·
        refine ⟨3643236887855791213240967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428824591903860808827311 3643236887855791213240967)
        ·
          refine ⟨5464855331783686819861451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643236887855791213240967 5464855331783686819861451)
          ·
            refine ⟨8197282997675530229792177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464855331783686819861451 8197282997675530229792177)
            ·
              refine ⟨6147962248256647672344133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8197282997675530229792177 6147962248256647672344133)
              ·
                refine ⟨1152742921548121438564525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6147962248256647672344133 1152742921548121438564525)
                ·
                  refine ⟨432278595580545539461697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152742921548121438564525 432278595580545539461697)
                  ·
                    rfl

theorem cell20_947092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_947092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947092 prefixEnd_947092 := by exact prefixLift 947092
  have htrace : WordTrace (prefixWord ++ tailWord_947092) baseStart_947092 baseEnd_947092 := by
    simpa [prefixWord, tailWord_947092, baseEnd_947092] using wordTrace_append hprefix tailTrace_947092
  have hstable : (prefixWord ++ tailWord_947092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947092).length < 2 ^ (prefixWord ++ tailWord_947092).sum := by decide
  have hdescent : baseEnd_947092 < baseStart_947092 := by decide
  rcases family_descends (prefixWord ++ tailWord_947092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947106 : List Nat := [3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_947106 : Nat := 118140960795 + 947106 * 2 ^ 59
def prefixEnd_947106 : Nat := 4983230072969 + 3 ^ 40 * 947106 * 2
def baseEnd_947106 : Nat := 144094995187341237664991

theorem tailTrace_947106 : CollatzResearch.WordTrace tailWord_947106 prefixEnd_947106 144094995187341237664991 := by
  unfold tailWord_947106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635948426701047418027293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23029195804536126448072781 8635948426701047418027293)
  ·
    refine ⟨3238480660012892781760235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8635948426701047418027293 3238480660012892781760235)
    ·
      refine ⟨4857720990019339172640353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238480660012892781760235 4857720990019339172640353)
      ·
        refine ⟨3643290742514504379480265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4857720990019339172640353 3643290742514504379480265)
        ·
          refine ⟨2732468056885878284610199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3643290742514504379480265 2732468056885878284610199)
          ·
            refine ⟨4098702085328817426915299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732468056885878284610199 4098702085328817426915299)
            ·
              refine ⟨6148053127993226140372949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098702085328817426915299 6148053127993226140372949)
              ·
                refine ⟨144094995187341237664991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6148053127993226140372949 144094995187341237664991)
                ·
                  rfl

theorem cell20_947106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_947106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947106 prefixEnd_947106 := by exact prefixLift 947106
  have htrace : WordTrace (prefixWord ++ tailWord_947106) baseStart_947106 baseEnd_947106 := by
    simpa [prefixWord, tailWord_947106, baseEnd_947106] using wordTrace_append hprefix tailTrace_947106
  have hstable : (prefixWord ++ tailWord_947106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947106).length < 2 ^ (prefixWord ++ tailWord_947106).sum := by decide
  have hdescent : baseEnd_947106 < baseStart_947106 := by decide
  rcases family_descends (prefixWord ++ tailWord_947106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947113 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_947113 : Nat := 118140960795 + 947113 * 2 ^ 59
def prefixEnd_947113 : Nat := 4983230072969 + 3 ^ 40 * 947113 * 2
def baseEnd_947113 : Nat := 432288180552762799761611

theorem tailTrace_947113 : CollatzResearch.WordTrace tailWord_947113 prefixEnd_947113 432288180552762799761611 := by
  unfold tailWord_947113
  simp only [CollatzResearch.WordTrace]
  refine ⟨34544049017778829867613993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23029366011852553245075995 34544049017778829867613993)
  ·
    refine ⟨25908036763334122400710495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34544049017778829867613993 25908036763334122400710495)
    ·
      refine ⟨38862055145001183601065743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25908036763334122400710495 38862055145001183601065743)
      ·
        refine ⟨58293082717501775401598615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38862055145001183601065743 58293082717501775401598615)
        ·
          refine ⟨87439624076252663102397923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58293082717501775401598615 87439624076252663102397923)
          ·
            refine ⟨131159436114378994653596885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87439624076252663102397923 131159436114378994653596885)
            ·
              refine ⟨3074049283930757687193677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131159436114378994653596885 3074049283930757687193677)
              ·
                refine ⟨1152768481474034132697629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3074049283930757687193677 1152768481474034132697629)
                ·
                  refine ⟨432288180552762799761611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152768481474034132697629 432288180552762799761611)
                  ·
                    rfl

theorem cell20_947113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_947113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947113 prefixEnd_947113 := by exact prefixLift 947113
  have htrace : WordTrace (prefixWord ++ tailWord_947113) baseStart_947113 baseEnd_947113 := by
    simpa [prefixWord, tailWord_947113, baseEnd_947113] using wordTrace_append hprefix tailTrace_947113
  have hstable : (prefixWord ++ tailWord_947113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947113).length < 2 ^ (prefixWord ++ tailWord_947113).sum := by decide
  have hdescent : baseEnd_947113 < baseStart_947113 := by decide
  rcases family_descends (prefixWord ++ tailWord_947113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947127 : List Nat := [1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_947127 : Nat := 118140960795 + 947127 * 2 ^ 59
def prefixEnd_947127 : Nat := 4983230072969 + 3 ^ 40 * 947127 * 2
def baseEnd_947127 : Nat := 144098190178080324431629

theorem tailTrace_947127 : CollatzResearch.WordTrace tailWord_947127 prefixEnd_947127 144098190178080324431629 := by
  unfold tailWord_947127
  simp only [CollatzResearch.WordTrace]
  refine ⟨34544559639728110258623635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23029706426485406839082423 34544559639728110258623635)
  ·
    refine ⟨51816839459592165387935453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34544559639728110258623635 51816839459592165387935453)
    ·
      refine ⟨19431314797347062020475795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51816839459592165387935453 19431314797347062020475795)
      ·
        refine ⟨29146972196020593030713693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19431314797347062020475795 29146972196020593030713693)
        ·
          refine ⟨10930114573507722386517635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29146972196020593030713693 10930114573507722386517635)
          ·
            refine ⟨16395171860261583579776453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10930114573507722386517635 16395171860261583579776453)
            ·
              refine ⟨3074094723799046921208085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16395171860261583579776453 3074094723799046921208085)
              ·
                refine ⟨144098190178080324431629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3074094723799046921208085 144098190178080324431629)
                ·
                  rfl

theorem cell20_947127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_947127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947127 prefixEnd_947127 := by exact prefixLift 947127
  have htrace : WordTrace (prefixWord ++ tailWord_947127) baseStart_947127 baseEnd_947127 := by
    simpa [prefixWord, tailWord_947127, baseEnd_947127] using wordTrace_append hprefix tailTrace_947127
  have hstable : (prefixWord ++ tailWord_947127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947127).length < 2 ^ (prefixWord ++ tailWord_947127).sum := by decide
  have hdescent : baseEnd_947127 < baseStart_947127 := by decide
  rcases family_descends (prefixWord ++ tailWord_947127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947142 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_947142 : Nat := 118140960795 + 947142 * 2 ^ 59
def prefixEnd_947142 : Nat := 4983230072969 + 3 ^ 40 * 947142 * 2
def baseEnd_947142 : Nat := 432301416942967587794827

theorem tailTrace_947142 : CollatzResearch.WordTrace tailWord_947142 prefixEnd_947142 432301416942967587794827 := by
  unfold tailWord_947142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079534585458555244388115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23030071156449178546946453 1079534585458555244388115)
  ·
    refine ⟨1619301878187832866582173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1079534585458555244388115 1619301878187832866582173)
    ·
      refine ⟨607238204320437324968315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1619301878187832866582173 607238204320437324968315)
      ·
        refine ⟨910857306480655987452473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607238204320437324968315 910857306480655987452473)
        ·
          refine ⟨683142979860491990589355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910857306480655987452473 683142979860491990589355)
          ·
            refine ⟨1024714469790737985884033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683142979860491990589355 1024714469790737985884033)
            ·
              refine ⟨768535852343053489413025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024714469790737985884033 768535852343053489413025)
              ·
                refine ⟨576401889257290117059769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768535852343053489413025 576401889257290117059769)
                ·
                  refine ⟨432301416942967587794827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576401889257290117059769 432301416942967587794827)
                  ·
                    rfl

theorem cell20_947142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_947142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947142 prefixEnd_947142 := by exact prefixLift 947142
  have htrace : WordTrace (prefixWord ++ tailWord_947142) baseStart_947142 baseEnd_947142 := by
    simpa [prefixWord, tailWord_947142, baseEnd_947142] using wordTrace_append hprefix tailTrace_947142
  have hstable : (prefixWord ++ tailWord_947142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947142).length < 2 ^ (prefixWord ++ tailWord_947142).sum := by decide
  have hdescent : baseEnd_947142 < baseStart_947142 := by decide
  rcases family_descends (prefixWord ++ tailWord_947142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947144 : List Nat := [2, 1, 3, 1, 6, 7]
def baseStart_947144 : Nat := 118140960795 + 947144 * 2 ^ 59
def prefixEnd_947144 : Nat := 4983230072969 + 3 ^ 40 * 947144 * 2
def baseEnd_947144 : Nat := 16011197399906091471413

theorem tailTrace_947144 : CollatzResearch.WordTrace tailWord_947144 prefixEnd_947144 16011197399906091471413 := by
  unfold tailWord_947144
  simp only [CollatzResearch.WordTrace]
  refine ⟨17272589840333261080996243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23030119787111014774661657 17272589840333261080996243)
  ·
    refine ⟨25908884760499891621494365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17272589840333261080996243 25908884760499891621494365)
    ·
      refine ⟨9715831785187459358060387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25908884760499891621494365 9715831785187459358060387)
      ·
        refine ⟨14573747677781189037090581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9715831785187459358060387 14573747677781189037090581)
        ·
          refine ⟨683144422395993236113621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14573747677781189037090581 683144422395993236113621)
          ·
            refine ⟨16011197399906091471413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 683144422395993236113621 16011197399906091471413)
            ·
              rfl

theorem cell20_947144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 7].length) (baseStart_947144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947144 prefixEnd_947144 := by exact prefixLift 947144
  have htrace : WordTrace (prefixWord ++ tailWord_947144) baseStart_947144 baseEnd_947144 := by
    simpa [prefixWord, tailWord_947144, baseEnd_947144] using wordTrace_append hprefix tailTrace_947144
  have hstable : (prefixWord ++ tailWord_947144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947144).length < 2 ^ (prefixWord ++ tailWord_947144).sum := by decide
  have hdescent : baseEnd_947144 < baseStart_947144 := by decide
  rcases family_descends (prefixWord ++ tailWord_947144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947151 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_947151 : Nat := 118140960795 + 947151 * 2 ^ 59
def prefixEnd_947151 : Nat := 4983230072969 + 3 ^ 40 * 947151 * 2
def baseEnd_947151 : Nat := 432305524788203556494789

theorem tailTrace_947151 : CollatzResearch.WordTrace tailWord_947151 prefixEnd_947151 432305524788203556494789 := by
  unfold tailWord_947151
  simp only [CollatzResearch.WordTrace]
  refine ⟨34545434991641162357497307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23030289994427441571664871 34545434991641162357497307)
  ·
    refine ⟨51818152487461743536245961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34545434991641162357497307 51818152487461743536245961)
    ·
      refine ⟨38863614365596307652184471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51818152487461743536245961 38863614365596307652184471)
      ·
        refine ⟨58295421548394461478276707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38863614365596307652184471 58295421548394461478276707)
        ·
          refine ⟨87443132322591692217415061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58295421548394461478276707 87443132322591692217415061)
          ·
            refine ⟨4098896827621485572691331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87443132322591692217415061 4098896827621485572691331)
            ·
              refine ⟨6148345241432228359036997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098896827621485572691331 6148345241432228359036997)
              ·
                refine ⟨1152814732768542817319437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6148345241432228359036997 1152814732768542817319437)
                ·
                  refine ⟨432305524788203556494789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152814732768542817319437 432305524788203556494789)
                  ·
                    rfl

theorem cell20_947151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_947151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947151 prefixEnd_947151 := by exact prefixLift 947151
  have htrace : WordTrace (prefixWord ++ tailWord_947151) baseStart_947151 baseEnd_947151 := by
    simpa [prefixWord, tailWord_947151, baseEnd_947151] using wordTrace_append hprefix tailTrace_947151
  have hstable : (prefixWord ++ tailWord_947151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947151).length < 2 ^ (prefixWord ++ tailWord_947151).sum := by decide
  have hdescent : baseEnd_947151 < baseStart_947151 := by decide
  rcases family_descends (prefixWord ++ tailWord_947151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947175 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_947175 : Nat := 118140960795 + 947175 * 2 ^ 59
def prefixEnd_947175 : Nat := 4983230072969 + 3 ^ 40 * 947175 * 2
def baseEnd_947175 : Nat := 432316479042166139694691

theorem tailTrace_947175 : CollatzResearch.WordTrace tailWord_947175 prefixEnd_947175 432316479042166139694691 := by
  unfold tailWord_947175
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546310343554214456370979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23030873562369476304247319 34546310343554214456370979)
  ·
    refine ⟨51819465515331321684556469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34546310343554214456370979 51819465515331321684556469)
    ·
      refine ⟨4858074892062311407927169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51819465515331321684556469 4858074892062311407927169)
      ·
        refine ⟨3643556169046733555945377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4858074892062311407927169 3643556169046733555945377)
        ·
          refine ⟨2732667126785050166959033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3643556169046733555945377 2732667126785050166959033)
          ·
            refine ⟨2049500345088787625219275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732667126785050166959033 2049500345088787625219275)
            ·
              refine ⟨3074250517633181437828913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049500345088787625219275 3074250517633181437828913)
              ·
                refine ⟨2305687888224886078371685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074250517633181437828913 2305687888224886078371685)
                ·
                  refine ⟨432316479042166139694691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305687888224886078371685 432316479042166139694691)
                  ·
                    rfl

theorem cell20_947175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_947175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947175 prefixEnd_947175 := by exact prefixLift 947175
  have htrace : WordTrace (prefixWord ++ tailWord_947175) baseStart_947175 baseEnd_947175 := by
    simpa [prefixWord, tailWord_947175, baseEnd_947175] using wordTrace_append hprefix tailTrace_947175
  have hstable : (prefixWord ++ tailWord_947175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947175).length < 2 ^ (prefixWord ++ tailWord_947175).sum := by decide
  have hdescent : baseEnd_947175 < baseStart_947175 := by decide
  rcases family_descends (prefixWord ++ tailWord_947175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947223 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 3]
def baseStart_947223 : Nat := 118140960795 + 947223 * 2 ^ 59
def prefixEnd_947223 : Nat := 4983230072969 + 3 ^ 40 * 947223 * 2
def baseEnd_947223 : Nat := 432338387550091306094495

theorem tailTrace_947223 : CollatzResearch.WordTrace tailWord_947223 prefixEnd_947223 432338387550091306094495 := by
  unfold tailWord_947223
  simp only [CollatzResearch.WordTrace]
  refine ⟨34548061047380318654118323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23032040698253545769412215 34548061047380318654118323)
  ·
    refine ⟨51822091571070477981177485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34548061047380318654118323 51822091571070477981177485)
    ·
      refine ⟨19433284339151429242941557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51822091571070477981177485 19433284339151429242941557)
      ·
        refine ⟨1821870406795446491525771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19433284339151429242941557 1821870406795446491525771)
        ·
          refine ⟨2732805610193169737288657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821870406795446491525771 2732805610193169737288657)
          ·
            refine ⟨2049604207644877302966493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732805610193169737288657 2049604207644877302966493)
            ·
              refine ⟨768601577866828988612435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2049604207644877302966493 768601577866828988612435)
              ·
                refine ⟨1152902366800243482918653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768601577866828988612435 1152902366800243482918653)
                ·
                  refine ⟨432338387550091306094495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152902366800243482918653 432338387550091306094495)
                  ·
                    rfl

theorem cell20_947223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_947223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947223 prefixEnd_947223 := by exact prefixLift 947223
  have htrace : WordTrace (prefixWord ++ tailWord_947223) baseStart_947223 baseEnd_947223 := by
    simpa [prefixWord, tailWord_947223, baseEnd_947223] using wordTrace_append hprefix tailTrace_947223
  have hstable : (prefixWord ++ tailWord_947223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947223).length < 2 ^ (prefixWord ++ tailWord_947223).sum := by decide
  have hdescent : baseEnd_947223 < baseStart_947223 := by decide
  rcases family_descends (prefixWord ++ tailWord_947223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947248 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_947248 : Nat := 118140960795 + 947248 * 2 ^ 59
def prefixEnd_947248 : Nat := 4983230072969 + 3 ^ 40 * 947248 * 2
def baseEnd_947248 : Nat := 432349798231302330261059

theorem tailTrace_947248 : CollatzResearch.WordTrace tailWord_947248 prefixEnd_947248 432349798231302330261059 := by
  unfold tailWord_947248
  simp only [CollatzResearch.WordTrace]
  refine ⟨17274486436144873961889199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23032648581526498615852265 17274486436144873961889199)
  ·
    refine ⟨25911729654217310942833799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17274486436144873961889199 25911729654217310942833799)
    ·
      refine ⟨38867594481325966414250699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25911729654217310942833799 38867594481325966414250699)
      ·
        refine ⟨58301391721988949621376049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38867594481325966414250699 58301391721988949621376049)
        ·
          refine ⟨43726043791491712216032037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58301391721988949621376049 43726043791491712216032037)
          ·
            refine ⟨8198633210904696040506007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43726043791491712216032037 8198633210904696040506007)
            ·
              refine ⟨12297949816357044060759011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198633210904696040506007 12297949816357044060759011)
              ·
                refine ⟨18446924724535566091138517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12297949816357044060759011 18446924724535566091138517)
                ·
                  refine ⟨432349798231302330261059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18446924724535566091138517 432349798231302330261059)
                  ·
                    rfl

theorem cell20_947248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_947248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947248 prefixEnd_947248 := by exact prefixLift 947248
  have htrace : WordTrace (prefixWord ++ tailWord_947248) baseStart_947248 baseEnd_947248 := by
    simpa [prefixWord, tailWord_947248, baseEnd_947248] using wordTrace_append hprefix tailTrace_947248
  have hstable : (prefixWord ++ tailWord_947248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947248).length < 2 ^ (prefixWord ++ tailWord_947248).sum := by decide
  have hdescent : baseEnd_947248 < baseStart_947248 := by decide
  rcases family_descends (prefixWord ++ tailWord_947248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947282 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_947282 : Nat := 118140960795 + 947282 * 2 ^ 59
def prefixEnd_947282 : Nat := 4983230072969 + 3 ^ 40 * 947282 * 2
def baseEnd_947282 : Nat := 432365316757749323127587

theorem tailTrace_947282 : CollatzResearch.WordTrace tailWord_947282 prefixEnd_947282 432365316757749323127587 := by
  unfold tailWord_947282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637553238541642932629025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23033475302777714487010733 8637553238541642932629025)
  ·
    refine ⟨6478164928906232199471769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8637553238541642932629025 6478164928906232199471769)
    ·
      refine ⟨4858623696679674149603827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6478164928906232199471769 4858623696679674149603827)
      ·
        refine ⟨7287935545019511224405741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858623696679674149603827 7287935545019511224405741)
        ·
          refine ⟨2732975829382316709152153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7287935545019511224405741 2732975829382316709152153)
          ·
            refine ⟨2049731872036737531864115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732975829382316709152153 2049731872036737531864115)
            ·
              refine ⟨3074597808055106297796173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049731872036737531864115 3074597808055106297796173)
              ·
                refine ⟨1152974178020664861673565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3074597808055106297796173 1152974178020664861673565)
                ·
                  refine ⟨432365316757749323127587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152974178020664861673565 432365316757749323127587)
                  ·
                    rfl

theorem cell20_947282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_947282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947282 prefixEnd_947282 := by exact prefixLift 947282
  have htrace : WordTrace (prefixWord ++ tailWord_947282) baseStart_947282 baseEnd_947282 := by
    simpa [prefixWord, tailWord_947282, baseEnd_947282] using wordTrace_append hprefix tailTrace_947282
  have hstable : (prefixWord ++ tailWord_947282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947282).length < 2 ^ (prefixWord ++ tailWord_947282).sum := by decide
  have hdescent : baseEnd_947282 < baseStart_947282 := by decide
  rcases family_descends (prefixWord ++ tailWord_947282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947326 : List Nat := [4, 2, 4, 1, 2, 1, 1, 5]
def baseStart_947326 : Nat := 118140960795 + 947326 * 2 ^ 59
def prefixEnd_947326 : Nat := 4983230072969 + 3 ^ 40 * 947326 * 2
def baseEnd_947326 : Nat := 144128466518893575220247

theorem tailTrace_947326 : CollatzResearch.WordTrace tailWord_947326 prefixEnd_947326 144128466518893575220247 := by
  unfold tailWord_947326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318977220750895905639729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23034545177338111496745221 4318977220750895905639729)
  ·
    refine ⟨3239232915563171929229797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4318977220750895905639729 3239232915563171929229797)
    ·
      refine ⟨607356171668094736730587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3239232915563171929229797 607356171668094736730587)
      ·
        refine ⟨911034257502142105095881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607356171668094736730587 911034257502142105095881)
        ·
          refine ⟨683275693126606578821911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911034257502142105095881 683275693126606578821911)
          ·
            refine ⟨1024913539689909868232867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683275693126606578821911 1024913539689909868232867)
            ·
              refine ⟨1537370309534864802349301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024913539689909868232867 1537370309534864802349301)
              ·
                refine ⟨144128466518893575220247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1537370309534864802349301 144128466518893575220247)
                ·
                  rfl

theorem cell20_947326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_947326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947326 prefixEnd_947326 := by exact prefixLift 947326
  have htrace : WordTrace (prefixWord ++ tailWord_947326) baseStart_947326 baseEnd_947326 := by
    simpa [prefixWord, tailWord_947326, baseEnd_947326] using wordTrace_append hprefix tailTrace_947326
  have hstable : (prefixWord ++ tailWord_947326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947326).length < 2 ^ (prefixWord ++ tailWord_947326).sum := by decide
  have hdescent : baseEnd_947326 < baseStart_947326 := by decide
  rcases family_descends (prefixWord ++ tailWord_947326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947365 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 2]
def baseStart_947365 : Nat := 118140960795 + 947365 * 2 ^ 59
def prefixEnd_947365 : Nat := 4983230072969 + 3 ^ 40 * 947365 * 2
def baseEnd_947365 : Nat := 432403200219369923360581

theorem tailTrace_947365 : CollatzResearch.WordTrace tailWord_947365 prefixEnd_947365 432403200219369923360581 := by
  unfold tailWord_947365
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553240212865876905787549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23035493475243917937191699 34553240212865876905787549)
  ·
    refine ⟨12957465079824703839670331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34553240212865876905787549 12957465079824703839670331)
    ·
      refine ⟨19436197619737055759505497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12957465079824703839670331 19436197619737055759505497)
      ·
        refine ⟨14577148214802791819629123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19436197619737055759505497 14577148214802791819629123)
        ·
          refine ⟨21865722322204187729443685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14577148214802791819629123 21865722322204187729443685)
          ·
            refine ⟨4099822935413285199270691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21865722322204187729443685 4099822935413285199270691)
            ·
              refine ⟨6149734403119927798906037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099822935413285199270691 6149734403119927798906037)
              ·
                refine ⟨576537600292493231147441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6149734403119927798906037 576537600292493231147441)
                ·
                  refine ⟨432403200219369923360581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576537600292493231147441 432403200219369923360581)
                  ·
                    rfl

theorem cell20_947365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_947365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947365 prefixEnd_947365 := by exact prefixLift 947365
  have htrace : WordTrace (prefixWord ++ tailWord_947365) baseStart_947365 baseEnd_947365 := by
    simpa [prefixWord, tailWord_947365, baseEnd_947365] using wordTrace_append hprefix tailTrace_947365
  have hstable : (prefixWord ++ tailWord_947365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947365).length < 2 ^ (prefixWord ++ tailWord_947365).sum := by decide
  have hdescent : baseEnd_947365 < baseStart_947365 := by decide
  rcases family_descends (prefixWord ++ tailWord_947365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947379 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_947379 : Nat := 118140960795 + 947379 * 2 ^ 59
def prefixEnd_947379 : Nat := 4983230072969 + 3 ^ 40 * 947379 * 2
def baseEnd_947379 : Nat := 432409590200848096893857

theorem tailTrace_947379 : CollatzResearch.WordTrace tailWord_947379 prefixEnd_947379 432409590200848096893857 := by
  unfold tailWord_947379
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553750834815157296797191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23035833889876771531198127 34553750834815157296797191)
  ·
    refine ⟨51830626252222735945195787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34553750834815157296797191 51830626252222735945195787)
    ·
      refine ⟨77745939378334103917793681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51830626252222735945195787 77745939378334103917793681)
      ·
        refine ⟨58309454533750577938345261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77745939378334103917793681 58309454533750577938345261)
        ·
          refine ⟨21866045450156466726879473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58309454533750577938345261 21866045450156466726879473)
          ·
            refine ⟨16399534087617350045159605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21866045450156466726879473 16399534087617350045159605)
            ·
              refine ⟨1537456320714126566733713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16399534087617350045159605 1537456320714126566733713)
              ·
                refine ⟨1153092240535594925050285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537456320714126566733713 1153092240535594925050285)
                ·
                  refine ⟨432409590200848096893857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153092240535594925050285 432409590200848096893857)
                  ·
                    rfl

theorem cell20_947379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_947379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947379 prefixEnd_947379 := by exact prefixLift 947379
  have htrace : WordTrace (prefixWord ++ tailWord_947379) baseStart_947379 baseEnd_947379 := by
    simpa [prefixWord, tailWord_947379, baseEnd_947379] using wordTrace_append hprefix tailTrace_947379
  have hstable : (prefixWord ++ tailWord_947379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947379).length < 2 ^ (prefixWord ++ tailWord_947379).sum := by decide
  have hdescent : baseEnd_947379 < baseStart_947379 := by decide
  rcases family_descends (prefixWord ++ tailWord_947379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947406 : List Nat := [4, 1, 1, 1, 6, 1, 2, 4]
def baseStart_947406 : Nat := 118140960795 + 947406 * 2 ^ 59
def prefixEnd_947406 : Nat := 4983230072969 + 3 ^ 40 * 947406 * 2
def baseEnd_947406 : Nat := 144140637912185334331249

theorem tailTrace_947406 : CollatzResearch.WordTrace tailWord_947406 prefixEnd_947406 144140637912185334331249 := by
  unfold tailWord_947406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319341950714667613503759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23036490403811560605353381 4319341950714667613503759)
  ·
    refine ⟨6479012926072001420255639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319341950714667613503759 6479012926072001420255639)
    ·
      refine ⟨9718519389108002130383459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6479012926072001420255639 9718519389108002130383459)
      ·
        refine ⟨14577779083662003195575189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9718519389108002130383459 14577779083662003195575189)
        ·
          refine ⟨683333394546656399792587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14577779083662003195575189 683333394546656399792587)
          ·
            refine ⟨1025000091819984599688881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683333394546656399792587 1025000091819984599688881)
            ·
              refine ⟨768750068864988449766661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025000091819984599688881 768750068864988449766661)
              ·
                refine ⟨144140637912185334331249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768750068864988449766661 144140637912185334331249)
                ·
                  rfl

theorem cell20_947406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_947406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947406 prefixEnd_947406 := by exact prefixLift 947406
  have htrace : WordTrace (prefixWord ++ tailWord_947406) baseStart_947406 baseEnd_947406 := by
    simpa [prefixWord, tailWord_947406, baseEnd_947406] using wordTrace_append hprefix tailTrace_947406
  have hstable : (prefixWord ++ tailWord_947406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947406).length < 2 ^ (prefixWord ++ tailWord_947406).sum := by decide
  have hdescent : baseEnd_947406 < baseStart_947406 := by decide
  rcases family_descends (prefixWord ++ tailWord_947406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947407 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_947407 : Nat := 118140960795 + 947407 * 2 ^ 59
def prefixEnd_947407 : Nat := 4983230072969 + 3 ^ 40 * 947407 * 2
def baseEnd_947407 : Nat := 432422370163804443960409

theorem tailTrace_947407 : CollatzResearch.WordTrace tailWord_947407 prefixEnd_947407 432422370163804443960409 := by
  unfold tailWord_947407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34554772078713718078816475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23036514719142478719210983 34554772078713718078816475)
  ·
    refine ⟨51832158118070577118224713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34554772078713718078816475 51832158118070577118224713)
    ·
      refine ⟨38874118588552932838668535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51832158118070577118224713 38874118588552932838668535)
      ·
        refine ⟨58311177882829399258002803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38874118588552932838668535 58311177882829399258002803)
        ·
          refine ⟨87466766824244098887004205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58311177882829399258002803 87466766824244098887004205)
          ·
            refine ⟨32800037559091537082626577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87466766824244098887004205 32800037559091537082626577)
            ·
              refine ⟨24600028169318652811969933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32800037559091537082626577 24600028169318652811969933)
              ·
                refine ⟨9225010563494494804488725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24600028169318652811969933 9225010563494494804488725)
                ·
                  refine ⟨432422370163804443960409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9225010563494494804488725 432422370163804443960409)
                  ·
                    rfl

theorem cell20_947407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_947407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947407 prefixEnd_947407 := by exact prefixLift 947407
  have htrace : WordTrace (prefixWord ++ tailWord_947407) baseStart_947407 baseEnd_947407 := by
    simpa [prefixWord, tailWord_947407, baseEnd_947407] using wordTrace_append hprefix tailTrace_947407
  have hstable : (prefixWord ++ tailWord_947407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947407).length < 2 ^ (prefixWord ++ tailWord_947407).sum := by decide
  have hdescent : baseEnd_947407 < baseStart_947407 := by decide
  rcases family_descends (prefixWord ++ tailWord_947407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947437 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 2]
def baseStart_947437 : Nat := 118140960795 + 947437 * 2 ^ 59
def prefixEnd_947437 : Nat := 4983230072969 + 3 ^ 40 * 947437 * 2
def baseEnd_947437 : Nat := 432436062981257672960287

theorem tailTrace_947437 : CollatzResearch.WordTrace tailWord_947437 prefixEnd_947437 432436062981257672960287 := by
  unfold tailWord_947437
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555866268605033202408565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23037244179070022134939043 34555866268605033202408565)
  ·
    refine ⟨3239612462681721862725803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34555866268605033202408565 3239612462681721862725803)
    ·
      refine ⟨4859418694022582794088705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3239612462681721862725803 4859418694022582794088705)
      ·
        refine ⟨3644564020516937095566529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4859418694022582794088705 3644564020516937095566529)
        ·
          refine ⟨2733423015387702821674897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3644564020516937095566529 2733423015387702821674897)
          ·
            refine ⟨2050067261540777116256173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733423015387702821674897 2050067261540777116256173)
            ·
              refine ⟨768775223077791418596065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2050067261540777116256173 768775223077791418596065)
              ·
                refine ⟨576581417308343563947049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768775223077791418596065 576581417308343563947049)
                ·
                  refine ⟨432436062981257672960287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576581417308343563947049 432436062981257672960287)
                  ·
                    rfl

theorem cell20_947437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_947437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947437 prefixEnd_947437 := by exact prefixLift 947437
  have htrace : WordTrace (prefixWord ++ tailWord_947437) baseStart_947437 baseEnd_947437 := by
    simpa [prefixWord, tailWord_947437, baseEnd_947437] using wordTrace_append hprefix tailTrace_947437
  have hstable : (prefixWord ++ tailWord_947437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947437).length < 2 ^ (prefixWord ++ tailWord_947437).sum := by decide
  have hdescent : baseEnd_947437 < baseStart_947437 := by decide
  rcases family_descends (prefixWord ++ tailWord_947437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947455 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_947455 : Nat := 118140960795 + 947455 * 2 ^ 59
def prefixEnd_947455 : Nat := 4983230072969 + 3 ^ 40 * 947455 * 2
def baseEnd_947455 : Nat := 432444278671729610360213

theorem tailTrace_947455 : CollatzResearch.WordTrace tailWord_947455 prefixEnd_947455 432444278671729610360213 := by
  unfold tailWord_947455
  simp only [CollatzResearch.WordTrace]
  refine ⟨34556522782539822276563819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23037681855026548184375879 34556522782539822276563819)
  ·
    refine ⟨51834784173809733414845729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34556522782539822276563819 51834784173809733414845729)
    ·
      refine ⟨38876088130357300061134297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51834784173809733414845729 38876088130357300061134297)
      ·
        refine ⟨29157066097767975045850723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38876088130357300061134297 29157066097767975045850723)
        ·
          refine ⟨43735599146651962568776085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29157066097767975045850723 43735599146651962568776085)
          ·
            refine ⟨2050106209999310745411379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43735599146651962568776085 2050106209999310745411379)
            ·
              refine ⟨3075159314998966118117069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050106209999310745411379 3075159314998966118117069)
              ·
                refine ⟨1153184743124612294293901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3075159314998966118117069 1153184743124612294293901)
                ·
                  refine ⟨432444278671729610360213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153184743124612294293901 432444278671729610360213)
                  ·
                    rfl

theorem cell20_947455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_947455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947455 prefixEnd_947455 := by exact prefixLift 947455
  have htrace : WordTrace (prefixWord ++ tailWord_947455) baseStart_947455 baseEnd_947455 := by
    simpa [prefixWord, tailWord_947455, baseEnd_947455] using wordTrace_append hprefix tailTrace_947455
  have hstable : (prefixWord ++ tailWord_947455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947455).length < 2 ^ (prefixWord ++ tailWord_947455).sum := by decide
  have hdescent : baseEnd_947455 < baseStart_947455 := by decide
  rcases family_descends (prefixWord ++ tailWord_947455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947479 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 2]
def baseStart_947479 : Nat := 118140960795 + 947479 * 2 ^ 59
def prefixEnd_947479 : Nat := 4983230072969 + 3 ^ 40 * 947479 * 2
def baseEnd_947479 : Nat := 432455232925692193560115

theorem tailTrace_947479 : CollatzResearch.WordTrace tailWord_947479 prefixEnd_947479 432455232925692193560115 := by
  unfold tailWord_947479
  simp only [CollatzResearch.WordTrace]
  refine ⟨34557398134452874375437491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23038265422968582916958327 34557398134452874375437491)
  ·
    refine ⟨51836097201679311563156237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34557398134452874375437491 51836097201679311563156237)
    ·
      refine ⟨19438536450629741836183589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51836097201679311563156237 19438536450629741836183589)
      ·
        refine ⟨3644725584493076594284423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19438536450629741836183589 3644725584493076594284423)
        ·
          refine ⟨5467088376739614891426635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644725584493076594284423 5467088376739614891426635)
          ·
            refine ⟨8200632565109422337139953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467088376739614891426635 8200632565109422337139953)
            ·
              refine ⟨6150474423832066752854965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8200632565109422337139953 6150474423832066752854965)
              ·
                refine ⟨576606977234256258080153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6150474423832066752854965 576606977234256258080153)
                ·
                  refine ⟨432455232925692193560115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576606977234256258080153 432455232925692193560115)
                  ·
                    rfl

theorem cell20_947479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 2].length) (baseStart_947479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947479 prefixEnd_947479 := by exact prefixLift 947479
  have htrace : WordTrace (prefixWord ++ tailWord_947479) baseStart_947479 baseEnd_947479 := by
    simpa [prefixWord, tailWord_947479, baseEnd_947479] using wordTrace_append hprefix tailTrace_947479
  have hstable : (prefixWord ++ tailWord_947479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947479).length < 2 ^ (prefixWord ++ tailWord_947479).sum := by decide
  have hdescent : baseEnd_947479 < baseStart_947479 := by decide
  rcases family_descends (prefixWord ++ tailWord_947479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947486 : List Nat := [4, 3, 2, 1, 10]
def baseStart_947486 : Nat := 118140960795 + 947486 * 2 ^ 59
def prefixEnd_947486 : Nat := 4983230072969 + 3 ^ 40 * 947486 * 2
def baseEnd_947486 : Nat := 5338992937239892349713

theorem tailTrace_947486 : CollatzResearch.WordTrace tailWord_947486 prefixEnd_947486 5338992937239892349713 := by
  unfold tailWord_947486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319706680678439321367789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23038435630285009713961541 4319706680678439321367789)
  ·
    refine ⟨1619890005254414745512921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4319706680678439321367789 1619890005254414745512921)
    ·
      refine ⟨1214917503940811059134691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1619890005254414745512921 1214917503940811059134691)
      ·
        refine ⟨1822376255911216588702037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214917503940811059134691 1822376255911216588702037)
        ·
          refine ⟨5338992937239892349713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1822376255911216588702037 5338992937239892349713)
          ·
            rfl

theorem cell20_947486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 10].length) (baseStart_947486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947486 prefixEnd_947486 := by exact prefixLift 947486
  have htrace : WordTrace (prefixWord ++ tailWord_947486) baseStart_947486 baseEnd_947486 := by
    simpa [prefixWord, tailWord_947486, baseEnd_947486] using wordTrace_append hprefix tailTrace_947486
  have hstable : (prefixWord ++ tailWord_947486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947486).length < 2 ^ (prefixWord ++ tailWord_947486).sum := by decide
  have hdescent : baseEnd_947486 < baseStart_947486 := by decide
  rcases family_descends (prefixWord ++ tailWord_947486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947493 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_947493 : Nat := 118140960795 + 947493 * 2 ^ 59
def prefixEnd_947493 : Nat := 4983230072969 + 3 ^ 40 * 947493 * 2
def baseEnd_947493 : Nat := 432461622907170367093391

theorem tailTrace_947493 : CollatzResearch.WordTrace tailWord_947493 prefixEnd_947493 432461622907170367093391 := by
  unfold tailWord_947493
  simp only [CollatzResearch.WordTrace]
  refine ⟨34557908756402154766447133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23038605837601436510964755 34557908756402154766447133)
  ·
    refine ⟨12959215783650808037417675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34557908756402154766447133 12959215783650808037417675)
    ·
      refine ⟨19438823675476212056126513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12959215783650808037417675 19438823675476212056126513)
      ·
        refine ⟨14579117756607159042094885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19438823675476212056126513 14579117756607159042094885)
        ·
          refine ⟨2733584579363842320392791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14579117756607159042094885 2733584579363842320392791)
          ·
            refine ⟨4100376869045763480589187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733584579363842320392791 4100376869045763480589187)
            ·
              refine ⟨6150565303568645220883781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100376869045763480589187 6150565303568645220883781)
              ·
                refine ⟨1153230994419120978915709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6150565303568645220883781 1153230994419120978915709)
                ·
                  refine ⟨432461622907170367093391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153230994419120978915709 432461622907170367093391)
                  ·
                    rfl

theorem cell20_947493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_947493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947493 prefixEnd_947493 := by exact prefixLift 947493
  have htrace : WordTrace (prefixWord ++ tailWord_947493) baseStart_947493 baseEnd_947493 := by
    simpa [prefixWord, tailWord_947493, baseEnd_947493] using wordTrace_append hprefix tailTrace_947493
  have hstable : (prefixWord ++ tailWord_947493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947493).length < 2 ^ (prefixWord ++ tailWord_947493).sum := by decide
  have hdescent : baseEnd_947493 < baseStart_947493 := by decide
  rcases family_descends (prefixWord ++ tailWord_947493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947496 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 2]
def baseStart_947496 : Nat := 118140960795 + 947496 * 2 ^ 59
def prefixEnd_947496 : Nat := 4983230072969 + 3 ^ 40 * 947496 * 2
def baseEnd_947496 : Nat := 432462992188915689993379

theorem tailTrace_947496 : CollatzResearch.WordTrace tailWord_947496 prefixEnd_947496 432462992188915689993379 := by
  unfold tailWord_947496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17279009087695643139403171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23038678783594190852537561 17279009087695643139403171)
  ·
    refine ⟨25918513631543464709104757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17279009087695643139403171 25918513631543464709104757)
    ·
      refine ⟨2429860652957199816478571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25918513631543464709104757 2429860652957199816478571)
      ·
        refine ⟨3644790979435799724717857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429860652957199816478571 3644790979435799724717857)
        ·
          refine ⟨2733593234576849793538393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3644790979435799724717857 2733593234576849793538393)
          ·
            refine ⟨2050194925932637345153795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733593234576849793538393 2050194925932637345153795)
            ·
              refine ⟨3075292388898956017730693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050194925932637345153795 3075292388898956017730693)
              ·
                refine ⟨576617322918554253324505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3075292388898956017730693 576617322918554253324505)
                ·
                  refine ⟨432462992188915689993379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576617322918554253324505 432462992188915689993379)
                  ·
                    rfl

theorem cell20_947496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_947496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947496 prefixEnd_947496 := by exact prefixLift 947496
  have htrace : WordTrace (prefixWord ++ tailWord_947496) baseStart_947496 baseEnd_947496 := by
    simpa [prefixWord, tailWord_947496, baseEnd_947496] using wordTrace_append hprefix tailTrace_947496
  have hstable : (prefixWord ++ tailWord_947496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947496).length < 2 ^ (prefixWord ++ tailWord_947496).sum := by decide
  have hdescent : baseEnd_947496 < baseStart_947496 := by decide
  rcases family_descends (prefixWord ++ tailWord_947496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947507 : List Nat := [1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_947507 : Nat := 118140960795 + 947507 * 2 ^ 59
def prefixEnd_947507 : Nat := 4983230072969 + 3 ^ 40 * 947507 * 2
def baseEnd_947507 : Nat := 144156004296216180208889

theorem tailTrace_947507 : CollatzResearch.WordTrace tailWord_947507 prefixEnd_947507 144156004296216180208889 := by
  unfold tailWord_947507
  simp only [CollatzResearch.WordTrace]
  refine ⟨34558419378351435157456775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23038946252234290104971183 34558419378351435157456775)
  ·
    refine ⟨51837629067527152736185163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34558419378351435157456775 51837629067527152736185163)
    ·
      refine ⟨77756443601290729104277745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51837629067527152736185163 77756443601290729104277745)
      ·
        refine ⟨58317332700968046828208309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77756443601290729104277745 58317332700968046828208309)
        ·
          refine ⟨5467249940715754390144529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58317332700968046828208309 5467249940715754390144529)
          ·
            refine ⟨4100437455536815792608397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5467249940715754390144529 4100437455536815792608397)
            ·
              refine ⟨1537664045826305922228149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4100437455536815792608397 1537664045826305922228149)
              ·
                refine ⟨144156004296216180208889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1537664045826305922228149 144156004296216180208889)
                ·
                  rfl

theorem cell20_947507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_947507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947507 prefixEnd_947507 := by exact prefixLift 947507
  have htrace : WordTrace (prefixWord ++ tailWord_947507) baseStart_947507 baseEnd_947507 := by
    simpa [prefixWord, tailWord_947507, baseEnd_947507] using wordTrace_append hprefix tailTrace_947507
  have hstable : (prefixWord ++ tailWord_947507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947507).length < 2 ^ (prefixWord ++ tailWord_947507).sum := by decide
  have hdescent : baseEnd_947507 < baseStart_947507 := by decide
  rcases family_descends (prefixWord ++ tailWord_947507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947555 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 2]
def baseStart_947555 : Nat := 118140960795 + 947555 * 2 ^ 59
def prefixEnd_947555 : Nat := 4983230072969 + 3 ^ 40 * 947555 * 2
def baseEnd_947555 : Nat := 432489921396573707026471

theorem tailTrace_947555 : CollatzResearch.WordTrace tailWord_947555 prefixEnd_947555 432489921396573707026471 := by
  unfold tailWord_947555
  simp only [CollatzResearch.WordTrace]
  refine ⟨34560170082177539355204119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23040113388118359570136079 34560170082177539355204119)
  ·
    refine ⟨51840255123266309032806179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34560170082177539355204119 51840255123266309032806179)
    ·
      refine ⟨77760382684899463549209269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51840255123266309032806179 77760382684899463549209269)
      ·
        refine ⟨7290035876709324707738369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77760382684899463549209269 7290035876709324707738369)
        ·
          refine ⟨5467526907531993530803777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7290035876709324707738369 5467526907531993530803777)
          ·
            refine ⟨4100645180648995148102833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5467526907531993530803777 4100645180648995148102833)
            ·
              refine ⟨3075483885486746361077125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100645180648995148102833 3075483885486746361077125)
              ·
                refine ⟨576653228528764942701961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3075483885486746361077125 576653228528764942701961)
                ·
                  refine ⟨432489921396573707026471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576653228528764942701961 432489921396573707026471)
                  ·
                    rfl

theorem cell20_947555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 2].length) (baseStart_947555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947555 prefixEnd_947555 := by exact prefixLift 947555
  have htrace : WordTrace (prefixWord ++ tailWord_947555) baseStart_947555 baseEnd_947555 := by
    simpa [prefixWord, tailWord_947555, baseEnd_947555] using wordTrace_append hprefix tailTrace_947555
  have hstable : (prefixWord ++ tailWord_947555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947555).length < 2 ^ (prefixWord ++ tailWord_947555).sum := by decide
  have hdescent : baseEnd_947555 < baseStart_947555 := by decide
  rcases family_descends (prefixWord ++ tailWord_947555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947586 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_947586 : Nat := 118140960795 + 947586 * 2 ^ 59
def prefixEnd_947586 : Nat := 4983230072969 + 3 ^ 40 * 947586 * 2
def baseEnd_947586 : Nat := 432504070641275376993011

theorem tailTrace_947586 : CollatzResearch.WordTrace tailWord_947586 prefixEnd_947586 432504070641275376993011 := by
  unfold tailWord_947586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8640325186266307912395653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23040867163376821099721741 8640325186266307912395653)
  ·
    refine ⟨1620060972424932733574185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8640325186266307912395653 1620060972424932733574185)
    ·
      refine ⟨1215045729318699550180639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1620060972424932733574185 1215045729318699550180639)
      ·
        refine ⟨1822568593978049325270959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215045729318699550180639 1822568593978049325270959)
        ·
          refine ⟨2733852890967073987906439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822568593978049325270959 2733852890967073987906439)
          ·
            refine ⟨4100779336450610981859659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733852890967073987906439 4100779336450610981859659)
            ·
              refine ⟨6151169004675916472789489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100779336450610981859659 6151169004675916472789489)
              ·
                refine ⟨4613376753506937354592117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6151169004675916472789489 4613376753506937354592117)
                ·
                  refine ⟨432504070641275376993011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4613376753506937354592117 432504070641275376993011)
                  ·
                    rfl

theorem cell20_947586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_947586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947586 prefixEnd_947586 := by exact prefixLift 947586
  have htrace : WordTrace (prefixWord ++ tailWord_947586) baseStart_947586 baseEnd_947586 := by
    simpa [prefixWord, tailWord_947586, baseEnd_947586] using wordTrace_append hprefix tailTrace_947586
  have hstable : (prefixWord ++ tailWord_947586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947586).length < 2 ^ (prefixWord ++ tailWord_947586).sum := by decide
  have hdescent : baseEnd_947586 < baseStart_947586 := by decide
  rcases family_descends (prefixWord ++ tailWord_947586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947610 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_947610 : Nat := 118140960795 + 947610 * 2 ^ 59
def prefixEnd_947610 : Nat := 4983230072969 + 3 ^ 40 * 947610 * 2
def baseEnd_947610 : Nat := 432515024895237960192913

theorem tailTrace_947610 : CollatzResearch.WordTrace tailWord_947610 prefixEnd_947610 432515024895237960192913 := by
  unfold tailWord_947610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8640544024244570937114071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23041450731318855832304189 8640544024244570937114071)
  ·
    refine ⟨12960816036366856405671107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8640544024244570937114071 12960816036366856405671107)
    ·
      refine ⟨19441224054550284608506661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12960816036366856405671107 19441224054550284608506661)
      ·
        refine ⟨3645229510228178364094999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19441224054550284608506661 3645229510228178364094999)
        ·
          refine ⟨5467844265342267546142499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645229510228178364094999 5467844265342267546142499)
          ·
            refine ⟨8201766398013401319213749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467844265342267546142499 8201766398013401319213749)
            ·
              refine ⟨768915599813756373676289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8201766398013401319213749 768915599813756373676289)
              ·
                refine ⟨576686699860317280257217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768915599813756373676289 576686699860317280257217)
                ·
                  refine ⟨432515024895237960192913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576686699860317280257217 432515024895237960192913)
                  ·
                    rfl

theorem cell20_947610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_947610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947610 prefixEnd_947610 := by exact prefixLift 947610
  have htrace : WordTrace (prefixWord ++ tailWord_947610) baseStart_947610 baseEnd_947610 := by
    simpa [prefixWord, tailWord_947610, baseEnd_947610] using wordTrace_append hprefix tailTrace_947610
  have hstable : (prefixWord ++ tailWord_947610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947610).length < 2 ^ (prefixWord ++ tailWord_947610).sum := by decide
  have hdescent : baseEnd_947610 < baseStart_947610 := by decide
  rcases family_descends (prefixWord ++ tailWord_947610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947635 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_947635 : Nat := 118140960795 + 947635 * 2 ^ 59
def prefixEnd_947635 : Nat := 4983230072969 + 3 ^ 40 * 947635 * 2
def baseEnd_947635 : Nat := 432526435576448984359477

theorem tailTrace_947635 : CollatzResearch.WordTrace tailWord_947635 prefixEnd_947635 432526435576448984359477 := by
  unfold tailWord_947635
  simp only [CollatzResearch.WordTrace]
  refine ⟨34563087921887713018116359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23042058614591808678744239 34563087921887713018116359)
  ·
    refine ⟨51844631882831569527174539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34563087921887713018116359 51844631882831569527174539)
    ·
      refine ⟨77766947824247354290761809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51844631882831569527174539 77766947824247354290761809)
      ·
        refine ⟨58325210868185515718071357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77766947824247354290761809 58325210868185515718071357)
        ·
          refine ⟨21871954075569568394276759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58325210868185515718071357 21871954075569568394276759)
          ·
            refine ⟨32807931113354352591415139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21871954075569568394276759 32807931113354352591415139)
            ·
              refine ⟨49211896670031528887122709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32807931113354352591415139 49211896670031528887122709)
              ·
                refine ⟨2306807656407727916583877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49211896670031528887122709 2306807656407727916583877)
                ·
                  refine ⟨432526435576448984359477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306807656407727916583877 432526435576448984359477)
                  ·
                    rfl

theorem cell20_947635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_947635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947635 prefixEnd_947635 := by exact prefixLift 947635
  have htrace : WordTrace (prefixWord ++ tailWord_947635) baseStart_947635 baseEnd_947635 := by
    simpa [prefixWord, tailWord_947635, baseEnd_947635] using wordTrace_append hprefix tailTrace_947635
  have hstable : (prefixWord ++ tailWord_947635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947635).length < 2 ^ (prefixWord ++ tailWord_947635).sum := by decide
  have hdescent : baseEnd_947635 < baseStart_947635 := by decide
  rcases family_descends (prefixWord ++ tailWord_947635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947669 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 2]
def baseStart_947669 : Nat := 118140960795 + 947669 * 2 ^ 59
def prefixEnd_947669 : Nat := 4983230072969 + 3 ^ 40 * 947669 * 2
def baseEnd_947669 : Nat := 432541954102895977226005

theorem tailTrace_947669 : CollatzResearch.WordTrace tailWord_947669 prefixEnd_947669 432541954102895977226005 := by
  unfold tailWord_947669
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564328003764536824854061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23042885335843024549902707 34564328003764536824854061)
  ·
    refine ⟨12961623001411701309320273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34564328003764536824854061 12961623001411701309320273)
    ·
      refine ⟨9721217251058775981990205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12961623001411701309320273 9721217251058775981990205)
      ·
        refine ⟨3645456469147040993246327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9721217251058775981990205 3645456469147040993246327)
        ·
          refine ⟨5468184703720561489869491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645456469147040993246327 5468184703720561489869491)
          ·
            refine ⟨8202277055580842234804237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468184703720561489869491 8202277055580842234804237)
            ·
              refine ⟨3075853895842815838051589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8202277055580842234804237 3075853895842815838051589)
              ·
                refine ⟨576722605470527969634673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3075853895842815838051589 576722605470527969634673)
                ·
                  refine ⟨432541954102895977226005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576722605470527969634673 432541954102895977226005)
                  ·
                    rfl

theorem cell20_947669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_947669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947669 prefixEnd_947669 := by exact prefixLift 947669
  have htrace : WordTrace (prefixWord ++ tailWord_947669) baseStart_947669 baseEnd_947669 := by
    simpa [prefixWord, tailWord_947669, baseEnd_947669] using wordTrace_append hprefix tailTrace_947669
  have hstable : (prefixWord ++ tailWord_947669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947669).length < 2 ^ (prefixWord ++ tailWord_947669).sum := by decide
  have hdescent : baseEnd_947669 < baseStart_947669 := by decide
  rcases family_descends (prefixWord ++ tailWord_947669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947680 : List Nat := [2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_947680 : Nat := 118140960795 + 947680 * 2 ^ 59
def prefixEnd_947680 : Nat := 4983230072969 + 3 ^ 40 * 947680 * 2
def baseEnd_947680 : Nat := 144182324934209609286431

theorem tailTrace_947680 : CollatzResearch.WordTrace tailWord_947680 prefixEnd_947680 144182324934209609286431 := by
  unfold tailWord_947680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17282364603362342851752247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23043152804483123802336329 17282364603362342851752247)
  ·
    refine ⟨25923546905043514277628371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17282364603362342851752247 25923546905043514277628371)
    ·
      refine ⟨38885320357565271416442557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25923546905043514277628371 38885320357565271416442557)
      ·
        refine ⟨14581995134086976781165959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38885320357565271416442557 14581995134086976781165959)
        ·
          refine ⟨21872992701130465171748939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14581995134086976781165959 21872992701130465171748939)
          ·
            refine ⟨32809489051695697757623409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21872992701130465171748939 32809489051695697757623409)
            ·
              refine ⟨24607116788771773318217557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32809489051695697757623409 24607116788771773318217557)
              ·
                refine ⟨144182324934209609286431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24607116788771773318217557 144182324934209609286431)
                ·
                  rfl

theorem cell20_947680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_947680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947680 prefixEnd_947680 := by exact prefixLift 947680
  have htrace : WordTrace (prefixWord ++ tailWord_947680) baseStart_947680 baseEnd_947680 := by
    simpa [prefixWord, tailWord_947680, baseEnd_947680] using wordTrace_append hprefix tailTrace_947680
  have hstable : (prefixWord ++ tailWord_947680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947680).length < 2 ^ (prefixWord ++ tailWord_947680).sum := by decide
  have hdescent : baseEnd_947680 < baseStart_947680 := by decide
  rcases family_descends (prefixWord ++ tailWord_947680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947683 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_947683 : Nat := 118140960795 + 947683 * 2 ^ 59
def prefixEnd_947683 : Nat := 4983230072969 + 3 ^ 40 * 947683 * 2
def baseEnd_947683 : Nat := 432548344084374150759281

theorem tailTrace_947683 : CollatzResearch.WordTrace tailWord_947683 prefixEnd_947683 432548344084374150759281 := by
  unfold tailWord_947683
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564838625713817215863703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23043225750475878143909135 34564838625713817215863703)
  ·
    refine ⟨51847257938570725823795555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34564838625713817215863703 51847257938570725823795555)
    ·
      refine ⟨77770886907856088735693333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51847257938570725823795555 77770886907856088735693333)
      ·
        refine ⟨3645510323805754159485625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77770886907856088735693333 3645510323805754159485625)
        ·
          refine ⟨2734132742854315619614219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645510323805754159485625 2734132742854315619614219)
          ·
            refine ⟨4101199114281473429421329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734132742854315619614219 4101199114281473429421329)
            ·
              refine ⟨3075899335711105072065997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101199114281473429421329 3075899335711105072065997)
              ·
                refine ⟨1153462250891664402024749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3075899335711105072065997 1153462250891664402024749)
                ·
                  refine ⟨432548344084374150759281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153462250891664402024749 432548344084374150759281)
                  ·
                    rfl

theorem cell20_947683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_947683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947683 prefixEnd_947683 := by exact prefixLift 947683
  have htrace : WordTrace (prefixWord ++ tailWord_947683) baseStart_947683 baseEnd_947683 := by
    simpa [prefixWord, tailWord_947683, baseEnd_947683] using wordTrace_append hprefix tailTrace_947683
  have hstable : (prefixWord ++ tailWord_947683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947683).length < 2 ^ (prefixWord ++ tailWord_947683).sum := by decide
  have hdescent : baseEnd_947683 < baseStart_947683 := by decide
  rcases family_descends (prefixWord ++ tailWord_947683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947693 : List Nat := [1, 5, 1, 3, 2, 1, 3, 4]
def baseStart_947693 : Nat := 118140960795 + 947693 * 2 ^ 59
def prefixEnd_947693 : Nat := 4983230072969 + 3 ^ 40 * 947693 * 2
def baseEnd_947693 : Nat := 144184302785619520141969

theorem tailTrace_947693 : CollatzResearch.WordTrace tailWord_947693 prefixEnd_947693 144184302785619520141969 := by
  unfold tailWord_947693
  simp only [CollatzResearch.WordTrace]
  refine ⟨34565203355677588923727733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23043468903785059282485155 34565203355677588923727733)
  ·
    refine ⟨3240487814594773961599475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34565203355677588923727733 3240487814594773961599475)
    ·
      refine ⟨4860731721892160942399213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3240487814594773961599475 4860731721892160942399213)
      ·
        refine ⟨1822774395709560353399705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4860731721892160942399213 1822774395709560353399705)
        ·
          refine ⟨1367080796782170265049779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822774395709560353399705 1367080796782170265049779)
          ·
            refine ⟨2050621195173255397574669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367080796782170265049779 2050621195173255397574669)
            ·
              refine ⟨768982948189970774090501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2050621195173255397574669 768982948189970774090501)
              ·
                refine ⟨144184302785619520141969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 768982948189970774090501 144184302785619520141969)
                ·
                  rfl

theorem cell20_947693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_947693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947693 prefixEnd_947693 := by exact prefixLift 947693
  have htrace : WordTrace (prefixWord ++ tailWord_947693) baseStart_947693 baseEnd_947693 := by
    simpa [prefixWord, tailWord_947693, baseEnd_947693] using wordTrace_append hprefix tailTrace_947693
  have hstable : (prefixWord ++ tailWord_947693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947693).length < 2 ^ (prefixWord ++ tailWord_947693).sum := by decide
  have hdescent : baseEnd_947693 < baseStart_947693 := by decide
  rcases family_descends (prefixWord ++ tailWord_947693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947714 : List Nat := [3, 4, 1, 2, 1, 2, 7]
def baseStart_947714 : Nat := 118140960795 + 947714 * 2 ^ 59
def prefixEnd_947714 : Nat := 4983230072969 + 3 ^ 40 * 947714 * 2
def baseEnd_947714 : Nat := 48062499258786202302869

theorem tailTrace_947714 : CollatzResearch.WordTrace tailWord_947714 prefixEnd_947714 48062499258786202302869 := by
  unfold tailWord_947714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641492322150377377560549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23043979525734339673494797 8641492322150377377560549)
  ·
    refine ⟨1620279810403195758292603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8641492322150377377560549 1620279810403195758292603)
    ·
      refine ⟨2430419715604793637438905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620279810403195758292603 2430419715604793637438905)
      ·
        refine ⟨1822814786703595228079179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2430419715604793637438905 1822814786703595228079179)
        ·
          refine ⟨2734222180055392842118769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822814786703595228079179 2734222180055392842118769)
          ·
            refine ⟨2050666635041544631589077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2734222180055392842118769 2050666635041544631589077)
            ·
              refine ⟨48062499258786202302869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2050666635041544631589077 48062499258786202302869)
              ·
                rfl

theorem cell20_947714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_947714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947714 prefixEnd_947714 := by exact prefixLift 947714
  have htrace : WordTrace (prefixWord ++ tailWord_947714) baseStart_947714 baseEnd_947714 := by
    simpa [prefixWord, tailWord_947714, baseEnd_947714] using wordTrace_append hprefix tailTrace_947714
  have hstable : (prefixWord ++ tailWord_947714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947714).length < 2 ^ (prefixWord ++ tailWord_947714).sum := by decide
  have hdescent : baseEnd_947714 < baseStart_947714 := by decide
  rcases family_descends (prefixWord ++ tailWord_947714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947752 : List Nat := [2, 1, 5, 2, 2, 1, 1, 6]
def baseStart_947752 : Nat := 118140960795 + 947752 * 2 ^ 59
def prefixEnd_947752 : Nat := 4983230072969 + 3 ^ 40 * 947752 * 2
def baseEnd_947752 : Nat := 144193279188172192486333

theorem tailTrace_947752 : CollatzResearch.WordTrace tailWord_947752 prefixEnd_947752 144193279188172192486333 := by
  unfold tailWord_947752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17283677631231921000062755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23044903508309228000083673 17283677631231921000062755)
  ·
    refine ⟨25925516446847881500094133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17283677631231921000062755 25925516446847881500094133)
    ·
      refine ⟨2430517166891988890633825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25925516446847881500094133 2430517166891988890633825)
      ·
        refine ⟨1822887875168991667975369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2430517166891988890633825 1822887875168991667975369)
        ·
          refine ⟨1367165906376743750981527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822887875168991667975369 1367165906376743750981527)
          ·
            refine ⟨2050748859565115626472291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367165906376743750981527 2050748859565115626472291)
            ·
              refine ⟨3076123289347673439708437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050748859565115626472291 3076123289347673439708437)
              ·
                refine ⟨144193279188172192486333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3076123289347673439708437 144193279188172192486333)
                ·
                  rfl

theorem cell20_947752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_947752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947752 prefixEnd_947752 := by exact prefixLift 947752
  have htrace : WordTrace (prefixWord ++ tailWord_947752) baseStart_947752 baseEnd_947752 := by
    simpa [prefixWord, tailWord_947752, baseEnd_947752] using wordTrace_append hprefix tailTrace_947752
  have hstable : (prefixWord ++ tailWord_947752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947752).length < 2 ^ (prefixWord ++ tailWord_947752).sum := by decide
  have hdescent : baseEnd_947752 < baseStart_947752 := by decide
  rcases family_descends (prefixWord ++ tailWord_947752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947783 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 4]
def baseStart_947783 : Nat := 118140960795 + 947783 * 2 ^ 59
def prefixEnd_947783 : Nat := 4983230072969 + 3 ^ 40 * 947783 * 2
def baseEnd_947783 : Nat := 432593986809218247425539

theorem tailTrace_947783 : CollatzResearch.WordTrace tailWord_947783 prefixEnd_947783 432593986809218247425539 := by
  unfold tailWord_947783
  simp only [CollatzResearch.WordTrace]
  refine ⟨34568485925351534294504003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23045657283567689529669335 34568485925351534294504003)
  ·
    refine ⟨51852728888027301441756005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34568485925351534294504003 51852728888027301441756005)
    ·
      refine ⟨9722386666505119020329251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51852728888027301441756005 9722386666505119020329251)
      ·
        refine ⟨14583579999757678530493877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722386666505119020329251 14583579999757678530493877)
        ·
          refine ⟨1367210624977282362233801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14583579999757678530493877 1367210624977282362233801)
          ·
            refine ⟨1025407968732961771675351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367210624977282362233801 1025407968732961771675351)
            ·
              refine ⟨1538111953099442657513027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025407968732961771675351 1538111953099442657513027)
              ·
                refine ⟨2307167929649163986269541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538111953099442657513027 2307167929649163986269541)
                ·
                  refine ⟨432593986809218247425539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2307167929649163986269541 432593986809218247425539)
                  ·
                    rfl

theorem cell20_947783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_947783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947783 prefixEnd_947783 := by exact prefixLift 947783
  have htrace : WordTrace (prefixWord ++ tailWord_947783) baseStart_947783 baseEnd_947783 := by
    simpa [prefixWord, tailWord_947783, baseEnd_947783] using wordTrace_append hprefix tailTrace_947783
  have hstable : (prefixWord ++ tailWord_947783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947783).length < 2 ^ (prefixWord ++ tailWord_947783).sum := by decide
  have hdescent : baseEnd_947783 < baseStart_947783 := by decide
  rcases family_descends (prefixWord ++ tailWord_947783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947839 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_947839 : Nat := 118140960795 + 947839 * 2 ^ 59
def prefixEnd_947839 : Nat := 4983230072969 + 3 ^ 40 * 947839 * 2
def baseEnd_947839 : Nat := 432619546735130941558643

theorem tailTrace_947839 : CollatzResearch.WordTrace tailWord_947839 prefixEnd_947839 432619546735130941558643 := by
  unfold tailWord_947839
  simp only [CollatzResearch.WordTrace]
  refine ⟨34570528413148655858542571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23047018942099103905695047 34570528413148655858542571)
  ·
    refine ⟨51855792619722983787813857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34570528413148655858542571 51855792619722983787813857)
    ·
      refine ⟨38891844464792237840860393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51855792619722983787813857 38891844464792237840860393)
      ·
        refine ⟨29168883348594178380645295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38891844464792237840860393 29168883348594178380645295)
        ·
          refine ⟨43753325022891267570967943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29168883348594178380645295 43753325022891267570967943)
          ·
            refine ⟨65629987534336901356451915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43753325022891267570967943 65629987534336901356451915)
            ·
              refine ⟨98444981301505352034677873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65629987534336901356451915 98444981301505352034677873)
              ·
                refine ⟨73833735976129014026008405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98444981301505352034677873 73833735976129014026008405)
                ·
                  refine ⟨432619546735130941558643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73833735976129014026008405 432619546735130941558643)
                  ·
                    rfl

theorem cell20_947839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_947839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947839 prefixEnd_947839 := by exact prefixLift 947839
  have htrace : WordTrace (prefixWord ++ tailWord_947839) baseStart_947839 baseEnd_947839 := by
    simpa [prefixWord, tailWord_947839, baseEnd_947839] using wordTrace_append hprefix tailTrace_947839
  have hstable : (prefixWord ++ tailWord_947839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947839).length < 2 ^ (prefixWord ++ tailWord_947839).sum := by decide
  have hdescent : baseEnd_947839 < baseStart_947839 := by decide
  rcases family_descends (prefixWord ++ tailWord_947839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947863 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_947863 : Nat := 118140960795 + 947863 * 2 ^ 59
def prefixEnd_947863 : Nat := 4983230072969 + 3 ^ 40 * 947863 * 2
def baseEnd_947863 : Nat := 432630500989093524758545

theorem tailTrace_947863 : CollatzResearch.WordTrace tailWord_947863 prefixEnd_947863 432630500989093524758545 := by
  unfold tailWord_947863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34571403765061707957416243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23047602510041138638277495 34571403765061707957416243)
  ·
    refine ⟨51857105647592561936124365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34571403765061707957416243 51857105647592561936124365)
    ·
      refine ⟨19446414617847210726046637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51857105647592561936124365 19446414617847210726046637)
      ·
        refine ⟨7292405481692704022267489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19446414617847210726046637 7292405481692704022267489)
        ·
          refine ⟨5469304111269528016700617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7292405481692704022267489 5469304111269528016700617)
          ·
            refine ⟨4101978083452146012525463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5469304111269528016700617 4101978083452146012525463)
            ·
              refine ⟨6152967125178219018788195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101978083452146012525463 6152967125178219018788195)
              ·
                refine ⟨9229450687767328528182293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152967125178219018788195 9229450687767328528182293)
                ·
                  refine ⟨432630500989093524758545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9229450687767328528182293 432630500989093524758545)
                  ·
                    rfl

theorem cell20_947863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_947863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947863 prefixEnd_947863 := by exact prefixLift 947863
  have htrace : WordTrace (prefixWord ++ tailWord_947863) baseStart_947863 baseEnd_947863 := by
    simpa [prefixWord, tailWord_947863, baseEnd_947863] using wordTrace_append hprefix tailTrace_947863
  have hstable : (prefixWord ++ tailWord_947863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947863).length < 2 ^ (prefixWord ++ tailWord_947863).sum := by decide
  have hdescent : baseEnd_947863 < baseStart_947863 := by decide
  rcases family_descends (prefixWord ++ tailWord_947863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947886 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_947886 : Nat := 118140960795 + 947886 * 2 ^ 59
def prefixEnd_947886 : Nat := 4983230072969 + 3 ^ 40 * 947886 * 2
def baseEnd_947886 : Nat := 432640998815807666991785

theorem tailTrace_947886 : CollatzResearch.WordTrace tailWord_947886 prefixEnd_947886 432640998815807666991785 := by
  unfold tailWord_947886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321530330497297860687939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23048161762652255257002341 4321530330497297860687939)
  ·
    refine ⟨6482295495745946791031909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321530330497297860687939 6482295495745946791031909)
    ·
      refine ⟨1215430405452365023318483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6482295495745946791031909 1215430405452365023318483)
      ·
        refine ⟨1823145608178547534977725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215430405452365023318483 1823145608178547534977725)
        ·
          refine ⟨683679603066955325616647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1823145608178547534977725 683679603066955325616647)
          ·
            refine ⟨1025519404600432988424971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683679603066955325616647 1025519404600432988424971)
            ·
              refine ⟨1538279106900649482637457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025519404600432988424971 1538279106900649482637457)
              ·
                refine ⟨1153709330175487111978093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538279106900649482637457 1153709330175487111978093)
                ·
                  refine ⟨432640998815807666991785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153709330175487111978093 432640998815807666991785)
                  ·
                    rfl

theorem cell20_947886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_947886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947886 prefixEnd_947886 := by exact prefixLift 947886
  have htrace : WordTrace (prefixWord ++ tailWord_947886) baseStart_947886 baseEnd_947886 := by
    simpa [prefixWord, tailWord_947886, baseEnd_947886] using wordTrace_append hprefix tailTrace_947886
  have hstable : (prefixWord ++ tailWord_947886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947886).length < 2 ^ (prefixWord ++ tailWord_947886).sum := by decide
  have hdescent : baseEnd_947886 < baseStart_947886 := by decide
  rcases family_descends (prefixWord ++ tailWord_947886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947911 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 3]
def baseStart_947911 : Nat := 118140960795 + 947911 * 2 ^ 59
def prefixEnd_947911 : Nat := 4983230072969 + 3 ^ 40 * 947911 * 2
def baseEnd_947911 : Nat := 432652409497018691158349

theorem tailTrace_947911 : CollatzResearch.WordTrace tailWord_947911 prefixEnd_947911 432652409497018691158349 := by
  unfold tailWord_947911
  simp only [CollatzResearch.WordTrace]
  refine ⟨34573154468887812155163587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23048769645925208103442391 34573154468887812155163587)
  ·
    refine ⟨51859731703331718232745381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34573154468887812155163587 51859731703331718232745381)
    ·
      refine ⟨9723699694374697168639759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51859731703331718232745381 9723699694374697168639759)
      ·
        refine ⟨14585549541562045752959639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9723699694374697168639759 14585549541562045752959639)
        ·
          refine ⟨21878324312343068629439459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585549541562045752959639 21878324312343068629439459)
          ·
            refine ⟨32817486468514602944159189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21878324312343068629439459 32817486468514602944159189)
            ·
              refine ⟨769159839105811006503731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32817486468514602944159189 769159839105811006503731)
              ·
                refine ⟨1153739758658716509755597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769159839105811006503731 1153739758658716509755597)
                ·
                  refine ⟨432652409497018691158349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153739758658716509755597 432652409497018691158349)
                  ·
                    rfl

theorem cell20_947911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_947911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947911 prefixEnd_947911 := by exact prefixLift 947911
  have htrace : WordTrace (prefixWord ++ tailWord_947911) baseStart_947911 baseEnd_947911 := by
    simpa [prefixWord, tailWord_947911, baseEnd_947911] using wordTrace_append hprefix tailTrace_947911
  have hstable : (prefixWord ++ tailWord_947911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947911).length < 2 ^ (prefixWord ++ tailWord_947911).sum := by decide
  have hdescent : baseEnd_947911 < baseStart_947911 := by decide
  rcases family_descends (prefixWord ++ tailWord_947911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947946 : List Nat := [3, 1, 3, 1, 1, 1, 10]
def baseStart_947946 : Nat := 118140960795 + 947946 * 2 ^ 59
def prefixEnd_947946 : Nat := 4983230072969 + 3 ^ 40 * 947946 * 2
def baseEnd_947946 : Nat := 48074264938968236110171

theorem tailTrace_947946 : CollatzResearch.WordTrace tailWord_947946 prefixEnd_947946 48074264938968236110171 := by
  unfold tailWord_947946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643607755940253283171923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23049620682507342088458461 8643607755940253283171923)
  ·
    refine ⟨12965411633910379924757885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8643607755940253283171923 12965411633910379924757885)
    ·
      refine ⟨4862029362716392471784207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12965411633910379924757885 4862029362716392471784207)
      ·
        refine ⟨7293044044074588707676311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862029362716392471784207 7293044044074588707676311)
        ·
          refine ⟨10939566066111883061514467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293044044074588707676311 10939566066111883061514467)
          ·
            refine ⟨16409349099167824592271701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10939566066111883061514467 16409349099167824592271701)
            ·
              refine ⟨48074264938968236110171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16409349099167824592271701 48074264938968236110171)
              ·
                rfl

theorem cell20_947946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_947946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947946 prefixEnd_947946 := by exact prefixLift 947946
  have htrace : WordTrace (prefixWord ++ tailWord_947946) baseStart_947946 baseEnd_947946 := by
    simpa [prefixWord, tailWord_947946, baseEnd_947946] using wordTrace_append hprefix tailTrace_947946
  have hstable : (prefixWord ++ tailWord_947946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947946).length < 2 ^ (prefixWord ++ tailWord_947946).sum := by decide
  have hdescent : baseEnd_947946 < baseStart_947946 := by decide
  rcases family_descends (prefixWord ++ tailWord_947946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947966 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_947966 : Nat := 118140960795 + 947966 * 2 ^ 59
def prefixEnd_947966 : Nat := 4983230072969 + 3 ^ 40 * 947966 * 2
def baseEnd_947966 : Nat := 432677512995682944324791

theorem tailTrace_947966 : CollatzResearch.WordTrace tailWord_947966 prefixEnd_947966 432677512995682944324791 := by
  unfold tailWord_947966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321895060461069568551969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23050106989125704365610501 4321895060461069568551969)
  ·
    refine ⟨3241421295345802176413977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4321895060461069568551969 3241421295345802176413977)
    ·
      refine ⟨2431065971509351632310483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3241421295345802176413977 2431065971509351632310483)
      ·
        refine ⟨3646598957264027448465725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431065971509351632310483 3646598957264027448465725)
        ·
          refine ⟨1367474608974010293174647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3646598957264027448465725 1367474608974010293174647)
          ·
            refine ⟨2051211913461015439761971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367474608974010293174647 2051211913461015439761971)
            ·
              refine ⟨3076817870191523159642957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051211913461015439761971 3076817870191523159642957)
              ·
                refine ⟨1153806701321821184866109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3076817870191523159642957 1153806701321821184866109)
                ·
                  refine ⟨432677512995682944324791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153806701321821184866109 432677512995682944324791)
                  ·
                    rfl

theorem cell20_947966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_947966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_947966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_947966 prefixEnd_947966 := by exact prefixLift 947966
  have htrace : WordTrace (prefixWord ++ tailWord_947966) baseStart_947966 baseEnd_947966 := by
    simpa [prefixWord, tailWord_947966, baseEnd_947966] using wordTrace_append hprefix tailTrace_947966
  have hstable : (prefixWord ++ tailWord_947966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947966).length < 2 ^ (prefixWord ++ tailWord_947966).sum := by decide
  have hdescent : baseEnd_947966 < baseStart_947966 := by decide
  rcases family_descends (prefixWord ++ tailWord_947966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948049 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 2]
def baseStart_948049 : Nat := 118140960795 + 948049 * 2 ^ 59
def prefixEnd_948049 : Nat := 4983230072969 + 3 ^ 40 * 948049 * 2
def baseEnd_948049 : Nat := 432715396457303544557785

theorem tailTrace_948049 : CollatzResearch.WordTrace tailWord_948049 prefixEnd_948049 432715396457303544557785 := by
  unfold tailWord_948049
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578187742387861723687201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23052125161591907815791467 34578187742387861723687201)
  ·
    refine ⟨25933640806790896292765401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34578187742387861723687201 25933640806790896292765401)
    ·
      refine ⟨19450230605093172219574051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25933640806790896292765401 19450230605093172219574051)
      ·
        refine ⟨29175345907639758329361077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19450230605093172219574051 29175345907639758329361077)
        ·
          refine ⟨2735188678841227343377601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29175345907639758329361077 2735188678841227343377601)
          ·
            refine ⟨2051391509130920507533201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735188678841227343377601 2051391509130920507533201)
            ·
              refine ⟨1538543631848190380649901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051391509130920507533201 1538543631848190380649901)
              ·
                refine ⟨576953861943071392743713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1538543631848190380649901 576953861943071392743713)
                ·
                  refine ⟨432715396457303544557785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576953861943071392743713 432715396457303544557785)
                  ·
                    rfl

theorem cell20_948049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_948049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948049 prefixEnd_948049 := by exact prefixLift 948049
  have htrace : WordTrace (prefixWord ++ tailWord_948049) baseStart_948049 baseEnd_948049 := by
    simpa [prefixWord, tailWord_948049, baseEnd_948049] using wordTrace_append hprefix tailTrace_948049
  have hstable : (prefixWord ++ tailWord_948049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948049).length < 2 ^ (prefixWord ++ tailWord_948049).sum := by decide
  have hdescent : baseEnd_948049 < baseStart_948049 := by decide
  rcases family_descends (prefixWord ++ tailWord_948049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948063 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 3]
def baseStart_948063 : Nat := 118140960795 + 948063 * 2 ^ 59
def prefixEnd_948063 : Nat := 4983230072969 + 3 ^ 40 * 948063 * 2
def baseEnd_948063 : Nat := 432721786438781718091061

theorem tailTrace_948063 : CollatzResearch.WordTrace tailWord_948063 prefixEnd_948063 432721786438781718091061 := by
  unfold tailWord_948063
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578698364337142114696843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23052465576224761409797895 34578698364337142114696843)
  ·
    refine ⟨51868047546505713172045265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34578698364337142114696843 51868047546505713172045265)
    ·
      refine ⟨38901035659879284879033949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51868047546505713172045265 38901035659879284879033949)
      ·
        refine ⟨14587888372454731829637731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38901035659879284879033949 14587888372454731829637731)
        ·
          refine ⟨21881832558682097744456597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14587888372454731829637731 21881832558682097744456597)
          ·
            refine ⟨1025710901188223331771403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21881832558682097744456597 1025710901188223331771403)
            ·
              refine ⟨1538566351782334997657105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025710901188223331771403 1538566351782334997657105)
              ·
                refine ⟨1153924763836751248242829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538566351782334997657105 1153924763836751248242829)
                ·
                  refine ⟨432721786438781718091061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153924763836751248242829 432721786438781718091061)
                  ·
                    rfl

theorem cell20_948063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_948063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948063 prefixEnd_948063 := by exact prefixLift 948063
  have htrace : WordTrace (prefixWord ++ tailWord_948063) baseStart_948063 baseEnd_948063 := by
    simpa [prefixWord, tailWord_948063, baseEnd_948063] using wordTrace_append hprefix tailTrace_948063
  have hstable : (prefixWord ++ tailWord_948063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948063).length < 2 ^ (prefixWord ++ tailWord_948063).sum := by decide
  have hdescent : baseEnd_948063 < baseStart_948063 := by decide
  rcases family_descends (prefixWord ++ tailWord_948063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948094 : List Nat := [4, 2, 3, 1, 1, 2, 1, 6]
def baseStart_948094 : Nat := 118140960795 + 948094 * 2 ^ 59
def prefixEnd_948094 : Nat := 4983230072969 + 3 ^ 40 * 948094 * 2
def baseEnd_948094 : Nat := 144245311894494462685867

theorem tailTrace_948094 : CollatzResearch.WordTrace tailWord_948094 prefixEnd_948094 144245311894494462685867 := by
  unfold tailWord_948094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322478628403104301134417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23053219351483222939383557 4322478628403104301134417)
  ·
    refine ⟨3241858971302328225850813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4322478628403104301134417 3241858971302328225850813)
    ·
      refine ⟨1215697114238373084694055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3241858971302328225850813 1215697114238373084694055)
      ·
        refine ⟨1823545671357559627041083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215697114238373084694055 1823545671357559627041083)
        ·
          refine ⟨2735318507036339440561625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823545671357559627041083 2735318507036339440561625)
          ·
            refine ⟨2051488880277254580421219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735318507036339440561625 2051488880277254580421219)
            ·
              refine ⟨3077233320415881870631829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051488880277254580421219 3077233320415881870631829)
              ·
                refine ⟨144245311894494462685867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3077233320415881870631829 144245311894494462685867)
                ·
                  rfl

theorem cell20_948094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_948094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948094 prefixEnd_948094 := by exact prefixLift 948094
  have htrace : WordTrace (prefixWord ++ tailWord_948094) baseStart_948094 baseEnd_948094 := by
    simpa [prefixWord, tailWord_948094, baseEnd_948094] using wordTrace_append hprefix tailTrace_948094
  have hstable : (prefixWord ++ tailWord_948094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948094).length < 2 ^ (prefixWord ++ tailWord_948094).sum := by decide
  have hdescent : baseEnd_948094 < baseStart_948094 := by decide
  rcases family_descends (prefixWord ++ tailWord_948094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948104 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 2]
def baseStart_948104 : Nat := 118140960795 + 948104 * 2 ^ 59
def prefixEnd_948104 : Nat := 4983230072969 + 3 ^ 40 * 948104 * 2
def baseEnd_948104 : Nat := 432740499955967797724227

theorem tailTrace_948104 : CollatzResearch.WordTrace tailWord_948104 prefixEnd_948104 432740499955967797724227 := by
  unfold tailWord_948104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290096878594303058469683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23053462504792404077959577 17290096878594303058469683)
  ·
    refine ⟨25935145317891454587704525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17290096878594303058469683 25935145317891454587704525)
    ·
      refine ⟨9725679494209295470389197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25935145317891454587704525 9725679494209295470389197)
      ·
        refine ⟨3647129810328485801395949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9725679494209295470389197 3647129810328485801395949)
        ·
          refine ⟨1367673678873182175523481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3647129810328485801395949 1367673678873182175523481)
          ·
            refine ⟨1025755259154886631642611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367673678873182175523481 1025755259154886631642611)
            ·
              refine ⟨1538632888732329947463917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025755259154886631642611 1538632888732329947463917)
              ·
                refine ⟨576987333274623730298969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1538632888732329947463917 576987333274623730298969)
                ·
                  refine ⟨432740499955967797724227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576987333274623730298969 432740499955967797724227)
                  ·
                    rfl

theorem cell20_948104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_948104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948104 prefixEnd_948104 := by exact prefixLift 948104
  have htrace : WordTrace (prefixWord ++ tailWord_948104) baseStart_948104 baseEnd_948104 := by
    simpa [prefixWord, tailWord_948104, baseEnd_948104] using wordTrace_append hprefix tailTrace_948104
  have hstable : (prefixWord ++ tailWord_948104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948104).length < 2 ^ (prefixWord ++ tailWord_948104).sum := by decide
  have hdescent : baseEnd_948104 < baseStart_948104 := by decide
  rcases family_descends (prefixWord ++ tailWord_948104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948105 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_948105 : Nat := 118140960795 + 948105 * 2 ^ 59
def prefixEnd_948105 : Nat := 4983230072969 + 3 ^ 40 * 948105 * 2
def baseEnd_948105 : Nat := 432740956383216238690889

theorem tailTrace_948105 : CollatzResearch.WordTrace tailWord_948105 prefixEnd_948105 432740956383216238690889 := by
  unfold tailWord_948105
  simp only [CollatzResearch.WordTrace]
  refine ⟨34580230230184983287725769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23053486820123322191817179 34580230230184983287725769)
  ·
    refine ⟨25935172672638737465794327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34580230230184983287725769 25935172672638737465794327)
    ·
      refine ⟨38902759008958106198691491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25935172672638737465794327 38902759008958106198691491)
      ·
        refine ⟨58354138513437159298037237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38902759008958106198691491 58354138513437159298037237)
        ·
          refine ⟨5470700485634733684190991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58354138513437159298037237 5470700485634733684190991)
          ·
            refine ⟨8206050728452100526286487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470700485634733684190991 8206050728452100526286487)
            ·
              refine ⟨12309076092678150789429731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206050728452100526286487 12309076092678150789429731)
              ·
                refine ⟨18463614139017226184144597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12309076092678150789429731 18463614139017226184144597)
                ·
                  refine ⟨432740956383216238690889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18463614139017226184144597 432740956383216238690889)
                  ·
                    rfl

theorem cell20_948105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_948105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948105 prefixEnd_948105 := by exact prefixLift 948105
  have htrace : WordTrace (prefixWord ++ tailWord_948105) baseStart_948105 baseEnd_948105 := by
    simpa [prefixWord, tailWord_948105, baseEnd_948105] using wordTrace_append hprefix tailTrace_948105
  have hstable : (prefixWord ++ tailWord_948105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948105).length < 2 ^ (prefixWord ++ tailWord_948105).sum := by decide
  have hdescent : baseEnd_948105 < baseStart_948105 := by decide
  rcases family_descends (prefixWord ++ tailWord_948105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948112 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_948112 : Nat := 118140960795 + 948112 * 2 ^ 59
def prefixEnd_948112 : Nat := 4983230072969 + 3 ^ 40 * 948112 * 2
def baseEnd_948112 : Nat := 432744151373955325457527

theorem tailTrace_948112 : CollatzResearch.WordTrace tailWord_948112 prefixEnd_948112 432744151373955325457527 := by
  unfold tailWord_948112
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290242770579811741615295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23053657027439748988820393 17290242770579811741615295)
  ·
    refine ⟨25935364155869717612422943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17290242770579811741615295 25935364155869717612422943)
    ·
      refine ⟨38903046233804576418634415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25935364155869717612422943 38903046233804576418634415)
      ·
        refine ⟨58354569350706864627951623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38903046233804576418634415 58354569350706864627951623)
        ·
          refine ⟨87531854026060296941927435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58354569350706864627951623 87531854026060296941927435)
          ·
            refine ⟨131297781039090445412891153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87531854026060296941927435 131297781039090445412891153)
            ·
              refine ⟨98473335779317834059668365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131297781039090445412891153 98473335779317834059668365)
              ·
                refine ⟨36927500917244187772375637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98473335779317834059668365 36927500917244187772375637)
                ·
                  refine ⟨432744151373955325457527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36927500917244187772375637 432744151373955325457527)
                  ·
                    rfl

theorem cell20_948112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_948112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948112 prefixEnd_948112 := by exact prefixLift 948112
  have htrace : WordTrace (prefixWord ++ tailWord_948112) baseStart_948112 baseEnd_948112 := by
    simpa [prefixWord, tailWord_948112, baseEnd_948112] using wordTrace_append hprefix tailTrace_948112
  have hstable : (prefixWord ++ tailWord_948112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948112).length < 2 ^ (prefixWord ++ tailWord_948112).sum := by decide
  have hdescent : baseEnd_948112 < baseStart_948112 := by decide
  rcases family_descends (prefixWord ++ tailWord_948112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948122 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_948122 : Nat := 118140960795 + 948122 * 2 ^ 59
def prefixEnd_948122 : Nat := 4983230072969 + 3 ^ 40 * 948122 * 2
def baseEnd_948122 : Nat := 432748715646439735124153

theorem tailTrace_948122 : CollatzResearch.WordTrace tailWord_948122 prefixEnd_948122 432748715646439735124153 := by
  unfold tailWord_948122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645212567780848797773655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23053900180748930127396413 8645212567780848797773655)
  ·
    refine ⟨12967818851671273196660483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8645212567780848797773655 12967818851671273196660483)
    ·
      refine ⟨19451728277506909794990725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12967818851671273196660483 19451728277506909794990725)
      ·
        refine ⟨3647199052032545586560761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19451728277506909794990725 3647199052032545586560761)
        ·
          refine ⟨2735399289024409189920571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3647199052032545586560761 2735399289024409189920571)
          ·
            refine ⟨4103098933536613784880857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735399289024409189920571 4103098933536613784880857)
            ·
              refine ⟨3077324200152460338660643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4103098933536613784880857 3077324200152460338660643)
              ·
                refine ⟨4615986300228690507990965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077324200152460338660643 4615986300228690507990965)
                ·
                  refine ⟨432748715646439735124153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4615986300228690507990965 432748715646439735124153)
                  ·
                    rfl

theorem cell20_948122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_948122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948122 prefixEnd_948122 := by exact prefixLift 948122
  have htrace : WordTrace (prefixWord ++ tailWord_948122) baseStart_948122 baseEnd_948122 := by
    simpa [prefixWord, tailWord_948122, baseEnd_948122] using wordTrace_append hprefix tailTrace_948122
  have hstable : (prefixWord ++ tailWord_948122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948122).length < 2 ^ (prefixWord ++ tailWord_948122).sum := by decide
  have hdescent : baseEnd_948122 < baseStart_948122 := by decide
  rcases family_descends (prefixWord ++ tailWord_948122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948184 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 2]
def baseStart_948184 : Nat := 118140960795 + 948184 * 2 ^ 59
def prefixEnd_948184 : Nat := 4983230072969 + 3 ^ 40 * 948184 * 2
def baseEnd_948184 : Nat := 432777014135843075057233

theorem tailTrace_948184 : CollatzResearch.WordTrace tailWord_948184 prefixEnd_948184 432777014135843075057233 := by
  unfold tailWord_948184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291555798449389889925803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23055407731265853186567737 17291555798449389889925803)
  ·
    refine ⟨25937333697674084834888705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17291555798449389889925803 25937333697674084834888705)
    ·
      refine ⟨19453000273255563626166529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25937333697674084834888705 19453000273255563626166529)
      ·
        refine ⟨14589750204941672719624897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19453000273255563626166529 14589750204941672719624897)
        ·
          refine ⟨10942312653706254539718673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14589750204941672719624897 10942312653706254539718673)
          ·
            refine ⟨8206734490279690904789005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10942312653706254539718673 8206734490279690904789005)
            ·
              refine ⟨3077525433854884089295877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8206734490279690904789005 3077525433854884089295877)
              ·
                refine ⟨577036018847790766742977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3077525433854884089295877 577036018847790766742977)
                ·
                  refine ⟨432777014135843075057233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577036018847790766742977 432777014135843075057233)
                  ·
                    rfl

theorem cell20_948184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_948184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948184 prefixEnd_948184 := by exact prefixLift 948184
  have htrace : WordTrace (prefixWord ++ tailWord_948184) baseStart_948184 baseEnd_948184 := by
    simpa [prefixWord, tailWord_948184, baseEnd_948184] using wordTrace_append hprefix tailTrace_948184
  have hstable : (prefixWord ++ tailWord_948184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948184).length < 2 ^ (prefixWord ++ tailWord_948184).sum := by decide
  have hdescent : baseEnd_948184 < baseStart_948184 := by decide
  rcases family_descends (prefixWord ++ tailWord_948184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948191 : List Nat := [1, 1, 2, 3, 4, 3, 1, 5]
def baseStart_948191 : Nat := 118140960795 + 948191 * 2 ^ 59
def prefixEnd_948191 : Nat := 4983230072969 + 3 ^ 40 * 948191 * 2
def baseEnd_948191 : Nat := 144260069708860720607957

theorem tailTrace_948191 : CollatzResearch.WordTrace tailWord_948191 prefixEnd_948191 144260069708860720607957 := by
  unfold tailWord_948191
  simp only [CollatzResearch.WordTrace]
  refine ⟨34583366907873419975356427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23055577938582279983570951 34583366907873419975356427)
  ·
    refine ⟨51875050361810129963034641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34583366907873419975356427 51875050361810129963034641)
    ·
      refine ⟨38906287771357597472275981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51875050361810129963034641 38906287771357597472275981)
      ·
        refine ⟨14589857914259099052103493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38906287771357597472275981 14589857914259099052103493)
        ·
          refine ⟨2735598358923581072269405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14589857914259099052103493 2735598358923581072269405)
          ·
            refine ⟨1025849384596342902101027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2735598358923581072269405 1025849384596342902101027)
            ·
              refine ⟨1538774076894514353151541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025849384596342902101027 1538774076894514353151541)
              ·
                refine ⟨144260069708860720607957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1538774076894514353151541 144260069708860720607957)
                ·
                  rfl

theorem cell20_948191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_948191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948191 prefixEnd_948191 := by exact prefixLift 948191
  have htrace : WordTrace (prefixWord ++ tailWord_948191) baseStart_948191 baseEnd_948191 := by
    simpa [prefixWord, tailWord_948191, baseEnd_948191] using wordTrace_append hprefix tailTrace_948191
  have hstable : (prefixWord ++ tailWord_948191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948191).length < 2 ^ (prefixWord ++ tailWord_948191).sum := by decide
  have hdescent : baseEnd_948191 < baseStart_948191 := by decide
  rcases family_descends (prefixWord ++ tailWord_948191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948263 : List Nat := [1, 1, 7, 1, 2, 2, 2, 4]
def baseStart_948263 : Nat := 118140960795 + 948263 * 2 ^ 59
def prefixEnd_948263 : Nat := 4983230072969 + 3 ^ 40 * 948263 * 2
def baseEnd_948263 : Nat := 144271023962823303807859

theorem tailTrace_948263 : CollatzResearch.WordTrace tailWord_948263 prefixEnd_948263 144271023962823303807859 := by
  unfold tailWord_948263
  simp only [CollatzResearch.WordTrace]
  refine ⟨34585992963612576271977443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23057328642408384181318295 34585992963612576271977443)
  ·
    refine ⟨51878989445418864407966165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34585992963612576271977443 51878989445418864407966165)
    ·
      refine ⟨1215913815127004634561707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51878989445418864407966165 1215913815127004634561707)
      ·
        refine ⟨1823870722690506951842561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215913815127004634561707 1823870722690506951842561)
        ·
          refine ⟨1367903042017880213881921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1823870722690506951842561 1367903042017880213881921)
          ·
            refine ⟨1025927281513410160411441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367903042017880213881921 1025927281513410160411441)
            ·
              refine ⟨769445461135057620308581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025927281513410160411441 769445461135057620308581)
              ·
                refine ⟨144271023962823303807859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769445461135057620308581 144271023962823303807859)
                ·
                  rfl

theorem cell20_948263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_948263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948263 prefixEnd_948263 := by exact prefixLift 948263
  have htrace : WordTrace (prefixWord ++ tailWord_948263) baseStart_948263 baseEnd_948263 := by
    simpa [prefixWord, tailWord_948263, baseEnd_948263] using wordTrace_append hprefix tailTrace_948263
  have hstable : (prefixWord ++ tailWord_948263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948263).length < 2 ^ (prefixWord ++ tailWord_948263).sum := by decide
  have hdescent : baseEnd_948263 < baseStart_948263 := by decide
  rcases family_descends (prefixWord ++ tailWord_948263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948288 : List Nat := [2, 1, 1, 2, 2, 6, 6]
def baseStart_948288 : Nat := 118140960795 + 948288 * 2 ^ 59
def prefixEnd_948288 : Nat := 4983230072969 + 3 ^ 40 * 948288 * 2
def baseEnd_948288 : Nat := 48091609174408992843349

theorem tailTrace_948288 : CollatzResearch.WordTrace tailWord_948288 prefixEnd_948288 48091609174408992843349 := by
  unfold tailWord_948288
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293452394261002770818759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23057936525681337027758345 17293452394261002770818759)
  ·
    refine ⟨25940178591391504156228139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17293452394261002770818759 25940178591391504156228139)
    ·
      refine ⟨38910267887087256234342209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25940178591391504156228139 38910267887087256234342209)
      ·
        refine ⟨29182700915315442175756657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38910267887087256234342209 29182700915315442175756657)
        ·
          refine ⟨21887025686486581631817493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29182700915315442175756657 21887025686486581631817493)
          ·
            refine ⟨1025954329054058513991445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21887025686486581631817493 1025954329054058513991445)
            ·
              refine ⟨48091609174408992843349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1025954329054058513991445 48091609174408992843349)
              ·
                rfl

theorem cell20_948288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 6].length) (baseStart_948288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948288 prefixEnd_948288 := by exact prefixLift 948288
  have htrace : WordTrace (prefixWord ++ tailWord_948288) baseStart_948288 baseEnd_948288 := by
    simpa [prefixWord, tailWord_948288, baseEnd_948288] using wordTrace_append hprefix tailTrace_948288
  have hstable : (prefixWord ++ tailWord_948288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948288).length < 2 ^ (prefixWord ++ tailWord_948288).sum := by decide
  have hdescent : baseEnd_948288 < baseStart_948288 := by decide
  rcases family_descends (prefixWord ++ tailWord_948288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948295 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_948295 : Nat := 118140960795 + 948295 * 2 ^ 59
def prefixEnd_948295 : Nat := 4983230072969 + 3 ^ 40 * 948295 * 2
def baseEnd_948295 : Nat := 432827677560420022356779

theorem tailTrace_948295 : CollatzResearch.WordTrace tailWord_948295 prefixEnd_948295 432827677560420022356779 := by
  unfold tailWord_948295
  simp only [CollatzResearch.WordTrace]
  refine ⟨34587160099496645737142339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23058106732997763824761559 34587160099496645737142339)
  ·
    refine ⟨51880740149244968605713509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34587160099496645737142339 51880740149244968605713509)
    ·
      refine ⟨9727638777983431613571283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51880740149244968605713509 9727638777983431613571283)
      ·
        refine ⟨14591458166975147420356925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727638777983431613571283 14591458166975147420356925)
        ·
          refine ⟨5471796812615680282633847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14591458166975147420356925 5471796812615680282633847)
          ·
            refine ⟨8207695218923520423950771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471796812615680282633847 8207695218923520423950771)
            ·
              refine ⟨12311542828385280635926157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207695218923520423950771 12311542828385280635926157)
              ·
                refine ⟨4616828560644480238472309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12311542828385280635926157 4616828560644480238472309)
                ·
                  refine ⟨432827677560420022356779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616828560644480238472309 432827677560420022356779)
                  ·
                    rfl

theorem cell20_948295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_948295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948295 prefixEnd_948295 := by exact prefixLift 948295
  have htrace : WordTrace (prefixWord ++ tailWord_948295) baseStart_948295 baseEnd_948295 := by
    simpa [prefixWord, tailWord_948295, baseEnd_948295] using wordTrace_append hprefix tailTrace_948295
  have hstable : (prefixWord ++ tailWord_948295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948295).length < 2 ^ (prefixWord ++ tailWord_948295).sum := by decide
  have hdescent : baseEnd_948295 < baseStart_948295 := by decide
  rcases family_descends (prefixWord ++ tailWord_948295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948312 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_948312 : Nat := 118140960795 + 948312 * 2 ^ 59
def prefixEnd_948312 : Nat := 4983230072969 + 3 ^ 40 * 948312 * 2
def baseEnd_948312 : Nat := 432835436823643518790043

theorem tailTrace_948312 : CollatzResearch.WordTrace tailWord_948312 prefixEnd_948312 432835436823643518790043 := by
  unfold tailWord_948312
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293890070217528820255595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23058520093623371760340793 17293890070217528820255595)
  ·
    refine ⟨25940835105326293230383393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17293890070217528820255595 25940835105326293230383393)
    ·
      refine ⟨19455626328994719922787545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25940835105326293230383393 19455626328994719922787545)
      ·
        refine ⟨14591719746746039942090659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19455626328994719922787545 14591719746746039942090659)
        ·
          refine ⟨21887579620119059913135989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14591719746746039942090659 21887579620119059913135989)
          ·
            refine ⟨2051960589386161866856499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21887579620119059913135989 2051960589386161866856499)
            ·
              refine ⟨3077940884079242800284749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051960589386161866856499 3077940884079242800284749)
              ·
                refine ⟨1154227831529716050106781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3077940884079242800284749 1154227831529716050106781)
                ·
                  refine ⟨432835436823643518790043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154227831529716050106781 432835436823643518790043)
                  ·
                    rfl

theorem cell20_948312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_948312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948312 prefixEnd_948312 := by exact prefixLift 948312
  have htrace : WordTrace (prefixWord ++ tailWord_948312) baseStart_948312 baseEnd_948312 := by
    simpa [prefixWord, tailWord_948312, baseEnd_948312] using wordTrace_append hprefix tailTrace_948312
  have hstable : (prefixWord ++ tailWord_948312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948312).length < 2 ^ (prefixWord ++ tailWord_948312).sum := by decide
  have hdescent : baseEnd_948312 < baseStart_948312 := by decide
  rcases family_descends (prefixWord ++ tailWord_948312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948353 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 2]
def baseStart_948353 : Nat := 118140960795 + 948353 * 2 ^ 59
def prefixEnd_948353 : Nat := 4983230072969 + 3 ^ 40 * 948353 * 2
def baseEnd_948353 : Nat := 432854150340829598423209

theorem tailTrace_948353 : CollatzResearch.WordTrace tailWord_948353 prefixEnd_948353 432854150340829598423209 := by
  unfold tailWord_948353
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589275533286521642753713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23059517022191014428502475 34589275533286521642753713)
  ·
    refine ⟨25941956649964891232065285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34589275533286521642753713 25941956649964891232065285)
    ·
      refine ⟨4864116871868417106012241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25941956649964891232065285 4864116871868417106012241)
      ·
        refine ⟨3648087653901312829509181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4864116871868417106012241 3648087653901312829509181)
        ·
          refine ⟨1368032870212992311065943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3648087653901312829509181 1368032870212992311065943)
          ·
            refine ⟨2052049305319488466598915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368032870212992311065943 2052049305319488466598915)
            ·
              refine ⟨3078073957979232699898373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052049305319488466598915 3078073957979232699898373)
              ·
                refine ⟨577138867121106131230945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3078073957979232699898373 577138867121106131230945)
                ·
                  refine ⟨432854150340829598423209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577138867121106131230945 432854150340829598423209)
                  ·
                    rfl

theorem cell20_948353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_948353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948353 prefixEnd_948353 := by exact prefixLift 948353
  have htrace : WordTrace (prefixWord ++ tailWord_948353) baseStart_948353 baseEnd_948353 := by
    simpa [prefixWord, tailWord_948353, baseEnd_948353] using wordTrace_append hprefix tailTrace_948353
  have hstable : (prefixWord ++ tailWord_948353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948353).length < 2 ^ (prefixWord ++ tailWord_948353).sum := by decide
  have hdescent : baseEnd_948353 < baseStart_948353 := by decide
  rcases family_descends (prefixWord ++ tailWord_948353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948381 : List Nat := [1, 4, 2, 1, 1, 4, 3, 4]
def baseStart_948381 : Nat := 118140960795 + 948381 * 2 ^ 59
def prefixEnd_948381 : Nat := 4983230072969 + 3 ^ 40 * 948381 * 2
def baseEnd_948381 : Nat := 144288976767928648496587

theorem tailTrace_948381 : CollatzResearch.WordTrace tailWord_948381 prefixEnd_948381 144288976767928648496587 := by
  unfold tailWord_948381
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590296777185082424772997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23060197851456721616515331 34590296777185082424772997)
  ·
    refine ⟨6485680645722202954644937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34590296777185082424772997 6485680645722202954644937)
    ·
      refine ⟨4864260484291652215983703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6485680645722202954644937 4864260484291652215983703)
      ·
        refine ⟨7296390726437478323975555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864260484291652215983703 7296390726437478323975555)
        ·
          refine ⟨10944586089656217485963333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296390726437478323975555 10944586089656217485963333)
          ·
            refine ⟨2052109891810540778618125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10944586089656217485963333 2052109891810540778618125)
            ·
              refine ⟨769541209428952791981797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2052109891810540778618125 769541209428952791981797)
              ·
                refine ⟨144288976767928648496587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769541209428952791981797 144288976767928648496587)
                ·
                  rfl

theorem cell20_948381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_948381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948381 prefixEnd_948381 := by exact prefixLift 948381
  have htrace : WordTrace (prefixWord ++ tailWord_948381) baseStart_948381 baseEnd_948381 := by
    simpa [prefixWord, tailWord_948381, baseEnd_948381] using wordTrace_append hprefix tailTrace_948381
  have hstable : (prefixWord ++ tailWord_948381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948381).length < 2 ^ (prefixWord ++ tailWord_948381).sum := by decide
  have hdescent : baseEnd_948381 < baseStart_948381 := by decide
  rcases family_descends (prefixWord ++ tailWord_948381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948398 : List Nat := [4, 1, 4, 2, 1, 1, 7]
def baseStart_948398 : Nat := 118140960795 + 948398 * 2 ^ 59
def prefixEnd_948398 : Nat := 4983230072969 + 3 ^ 40 * 948398 * 2
def baseEnd_948398 : Nat := 48097187729667715769225

theorem tailTrace_948398 : CollatzResearch.WordTrace tailWord_948398 prefixEnd_948398 48097187729667715769225 := by
  unfold tailWord_948398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323864602265436791017731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23060611212082329552094565 4323864602265436791017731)
  ·
    refine ⟨6485796903398155186526597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4323864602265436791017731 6485796903398155186526597)
    ·
      refine ⟨1216086919387154097473737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6485796903398155186526597 1216086919387154097473737)
      ·
        refine ⟨912065189540365573105303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216086919387154097473737 912065189540365573105303)
        ·
          refine ⟨1368097784310548359657955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912065189540365573105303 1368097784310548359657955)
          ·
            refine ⟨2052146676465822539486933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368097784310548359657955 2052146676465822539486933)
            ·
              refine ⟨48097187729667715769225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2052146676465822539486933 48097187729667715769225)
              ·
                rfl

theorem cell20_948398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 7].length) (baseStart_948398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948398 prefixEnd_948398 := by exact prefixLift 948398
  have htrace : WordTrace (prefixWord ++ tailWord_948398) baseStart_948398 baseEnd_948398 := by
    simpa [prefixWord, tailWord_948398, baseEnd_948398] using wordTrace_append hprefix tailTrace_948398
  have hstable : (prefixWord ++ tailWord_948398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948398).length < 2 ^ (prefixWord ++ tailWord_948398).sum := by decide
  have hdescent : baseEnd_948398 < baseStart_948398 := by decide
  rcases family_descends (prefixWord ++ tailWord_948398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948405 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 5]
def baseStart_948405 : Nat := 118140960795 + 948405 * 2 ^ 59
def prefixEnd_948405 : Nat := 4983230072969 + 3 ^ 40 * 948405 * 2
def baseEnd_948405 : Nat := 432877884557748528689663

theorem tailTrace_948405 : CollatzResearch.WordTrace tailWord_948405 prefixEnd_948405 432877884557748528689663 := by
  unfold tailWord_948405
  simp only [CollatzResearch.WordTrace]
  refine ⟨34591172129098134523646669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23060781419398756349097779 34591172129098134523646669)
  ·
    refine ⟨12971689548411800446367501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34591172129098134523646669 12971689548411800446367501)
    ·
      refine ⟨4864383580654425167387813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12971689548411800446367501 4864383580654425167387813)
      ·
        refine ⟨912071921372704718885215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4864383580654425167387813 912071921372704718885215)
        ·
          refine ⟨1368107882059057078327823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912071921372704718885215 1368107882059057078327823)
          ·
            refine ⟨2052161823088585617491735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368107882059057078327823 2052161823088585617491735)
            ·
              refine ⟨3078242734632878426237603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052161823088585617491735 3078242734632878426237603)
              ·
                refine ⟨4617364101949317639356405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078242734632878426237603 4617364101949317639356405)
                ·
                  refine ⟨432877884557748528689663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4617364101949317639356405 432877884557748528689663)
                  ·
                    rfl

theorem cell20_948405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_948405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948405 prefixEnd_948405 := by exact prefixLift 948405
  have htrace : WordTrace (prefixWord ++ tailWord_948405) baseStart_948405 baseEnd_948405 := by
    simpa [prefixWord, tailWord_948405, baseEnd_948405] using wordTrace_append hprefix tailTrace_948405
  have hstable : (prefixWord ++ tailWord_948405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948405).length < 2 ^ (prefixWord ++ tailWord_948405).sum := by decide
  have hdescent : baseEnd_948405 < baseStart_948405 := by decide
  rcases family_descends (prefixWord ++ tailWord_948405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948409 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_948409 : Nat := 118140960795 + 948409 * 2 ^ 59
def prefixEnd_948409 : Nat := 4983230072969 + 3 ^ 40 * 948409 * 2
def baseEnd_948409 : Nat := 432879710266742292556313

theorem tailTrace_948409 : CollatzResearch.WordTrace tailWord_948409 prefixEnd_948409 432879710266742292556313 := by
  unfold tailWord_948409
  simp only [CollatzResearch.WordTrace]
  refine ⟨34591318021083643206792281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23060878680722428804528187 34591318021083643206792281)
  ·
    refine ⟨25943488515812732405094211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34591318021083643206792281 25943488515812732405094211)
    ·
      refine ⟨38915232773719098607641317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25943488515812732405094211 38915232773719098607641317)
      ·
        refine ⟨7296606145072330988932747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38915232773719098607641317 7296606145072330988932747)
        ·
          refine ⟨10944909217608496483399121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296606145072330988932747 10944909217608496483399121)
          ·
            refine ⟨8208681913206372362549341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10944909217608496483399121 8208681913206372362549341)
            ·
              refine ⟨3078255717452389635956003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8208681913206372362549341 3078255717452389635956003)
              ·
                refine ⟨4617383576178584453934005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078255717452389635956003 4617383576178584453934005)
                ·
                  refine ⟨432879710266742292556313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4617383576178584453934005 432879710266742292556313)
                  ·
                    rfl

theorem cell20_948409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_948409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948409 prefixEnd_948409 := by exact prefixLift 948409
  have htrace : WordTrace (prefixWord ++ tailWord_948409) baseStart_948409 baseEnd_948409 := by
    simpa [prefixWord, tailWord_948409, baseEnd_948409] using wordTrace_append hprefix tailTrace_948409
  have hstable : (prefixWord ++ tailWord_948409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948409).length < 2 ^ (prefixWord ++ tailWord_948409).sum := by decide
  have hdescent : baseEnd_948409 < baseStart_948409 := by decide
  rcases family_descends (prefixWord ++ tailWord_948409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948412 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_948412 : Nat := 118140960795 + 948412 * 2 ^ 59
def prefixEnd_948412 : Nat := 4983230072969 + 3 ^ 40 * 948412 * 2
def baseEnd_948412 : Nat := 432881079548487615456301

theorem tailTrace_948412 : CollatzResearch.WordTrace tailWord_948412 prefixEnd_948412 432881079548487615456301 := by
  unfold tailWord_948412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295713720036387359575745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23060951626715183146100993 17295713720036387359575745)
  ·
    refine ⟨12971785290027290519681809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17295713720036387359575745 12971785290027290519681809)
    ·
      refine ⟨9728838967520467889761357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12971785290027290519681809 9728838967520467889761357)
      ·
        refine ⟨3648314612820175458660509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9728838967520467889761357 3648314612820175458660509)
        ·
          refine ⟨1368117979807565796997691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3648314612820175458660509 1368117979807565796997691)
          ·
            refine ⟨2052176969711348695496537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368117979807565796997691 2052176969711348695496537)
            ·
              refine ⟨1539132727283511521622403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052176969711348695496537 1539132727283511521622403)
              ·
                refine ⟨2308699090925267282433605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539132727283511521622403 2308699090925267282433605)
                ·
                  refine ⟨432881079548487615456301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308699090925267282433605 432881079548487615456301)
                  ·
                    rfl

theorem cell20_948412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_948412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948412 prefixEnd_948412 := by exact prefixLift 948412
  have htrace : WordTrace (prefixWord ++ tailWord_948412) baseStart_948412 baseEnd_948412 := by
    simpa [prefixWord, tailWord_948412, baseEnd_948412] using wordTrace_append hprefix tailTrace_948412
  have hstable : (prefixWord ++ tailWord_948412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948412).length < 2 ^ (prefixWord ++ tailWord_948412).sum := by decide
  have hdescent : baseEnd_948412 < baseStart_948412 := by decide
  rcases family_descends (prefixWord ++ tailWord_948412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948440 : List Nat := [2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_948440 : Nat := 118140960795 + 948440 * 2 ^ 59
def prefixEnd_948440 : Nat := 4983230072969 + 3 ^ 40 * 948440 * 2
def baseEnd_948440 : Nat := 144297953170481320840951

theorem tailTrace_948440 : CollatzResearch.WordTrace tailWord_948440 prefixEnd_948440 144297953170481320840951 := by
  unfold tailWord_948440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296224341985667750585387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23061632455980890334113849 17296224341985667750585387)
  ·
    refine ⟨25944336512978501625878081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17296224341985667750585387 25944336512978501625878081)
    ·
      refine ⟨19458252384733876219408561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25944336512978501625878081 19458252384733876219408561)
      ·
        refine ⟨14593689288550407164556421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19458252384733876219408561 14593689288550407164556421)
        ·
          refine ⟨2736316741603201343354329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14593689288550407164556421 2736316741603201343354329)
          ·
            refine ⟨2052237556202401007515747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736316741603201343354329 2052237556202401007515747)
            ·
              refine ⟨3078356334303601511273621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052237556202401007515747 3078356334303601511273621)
              ·
                refine ⟨144297953170481320840951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3078356334303601511273621 144297953170481320840951)
                ·
                  rfl

theorem cell20_948440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_948440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948440 prefixEnd_948440 := by exact prefixLift 948440
  have htrace : WordTrace (prefixWord ++ tailWord_948440) baseStart_948440 baseEnd_948440 := by
    simpa [prefixWord, tailWord_948440, baseEnd_948440] using wordTrace_append hprefix tailTrace_948440
  have hstable : (prefixWord ++ tailWord_948440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948440).length < 2 ^ (prefixWord ++ tailWord_948440).sum := by decide
  have hdescent : baseEnd_948440 < baseStart_948440 := by decide
  rcases family_descends (prefixWord ++ tailWord_948440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948492 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_948492 : Nat := 118140960795 + 948492 * 2 ^ 59
def prefixEnd_948492 : Nat := 4983230072969 + 3 ^ 40 * 948492 * 2
def baseEnd_948492 : Nat := 432917593728362892789307

theorem tailTrace_948492 : CollatzResearch.WordTrace tailWord_948492 prefixEnd_948492 432917593728362892789307 := by
  unfold tailWord_948492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297172639891474191031865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23062896853188632254709153 17297172639891474191031865)
  ·
    refine ⟨12972879479918605643273899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17297172639891474191031865 12972879479918605643273899)
    ·
      refine ⟨19459319219877908464910849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12972879479918605643273899 19459319219877908464910849)
      ·
        refine ⟨14594489414908431348683137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19459319219877908464910849 14594489414908431348683137)
        ·
          refine ⟨10945867061181323511512353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14594489414908431348683137 10945867061181323511512353)
          ·
            refine ⟨8209400295885992633634265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10945867061181323511512353 8209400295885992633634265)
            ·
              refine ⟨6157050221914494475225699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8209400295885992633634265 6157050221914494475225699)
              ·
                refine ⟨9235575332871741712838549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157050221914494475225699 9235575332871741712838549)
                ·
                  refine ⟨432917593728362892789307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9235575332871741712838549 432917593728362892789307)
                  ·
                    rfl

theorem cell20_948492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_948492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948492 prefixEnd_948492 := by exact prefixLift 948492
  have htrace : WordTrace (prefixWord ++ tailWord_948492) baseStart_948492 baseEnd_948492 := by
    simpa [prefixWord, tailWord_948492, baseEnd_948492] using wordTrace_append hprefix tailTrace_948492
  have hstable : (prefixWord ++ tailWord_948492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948492).length < 2 ^ (prefixWord ++ tailWord_948492).sum := by decide
  have hdescent : baseEnd_948492 < baseStart_948492 := by decide
  rcases family_descends (prefixWord ++ tailWord_948492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948564 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 2]
def baseStart_948564 : Nat := 118140960795 + 948564 * 2 ^ 59
def prefixEnd_948564 : Nat := 4983230072969 + 3 ^ 40 * 948564 * 2
def baseEnd_948564 : Nat := 432950456490250642389013

theorem tailTrace_948564 : CollatzResearch.WordTrace tailWord_948564 prefixEnd_948564 432950456490250642389013 := by
  unfold tailWord_948564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298485667761052339342373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23064647557014736452456497 17298485667761052339342373)
  ·
    refine ⟨3243466062705197313626695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17298485667761052339342373 3243466062705197313626695)
    ·
      refine ⟨4865199094057795970440043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243466062705197313626695 4865199094057795970440043)
      ·
        refine ⟨7297798641086693955660065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865199094057795970440043 7297798641086693955660065)
        ·
          refine ⟨5473348980815020466745049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7297798641086693955660065 5473348980815020466745049)
          ·
            refine ⟨4105011735611265350058787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473348980815020466745049 4105011735611265350058787)
            ·
              refine ⟨6157517603416898025088181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105011735611265350058787 6157517603416898025088181)
              ·
                refine ⟨577267275320334189852017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6157517603416898025088181 577267275320334189852017)
                ·
                  refine ⟨432950456490250642389013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577267275320334189852017 432950456490250642389013)
                  ·
                    rfl

theorem cell20_948564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_948564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948564 prefixEnd_948564 := by exact prefixLift 948564
  have htrace : WordTrace (prefixWord ++ tailWord_948564) baseStart_948564 baseEnd_948564 := by
    simpa [prefixWord, tailWord_948564, baseEnd_948564] using wordTrace_append hprefix tailTrace_948564
  have hstable : (prefixWord ++ tailWord_948564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948564).length < 2 ^ (prefixWord ++ tailWord_948564).sum := by decide
  have hdescent : baseEnd_948564 < baseStart_948564 := by decide
  rcases family_descends (prefixWord ++ tailWord_948564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948578 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_948578 : Nat := 118140960795 + 948578 * 2 ^ 59
def prefixEnd_948578 : Nat := 4983230072969 + 3 ^ 40 * 948578 * 2
def baseEnd_948578 : Nat := 432956846471728815922289

theorem tailTrace_948578 : CollatzResearch.WordTrace tailWord_948578 prefixEnd_948578 432956846471728815922289 := by
  unfold tailWord_948578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649370489367846267423597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23064987971647590046462925 8649370489367846267423597)
  ·
    refine ⟨3243513933512942350283849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8649370489367846267423597 3243513933512942350283849)
    ·
      refine ⟨2432635450134706762712887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243513933512942350283849 2432635450134706762712887)
      ·
        refine ⟨3648953175202060144069331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432635450134706762712887 3648953175202060144069331)
        ·
          refine ⟨5473429762803090216103997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648953175202060144069331 5473429762803090216103997)
          ·
            refine ⟨2052536161051158831038999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5473429762803090216103997 2052536161051158831038999)
            ·
              refine ⟨3078804241576738246558499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052536161051158831038999 3078804241576738246558499)
              ·
                refine ⟨4618206362365107369837749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078804241576738246558499 4618206362365107369837749)
                ·
                  refine ⟨432956846471728815922289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4618206362365107369837749 432956846471728815922289)
                  ·
                    rfl

theorem cell20_948578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_948578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948578 prefixEnd_948578 := by exact prefixLift 948578
  have htrace : WordTrace (prefixWord ++ tailWord_948578) baseStart_948578 baseEnd_948578 := by
    simpa [prefixWord, tailWord_948578, baseEnd_948578] using wordTrace_append hprefix tailTrace_948578
  have hstable : (prefixWord ++ tailWord_948578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948578).length < 2 ^ (prefixWord ++ tailWord_948578).sum := by decide
  have hdescent : baseEnd_948578 < baseStart_948578 := by decide
  rcases family_descends (prefixWord ++ tailWord_948578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948585 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 2]
def baseStart_948585 : Nat := 118140960795 + 948585 * 2 ^ 59
def prefixEnd_948585 : Nat := 4983230072969 + 3 ^ 40 * 948585 * 2
def baseEnd_948585 : Nat := 432960041462467902688927

theorem tailTrace_948585 : CollatzResearch.WordTrace tailWord_948585 prefixEnd_948585 432960041462467902688927 := by
  unfold tailWord_948585
  simp only [CollatzResearch.WordTrace]
  refine ⟨34597737268446025265199209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23065158178964016843466139 34597737268446025265199209)
  ·
    refine ⟨25948302951334518948899407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34597737268446025265199209 25948302951334518948899407)
    ·
      refine ⟨38922454427001778423349111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25948302951334518948899407 38922454427001778423349111)
      ·
        refine ⟨58383681640502667635023667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38922454427001778423349111 58383681640502667635023667)
        ·
          refine ⟨87575522460754001452535501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58383681640502667635023667 87575522460754001452535501)
          ·
            refine ⟨32840820922782750544700813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87575522460754001452535501 32840820922782750544700813)
            ·
              refine ⟨12315307846043531454262805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32840820922782750544700813 12315307846043531454262805)
              ·
                refine ⟨577280055283290536918569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12315307846043531454262805 577280055283290536918569)
                ·
                  refine ⟨432960041462467902688927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577280055283290536918569 432960041462467902688927)
                  ·
                    rfl

theorem cell20_948585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_948585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948585 prefixEnd_948585 := by exact prefixLift 948585
  have htrace : WordTrace (prefixWord ++ tailWord_948585) baseStart_948585 baseEnd_948585 := by
    simpa [prefixWord, tailWord_948585, baseEnd_948585] using wordTrace_append hprefix tailTrace_948585
  have hstable : (prefixWord ++ tailWord_948585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948585).length < 2 ^ (prefixWord ++ tailWord_948585).sum := by decide
  have hdescent : baseEnd_948585 < baseStart_948585 := by decide
  rcases family_descends (prefixWord ++ tailWord_948585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948609 : List Nat := [1, 2, 4, 3, 1, 1, 4, 4]
def baseStart_948609 : Nat := 118140960795 + 948609 * 2 ^ 59
def prefixEnd_948609 : Nat := 4983230072969 + 3 ^ 40 * 948609 * 2
def baseEnd_948609 : Nat := 144323665238810161962943

theorem tailTrace_948609 : CollatzResearch.WordTrace tailWord_948609 prefixEnd_948609 144323665238810161962943 := by
  unfold tailWord_948609
  simp only [CollatzResearch.WordTrace]
  refine ⟨34598612620359077364072881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23065741746906051576048587 34598612620359077364072881)
  ·
    refine ⟨25948959465269308023054661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34598612620359077364072881 25948959465269308023054661)
    ·
      refine ⟨4865429899737995254322749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25948959465269308023054661 4865429899737995254322749)
      ·
        refine ⟨1824536212401748220371031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4865429899737995254322749 1824536212401748220371031)
        ·
          refine ⟨2736804318602622330556547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824536212401748220371031 2736804318602622330556547)
          ·
            refine ⟨4105206477903933495834821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736804318602622330556547 4105206477903933495834821)
            ·
              refine ⟨769726214606987530469029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4105206477903933495834821 769726214606987530469029)
              ·
                refine ⟨144323665238810161962943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769726214606987530469029 144323665238810161962943)
                ·
                  rfl

theorem cell20_948609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_948609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948609 prefixEnd_948609 := by exact prefixLift 948609
  have htrace : WordTrace (prefixWord ++ tailWord_948609) baseStart_948609 baseEnd_948609 := by
    simpa [prefixWord, tailWord_948609, baseEnd_948609] using wordTrace_append hprefix tailTrace_948609
  have hstable : (prefixWord ++ tailWord_948609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948609).length < 2 ^ (prefixWord ++ tailWord_948609).sum := by decide
  have hdescent : baseEnd_948609 < baseStart_948609 := by decide
  rcases family_descends (prefixWord ++ tailWord_948609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948668 : List Nat := [2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_948668 : Nat := 118140960795 + 948668 * 2 ^ 59
def prefixEnd_948668 : Nat := 4983230072969 + 3 ^ 40 * 948668 * 2
def baseEnd_948668 : Nat := 144332641641362834307307

theorem tailTrace_948668 : CollatzResearch.WordTrace tailWord_948668 prefixEnd_948668 144332641641362834307307 := by
  unfold tailWord_948668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300382263572665220235329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23067176351430220293647105 17300382263572665220235329)
  ·
    refine ⟨12975286697679498915176497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17300382263572665220235329 12975286697679498915176497)
    ·
      refine ⟨9731465023259624186382373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12975286697679498915176497 9731465023259624186382373)
      ·
        refine ⟨1824649691861179534946695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9731465023259624186382373 1824649691861179534946695)
        ·
          refine ⟨2736974537791769302420043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824649691861179534946695 2736974537791769302420043)
          ·
            refine ⟨4105461806687653953630065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736974537791769302420043 4105461806687653953630065)
            ·
              refine ⟨3079096355015740465222549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105461806687653953630065 3079096355015740465222549)
              ·
                refine ⟨144332641641362834307307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3079096355015740465222549 144332641641362834307307)
                ·
                  rfl

theorem cell20_948668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_948668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948668 prefixEnd_948668 := by exact prefixLift 948668
  have htrace : WordTrace (prefixWord ++ tailWord_948668) baseStart_948668 baseEnd_948668 := by
    simpa [prefixWord, tailWord_948668, baseEnd_948668] using wordTrace_append hprefix tailTrace_948668
  have hstable : (prefixWord ++ tailWord_948668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948668).length < 2 ^ (prefixWord ++ tailWord_948668).sum := by decide
  have hdescent : baseEnd_948668 < baseStart_948668 := by decide
  rcases family_descends (prefixWord ++ tailWord_948668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948692 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_948692 : Nat := 118140960795 + 948692 * 2 ^ 59
def prefixEnd_948692 : Nat := 4983230072969 + 3 ^ 40 * 948692 * 2
def baseEnd_948692 : Nat := 433008879178051086121823

theorem tailTrace_948692 : CollatzResearch.WordTrace tailWord_948692 prefixEnd_948692 433008879178051086121823 := by
  unfold tailWord_948692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300819939529191269672165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23067759919372255026229553 17300819939529191269672165)
  ·
    refine ⟨3243903738661723363063531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17300819939529191269672165 3243903738661723363063531)
    ·
      refine ⟨4865855607992585044595297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243903738661723363063531 4865855607992585044595297)
      ·
        refine ⟨3649391705994438783446473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4865855607992585044595297 3649391705994438783446473)
        ·
          refine ⟨2737043779495829087584855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3649391705994438783446473 2737043779495829087584855)
          ·
            refine ⟨4105565669243743631377283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737043779495829087584855 4105565669243743631377283)
            ·
              refine ⟨6158348503865615447065925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105565669243743631377283 6158348503865615447065925)
              ·
                refine ⟨1154690344474802896324861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6158348503865615447065925 1154690344474802896324861)
                ·
                  refine ⟨433008879178051086121823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154690344474802896324861 433008879178051086121823)
                  ·
                    rfl

theorem cell20_948692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_948692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948692 prefixEnd_948692 := by exact prefixLift 948692
  have htrace : WordTrace (prefixWord ++ tailWord_948692) baseStart_948692 baseEnd_948692 := by
    simpa [prefixWord, tailWord_948692, baseEnd_948692] using wordTrace_append hprefix tailTrace_948692
  have hstable : (prefixWord ++ tailWord_948692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948692).length < 2 ^ (prefixWord ++ tailWord_948692).sum := by decide
  have hdescent : baseEnd_948692 < baseStart_948692 := by decide
  rcases family_descends (prefixWord ++ tailWord_948692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948720 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_948720 : Nat := 118140960795 + 948720 * 2 ^ 59
def prefixEnd_948720 : Nat := 4983230072969 + 3 ^ 40 * 948720 * 2
def baseEnd_948720 : Nat := 433021659141007433188375

theorem tailTrace_948720 : CollatzResearch.WordTrace tailWord_948720 prefixEnd_948720 433021659141007433188375 := by
  unfold tailWord_948720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301330561478471660681807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23068440748637962214242409 17301330561478471660681807)
  ·
    refine ⟨25951995842217707491022711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17301330561478471660681807 25951995842217707491022711)
    ·
      refine ⟨38927993763326561236534067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25951995842217707491022711 38927993763326561236534067)
      ·
        refine ⟨58391990644989841854801101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38927993763326561236534067 58391990644989841854801101)
        ·
          refine ⟨21896996491871190695550413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58391990644989841854801101 21896996491871190695550413)
          ·
            refine ⟨8211373684451696510831405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21896996491871190695550413 8211373684451696510831405)
            ·
              refine ⟨3079265131669386191561777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8211373684451696510831405 3079265131669386191561777)
              ·
                refine ⟨2309448848752039643671333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079265131669386191561777 2309448848752039643671333)
                ·
                  refine ⟨433021659141007433188375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2309448848752039643671333 433021659141007433188375)
                  ·
                    rfl

theorem cell20_948720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_948720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948720 prefixEnd_948720 := by exact prefixLift 948720
  have htrace : WordTrace (prefixWord ++ tailWord_948720) baseStart_948720 baseEnd_948720 := by
    simpa [prefixWord, tailWord_948720, baseEnd_948720] using wordTrace_append hprefix tailTrace_948720
  have hstable : (prefixWord ++ tailWord_948720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948720).length < 2 ^ (prefixWord ++ tailWord_948720).sum := by decide
  have hdescent : baseEnd_948720 < baseStart_948720 := by decide
  rcases family_descends (prefixWord ++ tailWord_948720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948820 : List Nat := [2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_948820 : Nat := 118140960795 + 948820 * 2 ^ 59
def prefixEnd_948820 : Nat := 4983230072969 + 3 ^ 40 * 948820 * 2
def baseEnd_948820 : Nat := 144355767288617176618211

theorem tailTrace_948820 : CollatzResearch.WordTrace tailWord_948820 prefixEnd_948820 144355767288617176618211 := by
  unfold tailWord_948820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17303154211297330200001957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23070872281729773600002609 17303154211297330200001957)
  ·
    refine ⟨3244341414618249412500367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17303154211297330200001957 3244341414618249412500367)
    ·
      refine ⟨4866512121927374118750551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244341414618249412500367 4866512121927374118750551)
      ·
        refine ⟨7299768182891061178125827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866512121927374118750551 7299768182891061178125827)
        ·
          refine ⟨10949652274336591767188741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299768182891061178125827 10949652274336591767188741)
          ·
            refine ⟨2053059801438110956347889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10949652274336591767188741 2053059801438110956347889)
            ·
              refine ⟨1539794851078583217260917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053059801438110956347889 1539794851078583217260917)
              ·
                refine ⟨144355767288617176618211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1539794851078583217260917 144355767288617176618211)
                ·
                  rfl

theorem cell20_948820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_948820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948820 prefixEnd_948820 := by exact prefixLift 948820
  have htrace : WordTrace (prefixWord ++ tailWord_948820) baseStart_948820 baseEnd_948820 := by
    simpa [prefixWord, tailWord_948820, baseEnd_948820] using wordTrace_append hprefix tailTrace_948820
  have hstable : (prefixWord ++ tailWord_948820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948820).length < 2 ^ (prefixWord ++ tailWord_948820).sum := by decide
  have hdescent : baseEnd_948820 < baseStart_948820 := by decide
  rcases family_descends (prefixWord ++ tailWord_948820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948868 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 2]
def baseStart_948868 : Nat := 118140960795 + 948868 * 2 ^ 59
def prefixEnd_948868 : Nat := 4983230072969 + 3 ^ 40 * 948868 * 2
def baseEnd_948868 : Nat := 433089210373776696254437

theorem tailTrace_948868 : CollatzResearch.WordTrace tailWord_948868 prefixEnd_948868 433089210373776696254437 := by
  unfold tailWord_948868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17304029563210382298875629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23072039417613843065167505 17304029563210382298875629)
  ·
    refine ⟨6489011086203893362078361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17304029563210382298875629 6489011086203893362078361)
    ·
      refine ⟨4866758314652920021558771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6489011086203893362078361 4866758314652920021558771)
      ·
        refine ⟨7300137471979380032338157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866758314652920021558771 7300137471979380032338157)
        ·
          refine ⟨2737551551992267512126809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7300137471979380032338157 2737551551992267512126809)
          ·
            refine ⟨2053163663994200634095107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2737551551992267512126809 2053163663994200634095107)
            ·
              refine ⟨3079745495991300951142661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053163663994200634095107 3079745495991300951142661)
              ·
                refine ⟨577452280498368928339249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3079745495991300951142661 577452280498368928339249)
                ·
                  refine ⟨433089210373776696254437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577452280498368928339249 433089210373776696254437)
                  ·
                    rfl

theorem cell20_948868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_948868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948868 prefixEnd_948868 := by exact prefixLift 948868
  have htrace : WordTrace (prefixWord ++ tailWord_948868) baseStart_948868 baseEnd_948868 := by
    simpa [prefixWord, tailWord_948868, baseEnd_948868] using wordTrace_append hprefix tailTrace_948868
  have hstable : (prefixWord ++ tailWord_948868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948868).length < 2 ^ (prefixWord ++ tailWord_948868).sum := by decide
  have hdescent : baseEnd_948868 < baseStart_948868 := by decide
  rcases family_descends (prefixWord ++ tailWord_948868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948882 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_948882 : Nat := 118140960795 + 948882 * 2 ^ 59
def prefixEnd_948882 : Nat := 4983230072969 + 3 ^ 40 * 948882 * 2
def baseEnd_948882 : Nat := 433095600355254869787713

theorem tailTrace_948882 : CollatzResearch.WordTrace tailWord_948882 prefixEnd_948882 433095600355254869787713 := by
  unfold tailWord_948882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652142437092511247190225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23072379832246696659173933 8652142437092511247190225)
  ·
    refine ⟨6489106827819383435392669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8652142437092511247190225 6489106827819383435392669)
    ·
      refine ⟨2433415060432268788272251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6489106827819383435392669 2433415060432268788272251)
      ·
        refine ⟨3650122590648403182408377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433415060432268788272251 3650122590648403182408377)
        ·
          refine ⟨2737591942986302386806283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650122590648403182408377 2737591942986302386806283)
          ·
            refine ⟨4106387914479453580209425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737591942986302386806283 4106387914479453580209425)
            ·
              refine ⟨3079790935859590185157069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106387914479453580209425 3079790935859590185157069)
              ·
                refine ⟨1154921600947346319433901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3079790935859590185157069 1154921600947346319433901)
                ·
                  refine ⟨433095600355254869787713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154921600947346319433901 433095600355254869787713)
                  ·
                    rfl

theorem cell20_948882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_948882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948882 prefixEnd_948882 := by exact prefixLift 948882
  have htrace : WordTrace (prefixWord ++ tailWord_948882) baseStart_948882 baseEnd_948882 := by
    simpa [prefixWord, tailWord_948882, baseEnd_948882] using wordTrace_append hprefix tailTrace_948882
  have hstable : (prefixWord ++ tailWord_948882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948882).length < 2 ^ (prefixWord ++ tailWord_948882).sum := by decide
  have hdescent : baseEnd_948882 < baseStart_948882 := by decide
  rcases family_descends (prefixWord ++ tailWord_948882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948927 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 2]
def baseStart_948927 : Nat := 118140960795 + 948927 * 2 ^ 59
def prefixEnd_948927 : Nat := 4983230072969 + 3 ^ 40 * 948927 * 2
def baseEnd_948927 : Nat := 433116139581434713287529

theorem tailTrace_948927 : CollatzResearch.WordTrace tailWord_948927 prefixEnd_948927 433116139581434713287529 := by
  unfold tailWord_948927
  simp only [CollatzResearch.WordTrace]
  refine ⟨34610211033207017674149035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23073474022138011782766023 34610211033207017674149035)
  ·
    refine ⟨51915316549810526511223553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34610211033207017674149035 51915316549810526511223553)
    ·
      refine ⟨38936487412357894883417665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51915316549810526511223553 38936487412357894883417665)
      ·
        refine ⟨29202365559268421162563249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38936487412357894883417665 29202365559268421162563249)
        ·
          refine ⟨21901774169451315871922437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29202365559268421162563249 21901774169451315871922437)
          ·
            refine ⟨4106582656772121725985457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21901774169451315871922437 4106582656772121725985457)
            ·
              refine ⟨3079936992579091294489093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106582656772121725985457 3079936992579091294489093)
              ·
                refine ⟨577488186108579617716705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3079936992579091294489093 577488186108579617716705)
                ·
                  refine ⟨433116139581434713287529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577488186108579617716705 433116139581434713287529)
                  ·
                    rfl

theorem cell20_948927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 2].length) (baseStart_948927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948927 prefixEnd_948927 := by exact prefixLift 948927
  have htrace : WordTrace (prefixWord ++ tailWord_948927) baseStart_948927 baseEnd_948927 := by
    simpa [prefixWord, tailWord_948927, baseEnd_948927] using wordTrace_append hprefix tailTrace_948927
  have hstable : (prefixWord ++ tailWord_948927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948927).length < 2 ^ (prefixWord ++ tailWord_948927).sum := by decide
  have hdescent : baseEnd_948927 < baseStart_948927 := by decide
  rcases family_descends (prefixWord ++ tailWord_948927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948969 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_948969 : Nat := 118140960795 + 948969 * 2 ^ 59
def prefixEnd_948969 : Nat := 4983230072969 + 3 ^ 40 * 948969 * 2
def baseEnd_948969 : Nat := 433135309525869233887357

theorem tailTrace_948969 : CollatzResearch.WordTrace tailWord_948969 prefixEnd_948969 433135309525869233887357 := by
  unfold tailWord_948969
  simp only [CollatzResearch.WordTrace]
  refine ⟨34611742899054858847177961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23074495266036572564785307 34611742899054858847177961)
  ·
    refine ⟨25958807174291144135383471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34611742899054858847177961 25958807174291144135383471)
    ·
      refine ⟨38938210761436716203075207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25958807174291144135383471 38938210761436716203075207)
      ·
        refine ⟨58407316142155074304612811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38938210761436716203075207 58407316142155074304612811)
        ·
          refine ⟨87610974213232611456919217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58407316142155074304612811 87610974213232611456919217)
          ·
            refine ⟨65708230659924458592689413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87610974213232611456919217 65708230659924458592689413)
            ·
              refine ⟨12320293248735835986129265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65708230659924458592689413 12320293248735835986129265)
              ·
                refine ⟨9240219936551876989596949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12320293248735835986129265 9240219936551876989596949)
                ·
                  refine ⟨433135309525869233887357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9240219936551876989596949 433135309525869233887357)
                  ·
                    rfl

theorem cell20_948969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_948969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948969 prefixEnd_948969 := by exact prefixLift 948969
  have htrace : WordTrace (prefixWord ++ tailWord_948969) baseStart_948969 baseEnd_948969 := by
    simpa [prefixWord, tailWord_948969, baseEnd_948969] using wordTrace_append hprefix tailTrace_948969
  have hstable : (prefixWord ++ tailWord_948969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948969).length < 2 ^ (prefixWord ++ tailWord_948969).sum := by decide
  have hdescent : baseEnd_948969 < baseStart_948969 := by decide
  rcases family_descends (prefixWord ++ tailWord_948969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948986 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_948986 : Nat := 118140960795 + 948986 * 2 ^ 59
def prefixEnd_948986 : Nat := 4983230072969 + 3 ^ 40 * 948986 * 2
def baseEnd_948986 : Nat := 433143068789092730320621

theorem tailTrace_948986 : CollatzResearch.WordTrace tailWord_948986 prefixEnd_948986 433143068789092730320621 := by
  unfold tailWord_948986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653090734998317687636703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23074908626662180500364541 8653090734998317687636703)
  ·
    refine ⟨12979636102497476531455055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653090734998317687636703 12979636102497476531455055)
    ·
      refine ⟨19469454153746214797182583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12979636102497476531455055 19469454153746214797182583)
      ·
        refine ⟨29204181230619322195773875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19469454153746214797182583 29204181230619322195773875)
        ·
          refine ⟨43806271845928983293660813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29204181230619322195773875 43806271845928983293660813)
          ·
            refine ⟨16427351942223368735122805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43806271845928983293660813 16427351942223368735122805)
            ·
              refine ⟨1540064244583440818917763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16427351942223368735122805 1540064244583440818917763)
              ·
                refine ⟨2310096366875161228376645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540064244583440818917763 2310096366875161228376645)
                ·
                  refine ⟨433143068789092730320621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310096366875161228376645 433143068789092730320621)
                  ·
                    rfl

theorem cell20_948986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_948986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_948986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_948986 prefixEnd_948986 := by exact prefixLift 948986
  have htrace : WordTrace (prefixWord ++ tailWord_948986) baseStart_948986 baseEnd_948986 := by
    simpa [prefixWord, tailWord_948986, baseEnd_948986] using wordTrace_append hprefix tailTrace_948986
  have hstable : (prefixWord ++ tailWord_948986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948986).length < 2 ^ (prefixWord ++ tailWord_948986).sum := by decide
  have hdescent : baseEnd_948986 < baseStart_948986 := by decide
  rcases family_descends (prefixWord ++ tailWord_948986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949007 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_949007 : Nat := 118140960795 + 949007 * 2 ^ 59
def prefixEnd_949007 : Nat := 4983230072969 + 3 ^ 40 * 949007 * 2
def baseEnd_949007 : Nat := 433152653761309990620535

theorem tailTrace_949007 : CollatzResearch.WordTrace tailWord_949007 prefixEnd_949007 433152653761309990620535 := by
  unfold tailWord_949007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34613128872917191337061275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23075419248611460891374183 34613128872917191337061275)
  ·
    refine ⟨51919693309375787005591913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34613128872917191337061275 51919693309375787005591913)
    ·
      refine ⟨38939769982031840254193935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51919693309375787005591913 38939769982031840254193935)
      ·
        refine ⟨58409654973047760381290903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38939769982031840254193935 58409654973047760381290903)
        ·
          refine ⟨87614482459571640571936355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58409654973047760381290903 87614482459571640571936355)
          ·
            refine ⟨131421723689357460857904533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87614482459571640571936355 131421723689357460857904533)
            ·
              refine ⟨6160393297938630977714275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131421723689357460857904533 6160393297938630977714275)
              ·
                refine ⟨9240589946907946466571413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160393297938630977714275 9240589946907946466571413)
                ·
                  refine ⟨433152653761309990620535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9240589946907946466571413 433152653761309990620535)
                  ·
                    rfl

theorem cell20_949007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_949007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949007 prefixEnd_949007 := by exact prefixLift 949007
  have htrace : WordTrace (prefixWord ++ tailWord_949007) baseStart_949007 baseEnd_949007 := by
    simpa [prefixWord, tailWord_949007, baseEnd_949007] using wordTrace_append hprefix tailTrace_949007
  have hstable : (prefixWord ++ tailWord_949007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949007).length < 2 ^ (prefixWord ++ tailWord_949007).sum := by decide
  have hdescent : baseEnd_949007 < baseStart_949007 := by decide
  rcases family_descends (prefixWord ++ tailWord_949007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949041 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 2]
def baseStart_949041 : Nat := 118140960795 + 949041 * 2 ^ 59
def prefixEnd_949041 : Nat := 4983230072969 + 3 ^ 40 * 949041 * 2
def baseEnd_949041 : Nat := 433168172287756983487063

theorem tailTrace_949041 : CollatzResearch.WordTrace tailWord_949041 prefixEnd_949041 433168172287756983487063 := by
  unfold tailWord_949041
  simp only [CollatzResearch.WordTrace]
  refine ⟨34614368954794015143798977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23076245969862676762532651 34614368954794015143798977)
  ·
    refine ⟨25960776716095511357849233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34614368954794015143798977 25960776716095511357849233)
    ·
      refine ⟨19470582537071633518386925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25960776716095511357849233 19470582537071633518386925)
      ·
        refine ⟨7301468451401862569395097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19470582537071633518386925 7301468451401862569395097)
        ·
          refine ⟨5476101338551396927046323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7301468451401862569395097 5476101338551396927046323)
          ·
            refine ⟨8214152007827095390569485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476101338551396927046323 8214152007827095390569485)
            ·
              refine ⟨3080307002935160771463557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8214152007827095390569485 3080307002935160771463557)
              ·
                refine ⟨577557563050342644649417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3080307002935160771463557 577557563050342644649417)
                ·
                  refine ⟨433168172287756983487063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577557563050342644649417 433168172287756983487063)
                  ·
                    rfl

theorem cell20_949041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_949041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949041 prefixEnd_949041 := by exact prefixLift 949041
  have htrace : WordTrace (prefixWord ++ tailWord_949041) baseStart_949041 baseEnd_949041 := by
    simpa [prefixWord, tailWord_949041, baseEnd_949041] using wordTrace_append hprefix tailTrace_949041
  have hstable : (prefixWord ++ tailWord_949041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949041).length < 2 ^ (prefixWord ++ tailWord_949041).sum := by decide
  have hdescent : baseEnd_949041 < baseStart_949041 := by decide
  rcases family_descends (prefixWord ++ tailWord_949041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949044 : List Nat := [2, 5, 1, 1, 4, 1, 1, 5]
def baseStart_949044 : Nat := 118140960795 + 949044 * 2 ^ 59
def prefixEnd_949044 : Nat := 4983230072969 + 3 ^ 40 * 949044 * 2
def baseEnd_949044 : Nat := 144389847189834102129017

theorem tailTrace_949044 : CollatzResearch.WordTrace tailWord_949044 prefixEnd_949044 144389847189834102129017 := by
  unfold tailWord_949044
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307239186891573328079093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23076318915855431104105457 17307239186891573328079093)
  ·
    refine ⟨1622553673771084999507415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17307239186891573328079093 1622553673771084999507415)
    ·
      refine ⟨2433830510656627499261123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622553673771084999507415 2433830510656627499261123)
      ·
        refine ⟨3650745765984941248891685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433830510656627499261123 3650745765984941248891685)
        ·
          refine ⟨684514831122176484167191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3650745765984941248891685 684514831122176484167191)
          ·
            refine ⟨1026772246683264726250787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684514831122176484167191 1026772246683264726250787)
            ·
              refine ⟨1540158370024897089376181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026772246683264726250787 1540158370024897089376181)
              ·
                refine ⟨144389847189834102129017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1540158370024897089376181 144389847189834102129017)
                ·
                  rfl

theorem cell20_949044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_949044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949044 prefixEnd_949044 := by exact prefixLift 949044
  have htrace : WordTrace (prefixWord ++ tailWord_949044) baseStart_949044 baseEnd_949044 := by
    simpa [prefixWord, tailWord_949044, baseEnd_949044] using wordTrace_append hprefix tailTrace_949044
  have hstable : (prefixWord ++ tailWord_949044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949044).length < 2 ^ (prefixWord ++ tailWord_949044).sum := by decide
  have hdescent : baseEnd_949044 < baseStart_949044 := by decide
  rcases family_descends (prefixWord ++ tailWord_949044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949055 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_949055 : Nat := 118140960795 + 949055 * 2 ^ 59
def prefixEnd_949055 : Nat := 4983230072969 + 3 ^ 40 * 949055 * 2
def baseEnd_949055 : Nat := 433174562269235157020339

theorem tailTrace_949055 : CollatzResearch.WordTrace tailWord_949055 prefixEnd_949055 433174562269235157020339 := by
  unfold tailWord_949055
  simp only [CollatzResearch.WordTrace]
  refine ⟨34614879576743295534808619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23076586384495530356539079 34614879576743295534808619)
  ·
    refine ⟨51922319365114943302212929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34614879576743295534808619 51922319365114943302212929)
    ·
      refine ⟨38941739523836207476659697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51922319365114943302212929 38941739523836207476659697)
      ·
        refine ⟨29206304642877155607494773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38941739523836207476659697 29206304642877155607494773)
        ·
          refine ⟨2738091060269733338202635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29206304642877155607494773 2738091060269733338202635)
          ·
            refine ⟨4107136590404600007303953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738091060269733338202635 4107136590404600007303953)
            ·
              refine ⟨3080352442803450005477965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4107136590404600007303953 3080352442803450005477965)
              ·
                refine ⟨1155132166051293752054237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3080352442803450005477965 1155132166051293752054237)
                ·
                  refine ⟨433174562269235157020339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155132166051293752054237 433174562269235157020339)
                  ·
                    rfl

theorem cell20_949055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_949055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949055 prefixEnd_949055 := by exact prefixLift 949055
  have htrace : WordTrace (prefixWord ++ tailWord_949055) baseStart_949055 baseEnd_949055 := by
    simpa [prefixWord, tailWord_949055, baseEnd_949055] using wordTrace_append hprefix tailTrace_949055
  have hstable : (prefixWord ++ tailWord_949055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949055).length < 2 ^ (prefixWord ++ tailWord_949055).sum := by decide
  have hdescent : baseEnd_949055 < baseStart_949055 := by decide
  rcases family_descends (prefixWord ++ tailWord_949055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949079 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 2]
def baseStart_949079 : Nat := 118140960795 + 949079 * 2 ^ 59
def prefixEnd_949079 : Nat := 4983230072969 + 3 ^ 40 * 949079 * 2
def baseEnd_949079 : Nat := 433185516523197740220241

theorem tailTrace_949079 : CollatzResearch.WordTrace tailWord_949079 prefixEnd_949079 433185516523197740220241 := by
  unfold tailWord_949079
  simp only [CollatzResearch.WordTrace]
  refine ⟨34615754928656347633682291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23077169952437565089121527 34615754928656347633682291)
  ·
    refine ⟨51923632392984521450523437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34615754928656347633682291 51923632392984521450523437)
    ·
      refine ⟨19471362147369195543946289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51923632392984521450523437 19471362147369195543946289)
      ·
        refine ⟨14603521610526896657959717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19471362147369195543946289 14603521610526896657959717)
        ·
          refine ⟨2738160301973793123367447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14603521610526896657959717 2738160301973793123367447)
          ·
            refine ⟨4107240452960689685051171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738160301973793123367447 4107240452960689685051171)
            ·
              refine ⟨6160860679441034527576757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107240452960689685051171 6160860679441034527576757)
              ·
                refine ⟨577580688697596986960321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6160860679441034527576757 577580688697596986960321)
                ·
                  refine ⟨433185516523197740220241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577580688697596986960321 433185516523197740220241)
                  ·
                    rfl

theorem cell20_949079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 2].length) (baseStart_949079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949079 prefixEnd_949079 := by exact prefixLift 949079
  have htrace : WordTrace (prefixWord ++ tailWord_949079) baseStart_949079 baseEnd_949079 := by
    simpa [prefixWord, tailWord_949079, baseEnd_949079] using wordTrace_append hprefix tailTrace_949079
  have hstable : (prefixWord ++ tailWord_949079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949079).length < 2 ^ (prefixWord ++ tailWord_949079).sum := by decide
  have hdescent : baseEnd_949079 < baseStart_949079 := by decide
  rcases family_descends (prefixWord ++ tailWord_949079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949093 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_949093 : Nat := 118140960795 + 949093 * 2 ^ 59
def prefixEnd_949093 : Nat := 4983230072969 + 3 ^ 40 * 949093 * 2
def baseEnd_949093 : Nat := 433191906504675913753517

theorem tailTrace_949093 : CollatzResearch.WordTrace tailWord_949093 prefixEnd_949093 433191906504675913753517 := by
  unfold tailWord_949093
  simp only [CollatzResearch.WordTrace]
  refine ⟨34616265550605628024691933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23077510367070418683127955 34616265550605628024691933)
  ·
    refine ⟨12981099581477110509259475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34616265550605628024691933 12981099581477110509259475)
    ·
      refine ⟨19471649372215665763889213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12981099581477110509259475 19471649372215665763889213)
      ·
        refine ⟨7301868514580874661458455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19471649372215665763889213 7301868514580874661458455)
        ·
          refine ⟨10952802771871311992187683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301868514580874661458455 10952802771871311992187683)
          ·
            refine ⟨16429204157806967988281525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952802771871311992187683 16429204157806967988281525)
            ·
              refine ⟨1540237889794403248901393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16429204157806967988281525 1540237889794403248901393)
              ·
                refine ⟨1155178417345802436676045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540237889794403248901393 1155178417345802436676045)
                ·
                  refine ⟨433191906504675913753517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155178417345802436676045 433191906504675913753517)
                  ·
                    rfl

theorem cell20_949093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_949093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949093 prefixEnd_949093 := by exact prefixLift 949093
  have htrace : WordTrace (prefixWord ++ tailWord_949093) baseStart_949093 baseEnd_949093 := by
    simpa [prefixWord, tailWord_949093, baseEnd_949093] using wordTrace_append hprefix tailTrace_949093
  have hstable : (prefixWord ++ tailWord_949093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949093).length < 2 ^ (prefixWord ++ tailWord_949093).sum := by decide
  have hdescent : baseEnd_949093 < baseStart_949093 := by decide
  rcases family_descends (prefixWord ++ tailWord_949093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949100 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_949100 : Nat := 118140960795 + 949100 * 2 ^ 59
def prefixEnd_949100 : Nat := 4983230072969 + 3 ^ 40 * 949100 * 2
def baseEnd_949100 : Nat := 433195101495415000520155

theorem tailTrace_949100 : CollatzResearch.WordTrace tailWord_949100 prefixEnd_949100 433195101495415000520155 := by
  unfold tailWord_949100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17308260430790134110098377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23077680574386845480131169 17308260430790134110098377)
  ·
    refine ⟨12981195323092600582573783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17308260430790134110098377 12981195323092600582573783)
    ·
      refine ⟨19471792984638900873860675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12981195323092600582573783 19471792984638900873860675)
      ·
        refine ⟨29207689476958351310791013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19471792984638900873860675 29207689476958351310791013)
        ·
          refine ⟨5476441776929690870773315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29207689476958351310791013 5476441776929690870773315)
          ·
            refine ⟨8214662665394536306159973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476441776929690870773315 8214662665394536306159973)
            ·
              refine ⟨1540249249761475557404995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8214662665394536306159973 1540249249761475557404995)
              ·
                refine ⟨2310373874642213336107493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540249249761475557404995 2310373874642213336107493)
                ·
                  refine ⟨433195101495415000520155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310373874642213336107493 433195101495415000520155)
                  ·
                    rfl

theorem cell20_949100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_949100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949100 prefixEnd_949100 := by exact prefixLift 949100
  have htrace : WordTrace (prefixWord ++ tailWord_949100) baseStart_949100 baseEnd_949100 := by
    simpa [prefixWord, tailWord_949100, baseEnd_949100] using wordTrace_append hprefix tailTrace_949100
  have hstable : (prefixWord ++ tailWord_949100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949100).length < 2 ^ (prefixWord ++ tailWord_949100).sum := by decide
  have hdescent : baseEnd_949100 < baseStart_949100 := by decide
  rcases family_descends (prefixWord ++ tailWord_949100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949152 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_949152 : Nat := 118140960795 + 949152 * 2 ^ 59
def prefixEnd_949152 : Nat := 4983230072969 + 3 ^ 40 * 949152 * 2
def baseEnd_949152 : Nat := 433218835712333930786609

theorem tailTrace_949152 : CollatzResearch.WordTrace tailWord_949152 prefixEnd_949152 433218835712333930786609 := by
  unfold tailWord_949152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309208728695940550544855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23078944971594587400726473 17309208728695940550544855)
  ·
    refine ⟨25963813093043910825817283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17309208728695940550544855 25963813093043910825817283)
    ·
      refine ⟨38945719639565866238725925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25963813093043910825817283 38945719639565866238725925)
      ·
        refine ⟨7302322432418599919761111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38945719639565866238725925 7302322432418599919761111)
        ·
          refine ⟨10953483648627899879641667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7302322432418599919761111 10953483648627899879641667)
          ·
            refine ⟨16430225472941849819462501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10953483648627899879641667 16430225472941849819462501)
            ·
              refine ⟨3080667276176596841149219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16430225472941849819462501 3080667276176596841149219)
              ·
                refine ⟨4621000914264895261723829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080667276176596841149219 4621000914264895261723829)
                ·
                  refine ⟨433218835712333930786609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4621000914264895261723829 433218835712333930786609)
                  ·
                    rfl

theorem cell20_949152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_949152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949152 prefixEnd_949152 := by exact prefixLift 949152
  have htrace : WordTrace (prefixWord ++ tailWord_949152) baseStart_949152 baseEnd_949152 := by
    simpa [prefixWord, tailWord_949152, baseEnd_949152] using wordTrace_append hprefix tailTrace_949152
  have hstable : (prefixWord ++ tailWord_949152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949152).length < 2 ^ (prefixWord ++ tailWord_949152).sum := by decide
  have hdescent : baseEnd_949152 < baseStart_949152 := by decide
  rcases family_descends (prefixWord ++ tailWord_949152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949165 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 3]
def baseStart_949165 : Nat := 118140960795 + 949165 * 2 ^ 59
def prefixEnd_949165 : Nat := 4983230072969 + 3 ^ 40 * 949165 * 2
def baseEnd_949165 : Nat := 433224769266563663353223

theorem tailTrace_949165 : CollatzResearch.WordTrace tailWord_949165 prefixEnd_949165 433224769266563663353223 := by
  unfold tailWord_949165
  simp only [CollatzResearch.WordTrace]
  refine ⟨34618891606344784321312949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23079261070896522880875299 34618891606344784321312949)
  ·
    refine ⟨3245521088094823530123089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34618891606344784321312949 3245521088094823530123089)
    ·
      refine ⟨2434140816071117647592317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3245521088094823530123089 2434140816071117647592317)
      ·
        refine ⟨912802806026669117847119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2434140816071117647592317 912802806026669117847119)
        ·
          refine ⟨1369204209040003676770679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912802806026669117847119 1369204209040003676770679)
          ·
            refine ⟨2053806313560005515156019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369204209040003676770679 2053806313560005515156019)
            ·
              refine ⟨3080709470340008272734029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053806313560005515156019 3080709470340008272734029)
              ·
                refine ⟨1155266051377503102275261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3080709470340008272734029 1155266051377503102275261)
                ·
                  refine ⟨433224769266563663353223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155266051377503102275261 433224769266563663353223)
                  ·
                    rfl

theorem cell20_949165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_949165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949165 prefixEnd_949165 := by exact prefixLift 949165
  have htrace : WordTrace (prefixWord ++ tailWord_949165) baseStart_949165 baseEnd_949165 := by
    simpa [prefixWord, tailWord_949165, baseEnd_949165] using wordTrace_append hprefix tailTrace_949165
  have hstable : (prefixWord ++ tailWord_949165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949165).length < 2 ^ (prefixWord ++ tailWord_949165).sum := by decide
  have hdescent : baseEnd_949165 < baseStart_949165 := by decide
  rcases family_descends (prefixWord ++ tailWord_949165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949206 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_949206 : Nat := 118140960795 + 949206 * 2 ^ 59
def prefixEnd_949206 : Nat := 4983230072969 + 3 ^ 40 * 949206 * 2
def baseEnd_949206 : Nat := 433243482783749742986389

theorem tailTrace_949206 : CollatzResearch.WordTrace tailWord_949206 prefixEnd_949206 433243482783749742986389 := by
  unfold tailWord_949206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163774187449765520222217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23080257999464165549036981 2163774187449765520222217)
  ·
    refine ⟨1622830640587324140166663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2163774187449765520222217 1622830640587324140166663)
    ·
      refine ⟨2434245960880986210249995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622830640587324140166663 2434245960880986210249995)
      ·
        refine ⟨3651368941321479315374993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434245960880986210249995 3651368941321479315374993)
        ·
          refine ⟨2738526705991109486531245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651368941321479315374993 2738526705991109486531245)
          ·
            refine ⟨1026947514746666057449217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2738526705991109486531245 1026947514746666057449217)
            ·
              refine ⟨770210636059999543086913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026947514746666057449217 770210636059999543086913)
              ·
                refine ⟨577657977044999657315185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770210636059999543086913 577657977044999657315185)
                ·
                  refine ⟨433243482783749742986389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577657977044999657315185 433243482783749742986389)
                  ·
                    rfl

theorem cell20_949206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_949206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949206 prefixEnd_949206 := by exact prefixLift 949206
  have htrace : WordTrace (prefixWord ++ tailWord_949206) baseStart_949206 baseEnd_949206 := by
    simpa [prefixWord, tailWord_949206, baseEnd_949206] using wordTrace_append hprefix tailTrace_949206
  have hstable : (prefixWord ++ tailWord_949206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949206).length < 2 ^ (prefixWord ++ tailWord_949206).sum := by decide
  have hdescent : baseEnd_949206 < baseStart_949206 := by decide
  rcases family_descends (prefixWord ++ tailWord_949206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949210 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_949210 : Nat := 118140960795 + 949210 * 2 ^ 59
def prefixEnd_949210 : Nat := 4983230072969 + 3 ^ 40 * 949210 * 2
def baseEnd_949210 : Nat := 433245308492743506853039

theorem tailTrace_949210 : CollatzResearch.WordTrace tailWord_949210 prefixEnd_949210 433245308492743506853039 := by
  unfold tailWord_949210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655133222795439251675271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23080355260787838004467389 8655133222795439251675271)
  ·
    refine ⟨12982699834193158877512907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8655133222795439251675271 12982699834193158877512907)
    ·
      refine ⟨19474049751289738316269361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982699834193158877512907 19474049751289738316269361)
      ·
        refine ⟨14605537313467303737202021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19474049751289738316269361 14605537313467303737202021)
        ·
          refine ⟨2738538246275119450725379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14605537313467303737202021 2738538246275119450725379)
          ·
            refine ⟨4107807369412679176088069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738538246275119450725379 4107807369412679176088069)
            ·
              refine ⟨770213881764877345516513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4107807369412679176088069 770213881764877345516513)
              ·
                refine ⟨577660411323658009137385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770213881764877345516513 577660411323658009137385)
                ·
                  refine ⟨433245308492743506853039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577660411323658009137385 433245308492743506853039)
                  ·
                    rfl

theorem cell20_949210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_949210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949210 prefixEnd_949210 := by exact prefixLift 949210
  have htrace : WordTrace (prefixWord ++ tailWord_949210) baseStart_949210 baseEnd_949210 := by
    simpa [prefixWord, tailWord_949210, baseEnd_949210] using wordTrace_append hprefix tailTrace_949210
  have hstable : (prefixWord ++ tailWord_949210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949210).length < 2 ^ (prefixWord ++ tailWord_949210).sum := by decide
  have hdescent : baseEnd_949210 < baseStart_949210 := by decide
  rcases family_descends (prefixWord ++ tailWord_949210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949242 : List Nat := [3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_949242 : Nat := 118140960795 + 949242 * 2 ^ 59
def prefixEnd_949242 : Nat := 4983230072969 + 3 ^ 40 * 949242 * 2
def baseEnd_949242 : Nat := 144419971388231205928747

theorem tailTrace_949242 : CollatzResearch.WordTrace tailWord_949242 prefixEnd_949242 144419971388231205928747 := by
  unfold tailWord_949242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655425006766456617966495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23081133351377217647910653 8655425006766456617966495)
  ·
    refine ⟨12983137510149684926949743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8655425006766456617966495 12983137510149684926949743)
    ·
      refine ⟨19474706265224527390424615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12983137510149684926949743 19474706265224527390424615)
      ·
        refine ⟨29212059397836791085636923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19474706265224527390424615 29212059397836791085636923)
        ·
          refine ⟨43818089096755186628455385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29212059397836791085636923 43818089096755186628455385)
          ·
            refine ⟨32863566822566389971341539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43818089096755186628455385 32863566822566389971341539)
            ·
              refine ⟨49295350233849584957012309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32863566822566389971341539 49295350233849584957012309)
              ·
                refine ⟨144419971388231205928747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49295350233849584957012309 144419971388231205928747)
                ·
                  rfl

theorem cell20_949242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_949242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949242 prefixEnd_949242 := by exact prefixLift 949242
  have htrace : WordTrace (prefixWord ++ tailWord_949242) baseStart_949242 baseEnd_949242 := by
    simpa [prefixWord, tailWord_949242, baseEnd_949242] using wordTrace_append hprefix tailTrace_949242
  have hstable : (prefixWord ++ tailWord_949242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949242).length < 2 ^ (prefixWord ++ tailWord_949242).sum := by decide
  have hdescent : baseEnd_949242 < baseStart_949242 := by decide
  rcases family_descends (prefixWord ++ tailWord_949242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949262 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_949262 : Nat := 118140960795 + 949262 * 2 ^ 59
def prefixEnd_949262 : Nat := 4983230072969 + 3 ^ 40 * 949262 * 2
def baseEnd_949262 : Nat := 433269042709662437119493

theorem tailTrace_949262 : CollatzResearch.WordTrace tailWord_949262 prefixEnd_949262 433269042709662437119493 := by
  unfold tailWord_949262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327803685874171235949255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23081619657995579925062693 4327803685874171235949255)
  ·
    refine ⟨6491705528811256853923883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4327803685874171235949255 6491705528811256853923883)
    ·
      refine ⟨9737558293216885280885825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6491705528811256853923883 9737558293216885280885825)
      ·
        refine ⟨7303168719912663960664369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9737558293216885280885825 7303168719912663960664369)
        ·
          refine ⟨5477376539934497970498277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7303168719912663960664369 5477376539934497970498277)
          ·
            refine ⟨1027008101237718369468427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5477376539934497970498277 1027008101237718369468427)
            ·
              refine ⟨1540512151856577554202641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027008101237718369468427 1540512151856577554202641)
              ·
                refine ⟨1155384113892433165651981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540512151856577554202641 1155384113892433165651981)
                ·
                  refine ⟨433269042709662437119493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155384113892433165651981 433269042709662437119493)
                  ·
                    rfl

theorem cell20_949262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_949262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949262 prefixEnd_949262 := by exact prefixLift 949262
  have htrace : WordTrace (prefixWord ++ tailWord_949262) baseStart_949262 baseEnd_949262 := by
    simpa [prefixWord, tailWord_949262, baseEnd_949262] using wordTrace_append hprefix tailTrace_949262
  have hstable : (prefixWord ++ tailWord_949262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949262).length < 2 ^ (prefixWord ++ tailWord_949262).sum := by decide
  have hdescent : baseEnd_949262 < baseStart_949262 := by decide
  rcases family_descends (prefixWord ++ tailWord_949262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949269 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 2]
def baseStart_949269 : Nat := 118140960795 + 949269 * 2 ^ 59
def prefixEnd_949269 : Nat := 4983230072969 + 3 ^ 40 * 949269 * 2
def baseEnd_949269 : Nat := 433272237700401523886131

theorem tailTrace_949269 : CollatzResearch.WordTrace tailWord_949269 prefixEnd_949269 433272237700401523886131 := by
  unfold tailWord_949269
  simp only [CollatzResearch.WordTrace]
  refine ⟨34622684797968010083098861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23081789865312006722065907 34622684797968010083098861)
  ·
    refine ⟨12983506799238003781162073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34622684797968010083098861 12983506799238003781162073)
    ·
      refine ⟨9737630099428502835871555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12983506799238003781162073 9737630099428502835871555)
      ·
        refine ⟨14606445149142754253807333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9737630099428502835871555 14606445149142754253807333)
        ·
          refine ⟨2738708465464266422588875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14606445149142754253807333 2738708465464266422588875)
          ·
            refine ⟨4108062698196399633883313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738708465464266422588875 4108062698196399633883313)
            ·
              refine ⟨3081047023647299725412485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108062698196399633883313 3081047023647299725412485)
              ·
                refine ⟨577696316933868698514841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3081047023647299725412485 577696316933868698514841)
                ·
                  refine ⟨433272237700401523886131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577696316933868698514841 433272237700401523886131)
                  ·
                    rfl

theorem cell20_949269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_949269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949269 prefixEnd_949269 := by exact prefixLift 949269
  have htrace : WordTrace (prefixWord ++ tailWord_949269) baseStart_949269 baseEnd_949269 := by
    simpa [prefixWord, tailWord_949269, baseEnd_949269] using wordTrace_append hprefix tailTrace_949269
  have hstable : (prefixWord ++ tailWord_949269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949269).length < 2 ^ (prefixWord ++ tailWord_949269).sum := by decide
  have hdescent : baseEnd_949269 < baseStart_949269 := by decide
  rcases family_descends (prefixWord ++ tailWord_949269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949273 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_949273 : Nat := 118140960795 + 949273 * 2 ^ 59
def prefixEnd_949273 : Nat := 4983230072969 + 3 ^ 40 * 949273 * 2
def baseEnd_949273 : Nat := 433274063409395287752781

theorem tailTrace_949273 : CollatzResearch.WordTrace tailWord_949273 prefixEnd_949273 433274063409395287752781 := by
  unfold tailWord_949273
  simp only [CollatzResearch.WordTrace]
  refine ⟨34622830689953518766244473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23081887126635679177496315 34622830689953518766244473)
  ·
    refine ⟨25967123017465139074683355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34622830689953518766244473 25967123017465139074683355)
    ·
      refine ⟨38950684526197708612025033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25967123017465139074683355 38950684526197708612025033)
      ·
        refine ⟨29213013394648281459018775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38950684526197708612025033 29213013394648281459018775)
        ·
          refine ⟨43819520091972422188528163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213013394648281459018775 43819520091972422188528163)
          ·
            refine ⟨65729280137958633282792245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43819520091972422188528163 65729280137958633282792245)
            ·
              refine ⟨6162120012933621870261773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65729280137958633282792245 6162120012933621870261773)
              ·
                refine ⟨2310795004850108201348165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6162120012933621870261773 2310795004850108201348165)
                ·
                  refine ⟨433274063409395287752781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310795004850108201348165 433274063409395287752781)
                  ·
                    rfl

theorem cell20_949273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_949273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949273 prefixEnd_949273 := by exact prefixLift 949273
  have htrace : WordTrace (prefixWord ++ tailWord_949273) baseStart_949273 baseEnd_949273 := by
    simpa [prefixWord, tailWord_949273, baseEnd_949273] using wordTrace_append hprefix tailTrace_949273
  have hstable : (prefixWord ++ tailWord_949273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949273).length < 2 ^ (prefixWord ++ tailWord_949273).sum := by decide
  have hdescent : baseEnd_949273 < baseStart_949273 := by decide
  rcases family_descends (prefixWord ++ tailWord_949273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949304 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_949304 : Nat := 118140960795 + 949304 * 2 ^ 59
def prefixEnd_949304 : Nat := 4983230072969 + 3 ^ 40 * 949304 * 2
def baseEnd_949304 : Nat := 433288212654096957719321

theorem tailTrace_949304 : CollatzResearch.WordTrace tailWord_949304 prefixEnd_949304 433288212654096957719321 := by
  unfold tailWord_949304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17311980676420605530311483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23082640901894140707081977 17311980676420605530311483)
  ·
    refine ⟨25967971014630908295467225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17311980676420605530311483 25967971014630908295467225)
    ·
      refine ⟨19475978260973181221600419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25967971014630908295467225 19475978260973181221600419)
      ·
        refine ⟨29213967391459771832400629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19475978260973181221600419 29213967391459771832400629)
        ·
          refine ⟨2738809442949353609287559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29213967391459771832400629 2738809442949353609287559)
          ·
            refine ⟨4108214164424030413931339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738809442949353609287559 4108214164424030413931339)
            ·
              refine ⟨6162321246636045620897009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108214164424030413931339 6162321246636045620897009)
              ·
                refine ⟨4621740934977034215672757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162321246636045620897009 4621740934977034215672757)
                ·
                  refine ⟨433288212654096957719321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4621740934977034215672757 433288212654096957719321)
                  ·
                    rfl

theorem cell20_949304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_949304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949304 prefixEnd_949304 := by exact prefixLift 949304
  have htrace : WordTrace (prefixWord ++ tailWord_949304) baseStart_949304 baseEnd_949304 := by
    simpa [prefixWord, tailWord_949304, baseEnd_949304] using wordTrace_append hprefix tailTrace_949304
  have hstable : (prefixWord ++ tailWord_949304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949304).length < 2 ^ (prefixWord ++ tailWord_949304).sum := by decide
  have hdescent : baseEnd_949304 < baseStart_949304 := by decide
  rcases family_descends (prefixWord ++ tailWord_949304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949328 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 2]
def baseStart_949328 : Nat := 118140960795 + 949328 * 2 ^ 59
def prefixEnd_949328 : Nat := 4983230072969 + 3 ^ 40 * 949328 * 2
def baseEnd_949328 : Nat := 433299166908059540919223

theorem tailTrace_949328 : CollatzResearch.WordTrace tailWord_949328 prefixEnd_949328 433299166908059540919223 := by
  unfold tailWord_949328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17312418352377131579748319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23083224469836175439664425 17312418352377131579748319)
  ·
    refine ⟨25968627528565697369622479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17312418352377131579748319 25968627528565697369622479)
    ·
      refine ⟨38952941292848546054433719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25968627528565697369622479 38952941292848546054433719)
      ·
        refine ⟨58429411939272819081650579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38952941292848546054433719 58429411939272819081650579)
        ·
          refine ⟨87644117908909228622475869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58429411939272819081650579 87644117908909228622475869)
          ·
            refine ⟨32866544215840960733428451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87644117908909228622475869 32866544215840960733428451)
            ·
              refine ⟨49299816323761441100142677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32866544215840960733428451 49299816323761441100142677)
              ·
                refine ⟨577732222544079387892297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 49299816323761441100142677 577732222544079387892297)
                ·
                  refine ⟨433299166908059540919223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577732222544079387892297 433299166908059540919223)
                  ·
                    rfl

theorem cell20_949328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_949328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949328 prefixEnd_949328 := by exact prefixLift 949328
  have htrace : WordTrace (prefixWord ++ tailWord_949328) baseStart_949328 baseEnd_949328 := by
    simpa [prefixWord, tailWord_949328, baseEnd_949328] using wordTrace_append hprefix tailTrace_949328
  have hstable : (prefixWord ++ tailWord_949328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949328).length < 2 ^ (prefixWord ++ tailWord_949328).sum := by decide
  have hdescent : baseEnd_949328 < baseStart_949328 := by decide
  rcases family_descends (prefixWord ++ tailWord_949328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949349 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_949349 : Nat := 118140960795 + 949349 * 2 ^ 59
def prefixEnd_949349 : Nat := 4983230072969 + 3 ^ 40 * 949349 * 2
def baseEnd_949349 : Nat := 433308751880276801219137

theorem tailTrace_949349 : CollatzResearch.WordTrace tailWord_949349 prefixEnd_949349 433308751880276801219137 := by
  unfold tailWord_949349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625602637678183746011101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23083735091785455830674067 34625602637678183746011101)
  ·
    refine ⟨12984600989129318904754163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34625602637678183746011101 12984600989129318904754163)
    ·
      refine ⟨19476901483693978357131245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12984600989129318904754163 19476901483693978357131245)
      ·
        refine ⟨7303838056385241883924217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19476901483693978357131245 7303838056385241883924217)
        ·
          refine ⟨5477878542288931412943163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7303838056385241883924217 5477878542288931412943163)
          ·
            refine ⟨8216817813433397119414745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477878542288931412943163 8216817813433397119414745)
            ·
              refine ⟨6162613360075047839561059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8216817813433397119414745 6162613360075047839561059)
              ·
                refine ⟨9243920040112571759341589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162613360075047839561059 9243920040112571759341589)
                ·
                  refine ⟨433308751880276801219137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9243920040112571759341589 433308751880276801219137)
                  ·
                    rfl

theorem cell20_949349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_949349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949349 prefixEnd_949349 := by exact prefixLift 949349
  have htrace : WordTrace (prefixWord ++ tailWord_949349) baseStart_949349 baseEnd_949349 := by
    simpa [prefixWord, tailWord_949349, baseEnd_949349] using wordTrace_append hprefix tailTrace_949349
  have hstable : (prefixWord ++ tailWord_949349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949349).length < 2 ^ (prefixWord ++ tailWord_949349).sum := by decide
  have hdescent : baseEnd_949349 < baseStart_949349 := by decide
  rcases family_descends (prefixWord ++ tailWord_949349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949356 : List Nat := [2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_949356 : Nat := 118140960795 + 949356 * 2 ^ 59
def prefixEnd_949356 : Nat := 4983230072969 + 3 ^ 40 * 949356 * 2
def baseEnd_949356 : Nat := 144437315623671962661925

theorem tailTrace_949356 : CollatzResearch.WordTrace tailWord_949356 prefixEnd_949356 144437315623671962661925 := by
  unfold tailWord_949356
  simp only [CollatzResearch.WordTrace]
  refine ⟨17312928974326411970757961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23083905299101882627677281 17312928974326411970757961)
  ·
    refine ⟨12984696730744808978068471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17312928974326411970757961 12984696730744808978068471)
    ·
      refine ⟨19477045096117213467102707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12984696730744808978068471 19477045096117213467102707)
      ·
        refine ⟨29215567644175820200654061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19477045096117213467102707 29215567644175820200654061)
        ·
          refine ⟨10955837866565932575245273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29215567644175820200654061 10955837866565932575245273)
          ·
            refine ⟨8216878399924449431433955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10955837866565932575245273 8216878399924449431433955)
            ·
              refine ⟨12325317599886674147150933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216878399924449431433955 12325317599886674147150933)
              ·
                refine ⟨144437315623671962661925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12325317599886674147150933 144437315623671962661925)
                ·
                  rfl

theorem cell20_949356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_949356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949356 prefixEnd_949356 := by exact prefixLift 949356
  have htrace : WordTrace (prefixWord ++ tailWord_949356) baseStart_949356 baseEnd_949356 := by
    simpa [prefixWord, tailWord_949356, baseEnd_949356] using wordTrace_append hprefix tailTrace_949356
  have hstable : (prefixWord ++ tailWord_949356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949356).length < 2 ^ (prefixWord ++ tailWord_949356).sum := by decide
  have hdescent : baseEnd_949356 < baseStart_949356 := by decide
  rcases family_descends (prefixWord ++ tailWord_949356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949390 : List Nat := [4, 1, 1, 3, 2, 3, 1, 5]
def baseStart_949390 : Nat := 118140960795 + 949390 * 2 ^ 59
def prefixEnd_949390 : Nat := 4983230072969 + 3 ^ 40 * 949390 * 2
def baseEnd_949390 : Nat := 144442488465820960284101

theorem tailTrace_949390 : CollatzResearch.WordTrace tailWord_949390 prefixEnd_949390 144442488465820960284101 := by
  unfold tailWord_949390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328387253816205968531703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23084732020353098498835749 4328387253816205968531703)
  ·
    refine ⟨6492580880724308952797555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328387253816205968531703 6492580880724308952797555)
    ·
      refine ⟨9738871321086463429196333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492580880724308952797555 9738871321086463429196333)
      ·
        refine ⟨3652076745407423785948625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9738871321086463429196333 3652076745407423785948625)
        ·
          refine ⟨2739057559055567839461469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652076745407423785948625 2739057559055567839461469)
          ·
            refine ⟨1027146584645837939798051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2739057559055567839461469 1027146584645837939798051)
            ·
              refine ⟨1540719876968756909697077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027146584645837939798051 1540719876968756909697077)
              ·
                refine ⟨144442488465820960284101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1540719876968756909697077 144442488465820960284101)
                ·
                  rfl

theorem cell20_949390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_949390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949390 prefixEnd_949390 := by exact prefixLift 949390
  have htrace : WordTrace (prefixWord ++ tailWord_949390) baseStart_949390 baseEnd_949390 := by
    simpa [prefixWord, tailWord_949390, baseEnd_949390] using wordTrace_append hprefix tailTrace_949390
  have hstable : (prefixWord ++ tailWord_949390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949390).length < 2 ^ (prefixWord ++ tailWord_949390).sum := by decide
  have hdescent : baseEnd_949390 < baseStart_949390 := by decide
  rcases family_descends (prefixWord ++ tailWord_949390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949401 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_949401 : Nat := 118140960795 + 949401 * 2 ^ 59
def prefixEnd_949401 : Nat := 4983230072969 + 3 ^ 40 * 949401 * 2
def baseEnd_949401 : Nat := 433332486097195731485591

theorem tailTrace_949401 : CollatzResearch.WordTrace tailWord_949401 prefixEnd_949401 433332486097195731485591 := by
  unfold tailWord_949401
  simp only [CollatzResearch.WordTrace]
  refine ⟨34627499233489796626904057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23084999488993197751269371 34627499233489796626904057)
  ·
    refine ⟨25970624425117347470178043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34627499233489796626904057 25970624425117347470178043)
    ·
      refine ⟨38955936637676021205267065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25970624425117347470178043 38955936637676021205267065)
      ·
        refine ⟨29216952478257015903950299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38955936637676021205267065 29216952478257015903950299)
        ·
          refine ⟨43825428717385523855925449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29216952478257015903950299 43825428717385523855925449)
          ·
            refine ⟨32869071538039142891944087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43825428717385523855925449 32869071538039142891944087)
            ·
              refine ⟨49303607307058714337916131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32869071538039142891944087 49303607307058714337916131)
              ·
                refine ⟨73955410960588071506874197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49303607307058714337916131 73955410960588071506874197)
                ·
                  refine ⟨433332486097195731485591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73955410960588071506874197 433332486097195731485591)
                  ·
                    rfl

theorem cell20_949401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_949401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949401 prefixEnd_949401 := by exact prefixLift 949401
  have htrace : WordTrace (prefixWord ++ tailWord_949401) baseStart_949401 baseEnd_949401 := by
    simpa [prefixWord, tailWord_949401, baseEnd_949401] using wordTrace_append hprefix tailTrace_949401
  have hstable : (prefixWord ++ tailWord_949401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949401).length < 2 ^ (prefixWord ++ tailWord_949401).sum := by decide
  have hdescent : baseEnd_949401 < baseStart_949401 := by decide
  rcases family_descends (prefixWord ++ tailWord_949401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949404 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_949404 : Nat := 118140960795 + 949404 * 2 ^ 59
def prefixEnd_949404 : Nat := 4983230072969 + 3 ^ 40 * 949404 * 2
def baseEnd_949404 : Nat := 433333855378941054385579

theorem tailTrace_949404 : CollatzResearch.WordTrace tailWord_949404 prefixEnd_949404 433333855378941054385579 := by
  unfold tailWord_949404
  simp only [CollatzResearch.WordTrace]
  refine ⟨17313804326239464069631633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23085072434985952092842177 17313804326239464069631633)
  ·
    refine ⟨12985353244679598052223725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17313804326239464069631633 12985353244679598052223725)
    ·
      refine ⟨4869507466754849269583897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12985353244679598052223725 4869507466754849269583897)
      ·
        refine ⟨3652130600066136952187923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4869507466754849269583897 3652130600066136952187923)
        ·
          refine ⟨5478195900099205428281885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652130600066136952187923 5478195900099205428281885)
          ·
            refine ⟨2054323462537202035605707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5478195900099205428281885 2054323462537202035605707)
            ·
              refine ⟨3081485193805803053408561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054323462537202035605707 3081485193805803053408561)
              ·
                refine ⟨2311113895354352290056421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081485193805803053408561 2311113895354352290056421)
                ·
                  refine ⟨433333855378941054385579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311113895354352290056421 433333855378941054385579)
                  ·
                    rfl

theorem cell20_949404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_949404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949404 prefixEnd_949404 := by exact prefixLift 949404
  have htrace : WordTrace (prefixWord ++ tailWord_949404) baseStart_949404 baseEnd_949404 := by
    simpa [prefixWord, tailWord_949404, baseEnd_949404] using wordTrace_append hprefix tailTrace_949404
  have hstable : (prefixWord ++ tailWord_949404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949404).length < 2 ^ (prefixWord ++ tailWord_949404).sum := by decide
  have hdescent : baseEnd_949404 < baseStart_949404 := by decide
  rcases family_descends (prefixWord ++ tailWord_949404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949462 : List Nat := [5, 2, 1, 2, 2, 2, 2, 4]
def baseStart_949462 : Nat := 118140960795 + 949462 * 2 ^ 59
def prefixEnd_949462 : Nat := 4983230072969 + 3 ^ 40 * 949462 * 2
def baseEnd_949462 : Nat := 144453442719783543484003

theorem tailTrace_949462 : CollatzResearch.WordTrace tailWord_949462 prefixEnd_949462 144453442719783543484003 := by
  unfold tailWord_949462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164357755391800252804665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23086482724179202696583093 2164357755391800252804665)
  ·
    refine ⟨1623268316543850189603499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2164357755391800252804665 1623268316543850189603499)
    ·
      refine ⟨2434902474815775284405249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623268316543850189603499 2434902474815775284405249)
      ·
        refine ⟨1826176856111831463303937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434902474815775284405249 1826176856111831463303937)
        ·
          refine ⟨1369632642083873597477953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1826176856111831463303937 1369632642083873597477953)
          ·
            refine ⟨1027224481562905198108465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369632642083873597477953 1027224481562905198108465)
            ·
              refine ⟨770418361172178898581349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027224481562905198108465 770418361172178898581349)
              ·
                refine ⟨144453442719783543484003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770418361172178898581349 144453442719783543484003)
                ·
                  rfl

theorem cell20_949462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_949462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949462 prefixEnd_949462 := by exact prefixLift 949462
  have htrace : WordTrace (prefixWord ++ tailWord_949462) baseStart_949462 baseEnd_949462 := by
    simpa [prefixWord, tailWord_949462, baseEnd_949462] using wordTrace_append hprefix tailTrace_949462
  have hstable : (prefixWord ++ tailWord_949462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949462).length < 2 ^ (prefixWord ++ tailWord_949462).sum := by decide
  have hdescent : baseEnd_949462 < baseStart_949462 := by decide
  rcases family_descends (prefixWord ++ tailWord_949462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949463 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_949463 : Nat := 118140960795 + 949463 * 2 ^ 59
def prefixEnd_949463 : Nat := 4983230072969 + 3 ^ 40 * 949463 * 2
def baseEnd_949463 : Nat := 433360784586599071418671

theorem tailTrace_949463 : CollatzResearch.WordTrace tailWord_949463 prefixEnd_949463 433360784586599071418671 := by
  unfold tailWord_949463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34629760559265181215661043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23086507039510120810440695 34629760559265181215661043)
  ·
    refine ⟨51944640838897771823491565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34629760559265181215661043 51944640838897771823491565)
    ·
      refine ⟨19479240314586664433809337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51944640838897771823491565 19479240314586664433809337)
      ·
        refine ⟨14609430235939998325357003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19479240314586664433809337 14609430235939998325357003)
        ·
          refine ⟨21914145353909997488035505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14609430235939998325357003 21914145353909997488035505)
          ·
            refine ⟨16435609015432498116026629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21914145353909997488035505 16435609015432498116026629)
            ·
              refine ⟨3081676690393593396754993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16435609015432498116026629 3081676690393593396754993)
              ·
                refine ⟨2311257517795195047566245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081676690393593396754993 2311257517795195047566245)
                ·
                  refine ⟨433360784586599071418671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311257517795195047566245 433360784586599071418671)
                  ·
                    rfl

theorem cell20_949463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_949463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949463 prefixEnd_949463 := by exact prefixLift 949463
  have htrace : WordTrace (prefixWord ++ tailWord_949463) baseStart_949463 baseEnd_949463 := by
    simpa [prefixWord, tailWord_949463, baseEnd_949463] using wordTrace_append hprefix tailTrace_949463
  have hstable : (prefixWord ++ tailWord_949463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949463).length < 2 ^ (prefixWord ++ tailWord_949463).sum := by decide
  have hdescent : baseEnd_949463 < baseStart_949463 := by decide
  rcases family_descends (prefixWord ++ tailWord_949463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949487 : List Nat := [1, 1, 2, 1, 7, 2, 6]
def baseStart_949487 : Nat := 118140960795 + 949487 * 2 ^ 59
def prefixEnd_949487 : Nat := 4983230072969 + 3 ^ 40 * 949487 * 2
def baseEnd_949487 : Nat := 48152415426729072735397

theorem tailTrace_949487 : CollatzResearch.WordTrace tailWord_949487 prefixEnd_949487 48152415426729072735397 := by
  unfold tailWord_949487
  simp only [CollatzResearch.WordTrace]
  refine ⟨34630635911178233314534715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23087090607452155543023143 34630635911178233314534715)
  ·
    refine ⟨51945953866767349971802073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34630635911178233314534715 51945953866767349971802073)
    ·
      refine ⟨38959465400075512478851555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51945953866767349971802073 38959465400075512478851555)
      ·
        refine ⟨58439198100113268718277333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38959465400075512478851555 58439198100113268718277333)
        ·
          refine ⟨1369668705471404735584625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58439198100113268718277333 1369668705471404735584625)
          ·
            refine ⟨1027251529103553551688469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369668705471404735584625 1027251529103553551688469)
            ·
              refine ⟨48152415426729072735397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1027251529103553551688469 48152415426729072735397)
              ·
                rfl

theorem cell20_949487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_949487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949487 prefixEnd_949487 := by exact prefixLift 949487
  have htrace : WordTrace (prefixWord ++ tailWord_949487) baseStart_949487 baseEnd_949487 := by
    simpa [prefixWord, tailWord_949487, baseEnd_949487] using wordTrace_append hprefix tailTrace_949487
  have hstable : (prefixWord ++ tailWord_949487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949487).length < 2 ^ (prefixWord ++ tailWord_949487).sum := by decide
  have hdescent : baseEnd_949487 < baseStart_949487 := by decide
  rcases family_descends (prefixWord ++ tailWord_949487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949497 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 2]
def baseStart_949497 : Nat := 118140960795 + 949497 * 2 ^ 59
def prefixEnd_949497 : Nat := 4983230072969 + 3 ^ 40 * 949497 * 2
def baseEnd_949497 : Nat := 433376303113046064285199

theorem tailTrace_949497 : CollatzResearch.WordTrace tailWord_949497 prefixEnd_949497 433376303113046064285199 := by
  unfold tailWord_949497
  simp only [CollatzResearch.WordTrace]
  refine ⟨34631000641142005022398745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23087333760761336681599163 34631000641142005022398745)
  ·
    refine ⟨25973250480856503766799059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34631000641142005022398745 25973250480856503766799059)
    ·
      refine ⟨38959875721284755650198589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25973250480856503766799059 38959875721284755650198589)
      ·
        refine ⟨14609953395481783368824471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38959875721284755650198589 14609953395481783368824471)
        ·
          refine ⟨21914930093222675053236707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14609953395481783368824471 21914930093222675053236707)
          ·
            refine ⟨32872395139834012579855061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21914930093222675053236707 32872395139834012579855061)
            ·
              refine ⟨770446761089859669840353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32872395139834012579855061 770446761089859669840353)
              ·
                refine ⟨577835070817394752380265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770446761089859669840353 577835070817394752380265)
                ·
                  refine ⟨433376303113046064285199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577835070817394752380265 433376303113046064285199)
                  ·
                    rfl

theorem cell20_949497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_949497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949497 prefixEnd_949497 := by exact prefixLift 949497
  have htrace : WordTrace (prefixWord ++ tailWord_949497) baseStart_949497 baseEnd_949497 := by
    simpa [prefixWord, tailWord_949497, baseEnd_949497] using wordTrace_append hprefix tailTrace_949497
  have hstable : (prefixWord ++ tailWord_949497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949497).length < 2 ^ (prefixWord ++ tailWord_949497).sum := by decide
  have hdescent : baseEnd_949497 < baseStart_949497 := by decide
  rcases family_descends (prefixWord ++ tailWord_949497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949556 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_949556 : Nat := 118140960795 + 949556 * 2 ^ 59
def prefixEnd_949556 : Nat := 4983230072969 + 3 ^ 40 * 949556 * 2
def baseEnd_949556 : Nat := 433403232320704081318291

theorem tailTrace_949556 : CollatzResearch.WordTrace tailWord_949556 prefixEnd_949556 433403232320704081318291 := by
  unfold tailWord_949556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17316576273964129049398261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23088768365285505399197681 17316576273964129049398261)
  ·
    refine ⟨1623429025684137098381087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17316576273964129049398261 1623429025684137098381087)
    ·
      refine ⟨2435143538526205647571631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623429025684137098381087 2435143538526205647571631)
      ·
        refine ⟨3652715307789308471357447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435143538526205647571631 3652715307789308471357447)
        ·
          refine ⟨5479072961683962707036171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652715307789308471357447 5479072961683962707036171)
          ·
            refine ⟨8218609442525944060554257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479072961683962707036171 8218609442525944060554257)
            ·
              refine ⟨6163957081894458045415693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8218609442525944060554257 6163957081894458045415693)
              ·
                refine ⟨2311483905710421767030885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6163957081894458045415693 2311483905710421767030885)
                ·
                  refine ⟨433403232320704081318291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311483905710421767030885 433403232320704081318291)
                  ·
                    rfl

theorem cell20_949556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_949556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949556 prefixEnd_949556 := by exact prefixLift 949556
  have htrace : WordTrace (prefixWord ++ tailWord_949556) baseStart_949556 baseEnd_949556 := by
    simpa [prefixWord, tailWord_949556, baseEnd_949556] using wordTrace_append hprefix tailTrace_949556
  have hstable : (prefixWord ++ tailWord_949556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949556).length < 2 ^ (prefixWord ++ tailWord_949556).sum := by decide
  have hdescent : baseEnd_949556 < baseStart_949556 := by decide
  rcases family_descends (prefixWord ++ tailWord_949556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949594 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_949594 : Nat := 118140960795 + 949594 * 2 ^ 59
def prefixEnd_949594 : Nat := 4983230072969 + 3 ^ 40 * 949594 * 2
def baseEnd_949594 : Nat := 433420576556144838051469

theorem tailTrace_949594 : CollatzResearch.WordTrace tailWord_949594 prefixEnd_949594 433420576556144838051469 := by
  unfold tailWord_949594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8658634630447647647169959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23089692347860393725786557 8658634630447647647169959)
  ·
    refine ⟨12987951945671471470754939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8658634630447647647169959 12987951945671471470754939)
    ·
      refine ⟨19481927918507207206132409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12987951945671471470754939 19481927918507207206132409)
      ·
        refine ⟨14611445938880405404599307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19481927918507207206132409 14611445938880405404599307)
        ·
          refine ⟨21917168908320608106898961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14611445938880405404599307 21917168908320608106898961)
          ·
            refine ⟨16437876681240456080174221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21917168908320608106898961 16437876681240456080174221)
            ·
              refine ⟨6164203755465171030065333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16437876681240456080174221 6164203755465171030065333)
              ·
                refine ⟨577894102074859784068625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6164203755465171030065333 577894102074859784068625)
                ·
                  refine ⟨433420576556144838051469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577894102074859784068625 433420576556144838051469)
                  ·
                    rfl

theorem cell20_949594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_949594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949594 prefixEnd_949594 := by exact prefixLift 949594
  have htrace : WordTrace (prefixWord ++ tailWord_949594) baseStart_949594 baseEnd_949594 := by
    simpa [prefixWord, tailWord_949594, baseEnd_949594] using wordTrace_append hprefix tailTrace_949594
  have hstable : (prefixWord ++ tailWord_949594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949594).length < 2 ^ (prefixWord ++ tailWord_949594).sum := by decide
  have hdescent : baseEnd_949594 < baseStart_949594 := by decide
  rcases family_descends (prefixWord ++ tailWord_949594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949597 : List Nat := [1, 4, 5, 1, 1, 1, 7]
def baseStart_949597 : Nat := 118140960795 + 949597 * 2 ^ 59
def prefixEnd_949597 : Nat := 4983230072969 + 3 ^ 40 * 949597 * 2
def baseEnd_949597 : Nat := 48157993981987795661273

theorem tailTrace_949597 : CollatzResearch.WordTrace tailWord_949597 prefixEnd_949597 48157993981987795661273 := by
  unfold tailWord_949597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34634647940779722101039045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23089765293853148067359363 34634647940779722101039045)
  ·
    refine ⟨6493996488896197893944821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34634647940779722101039045 6493996488896197893944821)
    ·
      refine ⟨608812170834018552557327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6493996488896197893944821 608812170834018552557327)
      ·
        refine ⟨913218256251027828835991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608812170834018552557327 913218256251027828835991)
        ·
          refine ⟨1369827384376541743253987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913218256251027828835991 1369827384376541743253987)
          ·
            refine ⟨2054741076564812614880981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369827384376541743253987 2054741076564812614880981)
            ·
              refine ⟨48157993981987795661273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2054741076564812614880981 48157993981987795661273)
              ·
                rfl

theorem cell20_949597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 7].length) (baseStart_949597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949597 prefixEnd_949597 := by exact prefixLift 949597
  have htrace : WordTrace (prefixWord ++ tailWord_949597) baseStart_949597 baseEnd_949597 := by
    simpa [prefixWord, tailWord_949597, baseEnd_949597] using wordTrace_append hprefix tailTrace_949597
  have hstable : (prefixWord ++ tailWord_949597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949597).length < 2 ^ (prefixWord ++ tailWord_949597).sum := by decide
  have hdescent : baseEnd_949597 < baseStart_949597 := by decide
  rcases family_descends (prefixWord ++ tailWord_949597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949615 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_949615 : Nat := 118140960795 + 949615 * 2 ^ 59
def prefixEnd_949615 : Nat := 4983230072969 + 3 ^ 40 * 949615 * 2
def baseEnd_949615 : Nat := 433430161528362098351383

theorem tailTrace_949615 : CollatzResearch.WordTrace tailWord_949615 prefixEnd_949615 433430161528362098351383 := by
  unfold tailWord_949615
  simp only [CollatzResearch.WordTrace]
  refine ⟨34635304454714511175194299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23090202969809674116796199 34635304454714511175194299)
  ·
    refine ⟨51952956682071766762791449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34635304454714511175194299 51952956682071766762791449)
    ·
      refine ⟨38964717511553825072093587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51952956682071766762791449 38964717511553825072093587)
      ·
        refine ⟨58447076267330737608140381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38964717511553825072093587 58447076267330737608140381)
        ·
          refine ⟨21917653600249026603052643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58447076267330737608140381 21917653600249026603052643)
          ·
            refine ⟨32876480400373539904578965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21917653600249026603052643 32876480400373539904578965)
            ·
              refine ⟨1541085018767509683027139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32876480400373539904578965 1541085018767509683027139)
              ·
                refine ⟨2311627528151264524540709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541085018767509683027139 2311627528151264524540709)
                ·
                  refine ⟨433430161528362098351383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311627528151264524540709 433430161528362098351383)
                  ·
                    rfl

theorem cell20_949615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_949615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949615 prefixEnd_949615 := by exact prefixLift 949615
  have htrace : WordTrace (prefixWord ++ tailWord_949615) baseStart_949615 baseEnd_949615 := by
    simpa [prefixWord, tailWord_949615, baseEnd_949615] using wordTrace_append hprefix tailTrace_949615
  have hstable : (prefixWord ++ tailWord_949615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949615).length < 2 ^ (prefixWord ++ tailWord_949615).sum := by decide
  have hdescent : baseEnd_949615 < baseStart_949615 := by decide
  rcases family_descends (prefixWord ++ tailWord_949615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949639 : List Nat := [1, 1, 4, 2, 2, 2, 4, 4]
def baseStart_949639 : Nat := 118140960795 + 949639 * 2 ^ 59
def prefixEnd_949639 : Nat := 4983230072969 + 3 ^ 40 * 949639 * 2
def baseEnd_949639 : Nat := 144480371927441560517095

theorem tailTrace_949639 : CollatzResearch.WordTrace tailWord_949639 prefixEnd_949639 144480371927441560517095 := by
  unfold tailWord_949639
  simp only [CollatzResearch.WordTrace]
  refine ⟨34636179806627563274067971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23090786537751708849378647 34636179806627563274067971)
  ·
    refine ⟨51954269709941344911101957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34636179806627563274067971 51954269709941344911101957)
    ·
      refine ⟨9741425570614002170831617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51954269709941344911101957 9741425570614002170831617)
      ·
        refine ⟨7306069177960501628123713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9741425570614002170831617 7306069177960501628123713)
        ·
          refine ⟨5479551883470376221092785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7306069177960501628123713 5479551883470376221092785)
          ·
            refine ⟨4109663912602782165819589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479551883470376221092785 4109663912602782165819589)
            ·
              refine ⟨770561983613021656091173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4109663912602782165819589 770561983613021656091173)
              ·
                refine ⟨144480371927441560517095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 770561983613021656091173 144480371927441560517095)
                ·
                  rfl

theorem cell20_949639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_949639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949639 prefixEnd_949639 := by exact prefixLift 949639
  have htrace : WordTrace (prefixWord ++ tailWord_949639) baseStart_949639 baseEnd_949639 := by
    simpa [prefixWord, tailWord_949639, baseEnd_949639] using wordTrace_append hprefix tailTrace_949639
  have hstable : (prefixWord ++ tailWord_949639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949639).length < 2 ^ (prefixWord ++ tailWord_949639).sum := by decide
  have hdescent : baseEnd_949639 < baseStart_949639 := by decide
  rcases family_descends (prefixWord ++ tailWord_949639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949656 : List Nat := [2, 1, 2, 5, 3, 1, 6]
def baseStart_949656 : Nat := 118140960795 + 949656 * 2 ^ 59
def prefixEnd_949656 : Nat := 4983230072969 + 3 ^ 40 * 949656 * 2
def baseEnd_949656 : Nat := 48160986116172019776061

theorem tailTrace_949656 : CollatzResearch.WordTrace tailWord_949656 prefixEnd_949656 48160986116172019776061 := by
  unfold tailWord_949656
  simp only [CollatzResearch.WordTrace]
  refine ⟨17318399923782987588718411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23091199898377316784957881 17318399923782987588718411)
  ·
    refine ⟨25977599885674481383077617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17318399923782987588718411 25977599885674481383077617)
    ·
      refine ⟨19483199914255861037308213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25977599885674481383077617 19483199914255861037308213)
      ·
        refine ⟨1826549991961486972247645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19483199914255861037308213 1826549991961486972247645)
        ·
          refine ⟨684956246985557614592867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1826549991961486972247645 684956246985557614592867)
          ·
            refine ⟨1027434370478336421889301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684956246985557614592867 1027434370478336421889301)
            ·
              refine ⟨48160986116172019776061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1027434370478336421889301 48160986116172019776061)
              ·
                rfl

theorem cell20_949656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 6].length) (baseStart_949656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949656 prefixEnd_949656 := by exact prefixLift 949656
  have htrace : WordTrace (prefixWord ++ tailWord_949656) baseStart_949656 baseEnd_949656 := by
    simpa [prefixWord, tailWord_949656, baseEnd_949656] using wordTrace_append hprefix tailTrace_949656
  have hstable : (prefixWord ++ tailWord_949656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949656).length < 2 ^ (prefixWord ++ tailWord_949656).sum := by decide
  have hdescent : baseEnd_949656 < baseStart_949656 := by decide
  rcases family_descends (prefixWord ++ tailWord_949656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949666 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_949666 : Nat := 118140960795 + 949666 * 2 ^ 59
def prefixEnd_949666 : Nat := 4983230072969 + 3 ^ 40 * 949666 * 2
def baseEnd_949666 : Nat := 433453439318032587651175

theorem tailTrace_949666 : CollatzResearch.WordTrace tailWord_949666 prefixEnd_949666 433453439318032587651175 := by
  unfold tailWord_949666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659291144382436721325213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23091443051686497923533901 8659291144382436721325213)
  ·
    refine ⟨3247234179143413770496955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8659291144382436721325213 3247234179143413770496955)
    ·
      refine ⟨4870851268715120655745433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247234179143413770496955 4870851268715120655745433)
      ·
        refine ⟨3653138451536340491809075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4870851268715120655745433 3653138451536340491809075)
        ·
          refine ⟨5479707677304510737713613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653138451536340491809075 5479707677304510737713613)
          ·
            refine ⟨2054890378989191526642605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5479707677304510737713613 2054890378989191526642605)
            ·
              refine ⟨770583892120946822490977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2054890378989191526642605 770583892120946822490977)
              ·
                refine ⟨577937919090710116868233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770583892120946822490977 577937919090710116868233)
                ·
                  refine ⟨433453439318032587651175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 577937919090710116868233 433453439318032587651175)
                  ·
                    rfl

theorem cell20_949666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_949666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949666 prefixEnd_949666 := by exact prefixLift 949666
  have htrace : WordTrace (prefixWord ++ tailWord_949666) baseStart_949666 baseEnd_949666 := by
    simpa [prefixWord, tailWord_949666, baseEnd_949666] using wordTrace_append hprefix tailTrace_949666
  have hstable : (prefixWord ++ tailWord_949666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949666).length < 2 ^ (prefixWord ++ tailWord_949666).sum := by decide
  have hdescent : baseEnd_949666 < baseStart_949666 := by decide
  rcases family_descends (prefixWord ++ tailWord_949666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949667 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_949667 : Nat := 118140960795 + 949667 * 2 ^ 59
def prefixEnd_949667 : Nat := 4983230072969 + 3 ^ 40 * 949667 * 2
def baseEnd_949667 : Nat := 433453895745281028617837

theorem tailTrace_949667 : CollatzResearch.WordTrace tailWord_949667 prefixEnd_949667 433453895745281028617837 := by
  unfold tailWord_949667
  simp only [CollatzResearch.WordTrace]
  refine ⟨34637201050526124056087255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23091467367017416037391503 34637201050526124056087255)
  ·
    refine ⟨51955801575789186084130883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34637201050526124056087255 51955801575789186084130883)
    ·
      refine ⟨77933702363683779126196325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51955801575789186084130883 77933702363683779126196325)
      ·
        refine ⟨14612569193190708586161811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77933702363683779126196325 14612569193190708586161811)
        ·
          refine ⟨21918853789786062879242717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14612569193190708586161811 21918853789786062879242717)
          ·
            refine ⟨8219570171169773579716019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21918853789786062879242717 8219570171169773579716019)
            ·
              refine ⟨12329355256754660369574029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8219570171169773579716019 12329355256754660369574029)
              ·
                refine ⟨4623508221282997638590261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12329355256754660369574029 4623508221282997638590261)
                ·
                  refine ⟨433453895745281028617837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4623508221282997638590261 433453895745281028617837)
                  ·
                    rfl

theorem cell20_949667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_949667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949667 prefixEnd_949667 := by exact prefixLift 949667
  have htrace : WordTrace (prefixWord ++ tailWord_949667) baseStart_949667 baseEnd_949667 := by
    simpa [prefixWord, tailWord_949667, baseEnd_949667] using wordTrace_append hprefix tailTrace_949667
  have hstable : (prefixWord ++ tailWord_949667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949667).length < 2 ^ (prefixWord ++ tailWord_949667).sum := by decide
  have hdescent : baseEnd_949667 < baseStart_949667 := by decide
  rcases family_descends (prefixWord ++ tailWord_949667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949677 : List Nat := [1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_949677 : Nat := 118140960795 + 949677 * 2 ^ 59
def prefixEnd_949677 : Nat := 4983230072969 + 3 ^ 40 * 949677 * 2
def baseEnd_949677 : Nat := 144486153339255146094821

theorem tailTrace_949677 : CollatzResearch.WordTrace tailWord_949677 prefixEnd_949677 144486153339255146094821 := by
  unfold tailWord_949677
  simp only [CollatzResearch.WordTrace]
  refine ⟨34637565780489895763951285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23091710520326597175967523 34637565780489895763951285)
  ·
    refine ⟨3247271791920927727870433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34637565780489895763951285 3247271791920927727870433)
    ·
      refine ⟨2435453843940695795902825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3247271791920927727870433 2435453843940695795902825)
      ·
        refine ⟨1826590382955521846927119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2435453843940695795902825 1826590382955521846927119)
        ·
          refine ⟨2739885574433282770390679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826590382955521846927119 2739885574433282770390679)
          ·
            refine ⟨4109828361649924155586019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739885574433282770390679 4109828361649924155586019)
            ·
              refine ⟨6164742542474886233379029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109828361649924155586019 6164742542474886233379029)
              ·
                refine ⟨144486153339255146094821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6164742542474886233379029 144486153339255146094821)
                ·
                  rfl

theorem cell20_949677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_949677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949677 prefixEnd_949677 := by exact prefixLift 949677
  have htrace : WordTrace (prefixWord ++ tailWord_949677) baseStart_949677 baseEnd_949677 := by
    simpa [prefixWord, tailWord_949677, baseEnd_949677] using wordTrace_append hprefix tailTrace_949677
  have hstable : (prefixWord ++ tailWord_949677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949677).length < 2 ^ (prefixWord ++ tailWord_949677).sum := by decide
  have hdescent : baseEnd_949677 < baseStart_949677 := by decide
  rcases family_descends (prefixWord ++ tailWord_949677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949712 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_949712 : Nat := 118140960795 + 949712 * 2 ^ 59
def prefixEnd_949712 : Nat := 4983230072969 + 3 ^ 40 * 949712 * 2
def baseEnd_949712 : Nat := 433474434971460872117653

theorem tailTrace_949712 : CollatzResearch.WordTrace tailWord_949712 prefixEnd_949712 433474434971460872117653 := by
  unfold tailWord_949712
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319421167681548370737695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23092561556908731160983593 17319421167681548370737695)
  ·
    refine ⟨25979131751522322556106543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17319421167681548370737695 25979131751522322556106543)
    ·
      refine ⟨38968697627283483834159815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25979131751522322556106543 38968697627283483834159815)
      ·
        refine ⟨58453046440925225751239723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38968697627283483834159815 58453046440925225751239723)
        ·
          refine ⟨87679569661387838626859585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58453046440925225751239723 87679569661387838626859585)
          ·
            refine ⟨65759677246040878970144689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87679569661387838626859585 65759677246040878970144689)
            ·
              refine ⟨49319757934530659227608517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65759677246040878970144689 49319757934530659227608517)
              ·
                refine ⟨9247454612724498605176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49319757934530659227608517 9247454612724498605176597)
                ·
                  refine ⟨433474434971460872117653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9247454612724498605176597 433474434971460872117653)
                  ·
                    rfl

theorem cell20_949712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_949712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949712 prefixEnd_949712 := by exact prefixLift 949712
  have htrace : WordTrace (prefixWord ++ tailWord_949712) baseStart_949712 baseEnd_949712 := by
    simpa [prefixWord, tailWord_949712, baseEnd_949712] using wordTrace_append hprefix tailTrace_949712
  have hstable : (prefixWord ++ tailWord_949712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949712).length < 2 ^ (prefixWord ++ tailWord_949712).sum := by decide
  have hdescent : baseEnd_949712 < baseStart_949712 := by decide
  rcases family_descends (prefixWord ++ tailWord_949712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949718 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_949718 : Nat := 118140960795 + 949718 * 2 ^ 59
def prefixEnd_949718 : Nat := 4983230072969 + 3 ^ 40 * 949718 * 2
def baseEnd_949718 : Nat := 433477173534951517917629

theorem tailTrace_949718 : CollatzResearch.WordTrace tailWord_949718 prefixEnd_949718 433477173534951517917629 := by
  unfold tailWord_949718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164941323333834985387113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23092707448894239844129205 2164941323333834985387113)
  ·
    refine ⟨1623705992500376239040335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2164941323333834985387113 1623705992500376239040335)
    ·
      refine ⟨2435558988750564358560503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623705992500376239040335 2435558988750564358560503)
      ·
        refine ⟨3653338483125846537840755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435558988750564358560503 3653338483125846537840755)
        ·
          refine ⟨5480007724688769806761133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653338483125846537840755 5480007724688769806761133)
          ·
            refine ⟨2055002896758288677535425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5480007724688769806761133 2055002896758288677535425)
            ·
              refine ⟨1541252172568716508151569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055002896758288677535425 1541252172568716508151569)
              ·
                refine ⟨1155939129426537381113677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541252172568716508151569 1155939129426537381113677)
                ·
                  refine ⟨433477173534951517917629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155939129426537381113677 433477173534951517917629)
                  ·
                    rfl

theorem cell20_949718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_949718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949718 prefixEnd_949718 := by exact prefixLift 949718
  have htrace : WordTrace (prefixWord ++ tailWord_949718) baseStart_949718 baseEnd_949718 := by
    simpa [prefixWord, tailWord_949718, baseEnd_949718] using wordTrace_append hprefix tailTrace_949718
  have hstable : (prefixWord ++ tailWord_949718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949718).length < 2 ^ (prefixWord ++ tailWord_949718).sum := by decide
  have hdescent : baseEnd_949718 < baseStart_949718 := by decide
  rcases family_descends (prefixWord ++ tailWord_949718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949722 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_949722 : Nat := 118140960795 + 949722 * 2 ^ 59
def prefixEnd_949722 : Nat := 4983230072969 + 3 ^ 40 * 949722 * 2
def baseEnd_949722 : Nat := 433478999243945281784279

theorem tailTrace_949722 : CollatzResearch.WordTrace tailWord_949722 prefixEnd_949722 433478999243945281784279 := by
  unfold tailWord_949722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659801766331717112334855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23092804710217912299559613 8659801766331717112334855)
  ·
    refine ⟨12989702649497575668502283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8659801766331717112334855 12989702649497575668502283)
    ·
      refine ⟨19484553974246363502753425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12989702649497575668502283 19484553974246363502753425)
      ·
        refine ⟨14613415480684772627065069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19484553974246363502753425 14613415480684772627065069)
        ·
          refine ⟨5480030805256789735149401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14613415480684772627065069 5480030805256789735149401)
          ·
            refine ⟨4110023103942592301362051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5480030805256789735149401 4110023103942592301362051)
            ·
              refine ⟨6165034655913888452043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110023103942592301362051 6165034655913888452043077)
              ·
                refine ⟨1155943997983854084758077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6165034655913888452043077 1155943997983854084758077)
                ·
                  refine ⟨433478999243945281784279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155943997983854084758077 433478999243945281784279)
                  ·
                    rfl

theorem cell20_949722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_949722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_949722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_949722 prefixEnd_949722 := by exact prefixLift 949722
  have htrace : WordTrace (prefixWord ++ tailWord_949722) baseStart_949722 baseEnd_949722 := by
    simpa [prefixWord, tailWord_949722, baseEnd_949722] using wordTrace_append hprefix tailTrace_949722
  have hstable : (prefixWord ++ tailWord_949722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949722).length < 2 ^ (prefixWord ++ tailWord_949722).sum := by decide
  have hdescent : baseEnd_949722 < baseStart_949722 := by decide
  rcases family_descends (prefixWord ++ tailWord_949722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
