import V185TrunkScan23Chunk0739

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4375855 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 8, 2]
def baseStart_4375855 : Nat := 118140960795 + 4375855 * 2 ^ 59
def prefixEnd_4375855 : Nat := 4983230072969 + 3 ^ 40 * 4375855 * 2
def baseEnd_4375855 : Nat := 2246916889380082180888315

theorem tailTrace_4375855 : CollatzResearch.WordTrace tailWord_4375855 prefixEnd_4375855 2246916889380082180888315 := by
  unfold tailWord_4375855
  simp only [CollatzResearch.WordTrace]
  refine ⟨159600543562032146380609019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106400362374688097587072679 159600543562032146380609019)
  ·
    refine ⟨239400815343048219570913529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159600543562032146380609019 239400815343048219570913529)
    ·
      refine ⟨179550611507286164678185147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239400815343048219570913529 179550611507286164678185147)
      ·
        refine ⟨269325917260929247017277721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179550611507286164678185147 269325917260929247017277721)
        ·
          refine ⟨201994437945696935262958291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269325917260929247017277721 201994437945696935262958291)
          ·
            refine ⟨302991656918545402894437437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201994437945696935262958291 302991656918545402894437437)
            ·
              refine ⟨113621871344454526085414039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302991656918545402894437437 113621871344454526085414039)
              ·
                refine ⟨170432807016681789128121059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113621871344454526085414039 170432807016681789128121059)
                ·
                  refine ⟨255649210525022683692181589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170432807016681789128121059 255649210525022683692181589)
                  ·
                    refine ⟨2995889185840109574517753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 255649210525022683692181589 2995889185840109574517753)
                    ·
                      refine ⟨2246916889380082180888315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995889185840109574517753 2246916889380082180888315)
                      ·
                        rfl

theorem cell23_4375855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8, 2].length) (baseStart_4375855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375855 prefixEnd_4375855 := by exact prefixLift 4375855
  have htrace : WordTrace (prefixWord ++ tailWord_4375855) baseStart_4375855 baseEnd_4375855 := by
    simpa [prefixWord, tailWord_4375855, baseEnd_4375855] using wordTrace_append hprefix tailTrace_4375855
  have hstable : (prefixWord ++ tailWord_4375855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375855).length < 2 ^ (prefixWord ++ tailWord_4375855).sum := by decide
  have hdescent : baseEnd_4375855 < baseStart_4375855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375875 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 3]
def baseStart_4375875 : Nat := 118140960795 + 4375875 * 2 ^ 59
def prefixEnd_4375875 : Nat := 4983230072969 + 3 ^ 40 * 4375875 * 2
def baseEnd_4375875 : Nat := 2246927158993172102638223

theorem tailTrace_4375875 : CollatzResearch.WordTrace tailWord_4375875 prefixEnd_4375875 2246927158993172102638223 := by
  unfold tailWord_4375875
  simp only [CollatzResearch.WordTrace]
  refine ⟨159601273021959689796337079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106400848681306459864224719 159601273021959689796337079)
  ·
    refine ⟨239401909532939534694505619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159601273021959689796337079 239401909532939534694505619)
    ·
      refine ⟨359102864299409302041758429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239401909532939534694505619 359102864299409302041758429)
      ·
        refine ⟨134663574112278488265659411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359102864299409302041758429 134663574112278488265659411)
        ·
          refine ⟨201995361168417732398489117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134663574112278488265659411 201995361168417732398489117)
          ·
            refine ⟨75748260438156649649433419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201995361168417732398489117 75748260438156649649433419)
            ·
              refine ⟨113622390657234974474150129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75748260438156649649433419 113622390657234974474150129)
              ·
                refine ⟨85216792992926230855612597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113622390657234974474150129 85216792992926230855612597)
                ·
                  refine ⟨7989074343086834142713681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85216792992926230855612597 7989074343086834142713681)
                  ·
                    refine ⟨5991805757315125607035261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7989074343086834142713681 5991805757315125607035261)
                    ·
                      refine ⟨2246927158993172102638223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991805757315125607035261 2246927158993172102638223)
                      ·
                        rfl

theorem cell23_4375875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_4375875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375875 prefixEnd_4375875 := by exact prefixLift 4375875
  have htrace : WordTrace (prefixWord ++ tailWord_4375875) baseStart_4375875 baseEnd_4375875 := by
    simpa [prefixWord, tailWord_4375875, baseEnd_4375875] using wordTrace_append hprefix tailTrace_4375875
  have hstable : (prefixWord ++ tailWord_4375875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375875).length < 2 ^ (prefixWord ++ tailWord_4375875).sum := by decide
  have hdescent : baseEnd_4375875 < baseStart_4375875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375876 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4375876 : Nat := 118140960795 + 4375876 * 2 ^ 59
def prefixEnd_4375876 : Nat := 4983230072969 + 3 ^ 40 * 4375876 * 2
def baseEnd_4375876 : Nat := 2246927672473826598725719

theorem tailTrace_4375876 : CollatzResearch.WordTrace tailWord_4375876 prefixEnd_4375876 2246927672473826598725719 := by
  unfold tailWord_4375876
  simp only [CollatzResearch.WordTrace]
  refine ⟨79800654747478033483561741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106400872996637377978082321 79800654747478033483561741)
  ·
    refine ⟨29925245530304262556335653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79800654747478033483561741 29925245530304262556335653)
    ·
      refine ⟨5610983536932049229312935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29925245530304262556335653 5610983536932049229312935)
      ·
        refine ⟨8416475305398073843969403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610983536932049229312935 8416475305398073843969403)
        ·
          refine ⟨12624712958097110765954105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8416475305398073843969403 12624712958097110765954105)
          ·
            refine ⟨9468534718572833074465579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12624712958097110765954105 9468534718572833074465579)
            ·
              refine ⟨14202802077859249611698369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9468534718572833074465579 14202802077859249611698369)
              ·
                refine ⟨10652101558394437208773777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14202802077859249611698369 10652101558394437208773777)
                ·
                  refine ⟨7989076168795827906580333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10652101558394437208773777 7989076168795827906580333)
                  ·
                    refine ⟨2995903563298435464967625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7989076168795827906580333 2995903563298435464967625)
                    ·
                      refine ⟨2246927672473826598725719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995903563298435464967625 2246927672473826598725719)
                      ·
                        rfl

theorem cell23_4375876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4375876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375876 prefixEnd_4375876 := by exact prefixLift 4375876
  have htrace : WordTrace (prefixWord ++ tailWord_4375876) baseStart_4375876 baseEnd_4375876 := by
    simpa [prefixWord, tailWord_4375876, baseEnd_4375876] using wordTrace_append hprefix tailTrace_4375876
  have hstable : (prefixWord ++ tailWord_4375876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375876).length < 2 ^ (prefixWord ++ tailWord_4375876).sum := by decide
  have hdescent : baseEnd_4375876 < baseStart_4375876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375892 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_4375892 : Nat := 118140960795 + 4375892 * 2 ^ 59
def prefixEnd_4375892 : Nat := 4983230072969 + 3 ^ 40 * 4375892 * 2
def baseEnd_4375892 : Nat := 2246935888164298536125645

theorem tailTrace_4375892 : CollatzResearch.WordTrace tailWord_4375892 prefixEnd_4375892 2246935888164298536125645 := by
  unfold tailWord_4375892
  simp only [CollatzResearch.WordTrace]
  refine ⟨79800946531449050849852965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106401262041932067799803953 79800946531449050849852965)
  ·
    refine ⟨14962677474646697034347431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79800946531449050849852965 14962677474646697034347431)
    ·
      refine ⟨22444016211970045551521147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14962677474646697034347431 22444016211970045551521147)
      ·
        refine ⟨33666024317955068327281721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22444016211970045551521147 33666024317955068327281721)
        ·
          refine ⟨25249518238466301245461291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33666024317955068327281721 25249518238466301245461291)
          ·
            refine ⟨37874277357699451868191937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25249518238466301245461291 37874277357699451868191937)
            ·
              refine ⟨28405708018274588901143953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37874277357699451868191937 28405708018274588901143953)
              ·
                refine ⟨21304281013705941675857965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28405708018274588901143953 21304281013705941675857965)
                ·
                  refine ⟨7989105380139728128446737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21304281013705941675857965 7989105380139728128446737)
                  ·
                    refine ⟨5991829035104796096335053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7989105380139728128446737 5991829035104796096335053)
                    ·
                      refine ⟨2246935888164298536125645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991829035104796096335053 2246935888164298536125645)
                      ·
                        rfl

theorem cell23_4375892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_4375892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375892 prefixEnd_4375892 := by exact prefixLift 4375892
  have htrace : WordTrace (prefixWord ++ tailWord_4375892) baseStart_4375892 baseEnd_4375892 := by
    simpa [prefixWord, tailWord_4375892, baseEnd_4375892] using wordTrace_append hprefix tailTrace_4375892
  have hstable : (prefixWord ++ tailWord_4375892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375892).length < 2 ^ (prefixWord ++ tailWord_4375892).sum := by decide
  have hdescent : baseEnd_4375892 < baseStart_4375892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375895 : List Nat := [1, 1, 3, 2, 3, 3, 2, 8]
def baseStart_4375895 : Nat := 118140960795 + 4375895 * 2 ^ 59
def prefixEnd_4375895 : Nat := 4983230072969 + 3 ^ 40 * 4375895 * 2
def baseEnd_4375895 : Nat := 83219904763194889792153

theorem tailTrace_4375895 : CollatzResearch.WordTrace tailWord_4375895 prefixEnd_4375895 83219904763194889792153 := by
  unfold tailWord_4375895
  simp only [CollatzResearch.WordTrace]
  refine ⟨159602002481887233212065139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106401334987924822141376759 159602002481887233212065139)
  ·
    refine ⟨239403003722830849818097709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159602002481887233212065139 239403003722830849818097709)
    ·
      refine ⟨89776126396061568681786641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239403003722830849818097709 89776126396061568681786641)
      ·
        refine ⟨67332094797046176511339981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89776126396061568681786641 67332094797046176511339981)
        ·
          refine ⟨25249535548892316191752493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67332094797046176511339981 25249535548892316191752493)
          ·
            refine ⟨9468575830834618571907185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25249535548892316191752493 9468575830834618571907185)
            ·
              refine ⟨7101431873125963928930389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9468575830834618571907185 7101431873125963928930389)
              ·
                refine ⟨83219904763194889792153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7101431873125963928930389 83219904763194889792153)
                ·
                  rfl

theorem cell23_4375895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 8].length) (baseStart_4375895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375895 prefixEnd_4375895 := by exact prefixLift 4375895
  have htrace : WordTrace (prefixWord ++ tailWord_4375895) baseStart_4375895 baseEnd_4375895 := by
    simpa [prefixWord, tailWord_4375895, baseEnd_4375895] using wordTrace_append hprefix tailTrace_4375895
  have hstable : (prefixWord ++ tailWord_4375895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375895).length < 2 ^ (prefixWord ++ tailWord_4375895).sum := by decide
  have hdescent : baseEnd_4375895 < baseStart_4375895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375905 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_4375905 : Nat := 118140960795 + 4375905 * 2 ^ 59
def prefixEnd_4375905 : Nat := 4983230072969 + 3 ^ 40 * 4375905 * 2
def baseEnd_4375905 : Nat := 2246942563412806985263085

theorem tailTrace_4375905 : CollatzResearch.WordTrace tailWord_4375905 prefixEnd_4375905 2246942563412806985263085 := by
  unfold tailWord_4375905
  simp only [CollatzResearch.WordTrace]
  refine ⟨159602367211851004919929169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106401578141234003279952779 159602367211851004919929169)
  ·
    refine ⟨119701775408888253689946877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159602367211851004919929169 119701775408888253689946877)
    ·
      refine ⟨44888165778333095133730079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119701775408888253689946877 44888165778333095133730079)
      ·
        refine ⟨67332248667499642700595119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44888165778333095133730079 67332248667499642700595119)
        ·
          refine ⟨100998373001249464050892679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67332248667499642700595119 100998373001249464050892679)
          ·
            refine ⟨151497559501874196076339019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100998373001249464050892679 151497559501874196076339019)
            ·
              refine ⟨227246339252811294114508529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151497559501874196076339019 227246339252811294114508529)
              ·
                refine ⟨170434754439608470585881397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227246339252811294114508529 170434754439608470585881397)
                ·
                  refine ⟨15978258228713294117426381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170434754439608470585881397 15978258228713294117426381)
                  ·
                    refine ⟨5991846835767485294034893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15978258228713294117426381 5991846835767485294034893)
                    ·
                      refine ⟨2246942563412806985263085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991846835767485294034893 2246942563412806985263085)
                      ·
                        rfl

theorem cell23_4375905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_4375905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375905 prefixEnd_4375905 := by exact prefixLift 4375905
  have htrace : WordTrace (prefixWord ++ tailWord_4375905) baseStart_4375905 baseEnd_4375905 := by
    simpa [prefixWord, tailWord_4375905, baseEnd_4375905] using wordTrace_append hprefix tailTrace_4375905
  have hstable : (prefixWord ++ tailWord_4375905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375905).length < 2 ^ (prefixWord ++ tailWord_4375905).sum := by decide
  have hdescent : baseEnd_4375905 < baseStart_4375905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375922 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_4375922 : Nat := 118140960795 + 4375922 * 2 ^ 59
def prefixEnd_4375922 : Nat := 4983230072969 + 3 ^ 40 * 4375922 * 2
def baseEnd_4375922 : Nat := 2246951292583933418750507

theorem tailTrace_4375922 : CollatzResearch.WordTrace tailWord_4375922 prefixEnd_4375922 2246951292583933418750507 := by
  unfold tailWord_4375922
  simp only [CollatzResearch.WordTrace]
  refine ⟨39900746813197354205824505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106401991501859611215532013 39900746813197354205824505)
  ·
    refine ⟨29925560109898015654368379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39900746813197354205824505 29925560109898015654368379)
    ·
      refine ⟨44888340164847023481552569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29925560109898015654368379 44888340164847023481552569)
      ·
        refine ⟨33666255123635267611164427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44888340164847023481552569 33666255123635267611164427)
        ·
          refine ⟨50499382685452901416746641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33666255123635267611164427 50499382685452901416746641)
          ·
            refine ⟨37874537014089676062559981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50499382685452901416746641 37874537014089676062559981)
            ·
              refine ⟨14202951380283628523459993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37874537014089676062559981 14202951380283628523459993)
              ·
                refine ⟨10652213535212721392594995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14202951380283628523459993 10652213535212721392594995)
                ·
                  refine ⟨15978320302819082088892493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10652213535212721392594995 15978320302819082088892493)
                  ·
                    refine ⟨5991870113557155783334685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15978320302819082088892493 5991870113557155783334685)
                    ·
                      refine ⟨2246951292583933418750507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991870113557155783334685 2246951292583933418750507)
                      ·
                        rfl

theorem cell23_4375922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_4375922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375922 prefixEnd_4375922 := by exact prefixLift 4375922
  have htrace : WordTrace (prefixWord ++ tailWord_4375922) baseStart_4375922 baseEnd_4375922 := by
    simpa [prefixWord, tailWord_4375922, baseEnd_4375922] using wordTrace_append hprefix tailTrace_4375922
  have hstable : (prefixWord ++ tailWord_4375922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375922).length < 2 ^ (prefixWord ++ tailWord_4375922).sum := by decide
  have hdescent : baseEnd_4375922 < baseStart_4375922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375934 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4375934 : Nat := 118140960795 + 4375934 * 2 ^ 59
def prefixEnd_4375934 : Nat := 4983230072969 + 3 ^ 40 * 4375934 * 2
def baseEnd_4375934 : Nat := 2246957454351787371800453

theorem tailTrace_4375934 : CollatzResearch.WordTrace tailWord_4375934 prefixEnd_4375934 2246957454351787371800453 := by
  unfold tailWord_4375934
  simp only [CollatzResearch.WordTrace]
  refine ⟨19950428116093242859091857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106402283285830628581823237 19950428116093242859091857)
  ·
    refine ⟨14962821087069932144318893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19950428116093242859091857 14962821087069932144318893)
    ·
      refine ⟨5611057907651224554119585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14962821087069932144318893 5611057907651224554119585)
      ·
        refine ⟨4208293430738418415589689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5611057907651224554119585 4208293430738418415589689)
        ·
          refine ⟨3156220073053813811692267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4208293430738418415589689 3156220073053813811692267)
          ·
            refine ⟨4734330109580720717538401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156220073053813811692267 4734330109580720717538401)
            ·
              refine ⟨3550747582185540538153801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734330109580720717538401 3550747582185540538153801)
              ·
                refine ⟨2663060686639155403615351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550747582185540538153801 2663060686639155403615351)
                ·
                  refine ⟨3994591029958733105423027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663060686639155403615351 3994591029958733105423027)
                  ·
                    refine ⟨5991886544938099658134541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3994591029958733105423027 5991886544938099658134541)
                    ·
                      refine ⟨2246957454351787371800453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991886544938099658134541 2246957454351787371800453)
                      ·
                        rfl

theorem cell23_4375934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4375934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375934 prefixEnd_4375934 := by exact prefixLift 4375934
  have htrace : WordTrace (prefixWord ++ tailWord_4375934) baseStart_4375934 baseEnd_4375934 := by
    simpa [prefixWord, tailWord_4375934, baseEnd_4375934] using wordTrace_append hprefix tailTrace_4375934
  have hstable : (prefixWord ++ tailWord_4375934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375934).length < 2 ^ (prefixWord ++ tailWord_4375934).sum := by decide
  have hdescent : baseEnd_4375934 < baseStart_4375934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375939 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 3]
def baseStart_4375939 : Nat := 118140960795 + 4375939 * 2 ^ 59
def prefixEnd_4375939 : Nat := 4983230072969 + 3 ^ 40 * 4375939 * 2
def baseEnd_4375939 : Nat := 2246960021755059852237929

theorem tailTrace_4375939 : CollatzResearch.WordTrace tailWord_4375939 prefixEnd_4375939 2246960021755059852237929 := by
  unfold tailWord_4375939
  simp only [CollatzResearch.WordTrace]
  refine ⟨159603607293727828726666871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106402404862485219151111247 159603607293727828726666871)
  ·
    refine ⟨239405410940591743090000307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159603607293727828726666871 239405410940591743090000307)
    ·
      refine ⟨359108116410887614635000461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239405410940591743090000307 359108116410887614635000461)
      ·
        refine ⟨134665543654082855488125173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359108116410887614635000461 134665543654082855488125173)
        ·
          refine ⟨12624894717570267702011735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134665543654082855488125173 12624894717570267702011735)
          ·
            refine ⟨18937342076355401553017603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12624894717570267702011735 18937342076355401553017603)
            ·
              refine ⟨28406013114533102329526405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18937342076355401553017603 28406013114533102329526405)
              ·
                refine ⟨5326127458974956686786201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28406013114533102329526405 5326127458974956686786201)
                ·
                  refine ⟨3994595594231217515089651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326127458974956686786201 3994595594231217515089651)
                  ·
                    refine ⟨5991893391346826272634477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3994595594231217515089651 5991893391346826272634477)
                    ·
                      refine ⟨2246960021755059852237929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991893391346826272634477 2246960021755059852237929)
                      ·
                        rfl

theorem cell23_4375939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_4375939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375939 prefixEnd_4375939 := by exact prefixLift 4375939
  have htrace : WordTrace (prefixWord ++ tailWord_4375939) baseStart_4375939 baseEnd_4375939 := by
    simpa [prefixWord, tailWord_4375939, baseEnd_4375939] using wordTrace_append hprefix tailTrace_4375939
  have hstable : (prefixWord ++ tailWord_4375939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375939).length < 2 ^ (prefixWord ++ tailWord_4375939).sum := by decide
  have hdescent : baseEnd_4375939 < baseStart_4375939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375940 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_4375940 : Nat := 118140960795 + 4375940 * 2 ^ 59
def prefixEnd_4375940 : Nat := 4983230072969 + 3 ^ 40 * 4375940 * 2
def baseEnd_4375940 : Nat := 2246960535235714348325425

theorem tailTrace_4375940 : CollatzResearch.WordTrace tailWord_4375940 prefixEnd_4375940 2246960535235714348325425 := by
  unfold tailWord_4375940
  simp only [CollatzResearch.WordTrace]
  refine ⟨79801821883362102948726637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106402429177816137264968849 79801821883362102948726637)
  ·
    refine ⟨29925683206260788605772489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79801821883362102948726637 29925683206260788605772489)
    ·
      refine ⟨22444262404695591454329367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29925683206260788605772489 22444262404695591454329367)
      ·
        refine ⟨33666393607043387181494051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22444262404695591454329367 33666393607043387181494051)
        ·
          refine ⟨50499590410565080772241077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33666393607043387181494051 50499590410565080772241077)
          ·
            refine ⟨4734336600990476322397601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50499590410565080772241077 4734336600990476322397601)
            ·
              refine ⟨3550752450742857241798201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734336600990476322397601 3550752450742857241798201)
              ·
                refine ⟨2663064338057142931348651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550752450742857241798201 2663064338057142931348651)
                ·
                  refine ⟨3994596507085714397022977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663064338057142931348651 3994596507085714397022977)
                  ·
                    refine ⟨2995947380314285797767233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994596507085714397022977 2995947380314285797767233)
                    ·
                      refine ⟨2246960535235714348325425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995947380314285797767233 2246960535235714348325425)
                      ·
                        rfl

theorem cell23_4375940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_4375940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375940 prefixEnd_4375940 := by exact prefixLift 4375940
  have htrace : WordTrace (prefixWord ++ tailWord_4375940) baseStart_4375940 baseEnd_4375940 := by
    simpa [prefixWord, tailWord_4375940, baseEnd_4375940] using wordTrace_append hprefix tailTrace_4375940
  have hstable : (prefixWord ++ tailWord_4375940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375940).length < 2 ^ (prefixWord ++ tailWord_4375940).sum := by decide
  have hdescent : baseEnd_4375940 < baseStart_4375940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375956 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4375956 : Nat := 118140960795 + 4375956 * 2 ^ 59
def prefixEnd_4375956 : Nat := 4983230072969 + 3 ^ 40 * 4375956 * 2
def baseEnd_4375956 : Nat := 2246968750926186285725351

theorem tailTrace_4375956 : CollatzResearch.WordTrace tailWord_4375956 prefixEnd_4375956 2246968750926186285725351 := by
  unfold tailWord_4375956
  simp only [CollatzResearch.WordTrace]
  refine ⟨79802113667333120315017861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106402818223110827086690481 79802113667333120315017861)
  ·
    refine ⟨14962896312624960059065849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79802113667333120315017861 14962896312624960059065849)
    ·
      refine ⟨11222172234468720044299387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14962896312624960059065849 11222172234468720044299387)
      ·
        refine ⟨16833258351703080066449081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11222172234468720044299387 16833258351703080066449081)
        ·
          refine ⟨12624943763777310049836811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16833258351703080066449081 12624943763777310049836811)
          ·
            refine ⟨18937415645665965074755217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12624943763777310049836811 18937415645665965074755217)
            ·
              refine ⟨14203061734249473806066413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18937415645665965074755217 14203061734249473806066413)
              ·
                refine ⟨5326148150343552677274905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14203061734249473806066413 5326148150343552677274905)
                ·
                  refine ⟨3994611112757664507956179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326148150343552677274905 3994611112757664507956179)
                  ·
                    refine ⟨5991916669136496761934269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3994611112757664507956179 5991916669136496761934269)
                    ·
                      refine ⟨2246968750926186285725351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991916669136496761934269 2246968750926186285725351)
                      ·
                        rfl

theorem cell23_4375956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4375956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375956 prefixEnd_4375956 := by exact prefixLift 4375956
  have htrace : WordTrace (prefixWord ++ tailWord_4375956) baseStart_4375956 baseEnd_4375956 := by
    simpa [prefixWord, tailWord_4375956, baseEnd_4375956] using wordTrace_append hprefix tailTrace_4375956
  have hstable : (prefixWord ++ tailWord_4375956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375956).length < 2 ^ (prefixWord ++ tailWord_4375956).sum := by decide
  have hdescent : baseEnd_4375956 < baseStart_4375956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375985 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 9]
def baseStart_4375985 : Nat := 118140960795 + 4375985 * 2 ^ 59
def prefixEnd_4375985 : Nat := 4983230072969 + 3 ^ 40 * 4375985 * 2
def baseEnd_4375985 : Nat := 249664849096129630251413

theorem tailTrace_4375985 : CollatzResearch.WordTrace tailWord_4375985 prefixEnd_4375985 249664849096129630251413 := by
  unfold tailWord_4375985
  simp only [CollatzResearch.WordTrace]
  refine ⟨159605285051561178582841409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106403523367707452388560939 159605285051561178582841409)
  ·
    refine ⟨119703963788670883937131057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159605285051561178582841409 119703963788670883937131057)
    ·
      refine ⟨89777972841503162952848293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119703963788670883937131057 89777972841503162952848293)
      ·
        refine ⟨16833369907781843053659055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89777972841503162952848293 16833369907781843053659055)
        ·
          refine ⟨25250054861672764580488583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16833369907781843053659055 25250054861672764580488583)
          ·
            refine ⟨37875082292509146870732875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25250054861672764580488583 37875082292509146870732875)
            ·
              refine ⟨56812623438763720306099313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37875082292509146870732875 56812623438763720306099313)
              ·
                refine ⟨42609467579072790229574485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56812623438763720306099313 42609467579072790229574485)
                ·
                  refine ⟨249664849096129630251413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42609467579072790229574485 249664849096129630251413)
                  ·
                    rfl

theorem cell23_4375985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_4375985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375985 prefixEnd_4375985 := by exact prefixLift 4375985
  have htrace : WordTrace (prefixWord ++ tailWord_4375985) baseStart_4375985 baseEnd_4375985 := by
    simpa [prefixWord, tailWord_4375985, baseEnd_4375985] using wordTrace_append hprefix tailTrace_4375985
  have hstable : (prefixWord ++ tailWord_4375985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375985).length < 2 ^ (prefixWord ++ tailWord_4375985).sum := by decide
  have hdescent : baseEnd_4375985 < baseStart_4375985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376015 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 1, 7]
def baseStart_4376015 : Nat := 118140960795 + 4376015 * 2 ^ 59
def prefixEnd_4376015 : Nat := 4983230072969 + 3 ^ 40 * 4376015 * 2
def baseEnd_4376015 : Nat := 748999682094933851629193

theorem tailTrace_4376015 : CollatzResearch.WordTrace tailWord_4376015 prefixEnd_4376015 748999682094933851629193 := by
  unfold tailWord_4376015
  simp only [CollatzResearch.WordTrace]
  refine ⟨159606379241452493706433499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106404252827634995804288999 159606379241452493706433499)
  ·
    refine ⟨239409568862178740559650249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159606379241452493706433499 239409568862178740559650249)
    ·
      refine ⟨179557176646634055419737687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239409568862178740559650249 179557176646634055419737687)
      ·
        refine ⟨269335764969951083129606531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179557176646634055419737687 269335764969951083129606531)
        ·
          refine ⟨404003647454926624694409797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269335764969951083129606531 404003647454926624694409797)
          ·
            refine ⟨75750683897798742130201837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 404003647454926624694409797 75750683897798742130201837)
            ·
              refine ⟨28406506461674528298825689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75750683897798742130201837 28406506461674528298825689)
              ·
                refine ⟨21304879846255896224119267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28406506461674528298825689 21304879846255896224119267)
                ·
                  refine ⟨31957319769383844336178901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21304879846255896224119267 31957319769383844336178901)
                  ·
                    refine ⟨748999682094933851629193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31957319769383844336178901 748999682094933851629193)
                    ·
                      rfl

theorem cell23_4376015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_4376015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376015 prefixEnd_4376015 := by exact prefixLift 4376015
  have htrace : WordTrace (prefixWord ++ tailWord_4376015) baseStart_4376015 baseEnd_4376015 := by
    simpa [prefixWord, tailWord_4376015, baseEnd_4376015] using wordTrace_append hprefix tailTrace_4376015
  have hstable : (prefixWord ++ tailWord_4376015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376015).length < 2 ^ (prefixWord ++ tailWord_4376015).sum := by decide
  have hdescent : baseEnd_4376015 < baseStart_4376015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376053 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 5]
def baseStart_4376053 : Nat := 118140960795 + 4376053 * 2 ^ 59
def prefixEnd_4376053 : Nat := 4983230072969 + 3 ^ 40 * 4376053 * 2
def baseEnd_4376053 : Nat := 249668728727741378468045

theorem tailTrace_4376053 : CollatzResearch.WordTrace tailWord_4376053 prefixEnd_4376053 249668728727741378468045 := by
  unfold tailWord_4376053
  simp only [CollatzResearch.WordTrace]
  refine ⟨159607765215314826196316813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106405176810209884130877875 159607765215314826196316813)
  ·
    refine ⟨59852911955743059823618805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159607765215314826196316813 59852911955743059823618805)
    ·
      refine ⟨5611210495850911858464263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59852911955743059823618805 5611210495850911858464263)
      ·
        refine ⟨8416815743776367787696395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5611210495850911858464263 8416815743776367787696395)
        ·
          refine ⟨12625223615664551681544593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8416815743776367787696395 12625223615664551681544593)
          ·
            refine ⟨9468917711748413761158445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12625223615664551681544593 9468917711748413761158445)
            ·
              refine ⟨3550844141905655160434417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9468917711748413761158445 3550844141905655160434417)
              ·
                refine ⟨2663133106429241370325813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550844141905655160434417 2663133106429241370325813)
                ·
                  refine ⟨249668728727741378468045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663133106429241370325813 249668728727741378468045)
                  ·
                    rfl

theorem cell23_4376053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_4376053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376053 prefixEnd_4376053 := by exact prefixLift 4376053
  have htrace : WordTrace (prefixWord ++ tailWord_4376053) baseStart_4376053 baseEnd_4376053 := by
    simpa [prefixWord, tailWord_4376053, baseEnd_4376053] using wordTrace_append hprefix tailTrace_4376053
  have hstable : (prefixWord ++ tailWord_4376053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376053).length < 2 ^ (prefixWord ++ tailWord_4376053).sum := by decide
  have hdescent : baseEnd_4376053 < baseStart_4376053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376055 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_4376055 : Nat := 118140960795 + 4376055 * 2 ^ 59
def prefixEnd_4376055 : Nat := 4983230072969 + 3 ^ 40 * 4376055 * 2
def baseEnd_4376055 : Nat := 2247019585510981398387395

theorem tailTrace_4376055 : CollatzResearch.WordTrace tailWord_4376055 prefixEnd_4376055 2247019585510981398387395 := by
  unfold tailWord_4376055
  simp only [CollatzResearch.WordTrace]
  refine ⟨159607838161307580537889619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106405225440871720358593079 159607838161307580537889619)
  ·
    refine ⟨239411757241961370806834429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159607838161307580537889619 239411757241961370806834429)
    ·
      refine ⟨89779408965735514052562911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239411757241961370806834429 89779408965735514052562911)
      ·
        refine ⟨134669113448603271078844367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89779408965735514052562911 134669113448603271078844367)
        ·
          refine ⟨202003670172904906618266551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134669113448603271078844367 202003670172904906618266551)
          ·
            refine ⟨303005505259357359927399827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202003670172904906618266551 303005505259357359927399827)
            ·
              refine ⟨454508257889036039891099741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303005505259357359927399827 454508257889036039891099741)
              ·
                refine ⟨170440596708388514959162403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 454508257889036039891099741 170440596708388514959162403)
                ·
                  refine ⟨255660895062582772438743605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170440596708388514959162403 255660895062582772438743605)
                  ·
                    refine ⟨23968208912117134916132213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255660895062582772438743605 23968208912117134916132213)
                    ·
                      refine ⟨2247019585510981398387395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23968208912117134916132213 2247019585510981398387395)
                      ·
                        rfl

theorem cell23_4376055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_4376055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376055 prefixEnd_4376055 := by exact prefixLift 4376055
  have htrace : WordTrace (prefixWord ++ tailWord_4376055) baseStart_4376055 baseEnd_4376055 := by
    simpa [prefixWord, tailWord_4376055, baseEnd_4376055] using wordTrace_append hprefix tailTrace_4376055
  have hstable : (prefixWord ++ tailWord_4376055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376055).length < 2 ^ (prefixWord ++ tailWord_4376055).sum := by decide
  have hdescent : baseEnd_4376055 < baseStart_4376055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376072 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_4376072 : Nat := 118140960795 + 4376072 * 2 ^ 59
def prefixEnd_4376072 : Nat := 4983230072969 + 3 ^ 40 * 4376072 * 2
def baseEnd_4376072 : Nat := 2247028314682107831874817

theorem tailTrace_4376072 : CollatzResearch.WordTrace tailWord_4376072 prefixEnd_4376072 2247028314682107831874817 := by
  unfold tailWord_4376072
  simp only [CollatzResearch.WordTrace]
  refine ⟨79804229101122996220629235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106405638801497328294172313 79804229101122996220629235)
  ·
    refine ⟨119706343651684494330943853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79804229101122996220629235 119706343651684494330943853)
    ·
      refine ⟨44889878869381685374103945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119706343651684494330943853 44889878869381685374103945)
      ·
        refine ⟨33667409152036264030577959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44889878869381685374103945 33667409152036264030577959)
        ·
          refine ⟨50501113728054396045866939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33667409152036264030577959 50501113728054396045866939)
          ·
            refine ⟨75751670592081594068800409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50501113728054396045866939 75751670592081594068800409)
            ·
              refine ⟨56813752944061195551600307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75751670592081594068800409 56813752944061195551600307)
              ·
                refine ⟨85220629416091793327400461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56813752944061195551600307 85220629416091793327400461)
                ·
                  refine ⟨31957736031034422497775173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85220629416091793327400461 31957736031034422497775173)
                  ·
                    refine ⟨5992075505818954218332845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31957736031034422497775173 5992075505818954218332845)
                    ·
                      refine ⟨2247028314682107831874817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5992075505818954218332845 2247028314682107831874817)
                      ·
                        rfl

theorem cell23_4376072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_4376072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376072 prefixEnd_4376072 := by exact prefixLift 4376072
  have htrace : WordTrace (prefixWord ++ tailWord_4376072) baseStart_4376072 baseEnd_4376072 := by
    simpa [prefixWord, tailWord_4376072, baseEnd_4376072] using wordTrace_append hprefix tailTrace_4376072
  have hstable : (prefixWord ++ tailWord_4376072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376072).length < 2 ^ (prefixWord ++ tailWord_4376072).sum := by decide
  have hdescent : baseEnd_4376072 < baseStart_4376072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376122 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_4376122 : Nat := 118140960795 + 4376122 * 2 ^ 59
def prefixEnd_4376122 : Nat := 4983230072969 + 3 ^ 40 * 4376122 * 2
def baseEnd_4376122 : Nat := 749017996238277545416529

theorem tailTrace_4376122 : CollatzResearch.WordTrace tailWord_4376122 prefixEnd_4376122 749017996238277545416529 := by
  unfold tailWord_4376122
  simp only [CollatzResearch.WordTrace]
  refine ⟨39902570463016212745144655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106406854568043233987052413 39902570463016212745144655)
  ·
    refine ⟨59853855694524319117716983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39902570463016212745144655 59853855694524319117716983)
    ·
      refine ⟨89780783541786478676575475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59853855694524319117716983 89780783541786478676575475)
      ·
        refine ⟨134671175312679718014863213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89780783541786478676575475 134671175312679718014863213)
        ·
          refine ⟨50501690742254894255573705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134671175312679718014863213 50501690742254894255573705)
          ·
            refine ⟨37876268056691170691680279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50501690742254894255573705 37876268056691170691680279)
            ·
              refine ⟨56814402085036756037520419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37876268056691170691680279 56814402085036756037520419)
              ·
                refine ⟨85221603127555134056280629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56814402085036756037520419 85221603127555134056280629)
                ·
                  refine ⟨7989525293208293817776309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85221603127555134056280629 7989525293208293817776309)
                  ·
                    refine ⟨749017996238277545416529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7989525293208293817776309 749017996238277545416529)
                    ·
                      rfl

theorem cell23_4376122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_4376122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376122 prefixEnd_4376122 := by exact prefixLift 4376122
  have htrace : WordTrace (prefixWord ++ tailWord_4376122) baseStart_4376122 baseEnd_4376122 := by
    simpa [prefixWord, tailWord_4376122, baseEnd_4376122] using wordTrace_append hprefix tailTrace_4376122
  have hstable : (prefixWord ++ tailWord_4376122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376122).length < 2 ^ (prefixWord ++ tailWord_4376122).sum := by decide
  have hdescent : baseEnd_4376122 < baseStart_4376122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376146 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_4376146 : Nat := 118140960795 + 4376146 * 2 ^ 59
def prefixEnd_4376146 : Nat := 4983230072969 + 3 ^ 40 * 4376146 * 2
def baseEnd_4376146 : Nat := 2247066312250540542349477

theorem tailTrace_4376146 : CollatzResearch.WordTrace tailWord_4376146 prefixEnd_4376146 2247066312250540542349477 := by
  unfold tailWord_4376146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39902789300994475769863073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106407438135985268719634861 39902789300994475769863073)
  ·
    refine ⟨29927091975745856827397305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39902789300994475769863073 29927091975745856827397305)
    ·
      refine ⟨22445318981809392620547979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29927091975745856827397305 22445318981809392620547979)
      ·
        refine ⟨33667978472714088930821969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22445318981809392620547979 33667978472714088930821969)
        ·
          refine ⟨25250983854535566698116477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33667978472714088930821969 25250983854535566698116477)
          ·
            refine ⟨9469118945450837511793679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25250983854535566698116477 9469118945450837511793679)
            ·
              refine ⟨14203678418176256267690519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469118945450837511793679 14203678418176256267690519)
              ·
                refine ⟨21305517627264384401535779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14203678418176256267690519 21305517627264384401535779)
                ·
                  refine ⟨31958276440896576602303669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21305517627264384401535779 31958276440896576602303669)
                  ·
                    refine ⟨2996088416334054056465969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31958276440896576602303669 2996088416334054056465969)
                    ·
                      refine ⟨2247066312250540542349477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996088416334054056465969 2247066312250540542349477)
                      ·
                        rfl

theorem cell23_4376146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_4376146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376146 prefixEnd_4376146 := by exact prefixLift 4376146
  have htrace : WordTrace (prefixWord ++ tailWord_4376146) baseStart_4376146 baseEnd_4376146 := by
    simpa [prefixWord, tailWord_4376146, baseEnd_4376146] using wordTrace_append hprefix tailTrace_4376146
  have hstable : (prefixWord ++ tailWord_4376146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376146).length < 2 ^ (prefixWord ++ tailWord_4376146).sum := by decide
  have hdescent : baseEnd_4376146 < baseStart_4376146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376156 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4376156 : Nat := 118140960795 + 4376156 * 2 ^ 59
def prefixEnd_4376156 : Nat := 4983230072969 + 3 ^ 40 * 4376156 * 2
def baseEnd_4376156 : Nat := 749023815685695167741477

theorem tailTrace_4376156 : CollatzResearch.WordTrace tailWord_4376156 prefixEnd_4376156 749023815685695167741477 := by
  unfold tailWord_4376156
  simp only [CollatzResearch.WordTrace]
  refine ⟨79805760966970837393658161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106407681289294449858210881 79805760966970837393658161)
  ·
    refine ⟨59854320725228128045243621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79805760966970837393658161 59854320725228128045243621)
    ·
      refine ⟨11222685135980274008483179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59854320725228128045243621 11222685135980274008483179)
      ·
        refine ⟨16834027703970411012724769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11222685135980274008483179 16834027703970411012724769)
        ·
          refine ⟨12625520777977808259543577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16834027703970411012724769 12625520777977808259543577)
          ·
            refine ⟨9469140583483356194657683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12625520777977808259543577 9469140583483356194657683)
            ·
              refine ⟨14203710875225034291986525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469140583483356194657683 14203710875225034291986525)
              ·
                refine ⟨5326391578209387859494947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14203710875225034291986525 5326391578209387859494947)
                ·
                  refine ⟨7989587367314081789242421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326391578209387859494947 7989587367314081789242421)
                  ·
                    refine ⟨749023815685695167741477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7989587367314081789242421 749023815685695167741477)
                    ·
                      rfl

theorem cell23_4376156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4376156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376156 prefixEnd_4376156 := by exact prefixLift 4376156
  have htrace : WordTrace (prefixWord ++ tailWord_4376156) baseStart_4376156 baseEnd_4376156 := by
    simpa [prefixWord, tailWord_4376156, baseEnd_4376156] using wordTrace_append hprefix tailTrace_4376156
  have hstable : (prefixWord ++ tailWord_4376156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376156).length < 2 ^ (prefixWord ++ tailWord_4376156).sum := by decide
  have hdescent : baseEnd_4376156 < baseStart_4376156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376172 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_4376172 : Nat := 118140960795 + 4376172 * 2 ^ 59
def prefixEnd_4376172 : Nat := 4983230072969 + 3 ^ 40 * 4376172 * 2
def baseEnd_4376172 : Nat := 2247079662747557440624357

theorem tailTrace_4376172 : CollatzResearch.WordTrace tailWord_4376172 prefixEnd_4376172 2247079662747557440624357 := by
  unfold tailWord_4376172
  simp only [CollatzResearch.WordTrace]
  refine ⟨79806052750941854759949385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106408070334589139679932513 79806052750941854759949385)
  ·
    refine ⟨59854539563206391069962039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79806052750941854759949385 59854539563206391069962039)
    ·
      refine ⟨89781809344809586604943059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59854539563206391069962039 89781809344809586604943059)
      ·
        refine ⟨134672714017214379907414589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89781809344809586604943059 134672714017214379907414589)
        ·
          refine ⟨50502267756455392465280471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134672714017214379907414589 50502267756455392465280471)
          ·
            refine ⟨75753401634683088697920707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50502267756455392465280471 75753401634683088697920707)
            ·
              refine ⟨113630102452024633046881061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75753401634683088697920707 113630102452024633046881061)
              ·
                refine ⟨21305644209754618696290199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113630102452024633046881061 21305644209754618696290199)
                ·
                  refine ⟨31958466314631928044435299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21305644209754618696290199 31958466314631928044435299)
                  ·
                    refine ⟨47937699471947892066652949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31958466314631928044435299 47937699471947892066652949)
                    ·
                      refine ⟨2247079662747557440624357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47937699471947892066652949 2247079662747557440624357)
                      ·
                        rfl

theorem cell23_4376172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_4376172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376172 prefixEnd_4376172 := by exact prefixLift 4376172
  have htrace : WordTrace (prefixWord ++ tailWord_4376172) baseStart_4376172 baseEnd_4376172 := by
    simpa [prefixWord, tailWord_4376172, baseEnd_4376172] using wordTrace_append hprefix tailTrace_4376172
  have hstable : (prefixWord ++ tailWord_4376172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376172).length < 2 ^ (prefixWord ++ tailWord_4376172).sum := by decide
  have hdescent : baseEnd_4376172 < baseStart_4376172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376189 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_4376189 : Nat := 118140960795 + 4376189 * 2 ^ 59
def prefixEnd_4376189 : Nat := 4983230072969 + 3 ^ 40 * 4376189 * 2
def baseEnd_4376189 : Nat := 2247088391918683874111779

theorem tailTrace_4376189 : CollatzResearch.WordTrace tailWord_4376189 prefixEnd_4376189 2247088391918683874111779 := by
  unfold tailWord_4376189
  simp only [CollatzResearch.WordTrace]
  refine ⟨159612725542822121423267621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106408483695214747615511747 159612725542822121423267621)
  ·
    refine ⟨29927386039279147766862679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159612725542822121423267621 29927386039279147766862679)
    ·
      refine ⟨44891079058918721650294019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29927386039279147766862679 44891079058918721650294019)
      ·
        refine ⟨67336618588378082475441029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44891079058918721650294019 67336618588378082475441029)
        ·
          refine ⟨12625615985320890464145193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67336618588378082475441029 12625615985320890464145193)
          ·
            refine ⟨9469211988990667848108895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12625615985320890464145193 9469211988990667848108895)
            ·
              refine ⟨14203817983486001772163343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469211988990667848108895 14203817983486001772163343)
              ·
                refine ⟨21305726975229002658245015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14203817983486001772163343 21305726975229002658245015)
                ·
                  refine ⟨31958590462843503987367523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21305726975229002658245015 31958590462843503987367523)
                  ·
                    refine ⟨47937885694265255981051285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31958590462843503987367523 47937885694265255981051285)
                    ·
                      refine ⟨2247088391918683874111779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47937885694265255981051285 2247088391918683874111779)
                      ·
                        rfl

theorem cell23_4376189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_4376189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376189 prefixEnd_4376189 := by exact prefixLift 4376189
  have htrace : WordTrace (prefixWord ++ tailWord_4376189) baseStart_4376189 baseEnd_4376189 := by
    simpa [prefixWord, tailWord_4376189, baseEnd_4376189] using wordTrace_append hprefix tailTrace_4376189
  have hstable : (prefixWord ++ tailWord_4376189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376189).length < 2 ^ (prefixWord ++ tailWord_4376189).sum := by decide
  have hdescent : baseEnd_4376189 < baseStart_4376189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376193 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_4376193 : Nat := 118140960795 + 4376193 * 2 ^ 59
def prefixEnd_4376193 : Nat := 4983230072969 + 3 ^ 40 * 4376193 * 2
def baseEnd_4376193 : Nat := 2247090445841301858461761

theorem tailTrace_4376193 : CollatzResearch.WordTrace tailWord_4376193 prefixEnd_4376193 2247090445841301858461761 := by
  unfold tailWord_4376193
  simp only [CollatzResearch.WordTrace]
  refine ⟨159612871434807630106413233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106408580956538420070942155 159612871434807630106413233)
  ·
    refine ⟨119709653576105722579809925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159612871434807630106413233 119709653576105722579809925)
    ·
      refine ⟨22445560045519822983714361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119709653576105722579809925 22445560045519822983714361)
      ·
        refine ⟨16834170034139867237785771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22445560045519822983714361 16834170034139867237785771)
        ·
          refine ⟨25251255051209800856678657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16834170034139867237785771 25251255051209800856678657)
          ·
            refine ⟨18938441288407350642508993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25251255051209800856678657 18938441288407350642508993)
            ·
              refine ⟨14203830966305512981881745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18938441288407350642508993 14203830966305512981881745)
              ·
                refine ⟨10652873224729134736411309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14203830966305512981881745 10652873224729134736411309)
                ·
                  refine ⟨3994827459273425526154241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10652873224729134736411309 3994827459273425526154241)
                  ·
                    refine ⟨2996120594455069144615681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994827459273425526154241 2996120594455069144615681)
                    ·
                      refine ⟨2247090445841301858461761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996120594455069144615681 2247090445841301858461761)
                      ·
                        rfl

theorem cell23_4376193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_4376193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376193 prefixEnd_4376193 := by exact prefixLift 4376193
  have htrace : WordTrace (prefixWord ++ tailWord_4376193) baseStart_4376193 baseEnd_4376193 := by
    simpa [prefixWord, tailWord_4376193, baseEnd_4376193] using wordTrace_append hprefix tailTrace_4376193
  have hstable : (prefixWord ++ tailWord_4376193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376193).length < 2 ^ (prefixWord ++ tailWord_4376193).sum := by decide
  have hdescent : baseEnd_4376193 < baseStart_4376193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376199 : List Nat := [1, 1, 4, 2, 1, 3, 4, 7]
def baseStart_4376199 : Nat := 118140960795 + 4376199 * 2 ^ 59
def prefixEnd_4376199 : Nat := 4983230072969 + 3 ^ 40 * 4376199 * 2
def baseEnd_4376199 : Nat := 83225686175008475369879

theorem tailTrace_4376199 : CollatzResearch.WordTrace tailWord_4376199 prefixEnd_4376199 83225686175008475369879 := by
  unfold tailWord_4376199
  simp only [CollatzResearch.WordTrace]
  refine ⟨159613090272785893131131651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106408726848523928754087767 159613090272785893131131651)
  ·
    refine ⟨239419635409178839696697477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159613090272785893131131651 239419635409178839696697477)
    ·
      refine ⟨44891181639221032443130777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239419635409178839696697477 44891181639221032443130777)
      ·
        refine ⟨33668386229415774332348083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44891181639221032443130777 33668386229415774332348083)
        ·
          refine ⟨50502579344123661498522125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33668386229415774332348083 50502579344123661498522125)
          ·
            refine ⟨18938467254046373061945797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50502579344123661498522125 18938467254046373061945797)
            ·
              refine ⟨3550962610133694949114837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18938467254046373061945797 3550962610133694949114837)
              ·
                refine ⟨83225686175008475369879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3550962610133694949114837 83225686175008475369879)
                ·
                  rfl

theorem cell23_4376199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 7].length) (baseStart_4376199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376199 prefixEnd_4376199 := by exact prefixLift 4376199
  have htrace : WordTrace (prefixWord ++ tailWord_4376199) baseStart_4376199 baseEnd_4376199 := by
    simpa [prefixWord, tailWord_4376199, baseEnd_4376199] using wordTrace_append hprefix tailTrace_4376199
  have hstable : (prefixWord ++ tailWord_4376199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376199).length < 2 ^ (prefixWord ++ tailWord_4376199).sum := by decide
  have hdescent : baseEnd_4376199 < baseStart_4376199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376270 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_4376270 : Nat := 118140960795 + 4376270 * 2 ^ 59
def prefixEnd_4376270 : Nat := 4983230072969 + 3 ^ 40 * 4376270 * 2
def baseEnd_4376270 : Nat := 2247129983851698057198907

theorem tailTrace_4376270 : CollatzResearch.WordTrace tailWord_4376270 prefixEnd_4376270 2247129983851698057198907 := by
  unfold tailWord_4376270
  simp only [CollatzResearch.WordTrace]
  refine ⟨19951959981941084032120783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106410453237019114837977509 19951959981941084032120783)
  ·
    refine ⟨29927939972911626048181175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19951959981941084032120783 29927939972911626048181175)
    ·
      refine ⟨44891909959367439072271763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29927939972911626048181175 44891909959367439072271763)
      ·
        refine ⟨67337864939051158608407645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44891909959367439072271763 67337864939051158608407645)
        ·
          refine ⟨25251699352144184478152867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67337864939051158608407645 25251699352144184478152867)
          ·
            refine ⟨37877549028216276717229301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25251699352144184478152867 37877549028216276717229301)
            ·
              refine ⟨3551020221395275942240247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37877549028216276717229301 3551020221395275942240247)
              ·
                refine ⟨5326530332092913913360371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551020221395275942240247 5326530332092913913360371)
                ·
                  refine ⟨7989795498139370870040557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326530332092913913360371 7989795498139370870040557)
                  ·
                    refine ⟨2996173311802264076265209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7989795498139370870040557 2996173311802264076265209)
                    ·
                      refine ⟨2247129983851698057198907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996173311802264076265209 2247129983851698057198907)
                      ·
                        rfl

theorem cell23_4376270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_4376270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376270 prefixEnd_4376270 := by exact prefixLift 4376270
  have htrace : WordTrace (prefixWord ++ tailWord_4376270) baseStart_4376270 baseEnd_4376270 := by
    simpa [prefixWord, tailWord_4376270, baseEnd_4376270] using wordTrace_append hprefix tailTrace_4376270
  have hstable : (prefixWord ++ tailWord_4376270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376270).length < 2 ^ (prefixWord ++ tailWord_4376270).sum := by decide
  have hdescent : baseEnd_4376270 < baseStart_4376270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376272 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 11]
def baseStart_4376272 : Nat := 118140960795 + 4376272 * 2 ^ 59
def prefixEnd_4376272 : Nat := 4983230072969 + 3 ^ 40 * 4376272 * 2
def baseEnd_4376272 : Nat := 249681223423667449930433

theorem tailTrace_4376272 : CollatzResearch.WordTrace tailWord_4376272 prefixEnd_4376272 249681223423667449930433 := by
  unfold tailWord_4376272
  simp only [CollatzResearch.WordTrace]
  refine ⟨79807876400760713299269535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106410501867680951065692713 79807876400760713299269535)
  ·
    refine ⟨119711814601141069948904303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79807876400760713299269535 119711814601141069948904303)
    ·
      refine ⟨179567721901711604923356455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119711814601141069948904303 179567721901711604923356455)
      ·
        refine ⟨269351582852567407385034683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179567721901711604923356455 269351582852567407385034683)
        ·
          refine ⟨404027374278851111077552025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269351582852567407385034683 404027374278851111077552025)
          ·
            refine ⟨303020530709138333308164019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404027374278851111077552025 303020530709138333308164019)
            ·
              refine ⟨454530796063707499962246029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303020530709138333308164019 454530796063707499962246029)
              ·
                refine ⟨170449048523890312485842261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 454530796063707499962246029 170449048523890312485842261)
                ·
                  refine ⟨249681223423667449930433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 170449048523890312485842261 249681223423667449930433)
                  ·
                    rfl

theorem cell23_4376272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_4376272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376272 prefixEnd_4376272 := by exact prefixLift 4376272
  have htrace : WordTrace (prefixWord ++ tailWord_4376272) baseStart_4376272 baseEnd_4376272 := by
    simpa [prefixWord, tailWord_4376272, baseEnd_4376272] using wordTrace_append hprefix tailTrace_4376272
  have hstable : (prefixWord ++ tailWord_4376272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376272).length < 2 ^ (prefixWord ++ tailWord_4376272).sum := by decide
  have hdescent : baseEnd_4376272 < baseStart_4376272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376278 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4376278 : Nat := 118140960795 + 4376278 * 2 ^ 59
def prefixEnd_4376278 : Nat := 4983230072969 + 3 ^ 40 * 4376278 * 2
def baseEnd_4376278 : Nat := 2247134091696934025898871

theorem tailTrace_4376278 : CollatzResearch.WordTrace tailWord_4376278 prefixEnd_4376278 2247134091696934025898871 := by
  unfold tailWord_4376278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9975998227468730601453593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106410647759666459748838325 9975998227468730601453593)
  ·
    refine ⟨7481998670601547951090195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9975998227468730601453593 7481998670601547951090195)
    ·
      refine ⟨11222998005902321926635293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7481998670601547951090195 11222998005902321926635293)
      ·
        refine ⟨4208624252213370722488235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11222998005902321926635293 4208624252213370722488235)
        ·
          refine ⟨6312936378320056083732353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208624252213370722488235 6312936378320056083732353)
          ·
            refine ⟨4734702283740042062799265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6312936378320056083732353 4734702283740042062799265)
            ·
              refine ⟨3551026712805031547099449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734702283740042062799265 3551026712805031547099449)
              ·
                refine ⟨2663270034603773660324587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3551026712805031547099449 2663270034603773660324587)
                ·
                  refine ⟨3994905051905660490486881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663270034603773660324587 3994905051905660490486881)
                  ·
                    refine ⟨2996178788929245367865161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994905051905660490486881 2996178788929245367865161)
                    ·
                      refine ⟨2247134091696934025898871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996178788929245367865161 2247134091696934025898871)
                      ·
                        rfl

theorem cell23_4376278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4376278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376278 prefixEnd_4376278 := by exact prefixLift 4376278
  have htrace : WordTrace (prefixWord ++ tailWord_4376278) baseStart_4376278 baseEnd_4376278 := by
    simpa [prefixWord, tailWord_4376278, baseEnd_4376278] using wordTrace_append hprefix tailTrace_4376278
  have hstable : (prefixWord ++ tailWord_4376278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376278).length < 2 ^ (prefixWord ++ tailWord_4376278).sum := by decide
  have hdescent : baseEnd_4376278 < baseStart_4376278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376279 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_4376279 : Nat := 118140960795 + 4376279 * 2 ^ 59
def prefixEnd_4376279 : Nat := 4983230072969 + 3 ^ 40 * 4376279 * 2
def baseEnd_4376279 : Nat := 2247134605177588521986365

theorem tailTrace_4376279 : CollatzResearch.WordTrace tailWord_4376279 prefixEnd_4376279 2247134605177588521986365 := by
  unfold tailWord_4376279
  simp only [CollatzResearch.WordTrace]
  refine ⟨159616008112496066794043891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106410672074997377862695927 159616008112496066794043891)
  ·
    refine ⟨239424012168744100191065837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159616008112496066794043891 239424012168744100191065837)
    ·
      refine ⟨89784004563279037571649689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239424012168744100191065837 89784004563279037571649689)
      ·
        refine ⟨67338003422459278178737267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89784004563279037571649689 67338003422459278178737267)
        ·
          refine ⟨101007005133688917268105901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67338003422459278178737267 101007005133688917268105901)
          ·
            refine ⟨37877626925133343975539713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101007005133688917268105901 37877626925133343975539713)
            ·
              refine ⟨28408220193850007981654785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37877626925133343975539713 28408220193850007981654785)
              ·
                refine ⟨21306165145387505986241089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28408220193850007981654785 21306165145387505986241089)
                ·
                  refine ⟨15979623859040629489680817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21306165145387505986241089 15979623859040629489680817)
                  ·
                    refine ⟨11984717894280472117260613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15979623859040629489680817 11984717894280472117260613)
                    ·
                      refine ⟨2247134605177588521986365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11984717894280472117260613 2247134605177588521986365)
                      ·
                        rfl

theorem cell23_4376279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_4376279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376279 prefixEnd_4376279 := by exact prefixLift 4376279
  have htrace : WordTrace (prefixWord ++ tailWord_4376279) baseStart_4376279 baseEnd_4376279 := by
    simpa [prefixWord, tailWord_4376279, baseEnd_4376279] using wordTrace_append hprefix tailTrace_4376279
  have hstable : (prefixWord ++ tailWord_4376279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376279).length < 2 ^ (prefixWord ++ tailWord_4376279).sum := by decide
  have hdescent : baseEnd_4376279 < baseStart_4376279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376296 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4376296 : Nat := 118140960795 + 4376296 * 2 ^ 59
def prefixEnd_4376296 : Nat := 4983230072969 + 3 ^ 40 * 4376296 * 2
def baseEnd_4376296 : Nat := 2247143334348714955473787

theorem tailTrace_4376296 : CollatzResearch.WordTrace tailWord_4376296 prefixEnd_4376296 2247143334348714955473787 := by
  unfold tailWord_4376296
  simp only [CollatzResearch.WordTrace]
  refine ⟨79808314076717239348706371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106411085435622985798275161 79808314076717239348706371)
  ·
    refine ⟨119712471115075859023059557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79808314076717239348706371 119712471115075859023059557)
    ·
      refine ⟨22446088334076723566823667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119712471115075859023059557 22446088334076723566823667)
      ·
        refine ⟨33669132501115085350235501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22446088334076723566823667 33669132501115085350235501)
        ·
          refine ⟨12625924687918157006338313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33669132501115085350235501 12625924687918157006338313)
          ·
            refine ⟨9469443515938617754753735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12625924687918157006338313 9469443515938617754753735)
            ·
              refine ⟨14204165273907926632130603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469443515938617754753735 14204165273907926632130603)
              ·
                refine ⟨21306247910861889948195905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14204165273907926632130603 21306247910861889948195905)
                ·
                  refine ⟨15979685933146417461146929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21306247910861889948195905 15979685933146417461146929)
                  ·
                    refine ⟨11984764449859813095860197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15979685933146417461146929 11984764449859813095860197)
                    ·
                      refine ⟨2247143334348714955473787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11984764449859813095860197 2247143334348714955473787)
                      ·
                        rfl

theorem cell23_4376296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4376296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376296 prefixEnd_4376296 := by exact prefixLift 4376296
  have htrace : WordTrace (prefixWord ++ tailWord_4376296) baseStart_4376296 baseEnd_4376296 := by
    simpa [prefixWord, tailWord_4376296, baseEnd_4376296] using wordTrace_append hprefix tailTrace_4376296
  have hstable : (prefixWord ++ tailWord_4376296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376296).length < 2 ^ (prefixWord ++ tailWord_4376296).sum := by decide
  have hdescent : baseEnd_4376296 < baseStart_4376296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376299 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 3]
def baseStart_4376299 : Nat := 118140960795 + 4376299 * 2 ^ 59
def prefixEnd_4376299 : Nat := 4983230072969 + 3 ^ 40 * 4376299 * 2
def baseEnd_4376299 : Nat := 2247144874790678443736273

theorem tailTrace_4376299 : CollatzResearch.WordTrace tailWord_4376299 prefixEnd_4376299 2247144874790678443736273 := by
  unfold tailWord_4376299
  simp only [CollatzResearch.WordTrace]
  refine ⟨159616737572423610209771951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106411158381615740139847967 159616737572423610209771951)
  ·
    refine ⟨239425106358635415314657927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159616737572423610209771951 239425106358635415314657927)
    ·
      refine ⟨359137659537953122971986891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239425106358635415314657927 359137659537953122971986891)
      ·
        refine ⟨538706489306929684457980337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359137659537953122971986891 538706489306929684457980337)
        ·
          refine ⟨404029866980197263343485253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538706489306929684457980337 404029866980197263343485253)
          ·
            refine ⟨75755600058786986876903485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 404029866980197263343485253 75755600058786986876903485)
            ·
              refine ⟨28408350022045120078838807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75755600058786986876903485 28408350022045120078838807)
              ·
                refine ⟨42612525033067680118258211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28408350022045120078838807 42612525033067680118258211)
                ·
                  refine ⟨63918787549601520177387317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42612525033067680118258211 63918787549601520177387317)
                  ·
                    refine ⟨5992386332775142516630061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63918787549601520177387317 5992386332775142516630061)
                    ·
                      refine ⟨2247144874790678443736273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5992386332775142516630061 2247144874790678443736273)
                      ·
                        rfl

theorem cell23_4376299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 3].length) (baseStart_4376299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376299 prefixEnd_4376299 := by exact prefixLift 4376299
  have htrace : WordTrace (prefixWord ++ tailWord_4376299) baseStart_4376299 baseEnd_4376299 := by
    simpa [prefixWord, tailWord_4376299, baseEnd_4376299] using wordTrace_append hprefix tailTrace_4376299
  have hstable : (prefixWord ++ tailWord_4376299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376299).length < 2 ^ (prefixWord ++ tailWord_4376299).sum := by decide
  have hdescent : baseEnd_4376299 < baseStart_4376299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376356 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_4376356 : Nat := 118140960795 + 4376356 * 2 ^ 59
def prefixEnd_4376356 : Nat := 4983230072969 + 3 ^ 40 * 4376356 * 2
def baseEnd_4376356 : Nat := 2247174143187984720723511

theorem tailTrace_4376356 : CollatzResearch.WordTrace tailWord_4376356 prefixEnd_4376356 2247174143187984720723511 := by
  unfold tailWord_4376356
  simp only [CollatzResearch.WordTrace]
  refine ⟨79809408266608554472298461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106412544355478072629731281 79809408266608554472298461)
  ·
    refine ⟨29928528099978207927111923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79809408266608554472298461 29928528099978207927111923)
    ·
      refine ⟨44892792149967311890667885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29928528099978207927111923 44892792149967311890667885)
      ·
        refine ⟨16834797056237741959000457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44892792149967311890667885 16834797056237741959000457)
        ·
          refine ⟨12626097792178306469250343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16834797056237741959000457 12626097792178306469250343)
          ·
            refine ⟨18939146688267459703875515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12626097792178306469250343 18939146688267459703875515)
            ·
              refine ⟨28408720032401189555813273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18939146688267459703875515 28408720032401189555813273)
              ·
                refine ⟨21306540024300892166859955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28408720032401189555813273 21306540024300892166859955)
                ·
                  refine ⟨31959810036451338250289933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21306540024300892166859955 31959810036451338250289933)
                  ·
                    refine ⟨11984928763669251843858725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31959810036451338250289933 11984928763669251843858725)
                    ·
                      refine ⟨2247174143187984720723511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11984928763669251843858725 2247174143187984720723511)
                      ·
                        rfl

theorem cell23_4376356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_4376356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376356 prefixEnd_4376356 := by exact prefixLift 4376356
  have htrace : WordTrace (prefixWord ++ tailWord_4376356) baseStart_4376356 baseEnd_4376356 := by
    simpa [prefixWord, tailWord_4376356, baseEnd_4376356] using wordTrace_append hprefix tailTrace_4376356
  have hstable : (prefixWord ++ tailWord_4376356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376356).length < 2 ^ (prefixWord ++ tailWord_4376356).sum := by decide
  have hdescent : baseEnd_4376356 < baseStart_4376356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376376 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_4376376 : Nat := 118140960795 + 4376376 * 2 ^ 59
def prefixEnd_4376376 : Nat := 4983230072969 + 3 ^ 40 * 4376376 * 2
def baseEnd_4376376 : Nat := 2247184412801074642473419

theorem tailTrace_4376376 : CollatzResearch.WordTrace tailWord_4376376 prefixEnd_4376376 2247184412801074642473419 := by
  unfold tailWord_4376376
  simp only [CollatzResearch.WordTrace]
  refine ⟨79809772996572326180162491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106413030662096434906883321 79809772996572326180162491)
  ·
    refine ⟨119714659494858489270243737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79809772996572326180162491 119714659494858489270243737)
    ·
      refine ⟨89785994621143866952682803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119714659494858489270243737 89785994621143866952682803)
      ·
        refine ⟨134678991931715800429024205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89785994621143866952682803 134678991931715800429024205)
        ·
          refine ⟨50504621974393425160884077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134678991931715800429024205 50504621974393425160884077)
          ·
            refine ⟨18939233240397534435331529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50504621974393425160884077 18939233240397534435331529)
            ·
              refine ⟨14204424930298150826498647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18939233240397534435331529 14204424930298150826498647)
              ·
                refine ⟨21306637395447226239747971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14204424930298150826498647 21306637395447226239747971)
                ·
                  refine ⟨31959956093170839359621957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21306637395447226239747971 31959956093170839359621957)
                  ·
                    refine ⟨5992491767469532379929117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31959956093170839359621957 5992491767469532379929117)
                    ·
                      refine ⟨2247184412801074642473419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5992491767469532379929117 2247184412801074642473419)
                      ·
                        rfl

theorem cell23_4376376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_4376376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376376 prefixEnd_4376376 := by exact prefixLift 4376376
  have htrace : WordTrace (prefixWord ++ tailWord_4376376) baseStart_4376376 baseEnd_4376376 := by
    simpa [prefixWord, tailWord_4376376, baseEnd_4376376] using wordTrace_append hprefix tailTrace_4376376
  have hstable : (prefixWord ++ tailWord_4376376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376376).length < 2 ^ (prefixWord ++ tailWord_4376376).sum := by decide
  have hdescent : baseEnd_4376376 < baseStart_4376376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376390 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4376390 : Nat := 118140960795 + 4376390 * 2 ^ 59
def prefixEnd_4376390 : Nat := 4983230072969 + 3 ^ 40 * 4376390 * 2
def baseEnd_4376390 : Nat := 2247191601530237587698355

theorem tailTrace_4376390 : CollatzResearch.WordTrace tailWord_4376390 prefixEnd_4376390 2247191601530237587698355 := by
  unfold tailWord_4376390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988126769221685398479207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106413371076729288500889749 4988126769221685398479207)
  ·
    refine ⟨7482190153832528097718811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4988126769221685398479207 7482190153832528097718811)
    ·
      refine ⟨11223285230748792146578217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482190153832528097718811 11223285230748792146578217)
      ·
        refine ⟨8417463923061594109933663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11223285230748792146578217 8417463923061594109933663)
        ·
          refine ⟨12626195884592391164900495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8417463923061594109933663 12626195884592391164900495)
          ·
            refine ⟨18939293826888586747350743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12626195884592391164900495 18939293826888586747350743)
            ·
              refine ⟨28408940740332880121026115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18939293826888586747350743 28408940740332880121026115)
              ·
                refine ⟨42613411110499320181539173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28408940740332880121026115 42613411110499320181539173)
                ·
                  refine ⟨7990014583218622534038595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42613411110499320181539173 7990014583218622534038595)
                  ·
                    refine ⟨11985021874827933801057893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7990014583218622534038595 11985021874827933801057893)
                    ·
                      refine ⟨2247191601530237587698355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11985021874827933801057893 2247191601530237587698355)
                      ·
                        rfl

theorem cell23_4376390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4376390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376390 prefixEnd_4376390 := by exact prefixLift 4376390
  have htrace : WordTrace (prefixWord ++ tailWord_4376390) baseStart_4376390 baseEnd_4376390 := by
    simpa [prefixWord, tailWord_4376390, baseEnd_4376390] using wordTrace_append hprefix tailTrace_4376390
  have hstable : (prefixWord ++ tailWord_4376390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376390).length < 2 ^ (prefixWord ++ tailWord_4376390).sum := by decide
  have hdescent : baseEnd_4376390 < baseStart_4376390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376423 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_4376423 : Nat := 118140960795 + 4376423 * 2 ^ 59
def prefixEnd_4376423 : Nat := 4983230072969 + 3 ^ 40 * 4376423 * 2
def baseEnd_4376423 : Nat := 2247208546391835958585703

theorem tailTrace_4376423 : CollatzResearch.WordTrace tailWord_4376423 prefixEnd_4376423 2247208546391835958585703 := by
  unfold tailWord_4376423
  simp only [CollatzResearch.WordTrace]
  refine ⟨159621260223974379387285923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106414173482649586258190615 159621260223974379387285923)
  ·
    refine ⟨239431890335961569080928885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159621260223974379387285923 239431890335961569080928885)
    ·
      refine ⟨22446739718996397101337083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239431890335961569080928885 22446739718996397101337083)
      ·
        refine ⟨33670109578494595652005625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22446739718996397101337083 33670109578494595652005625)
        ·
          refine ⟨25252582183870946739004219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33670109578494595652005625 25252582183870946739004219)
          ·
            refine ⟨37878873275806420108506329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25252582183870946739004219 37878873275806420108506329)
            ·
              refine ⟨28409154956854815081379747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37878873275806420108506329 28409154956854815081379747)
              ·
                refine ⟨42613732435282222622069621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28409154956854815081379747 42613732435282222622069621)
                ·
                  refine ⟨3995037415807708370819027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42613732435282222622069621 3995037415807708370819027)
                  ·
                    refine ⟨5992556123711562556228541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3995037415807708370819027 5992556123711562556228541)
                    ·
                      refine ⟨2247208546391835958585703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5992556123711562556228541 2247208546391835958585703)
                      ·
                        rfl

theorem cell23_4376423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_4376423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376423 prefixEnd_4376423 := by exact prefixLift 4376423
  have htrace : WordTrace (prefixWord ++ tailWord_4376423) baseStart_4376423 baseEnd_4376423 := by
    simpa [prefixWord, tailWord_4376423, baseEnd_4376423] using wordTrace_append hprefix tailTrace_4376423
  have hstable : (prefixWord ++ tailWord_4376423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376423).length < 2 ^ (prefixWord ++ tailWord_4376423).sum := by decide
  have hdescent : baseEnd_4376423 < baseStart_4376423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376473 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 2, 4]
def baseStart_4376473 : Nat := 118140960795 + 4376473 * 2 ^ 59
def prefixEnd_4376473 : Nat := 4983230072969 + 3 ^ 40 * 4376473 * 2
def baseEnd_4376473 : Nat := 749078073474853587653491

theorem tailTrace_4376473 : CollatzResearch.WordTrace tailWord_4376473 prefixEnd_4376473 749078073474853587653491 := by
  unfold tailWord_4376473
  simp only [CollatzResearch.WordTrace]
  refine ⟨159623083873793237926606073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106415389249195491951070715 159623083873793237926606073)
  ·
    refine ⟨119717312905344928444954555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159623083873793237926606073 119717312905344928444954555)
    ·
      refine ⟨179575969358017392667431833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119717312905344928444954555 179575969358017392667431833)
      ·
        refine ⟨134681977018513044500573875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179575969358017392667431833 134681977018513044500573875)
        ·
          refine ⟨202022965527769566750860813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134681977018513044500573875 202022965527769566750860813)
          ·
            refine ⟨75758612072913587531572805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202022965527769566750860813 75758612072913587531572805)
            ·
              refine ⟨14204739763671297662169901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75758612072913587531572805 14204739763671297662169901)
              ·
                refine ⟨5326777411376736623313713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14204739763671297662169901 5326777411376736623313713)
                ·
                  refine ⟨3995083058532552467485285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326777411376736623313713 3995083058532552467485285)
                  ·
                    refine ⟨749078073474853587653491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3995083058532552467485285 749078073474853587653491)
                    ·
                      rfl

theorem cell23_4376473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_4376473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376473 prefixEnd_4376473 := by exact prefixLift 4376473
  have htrace : WordTrace (prefixWord ++ tailWord_4376473) baseStart_4376473 baseEnd_4376473 := by
    simpa [prefixWord, tailWord_4376473, baseEnd_4376473] using wordTrace_append hprefix tailTrace_4376473
  have hstable : (prefixWord ++ tailWord_4376473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376473).length < 2 ^ (prefixWord ++ tailWord_4376473).sum := by decide
  have hdescent : baseEnd_4376473 < baseStart_4376473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376483 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 3]
def baseStart_4376483 : Nat := 118140960795 + 4376483 * 2 ^ 59
def prefixEnd_4376483 : Nat := 4983230072969 + 3 ^ 40 * 4376483 * 2
def baseEnd_4376483 : Nat := 2247239355231105723835427

theorem tailTrace_4376483 : CollatzResearch.WordTrace tailWord_4376483 prefixEnd_4376483 2247239355231105723835427 := by
  unfold tailWord_4376483
  simp only [CollatzResearch.WordTrace]
  refine ⟨159623448603757009634470103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106415632402504673089646735 159623448603757009634470103)
  ·
    refine ⟨239435172905635514451705155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159623448603757009634470103 239435172905635514451705155)
    ·
      refine ⟨359152759358453271677557733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239435172905635514451705155 359152759358453271677557733)
      ·
        refine ⟨67341142379709988439542075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 359152759358453271677557733 67341142379709988439542075)
        ·
          refine ⟨101011713569564982659313113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67341142379709988439542075 101011713569564982659313113)
          ·
            refine ⟨75758785177173736994484835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101011713569564982659313113 75758785177173736994484835)
            ·
              refine ⟨113638177765760605491727253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75758785177173736994484835 113638177765760605491727253)
              ·
                refine ⟨5326789582770028382424715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113638177765760605491727253 5326789582770028382424715)
                ·
                  refine ⟨7990184374155042573637073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326789582770028382424715 7990184374155042573637073)
                  ·
                    refine ⟨5992638280616281930227805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7990184374155042573637073 5992638280616281930227805)
                    ·
                      refine ⟨2247239355231105723835427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5992638280616281930227805 2247239355231105723835427)
                      ·
                        rfl

theorem cell23_4376483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_4376483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376483 prefixEnd_4376483 := by exact prefixLift 4376483
  have htrace : WordTrace (prefixWord ++ tailWord_4376483) baseStart_4376483 baseEnd_4376483 := by
    simpa [prefixWord, tailWord_4376483, baseEnd_4376483] using wordTrace_append hprefix tailTrace_4376483
  have hstable : (prefixWord ++ tailWord_4376483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376483).length < 2 ^ (prefixWord ++ tailWord_4376483).sum := by decide
  have hdescent : baseEnd_4376483 < baseStart_4376483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376494 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4376494 : Nat := 118140960795 + 4376494 * 2 ^ 59
def prefixEnd_4376494 : Nat := 4983230072969 + 3 ^ 40 * 4376494 * 2
def baseEnd_4376494 : Nat := 749081667839435060265959

theorem tailTrace_4376494 : CollatzResearch.WordTrace tailWord_4376494 prefixEnd_4376494 749081667839435060265959 := by
  unfold tailWord_4376494
  simp only [CollatzResearch.WordTrace]
  refine ⟨19952981225839644814140067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106415899871144772342080357 19952981225839644814140067)
  ·
    refine ⟨29929471838759467221210101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19952981225839644814140067 29929471838759467221210101)
    ·
      refine ⟨2805887984883700051988447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29929471838759467221210101 2805887984883700051988447)
      ·
        refine ⟨4208831977325550077982671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2805887984883700051988447 4208831977325550077982671)
        ·
          refine ⟨6313247965988325116974007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208831977325550077982671 6313247965988325116974007)
          ·
            refine ⟨9469871948982487675461011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6313247965988325116974007 9469871948982487675461011)
            ·
              refine ⟨14204807923473731513191517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469871948982487675461011 14204807923473731513191517)
              ·
                refine ⟨5326802971302649317446819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14204807923473731513191517 5326802971302649317446819)
                ·
                  refine ⟨7990204456953973976170229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326802971302649317446819 7990204456953973976170229)
                  ·
                    refine ⟨749081667839435060265959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7990204456953973976170229 749081667839435060265959)
                    ·
                      rfl

theorem cell23_4376494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4376494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376494 prefixEnd_4376494 := by exact prefixLift 4376494
  have htrace : WordTrace (prefixWord ++ tailWord_4376494) baseStart_4376494 baseEnd_4376494 := by
    simpa [prefixWord, tailWord_4376494, baseEnd_4376494] using wordTrace_append hprefix tailTrace_4376494
  have hstable : (prefixWord ++ tailWord_4376494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376494).length < 2 ^ (prefixWord ++ tailWord_4376494).sum := by decide
  have hdescent : baseEnd_4376494 < baseStart_4376494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376497 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4376497 : Nat := 118140960795 + 4376497 * 2 ^ 59
def prefixEnd_4376497 : Nat := 4983230072969 + 3 ^ 40 * 4376497 * 2
def baseEnd_4376497 : Nat := 2247246543960268669060363

theorem tailTrace_4376497 : CollatzResearch.WordTrace tailWord_4376497 prefixEnd_4376497 2247246543960268669060363 := by
  unfold tailWord_4376497
  simp only [CollatzResearch.WordTrace]
  refine ⟨159623959225706290025479745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106415972817137526683653163 159623959225706290025479745)
  ·
    refine ⟨119717969419279717519109809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159623959225706290025479745 119717969419279717519109809)
    ·
      refine ⟨89788477064459788139332357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119717969419279717519109809 89788477064459788139332357)
      ·
        refine ⟨16835339449586210276124817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89788477064459788139332357 16835339449586210276124817)
        ·
          refine ⟨12626504587189657707093613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16835339449586210276124817 12626504587189657707093613)
          ·
            refine ⟨4734939220196121640160105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12626504587189657707093613 4734939220196121640160105)
            ·
              refine ⟨3551204415147091230120079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734939220196121640160105 3551204415147091230120079)
              ·
                refine ⟨5326806622720636845180119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551204415147091230120079 5326806622720636845180119)
                ·
                  refine ⟨7990209934080955267770179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326806622720636845180119 7990209934080955267770179)
                  ·
                    refine ⟨11985314901121432901655269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7990209934080955267770179 11985314901121432901655269)
                    ·
                      refine ⟨2247246543960268669060363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11985314901121432901655269 2247246543960268669060363)
                      ·
                        rfl

theorem cell23_4376497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4376497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376497 prefixEnd_4376497 := by exact prefixLift 4376497
  have htrace : WordTrace (prefixWord ++ tailWord_4376497) baseStart_4376497 baseEnd_4376497 := by
    simpa [prefixWord, tailWord_4376497, baseEnd_4376497] using wordTrace_append hprefix tailTrace_4376497
  have hstable : (prefixWord ++ tailWord_4376497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376497).length < 2 ^ (prefixWord ++ tailWord_4376497).sum := by decide
  have hdescent : baseEnd_4376497 < baseStart_4376497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376534 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4376534 : Nat := 118140960795 + 4376534 * 2 ^ 59
def prefixEnd_4376534 : Nat := 4983230072969 + 3 ^ 40 * 4376534 * 2
def baseEnd_4376534 : Nat := 2247265542744485024297693

theorem tailTrace_4376534 : CollatzResearch.WordTrace tailWord_4376534 prefixEnd_4376534 2247265542744485024297693 := by
  unfold tailWord_4376534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976581795410765334036041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106416872484381496896384437 9976581795410765334036041)
  ·
    refine ⟨7482436346558074000527031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9976581795410765334036041 7482436346558074000527031)
    ·
      refine ⟨11223654519837111000790547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482436346558074000527031 11223654519837111000790547)
      ·
        refine ⟨16835481779755666501185821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11223654519837111000790547 16835481779755666501185821)
        ·
          refine ⟨6313305667408374937944683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16835481779755666501185821 6313305667408374937944683)
          ·
            refine ⟨9469958501112562406917025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6313305667408374937944683 9469958501112562406917025)
            ·
              refine ⟨7102468875834421805187769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9469958501112562406917025 7102468875834421805187769)
              ·
                refine ⟨5326851656875816353890827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7102468875834421805187769 5326851656875816353890827)
                ·
                  refine ⟨7990277485313724530836241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5326851656875816353890827 7990277485313724530836241)
                  ·
                    refine ⟨5992708113985293398127181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7990277485313724530836241 5992708113985293398127181)
                    ·
                      refine ⟨2247265542744485024297693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5992708113985293398127181 2247265542744485024297693)
                      ·
                        rfl

theorem cell23_4376534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4376534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376534 prefixEnd_4376534 := by exact prefixLift 4376534
  have htrace : WordTrace (prefixWord ++ tailWord_4376534) baseStart_4376534 baseEnd_4376534 := by
    simpa [prefixWord, tailWord_4376534, baseEnd_4376534] using wordTrace_append hprefix tailTrace_4376534
  have hstable : (prefixWord ++ tailWord_4376534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376534).length < 2 ^ (prefixWord ++ tailWord_4376534).sum := by decide
  have hdescent : baseEnd_4376534 < baseStart_4376534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376576 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 7]
def baseStart_4376576 : Nat := 118140960795 + 4376576 * 2 ^ 59
def prefixEnd_4376576 : Nat := 4983230072969 + 3 ^ 40 * 4376576 * 2
def baseEnd_4376576 : Nat := 249698567659108206663611

theorem tailTrace_4376576 : CollatzResearch.WordTrace tailWord_4376576 prefixEnd_4376576 249698567659108206663611 := by
  unfold tailWord_4376576
  simp only [CollatzResearch.WordTrace]
  refine ⟨79813420296210043258802791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106417893728280057678403721 79813420296210043258802791)
  ·
    refine ⟨119720130444315064888204187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79813420296210043258802791 119720130444315064888204187)
    ·
      refine ⟨179580195666472597332306281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119720130444315064888204187 179580195666472597332306281)
      ·
        refine ⟨134685146749854447999229711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179580195666472597332306281 134685146749854447999229711)
        ·
          refine ⟨202027720124781671998844567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134685146749854447999229711 202027720124781671998844567)
          ·
            refine ⟨303041580187172507998266851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202027720124781671998844567 303041580187172507998266851)
            ·
              refine ⟨454562370280758761997400277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303041580187172507998266851 454562370280758761997400277)
              ·
                refine ⟨10653805553455283484314069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 454562370280758761997400277 10653805553455283484314069)
                ·
                  refine ⟨249698567659108206663611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10653805553455283484314069 249698567659108206663611)
                  ·
                    rfl

theorem cell23_4376576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_4376576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376576 prefixEnd_4376576 := by exact prefixLift 4376576
  have htrace : WordTrace (prefixWord ++ tailWord_4376576) baseStart_4376576 baseEnd_4376576 := by
    simpa [prefixWord, tailWord_4376576, baseEnd_4376576] using wordTrace_append hprefix tailTrace_4376576
  have hstable : (prefixWord ++ tailWord_4376576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376576).length < 2 ^ (prefixWord ++ tailWord_4376576).sum := by decide
  have hdescent : baseEnd_4376576 < baseStart_4376576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376587 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 2, 2, 2]
def baseStart_4376587 : Nat := 118140960795 + 4376587 * 2 ^ 59
def prefixEnd_4376587 : Nat := 4983230072969 + 3 ^ 40 * 4376587 * 2
def baseEnd_4376587 : Nat := 2247292757219173316934949

theorem tailTrace_4376587 : CollatzResearch.WordTrace tailWord_4376587 prefixEnd_4376587 2247292757219173316934949 := by
  unfold tailWord_4376587
  simp only [CollatzResearch.WordTrace]
  refine ⟨159627241795380235396256015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106418161196920156930837343 159627241795380235396256015)
  ·
    refine ⟨239440862693070353094384023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159627241795380235396256015 239440862693070353094384023)
    ·
      refine ⟨359161294039605529641576035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239440862693070353094384023 359161294039605529641576035)
      ·
        refine ⟨538741941059408294462364053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359161294039605529641576035 538741941059408294462364053)
        ·
          refine ⟨25253528487159763802923315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 538741941059408294462364053 25253528487159763802923315)
          ·
            refine ⟨37880292730739645704384973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25253528487159763802923315 37880292730739645704384973)
            ·
              refine ⟨14205109774027367139144365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37880292730739645704384973 14205109774027367139144365)
              ·
                refine ⟨5326916165260262677179137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14205109774027367139144365 5326916165260262677179137)
                ·
                  refine ⟨3995187123945197007884353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5326916165260262677179137 3995187123945197007884353)
                  ·
                    refine ⟨2996390342958897755913265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3995187123945197007884353 2996390342958897755913265)
                    ·
                      refine ⟨2247292757219173316934949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996390342958897755913265 2247292757219173316934949)
                      ·
                        rfl

theorem cell23_4376587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 2, 2].length) (baseStart_4376587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376587 prefixEnd_4376587 := by exact prefixLift 4376587
  have htrace : WordTrace (prefixWord ++ tailWord_4376587) baseStart_4376587 baseEnd_4376587 := by
    simpa [prefixWord, tailWord_4376587, baseEnd_4376587] using wordTrace_append hprefix tailTrace_4376587
  have hstable : (prefixWord ++ tailWord_4376587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376587).length < 2 ^ (prefixWord ++ tailWord_4376587).sum := by decide
  have hdescent : baseEnd_4376587 < baseStart_4376587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376610 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_4376610 : Nat := 118140960795 + 4376610 * 2 ^ 59
def prefixEnd_4376610 : Nat := 4983230072969 + 3 ^ 40 * 4376610 * 2
def baseEnd_4376610 : Nat := 249700507474914080771927

theorem tailTrace_4376610 : CollatzResearch.WordTrace tailWord_4376610 prefixEnd_4376610 249700507474914080771927 := by
  unfold tailWord_4376610
  simp only [CollatzResearch.WordTrace]
  refine ⟨39907020168574227581085821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106418720449531273549562189 39907020168574227581085821)
  ·
    refine ⟨14965132563215335342907183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39907020168574227581085821 14965132563215335342907183)
    ·
      refine ⟨22447698844823003014360775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14965132563215335342907183 22447698844823003014360775)
      ·
        refine ⟨33671548267234504521541163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22447698844823003014360775 33671548267234504521541163)
        ·
          refine ⟨50507322400851756782311745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33671548267234504521541163 50507322400851756782311745)
          ·
            refine ⟨37880491800638817586733809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50507322400851756782311745 37880491800638817586733809)
            ·
              refine ⟨28410368850479113190050357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37880491800638817586733809 28410368850479113190050357)
              ·
                refine ⟨2663472079732416861567221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28410368850479113190050357 2663472079732416861567221)
                ·
                  refine ⟨249700507474914080771927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2663472079732416861567221 249700507474914080771927)
                  ·
                    rfl

theorem cell23_4376610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_4376610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376610 prefixEnd_4376610 := by exact prefixLift 4376610
  have htrace : WordTrace (prefixWord ++ tailWord_4376610) baseStart_4376610 baseEnd_4376610 := by
    simpa [prefixWord, tailWord_4376610, baseEnd_4376610] using wordTrace_append hprefix tailTrace_4376610
  have hstable : (prefixWord ++ tailWord_4376610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376610).length < 2 ^ (prefixWord ++ tailWord_4376610).sum := by decide
  have hdescent : baseEnd_4376610 < baseStart_4376610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376660 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_4376660 : Nat := 118140960795 + 4376660 * 2 ^ 59
def prefixEnd_4376660 : Nat := 4983230072969 + 3 ^ 40 * 4376660 * 2
def baseEnd_4376660 : Nat := 2247330241306951531322113

theorem tailTrace_4376660 : CollatzResearch.WordTrace tailWord_4376660 prefixEnd_4376660 2247330241306951531322113 := by
  unfold tailWord_4376660
  simp only [CollatzResearch.WordTrace]
  refine ⟨79814952162057884431831717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106419936216077179242442289 79814952162057884431831717)
  ·
    refine ⟨14965303530385853330968447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79814952162057884431831717 14965303530385853330968447)
    ·
      refine ⟨22447955295578779996452671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14965303530385853330968447 22447955295578779996452671)
      ·
        refine ⟨33671932943368169994679007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22447955295578779996452671 33671932943368169994679007)
        ·
          refine ⟨50507899415052254992018511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33671932943368169994679007 50507899415052254992018511)
          ·
            refine ⟨75761849122578382488027767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50507899415052254992018511 75761849122578382488027767)
            ·
              refine ⟨113642773683867573732041651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75761849122578382488027767 113642773683867573732041651)
              ·
                refine ⟨170464160525801360598062477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113642773683867573732041651 170464160525801360598062477)
                ·
                  refine ⟨63924060197175510224273429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170464160525801360598062477 63924060197175510224273429)
                  ·
                    refine ⟨2996440321742602041762817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63924060197175510224273429 2996440321742602041762817)
                    ·
                      refine ⟨2247330241306951531322113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996440321742602041762817 2247330241306951531322113)
                      ·
                        rfl

theorem cell23_4376660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_4376660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376660 prefixEnd_4376660 := by exact prefixLift 4376660
  have htrace : WordTrace (prefixWord ++ tailWord_4376660) baseStart_4376660 baseEnd_4376660 := by
    simpa [prefixWord, tailWord_4376660, baseEnd_4376660] using wordTrace_append hprefix tailTrace_4376660
  have hstable : (prefixWord ++ tailWord_4376660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376660).length < 2 ^ (prefixWord ++ tailWord_4376660).sum := by decide
  have hdescent : baseEnd_4376660 < baseStart_4376660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376687 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 1, 4]
def baseStart_4376687 : Nat := 118140960795 + 4376687 * 2 ^ 59
def prefixEnd_4376687 : Nat := 4983230072969 + 3 ^ 40 * 4376687 * 2
def baseEnd_4376687 : Nat := 749114701761540975228163

theorem tailTrace_4376687 : CollatzResearch.WordTrace tailWord_4376687 prefixEnd_4376687 749114701761540975228163 := by
  unfold tailWord_4376687
  simp only [CollatzResearch.WordTrace]
  refine ⟨159630889095017952474896315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106420592730011968316597543 159630889095017952474896315)
  ·
    refine ⟨239446333642526928712344473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159630889095017952474896315 239446333642526928712344473)
    ·
      refine ⟨179584750231895196534258355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239446333642526928712344473 179584750231895196534258355)
      ·
        refine ⟨269377125347842794801387533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179584750231895196534258355 269377125347842794801387533)
        ·
          refine ⟨101016422005441048050520325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269377125347842794801387533 101016422005441048050520325)
          ·
            refine ⟨18940579126020196509472561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101016422005441048050520325 18940579126020196509472561)
            ·
              refine ⟨14205434344515147382104421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18940579126020196509472561 14205434344515147382104421)
              ·
                refine ⟨2663518939596590134144579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14205434344515147382104421 2663518939596590134144579)
                ·
                  refine ⟨3995278409394885201216869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663518939596590134144579 3995278409394885201216869)
                  ·
                    refine ⟨749114701761540975228163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3995278409394885201216869 749114701761540975228163)
                    ·
                      rfl

theorem cell23_4376687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 4].length) (baseStart_4376687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376687 prefixEnd_4376687 := by exact prefixLift 4376687
  have htrace : WordTrace (prefixWord ++ tailWord_4376687) baseStart_4376687 baseEnd_4376687 := by
    simpa [prefixWord, tailWord_4376687, baseEnd_4376687] using wordTrace_append hprefix tailTrace_4376687
  have hstable : (prefixWord ++ tailWord_4376687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376687).length < 2 ^ (prefixWord ++ tailWord_4376687).sum := by decide
  have hdescent : baseEnd_4376687 < baseStart_4376687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376720 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 1, 5, 2]
def baseStart_4376720 : Nat := 118140960795 + 4376720 * 2 ^ 59
def prefixEnd_4376720 : Nat := 4983230072969 + 3 ^ 40 * 4376720 * 2
def baseEnd_4376720 : Nat := 2247361050146221296571837

theorem tailTrace_4376720 : CollatzResearch.WordTrace tailWord_4376720 prefixEnd_4376720 2247361050146221296571837 := by
  unfold tailWord_4376720
  simp only [CollatzResearch.WordTrace]
  refine ⟨79816046351949199555423807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106421395135932266073898409 79816046351949199555423807)
  ·
    refine ⟨119724069527923799333135711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79816046351949199555423807 119724069527923799333135711)
    ·
      refine ⟨179586104291885698999703567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119724069527923799333135711 179586104291885698999703567)
      ·
        refine ⟨269379156437828548499555351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179586104291885698999703567 269379156437828548499555351)
        ·
          refine ⟨404068734656742822749333027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269379156437828548499555351 404068734656742822749333027)
          ·
            refine ⟨606103101985114234123999541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404068734656742822749333027 606103101985114234123999541)
            ·
              refine ⟨56822165811104459449124957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 606103101985114234123999541 56822165811104459449124957)
              ·
                refine ⟨21308312179164172293421859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56822165811104459449124957 21308312179164172293421859)
                ·
                  refine ⟨31962468268746258440132789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21308312179164172293421859 31962468268746258440132789)
                  ·
                    refine ⟨2996481400194961728762449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31962468268746258440132789 2996481400194961728762449)
                    ·
                      refine ⟨2247361050146221296571837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996481400194961728762449 2247361050146221296571837)
                      ·
                        rfl

theorem cell23_4376720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 5, 2].length) (baseStart_4376720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376720 prefixEnd_4376720 := by exact prefixLift 4376720
  have htrace : WordTrace (prefixWord ++ tailWord_4376720) baseStart_4376720 baseEnd_4376720 := by
    simpa [prefixWord, tailWord_4376720, baseEnd_4376720] using wordTrace_append hprefix tailTrace_4376720
  have hstable : (prefixWord ++ tailWord_4376720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376720).length < 2 ^ (prefixWord ++ tailWord_4376720).sum := by decide
  have hdescent : baseEnd_4376720 < baseStart_4376720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376737 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_4376737 : Nat := 118140960795 + 4376737 * 2 ^ 59
def prefixEnd_4376737 : Nat := 4983230072969 + 3 ^ 40 * 4376737 * 2
def baseEnd_4376737 : Nat := 2247369779317347730059259

theorem tailTrace_4376737 : CollatzResearch.WordTrace tailWord_4376737 prefixEnd_4376737 2247369779317347730059259 := by
  unfold tailWord_4376737
  simp only [CollatzResearch.WordTrace]
  refine ⟨159632712744836811014216465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106421808496557874009477643 159632712744836811014216465)
  ·
    refine ⟨119724534558627608260662349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159632712744836811014216465 119724534558627608260662349)
    ·
      refine ⟨44896700459485353097748381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119724534558627608260662349 44896700459485353097748381)
      ·
        refine ⟨16836262672307007411655643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44896700459485353097748381 16836262672307007411655643)
        ·
          refine ⟨25254394008460511117483465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16836262672307007411655643 25254394008460511117483465)
          ·
            refine ⟨18940795506345383338112599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25254394008460511117483465 18940795506345383338112599)
            ·
              refine ⟨28411193259518075007168899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18940795506345383338112599 28411193259518075007168899)
              ·
                refine ⟨42616789889277112510753349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28411193259518075007168899 42616789889277112510753349)
                ·
                  refine ⟨7990648104239458595766253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42616789889277112510753349 7990648104239458595766253)
                  ·
                    refine ⟨2996493039089796973412345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7990648104239458595766253 2996493039089796973412345)
                    ·
                      refine ⟨2247369779317347730059259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996493039089796973412345 2247369779317347730059259)
                      ·
                        rfl

theorem cell23_4376737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_4376737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376737 prefixEnd_4376737 := by exact prefixLift 4376737
  have htrace : WordTrace (prefixWord ++ tailWord_4376737) baseStart_4376737 baseEnd_4376737 := by
    simpa [prefixWord, tailWord_4376737, baseEnd_4376737] using wordTrace_append hprefix tailTrace_4376737
  have hstable : (prefixWord ++ tailWord_4376737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376737).length < 2 ^ (prefixWord ++ tailWord_4376737).sum := by decide
  have hdescent : baseEnd_4376737 < baseStart_4376737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376763 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6]
def baseStart_4376763 : Nat := 118140960795 + 4376763 * 2 ^ 59
def prefixEnd_4376763 : Nat := 4983230072969 + 3 ^ 40 * 4376763 * 2
def baseEnd_4376763 : Nat := 2247383129814364628334139

theorem tailTrace_4376763 : CollatzResearch.WordTrace tailWord_4376763 prefixEnd_4376763 2247383129814364628334139 := by
  unfold tailWord_4376763
  simp only [CollatzResearch.WordTrace]
  refine ⟨159633661042742617454662943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106422440695161744969775295 159633661042742617454662943)
  ·
    refine ⟨239450491564113926181994415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159633661042742617454662943 239450491564113926181994415)
    ·
      refine ⟨359175737346170889272991623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239450491564113926181994415 359175737346170889272991623)
      ·
        refine ⟨538763606019256333909487435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359175737346170889272991623 538763606019256333909487435)
        ·
          refine ⟨808145409028884500864231153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538763606019256333909487435 808145409028884500864231153)
          ·
            refine ⟨606109056771663375648173365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 808145409028884500864231153 606109056771663375648173365)
            ·
              refine ⟨56822724072343441467016253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 606109056771663375648173365 56822724072343441467016253)
              ·
                refine ⟨21308521527128790550131095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56822724072343441467016253 21308521527128790550131095)
                ·
                  refine ⟨31962782290693185825196643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21308521527128790550131095 31962782290693185825196643)
                  ·
                    refine ⟨47944173436039778737794965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31962782290693185825196643 47944173436039778737794965)
                    ·
                      refine ⟨2247383129814364628334139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47944173436039778737794965 2247383129814364628334139)
                      ·
                        rfl

theorem cell23_4376763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_4376763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376763 prefixEnd_4376763 := by exact prefixLift 4376763
  have htrace : WordTrace (prefixWord ++ tailWord_4376763) baseStart_4376763 baseEnd_4376763 := by
    simpa [prefixWord, tailWord_4376763, baseEnd_4376763] using wordTrace_append hprefix tailTrace_4376763
  have hstable : (prefixWord ++ tailWord_4376763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376763).length < 2 ^ (prefixWord ++ tailWord_4376763).sum := by decide
  have hdescent : baseEnd_4376763 < baseStart_4376763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376764 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_4376764 : Nat := 118140960795 + 4376764 * 2 ^ 59
def prefixEnd_4376764 : Nat := 4983230072969 + 3 ^ 40 * 4376764 * 2
def baseEnd_4376764 : Nat := 749127881098339708140545

theorem tailTrace_4376764 : CollatzResearch.WordTrace tailWord_4376764 prefixEnd_4376764 749127881098339708140545 := by
  unfold tailWord_4376764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79816848757869497312724673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106422465010492663083632897 79816848757869497312724673)
  ·
    refine ⟨59862636568402122984543505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79816848757869497312724673 59862636568402122984543505)
    ·
      refine ⟨44896977426301592238407629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59862636568402122984543505 44896977426301592238407629)
      ·
        refine ⟨16836366534863097089402861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44896977426301592238407629 16836366534863097089402861)
        ·
          refine ⟨6313637450573661408526073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16836366534863097089402861 6313637450573661408526073)
          ·
            refine ⟨4735228087930246056394555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6313637450573661408526073 4735228087930246056394555)
            ·
              refine ⟨7102842131895369084591833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735228087930246056394555 7102842131895369084591833)
              ·
                refine ⟨5327131598921526813443875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7102842131895369084591833 5327131598921526813443875)
                ·
                  refine ⟨7990697398382290220165813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5327131598921526813443875 7990697398382290220165813)
                  ·
                    refine ⟨749127881098339708140545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7990697398382290220165813 749127881098339708140545)
                    ·
                      rfl

theorem cell23_4376764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_4376764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376764 prefixEnd_4376764 := by exact prefixLift 4376764
  have htrace : WordTrace (prefixWord ++ tailWord_4376764) baseStart_4376764 baseEnd_4376764 := by
    simpa [prefixWord, tailWord_4376764, baseEnd_4376764] using wordTrace_append hprefix tailTrace_4376764
  have hstable : (prefixWord ++ tailWord_4376764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376764).length < 2 ^ (prefixWord ++ tailWord_4376764).sum := by decide
  have hdescent : baseEnd_4376764 < baseStart_4376764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376767 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 5, 2, 2]
def baseStart_4376767 : Nat := 118140960795 + 4376767 * 2 ^ 59
def prefixEnd_4376767 : Nat := 4983230072969 + 3 ^ 40 * 4376767 * 2
def baseEnd_4376767 : Nat := 2247385183736982612684121

theorem tailTrace_4376767 : CollatzResearch.WordTrace tailWord_4376767 prefixEnd_4376767 2247385183736982612684121 := by
  unfold tailWord_4376767
  simp only [CollatzResearch.WordTrace]
  refine ⟨159633806934728126137808555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106422537956485417425205703 159633806934728126137808555)
  ·
    refine ⟨239450710402092189206712833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159633806934728126137808555 239450710402092189206712833)
    ·
      refine ⟨179588032801569141905034625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239450710402092189206712833 179588032801569141905034625)
      ·
        refine ⟨134691024601176856428775969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179588032801569141905034625 134691024601176856428775969)
        ·
          refine ⟨101018268450882642321581977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134691024601176856428775969 101018268450882642321581977)
          ·
            refine ⟨75763701338161981741186483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101018268450882642321581977 75763701338161981741186483)
            ·
              refine ⟨113645552007242972611779725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75763701338161981741186483 113645552007242972611779725)
              ·
                refine ⟨42617082002716114729417397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113645552007242972611779725 42617082002716114729417397)
                ·
                  refine ⟨3995351437754635755882881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42617082002716114729417397 3995351437754635755882881)
                  ·
                    refine ⟨2996513578315976816912161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3995351437754635755882881 2996513578315976816912161)
                    ·
                      refine ⟨2247385183736982612684121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996513578315976816912161 2247385183736982612684121)
                      ·
                        rfl

theorem cell23_4376767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_4376767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376767 prefixEnd_4376767 := by exact prefixLift 4376767
  have htrace : WordTrace (prefixWord ++ tailWord_4376767) baseStart_4376767 baseEnd_4376767 := by
    simpa [prefixWord, tailWord_4376767, baseEnd_4376767] using wordTrace_append hprefix tailTrace_4376767
  have hstable : (prefixWord ++ tailWord_4376767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376767).length < 2 ^ (prefixWord ++ tailWord_4376767).sum := by decide
  have hdescent : baseEnd_4376767 < baseStart_4376767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376773 : List Nat := [1, 3, 1, 1, 1, 1, 6, 9]
def baseStart_4376773 : Nat := 118140960795 + 4376773 * 2 ^ 59
def prefixEnd_4376773 : Nat := 4983230072969 + 3 ^ 40 * 4376773 * 2
def baseEnd_4376773 : Nat := 83236602393367021822559

theorem tailTrace_4376773 : CollatzResearch.WordTrace tailWord_4376773 prefixEnd_4376773 83236602393367021822559 := by
  unfold tailWord_4376773
  simp only [CollatzResearch.WordTrace]
  refine ⟨159634025772706389162526973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106422683848470926108351315 159634025772706389162526973)
  ·
    refine ⟨59862759664764895935947615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159634025772706389162526973 59862759664764895935947615)
    ·
      refine ⟨89794139497147343903921423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59862759664764895935947615 89794139497147343903921423)
      ·
        refine ⟨134691209245721015855882135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89794139497147343903921423 134691209245721015855882135)
        ·
          refine ⟨202036813868581523783823203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134691209245721015855882135 202036813868581523783823203)
          ·
            refine ⟨303055220802872285675734805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202036813868581523783823203 303055220802872285675734805)
            ·
              refine ⟨14205713475134638391050069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 303055220802872285675734805 14205713475134638391050069)
              ·
                refine ⟨83236602393367021822559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14205713475134638391050069 83236602393367021822559)
                ·
                  rfl

theorem cell23_4376773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 9].length) (baseStart_4376773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376773 prefixEnd_4376773 := by exact prefixLift 4376773
  have htrace : WordTrace (prefixWord ++ tailWord_4376773) baseStart_4376773 baseEnd_4376773 := by
    simpa [prefixWord, tailWord_4376773, baseEnd_4376773] using wordTrace_append hprefix tailTrace_4376773
  have hstable : (prefixWord ++ tailWord_4376773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376773).length < 2 ^ (prefixWord ++ tailWord_4376773).sum := by decide
  have hdescent : baseEnd_4376773 < baseStart_4376773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376800 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_4376800 : Nat := 118140960795 + 4376800 * 2 ^ 59
def prefixEnd_4376800 : Nat := 4983230072969 + 3 ^ 40 * 4376800 * 2
def baseEnd_4376800 : Nat := 2247402128598580983571469

theorem tailTrace_4376800 : CollatzResearch.WordTrace tailWord_4376800 prefixEnd_4376800 2247402128598580983571469 := by
  unfold tailWord_4376800
  simp only [CollatzResearch.WordTrace]
  refine ⟨79817505271804286386879927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106423340362405715182506569 79817505271804286386879927)
  ·
    refine ⟨119726257907706429580319891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79817505271804286386879927 119726257907706429580319891)
    ·
      refine ⟨179589386861559644370479837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119726257907706429580319891 179589386861559644370479837)
      ·
        refine ⟨67346020073084866638929939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179589386861559644370479837 67346020073084866638929939)
        ·
          refine ⟨101019030109627299958394909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67346020073084866638929939 101019030109627299958394909)
          ·
            refine ⟨37882136291110237484398091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101019030109627299958394909 37882136291110237484398091)
            ·
              refine ⟨56823204436665356226597137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37882136291110237484398091 56823204436665356226597137)
              ·
                refine ⟨42617403327499017169947853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56823204436665356226597137 42617403327499017169947853)
                ·
                  refine ⟨15981526247812131438730445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42617403327499017169947853 15981526247812131438730445)
                  ·
                    refine ⟨5993072342929549289523917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15981526247812131438730445 5993072342929549289523917)
                    ·
                      refine ⟨2247402128598580983571469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993072342929549289523917 2247402128598580983571469)
                      ·
                        rfl

theorem cell23_4376800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_4376800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376800 prefixEnd_4376800 := by exact prefixLift 4376800
  have htrace : WordTrace (prefixWord ++ tailWord_4376800) baseStart_4376800 baseEnd_4376800 := by
    simpa [prefixWord, tailWord_4376800, baseEnd_4376800] using wordTrace_append hprefix tailTrace_4376800
  have hstable : (prefixWord ++ tailWord_4376800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376800).length < 2 ^ (prefixWord ++ tailWord_4376800).sum := by decide
  have hdescent : baseEnd_4376800 < baseStart_4376800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376801 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_4376801 : Nat := 118140960795 + 4376801 * 2 ^ 59
def prefixEnd_4376801 : Nat := 4983230072969 + 3 ^ 40 * 4376801 * 2
def baseEnd_4376801 : Nat := 2247402642079235479658965

theorem tailTrace_4376801 : CollatzResearch.WordTrace tailWord_4376801 prefixEnd_4376801 2247402642079235479658965 := by
  unfold tailWord_4376801
  simp only [CollatzResearch.WordTrace]
  refine ⟨159635047016604949944546257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106423364677736633296364171 159635047016604949944546257)
  ·
    refine ⟨119726285262453712458409693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159635047016604949944546257 119726285262453712458409693)
    ·
      refine ⟨44897356973420142171903635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119726285262453712458409693 44897356973420142171903635)
      ·
        refine ⟨67346035460130213257855453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44897356973420142171903635 67346035460130213257855453)
        ·
          refine ⟨25254763297548829971695795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67346035460130213257855453 25254763297548829971695795)
          ·
            refine ⟨37882144946323244957543693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25254763297548829971695795 37882144946323244957543693)
            ·
              refine ⟨14205804354871216859078885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37882144946323244957543693 14205804354871216859078885)
              ·
                refine ⟨2663588316538353161077291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14205804354871216859078885 2663588316538353161077291)
                ·
                  refine ⟨3995382474807529741615937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663588316538353161077291 3995382474807529741615937)
                  ·
                    refine ⟨2996536856105647306211953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3995382474807529741615937 2996536856105647306211953)
                    ·
                      refine ⟨2247402642079235479658965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996536856105647306211953 2247402642079235479658965)
                      ·
                        rfl

theorem cell23_4376801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_4376801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376801 prefixEnd_4376801 := by exact prefixLift 4376801
  have htrace : WordTrace (prefixWord ++ tailWord_4376801) baseStart_4376801 baseEnd_4376801 := by
    simpa [prefixWord, tailWord_4376801, baseEnd_4376801] using wordTrace_append hprefix tailTrace_4376801
  have hstable : (prefixWord ++ tailWord_4376801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376801).length < 2 ^ (prefixWord ++ tailWord_4376801).sum := by decide
  have hdescent : baseEnd_4376801 < baseStart_4376801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376807 : List Nat := [1, 1, 5, 3, 1, 3, 1, 8]
def baseStart_4376807 : Nat := 118140960795 + 4376807 * 2 ^ 59
def prefixEnd_4376807 : Nat := 4983230072969 + 3 ^ 40 * 4376807 * 2
def baseEnd_4376807 : Nat := 83237248998635646525331

theorem tailTrace_4376807 : CollatzResearch.WordTrace tailWord_4376807 prefixEnd_4376807 83237248998635646525331 := by
  unfold tailWord_4376807
  simp only [CollatzResearch.WordTrace]
  refine ⟨159635265854583212969264675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106423510569722141979509783 159635265854583212969264675)
  ·
    refine ⟨239452898781874819453897013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159635265854583212969264675 239452898781874819453897013)
    ·
      refine ⟨22448709260800764323802845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239452898781874819453897013 22448709260800764323802845)
      ·
        refine ⟨8418265972800286621426067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22448709260800764323802845 8418265972800286621426067)
        ·
          refine ⟨12627398959200429932139101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8418265972800286621426067 12627398959200429932139101)
          ·
            refine ⟨4735274609700161224552163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12627398959200429932139101 4735274609700161224552163)
            ·
              refine ⟨7102911914550241836828245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735274609700161224552163 7102911914550241836828245)
              ·
                refine ⟨83237248998635646525331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7102911914550241836828245 83237248998635646525331)
                ·
                  rfl

theorem cell23_4376807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 8].length) (baseStart_4376807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376807 prefixEnd_4376807 := by exact prefixLift 4376807
  have htrace : WordTrace (prefixWord ++ tailWord_4376807) baseStart_4376807 baseEnd_4376807 := by
    simpa [prefixWord, tailWord_4376807, baseEnd_4376807] using wordTrace_append hprefix tailTrace_4376807
  have hstable : (prefixWord ++ tailWord_4376807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376807).length < 2 ^ (prefixWord ++ tailWord_4376807).sum := by decide
  have hdescent : baseEnd_4376807 < baseStart_4376807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376823 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_4376823 : Nat := 118140960795 + 4376823 * 2 ^ 59
def prefixEnd_4376823 : Nat := 4983230072969 + 3 ^ 40 * 4376823 * 2
def baseEnd_4376823 : Nat := 2247413938653634393583863

theorem tailTrace_4376823 : CollatzResearch.WordTrace tailWord_4376823 prefixEnd_4376823 2247413938653634393583863 := by
  unfold tailWord_4376823
  simp only [CollatzResearch.WordTrace]
  refine ⟨159635849422525247701847123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106423899615016831801231415 159635849422525247701847123)
  ·
    refine ⟨239453774133787871552770685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159635849422525247701847123 239453774133787871552770685)
    ·
      refine ⟨89795165300170451832289007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239453774133787871552770685 89795165300170451832289007)
      ·
        refine ⟨134692747950255677748433511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89795165300170451832289007 134692747950255677748433511)
        ·
          refine ⟨202039121925383516622650267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134692747950255677748433511 202039121925383516622650267)
          ·
            refine ⟨303058682888075274933975401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202039121925383516622650267 303058682888075274933975401)
            ·
              refine ⟨227294012166056456200481551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303058682888075274933975401 227294012166056456200481551)
              ·
                refine ⟨340941018249084684300722327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227294012166056456200481551 340941018249084684300722327)
                ·
                  refine ⟨511411527373627026451083491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340941018249084684300722327 511411527373627026451083491)
                  ·
                    refine ⟨767117291060440539676625237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511411527373627026451083491 767117291060440539676625237)
                    ·
                      refine ⟨2247413938653634393583863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 767117291060440539676625237 2247413938653634393583863)
                      ·
                        rfl

theorem cell23_4376823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_4376823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376823 prefixEnd_4376823 := by exact prefixLift 4376823
  have htrace : WordTrace (prefixWord ++ tailWord_4376823) baseStart_4376823 baseEnd_4376823 := by
    simpa [prefixWord, tailWord_4376823, baseEnd_4376823] using wordTrace_append hprefix tailTrace_4376823
  have hstable : (prefixWord ++ tailWord_4376823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376823).length < 2 ^ (prefixWord ++ tailWord_4376823).sum := by decide
  have hdescent : baseEnd_4376823 < baseStart_4376823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376834 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_4376834 : Nat := 118140960795 + 4376834 * 2 ^ 59
def prefixEnd_4376834 : Nat := 4983230072969 + 3 ^ 40 * 4376834 * 2
def baseEnd_4376834 : Nat := 2247419586940833850546313

theorem tailTrace_4376834 : CollatzResearch.WordTrace tailWord_4376834 prefixEnd_4376834 2247419586940833850546313 := by
  unfold tailWord_4376834
  simp only [CollatzResearch.WordTrace]
  refine ⟨39909062656371349145124389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106424167083656931053665037 39909062656371349145124389)
  ·
    refine ⟨7482949248069627964710823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39909062656371349145124389 7482949248069627964710823)
    ·
      refine ⟨11224423872104441947066235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482949248069627964710823 11224423872104441947066235)
      ·
        refine ⟨16836635808156662920599353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11224423872104441947066235 16836635808156662920599353)
        ·
          refine ⟨12627476856117497190449515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16836635808156662920599353 12627476856117497190449515)
          ·
            refine ⟨18941215284176245785674273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12627476856117497190449515 18941215284176245785674273)
            ·
              refine ⟨14205911463132184339255705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18941215284176245785674273 14205911463132184339255705)
              ·
                refine ⟨10654433597349138254441779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14205911463132184339255705 10654433597349138254441779)
                ·
                  refine ⟨15981650396023707381662669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10654433597349138254441779 15981650396023707381662669)
                  ·
                    refine ⟨5993118898508890268123501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15981650396023707381662669 5993118898508890268123501)
                    ·
                      refine ⟨2247419586940833850546313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993118898508890268123501 2247419586940833850546313)
                      ·
                        rfl

theorem cell23_4376834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_4376834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376834 prefixEnd_4376834 := by exact prefixLift 4376834
  have htrace : WordTrace (prefixWord ++ tailWord_4376834) baseStart_4376834 baseEnd_4376834 := by
    simpa [prefixWord, tailWord_4376834, baseEnd_4376834] using wordTrace_append hprefix tailTrace_4376834
  have hstable : (prefixWord ++ tailWord_4376834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376834).length < 2 ^ (prefixWord ++ tailWord_4376834).sum := by decide
  have hdescent : baseEnd_4376834 < baseStart_4376834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376844 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 1, 3, 2]
def baseStart_4376844 : Nat := 118140960795 + 4376844 * 2 ^ 59
def prefixEnd_4376844 : Nat := 4983230072969 + 3 ^ 40 * 4376844 * 2
def baseEnd_4376844 : Nat := 2247424721747378811421267

theorem tailTrace_4376844 : CollatzResearch.WordTrace tailWord_4376844 prefixEnd_4376844 2247424721747378811421267 := by
  unfold tailWord_4376844
  simp only [CollatzResearch.WordTrace]
  refine ⟨79818307677724584144180793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106424410236966112192241057 79818307677724584144180793)
  ·
    refine ⟨59863730758293438108135595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79818307677724584144180793 59863730758293438108135595)
    ·
      refine ⟨89795596137440157162203393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59863730758293438108135595 89795596137440157162203393)
      ·
        refine ⟨67346697103080117871652545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89795596137440157162203393 67346697103080117871652545)
        ·
          refine ⟨50510022827310088403739409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67346697103080117871652545 50510022827310088403739409)
          ·
            refine ⟨37882517120482566302804557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50510022827310088403739409 37882517120482566302804557)
            ·
              refine ⟨14205943920180962363551709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37882517120482566302804557 14205943920180962363551709)
              ·
                refine ⟨5327228970067860886331891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14205943920180962363551709 5327228970067860886331891)
                ·
                  refine ⟨7990843455101791329497837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5327228970067860886331891 7990843455101791329497837)
                  ·
                    refine ⟨2996566295663171748561689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7990843455101791329497837 2996566295663171748561689)
                    ·
                      refine ⟨2247424721747378811421267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996566295663171748561689 2247424721747378811421267)
                      ·
                        rfl

theorem cell23_4376844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_4376844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376844 prefixEnd_4376844 := by exact prefixLift 4376844
  have htrace : WordTrace (prefixWord ++ tailWord_4376844) baseStart_4376844 baseEnd_4376844 := by
    simpa [prefixWord, tailWord_4376844, baseEnd_4376844] using wordTrace_append hprefix tailTrace_4376844
  have hstable : (prefixWord ++ tailWord_4376844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376844).length < 2 ^ (prefixWord ++ tailWord_4376844).sum := by decide
  have hdescent : baseEnd_4376844 < baseStart_4376844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376860 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4376860 : Nat := 118140960795 + 4376860 * 2 ^ 59
def prefixEnd_4376860 : Nat := 4983230072969 + 3 ^ 40 * 4376860 * 2
def baseEnd_4376860 : Nat := 2247432937437850748821193

theorem tailTrace_4376860 : CollatzResearch.WordTrace tailWord_4376860 prefixEnd_4376860 2247432937437850748821193 := by
  unfold tailWord_4376860
  simp only [CollatzResearch.WordTrace]
  refine ⟨79818599461695601510472017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106424799282260802013962689 79818599461695601510472017)
  ·
    refine ⟨59863949596271701132854013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79818599461695601510472017 59863949596271701132854013)
    ·
      refine ⟨22448981098601887924820255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59863949596271701132854013 22448981098601887924820255)
      ·
        refine ⟨33673471647902831887230383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22448981098601887924820255 33673471647902831887230383)
        ·
          refine ⟨50510207471854247830845575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33673471647902831887230383 50510207471854247830845575)
          ·
            refine ⟨75765311207781371746268363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50510207471854247830845575 75765311207781371746268363)
            ·
              refine ⟨113647966811672057619402545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75765311207781371746268363 113647966811672057619402545)
              ·
                refine ⟨85235975108754043214551909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113647966811672057619402545 85235975108754043214551909)
                ·
                  refine ⟨15981745332891383102728483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85235975108754043214551909 15981745332891383102728483)
                  ·
                    refine ⟨23972617999337074654092725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15981745332891383102728483 23972617999337074654092725)
                    ·
                      refine ⟨2247432937437850748821193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23972617999337074654092725 2247432937437850748821193)
                      ·
                        rfl

theorem cell23_4376860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4376860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376860 prefixEnd_4376860 := by exact prefixLift 4376860
  have htrace : WordTrace (prefixWord ++ tailWord_4376860) baseStart_4376860 baseEnd_4376860 := by
    simpa [prefixWord, tailWord_4376860, baseEnd_4376860] using wordTrace_append hprefix tailTrace_4376860
  have hstable : (prefixWord ++ tailWord_4376860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376860).length < 2 ^ (prefixWord ++ tailWord_4376860).sum := by decide
  have hdescent : baseEnd_4376860 < baseStart_4376860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376910 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_4376910 : Nat := 118140960795 + 4376910 * 2 ^ 59
def prefixEnd_4376910 : Nat := 4983230072969 + 3 ^ 40 * 4376910 * 2
def baseEnd_4376910 : Nat := 749152870490191851065321

theorem tailTrace_4376910 : CollatzResearch.WordTrace tailWord_4376910 prefixEnd_4376910 749152870490191851065321 := by
  unfold tailWord_4376910
  simp only [CollatzResearch.WordTrace]
  refine ⟨19954877821651257695033023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106426015048806707706842789 19954877821651257695033023)
  ·
    refine ⟨29932316732476886542549535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19954877821651257695033023 29932316732476886542549535)
    ·
      refine ⟨44898475098715329813824303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29932316732476886542549535 44898475098715329813824303)
      ·
        refine ⟨67347712648072994720736455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44898475098715329813824303 67347712648072994720736455)
        ·
          refine ⟨101021568972109492081104683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67347712648072994720736455 101021568972109492081104683)
          ·
            refine ⟨151532353458164238121657025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101021568972109492081104683 151532353458164238121657025)
            ·
              refine ⟨113649265093623178591242769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151532353458164238121657025 113649265093623178591242769)
              ·
                refine ⟨85236948820217383943432077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113649265093623178591242769 85236948820217383943432077)
                ·
                  refine ⟨31963855807581518978787029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85236948820217383943432077 31963855807581518978787029)
                  ·
                    refine ⟨749152870490191851065321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31963855807581518978787029 749152870490191851065321)
                    ·
                      rfl

theorem cell23_4376910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_4376910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376910 prefixEnd_4376910 := by exact prefixLift 4376910
  have htrace : WordTrace (prefixWord ++ tailWord_4376910) baseStart_4376910 baseEnd_4376910 := by
    simpa [prefixWord, tailWord_4376910, baseEnd_4376910] using wordTrace_append hprefix tailTrace_4376910
  have hstable : (prefixWord ++ tailWord_4376910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376910).length < 2 ^ (prefixWord ++ tailWord_4376910).sum := by decide
  have hdescent : baseEnd_4376910 < baseStart_4376910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376947 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 6, 2]
def baseStart_4376947 : Nat := 118140960795 + 4376947 * 2 ^ 59
def prefixEnd_4376947 : Nat := 4983230072969 + 3 ^ 40 * 4376947 * 2
def baseEnd_4376947 : Nat := 2247477610254791908433293

theorem tailTrace_4376947 : CollatzResearch.WordTrace tailWord_4376947 prefixEnd_4376947 2247477610254791908433293 := by
  unfold tailWord_4376947
  simp only [CollatzResearch.WordTrace]
  refine ⟨159640372074076016879361095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106426914716050677919574063 159640372074076016879361095)
  ·
    refine ⟨239460558111114025319041643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159640372074076016879361095 239460558111114025319041643)
    ·
      refine ⟨359190837166671037978562465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239460558111114025319041643 359190837166671037978562465)
      ·
        refine ⟨269393127875003278483921849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359190837166671037978562465 269393127875003278483921849)
        ·
          refine ⟨202044845906252458862941387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269393127875003278483921849 202044845906252458862941387)
          ·
            refine ⟨303067268859378688294412081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202044845906252458862941387 303067268859378688294412081)
            ·
              refine ⟨227300451644534016220809061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303067268859378688294412081 227300451644534016220809061)
              ·
                refine ⟨42618834683350128041401699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227300451644534016220809061 42618834683350128041401699)
                ·
                  refine ⟨63928252025025192062102549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42618834683350128041401699 63928252025025192062102549)
                  ·
                    refine ⟨2996636813673055877911057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63928252025025192062102549 2996636813673055877911057)
                    ·
                      refine ⟨2247477610254791908433293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996636813673055877911057 2247477610254791908433293)
                      ·
                        rfl

theorem cell23_4376947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6, 2].length) (baseStart_4376947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376947 prefixEnd_4376947 := by exact prefixLift 4376947
  have htrace : WordTrace (prefixWord ++ tailWord_4376947) baseStart_4376947 baseEnd_4376947 := by
    simpa [prefixWord, tailWord_4376947, baseEnd_4376947] using wordTrace_append hprefix tailTrace_4376947
  have hstable : (prefixWord ++ tailWord_4376947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376947).length < 2 ^ (prefixWord ++ tailWord_4376947).sum := by decide
  have hdescent : baseEnd_4376947 < baseStart_4376947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4376964 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_4376964 : Nat := 118140960795 + 4376964 * 2 ^ 59
def prefixEnd_4376964 : Nat := 4983230072969 + 3 ^ 40 * 4376964 * 2
def baseEnd_4376964 : Nat := 2247486339425918341920715

theorem tailTrace_4376964 : CollatzResearch.WordTrace tailWord_4376964 prefixEnd_4376964 2247486339425918341920715 := by
  unfold tailWord_4376964
  simp only [CollatzResearch.WordTrace]
  refine ⟨79820496057507214391364973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106427328076676285855153297 79820496057507214391364973)
  ·
    refine ⟨29932686021565205396761865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79820496057507214391364973 29932686021565205396761865)
    ·
      refine ⟨22449514516173904047571399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29932686021565205396761865 22449514516173904047571399)
      ·
        refine ⟨33674271774260856071357099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22449514516173904047571399 33674271774260856071357099)
        ·
          refine ⟨50511407661391284107035649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33674271774260856071357099 50511407661391284107035649)
          ·
            refine ⟨37883555746043463080276737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50511407661391284107035649 37883555746043463080276737)
            ·
              refine ⟨28412666809532597310207553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37883555746043463080276737 28412666809532597310207553)
              ·
                refine ⟨21309500107149447982655665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28412666809532597310207553 21309500107149447982655665)
                ·
                  refine ⟨15982125080362085986991749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21309500107149447982655665 15982125080362085986991749)
                  ·
                    refine ⟨2996648452567891122560953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15982125080362085986991749 2996648452567891122560953)
                    ·
                      refine ⟨2247486339425918341920715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996648452567891122560953 2247486339425918341920715)
                      ·
                        rfl

theorem cell23_4376964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_4376964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4376964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4376964 prefixEnd_4376964 := by exact prefixLift 4376964
  have htrace : WordTrace (prefixWord ++ tailWord_4376964) baseStart_4376964 baseEnd_4376964 := by
    simpa [prefixWord, tailWord_4376964, baseEnd_4376964] using wordTrace_append hprefix tailTrace_4376964
  have hstable : (prefixWord ++ tailWord_4376964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4376964).length < 2 ^ (prefixWord ++ tailWord_4376964).sum := by decide
  have hdescent : baseEnd_4376964 < baseStart_4376964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4376964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377024 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 4, 3, 2]
def baseStart_4377024 : Nat := 118140960795 + 4377024 * 2 ^ 59
def prefixEnd_4377024 : Nat := 4983230072969 + 3 ^ 40 * 4377024 * 2
def baseEnd_4377024 : Nat := 2247517148265188107170439

theorem tailTrace_4377024 : CollatzResearch.WordTrace tailWord_4377024 prefixEnd_4377024 2247517148265188107170439 := by
  unfold tailWord_4377024
  simp only [CollatzResearch.WordTrace]
  refine ⟨79821590247398529514957063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106428786996531372686609417 79821590247398529514957063)
  ·
    refine ⟨119732385371097794272435595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79821590247398529514957063 119732385371097794272435595)
    ·
      refine ⟨179598578056646691408653393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119732385371097794272435595 179598578056646691408653393)
      ·
        refine ⟨134698933542485018556490045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179598578056646691408653393 134698933542485018556490045)
        ·
          refine ⟨50512100078431881958683767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134698933542485018556490045 50512100078431881958683767)
          ·
            refine ⟨75768150117647822938025651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50512100078431881958683767 75768150117647822938025651)
            ·
              refine ⟨113652225176471734407038477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75768150117647822938025651 113652225176471734407038477)
              ·
                refine ⟨42619584441176900402639429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113652225176471734407038477 42619584441176900402639429)
                ·
                  refine ⟨7991172082720668825494893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42619584441176900402639429 7991172082720668825494893)
                  ·
                    refine ⟨2996689531020250809560585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7991172082720668825494893 2996689531020250809560585)
                    ·
                      refine ⟨2247517148265188107170439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996689531020250809560585 2247517148265188107170439)
                      ·
                        rfl

theorem cell23_4377024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_4377024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377024 prefixEnd_4377024 := by exact prefixLift 4377024
  have htrace : WordTrace (prefixWord ++ tailWord_4377024) baseStart_4377024 baseEnd_4377024 := by
    simpa [prefixWord, tailWord_4377024, baseEnd_4377024] using wordTrace_append hprefix tailTrace_4377024
  have hstable : (prefixWord ++ tailWord_4377024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377024).length < 2 ^ (prefixWord ++ tailWord_4377024).sum := by decide
  have hdescent : baseEnd_4377024 < baseStart_4377024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377025 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4377025 : Nat := 118140960795 + 4377025 * 2 ^ 59
def prefixEnd_4377025 : Nat := 4983230072969 + 3 ^ 40 * 4377025 * 2
def baseEnd_4377025 : Nat := 749172553915280867752645

theorem tailTrace_4377025 : CollatzResearch.WordTrace tailWord_4377025 prefixEnd_4377025 749172553915280867752645 := by
  unfold tailWord_4377025
  simp only [CollatzResearch.WordTrace]
  refine ⟨159643216967793436200700529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106428811311862290800467019 159643216967793436200700529)
  ·
    refine ⟨119732412725845077150525397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159643216967793436200700529 119732412725845077150525397)
    ·
      refine ⟨2806228423261993995715439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 119732412725845077150525397 2806228423261993995715439)
      ·
        refine ⟨4209342634892990993573159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806228423261993995715439 4209342634892990993573159)
        ·
          refine ⟨6314013952339486490359739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209342634892990993573159 6314013952339486490359739)
          ·
            refine ⟨9471020928509229735539609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6314013952339486490359739 9471020928509229735539609)
            ·
              refine ⟨7103265696381922301654707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471020928509229735539609 7103265696381922301654707)
              ·
                refine ⟨10654898544572883452482061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7103265696381922301654707 10654898544572883452482061)
                ·
                  refine ⟨3995586954214831294680773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10654898544572883452482061 3995586954214831294680773)
                  ·
                    refine ⟨749172553915280867752645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3995586954214831294680773 749172553915280867752645)
                    ·
                      rfl

theorem cell23_4377025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4377025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377025 prefixEnd_4377025 := by exact prefixLift 4377025
  have htrace : WordTrace (prefixWord ++ tailWord_4377025) baseStart_4377025 baseEnd_4377025 := by
    simpa [prefixWord, tailWord_4377025, baseEnd_4377025] using wordTrace_append hprefix tailTrace_4377025
  have hstable : (prefixWord ++ tailWord_4377025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377025).length < 2 ^ (prefixWord ++ tailWord_4377025).sum := by decide
  have hdescent : baseEnd_4377025 < baseStart_4377025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377031 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_4377031 : Nat := 118140960795 + 4377031 * 2 ^ 59
def prefixEnd_4377031 : Nat := 4983230072969 + 3 ^ 40 * 4377031 * 2
def baseEnd_4377031 : Nat := 2247520742629769579782907

theorem tailTrace_4377031 : CollatzResearch.WordTrace tailWord_4377031 prefixEnd_4377031 2247520742629769579782907 := by
  unfold tailWord_4377031
  simp only [CollatzResearch.WordTrace]
  refine ⟨159643435805771699225418947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106428957203847799483612631 159643435805771699225418947)
  ·
    refine ⟨239465153708657548838128421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159643435805771699225418947 239465153708657548838128421)
    ·
      refine ⟨44899716320373290407149079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239465153708657548838128421 44899716320373290407149079)
      ·
        refine ⟨67349574480559935610723619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44899716320373290407149079 67349574480559935610723619)
        ·
          refine ⟨101024361720839903416085429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67349574480559935610723619 101024361720839903416085429)
          ·
            refine ⟨9471033911328740945258009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101024361720839903416085429 9471033911328740945258009)
            ·
              refine ⟨7103275433496555708943507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471033911328740945258009 7103275433496555708943507)
              ·
                refine ⟨10654913150244833563415261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7103275433496555708943507 10654913150244833563415261)
                ·
                  refine ⟨3995592431341812586280723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10654913150244833563415261 3995592431341812586280723)
                  ·
                    refine ⟨5993388647012718879421085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3995592431341812586280723 5993388647012718879421085)
                    ·
                      refine ⟨2247520742629769579782907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993388647012718879421085 2247520742629769579782907)
                      ·
                        rfl

theorem cell23_4377031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_4377031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377031 prefixEnd_4377031 := by exact prefixLift 4377031
  have htrace : WordTrace (prefixWord ++ tailWord_4377031) baseStart_4377031 baseEnd_4377031 := by
    simpa [prefixWord, tailWord_4377031, baseEnd_4377031] using wordTrace_append hprefix tailTrace_4377031
  have hstable : (prefixWord ++ tailWord_4377031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377031).length < 2 ^ (prefixWord ++ tailWord_4377031).sum := by decide
  have hdescent : baseEnd_4377031 < baseStart_4377031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377057 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_4377057 : Nat := 118140960795 + 4377057 * 2 ^ 59
def prefixEnd_4377057 : Nat := 4983230072969 + 3 ^ 40 * 4377057 * 2
def baseEnd_4377057 : Nat := 2247534093126786478057787

theorem tailTrace_4377057 : CollatzResearch.WordTrace tailWord_4377057 prefixEnd_4377057 2247534093126786478057787 := by
  unfold tailWord_4377057
  simp only [CollatzResearch.WordTrace]
  refine ⟨159644384103677505665865425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106429589402451670443910283 159644384103677505665865425)
  ·
    refine ⟨119733288077758129249399069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159644384103677505665865425 119733288077758129249399069)
    ·
      refine ⟨44899983029159298468524651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119733288077758129249399069 44899983029159298468524651)
      ·
        refine ⟨67349974543738947702786977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44899983029159298468524651 67349974543738947702786977)
        ·
          refine ⟨50512480907804210777090233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67349974543738947702786977 50512480907804210777090233)
          ·
            refine ⟨37884360680853158082817675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50512480907804210777090233 37884360680853158082817675)
            ·
              refine ⟨56826541021279737124226513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37884360680853158082817675 56826541021279737124226513)
              ·
                refine ⟨42619905765959802843169885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56826541021279737124226513 42619905765959802843169885)
                ·
                  refine ⟨15982464662234926066188707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42619905765959802843169885 15982464662234926066188707)
                  ·
                    refine ⟨23973696993352389099283061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15982464662234926066188707 23973696993352389099283061)
                    ·
                      refine ⟨2247534093126786478057787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23973696993352389099283061 2247534093126786478057787)
                      ·
                        rfl

theorem cell23_4377057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_4377057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377057 prefixEnd_4377057 := by exact prefixLift 4377057
  have htrace : WordTrace (prefixWord ++ tailWord_4377057) baseStart_4377057 baseEnd_4377057 := by
    simpa [prefixWord, tailWord_4377057, baseEnd_4377057] using wordTrace_append hprefix tailTrace_4377057
  have hstable : (prefixWord ++ tailWord_4377057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377057).length < 2 ^ (prefixWord ++ tailWord_4377057).sum := by decide
  have hdescent : baseEnd_4377057 < baseStart_4377057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377064 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 4, 4]
def baseStart_4377064 : Nat := 118140960795 + 4377064 * 2 ^ 59
def prefixEnd_4377064 : Nat := 4983230072969 + 3 ^ 40 * 4377064 * 2
def baseEnd_4377064 : Nat := 749179229163789316890085

theorem tailTrace_4377064 : CollatzResearch.WordTrace tailWord_4377064 prefixEnd_4377064 749179229163789316890085 := by
  unfold tailWord_4377064
  simp only [CollatzResearch.WordTrace]
  refine ⟨79822319707326072930685123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106429759609768097240913497 79822319707326072930685123)
  ·
    refine ⟨119733479560989109396027685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79822319707326072930685123 119733479560989109396027685)
    ·
      refine ⟨22450027417685458011755191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119733479560989109396027685 22450027417685458011755191)
      ·
        refine ⟨33675041126528187017632787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22450027417685458011755191 33675041126528187017632787)
        ·
          refine ⟨50512561689792280526449181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33675041126528187017632787 50512561689792280526449181)
          ·
            refine ⟨18942210633672105197418443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50512561689792280526449181 18942210633672105197418443)
            ·
              refine ⟨28413315950508157796127665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18942210633672105197418443 28413315950508157796127665)
              ·
                refine ⟨21309986962881118347095749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28413315950508157796127665 21309986962881118347095749)
                ·
                  refine ⟨3995622555540209690080453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21309986962881118347095749 3995622555540209690080453)
                  ·
                    refine ⟨749179229163789316890085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3995622555540209690080453 749179229163789316890085)
                    ·
                      rfl

theorem cell23_4377064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_4377064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377064 prefixEnd_4377064 := by exact prefixLift 4377064
  have htrace : WordTrace (prefixWord ++ tailWord_4377064) baseStart_4377064 baseEnd_4377064 := by
    simpa [prefixWord, tailWord_4377064, baseEnd_4377064] using wordTrace_append hprefix tailTrace_4377064
  have hstable : (prefixWord ++ tailWord_4377064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377064).length < 2 ^ (prefixWord ++ tailWord_4377064).sum := by decide
  have hdescent : baseEnd_4377064 < baseStart_4377064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377067 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4]
def baseStart_4377067 : Nat := 118140960795 + 4377067 * 2 ^ 59
def prefixEnd_4377067 : Nat := 4983230072969 + 3 ^ 40 * 4377067 * 2
def baseEnd_4377067 : Nat := 2247539227933331438932741

theorem tailTrace_4377067 : CollatzResearch.WordTrace tailWord_4377067 prefixEnd_4377067 2247539227933331438932741 := by
  unfold tailWord_4377067
  simp only [CollatzResearch.WordTrace]
  refine ⟨159644748833641277373729455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106429832555760851582486303 159644748833641277373729455)
  ·
    refine ⟨239467123250461916060594183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159644748833641277373729455 239467123250461916060594183)
    ·
      refine ⟨359200684875692874090891275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239467123250461916060594183 359200684875692874090891275)
      ·
        refine ⟨538801027313539311136336913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359200684875692874090891275 538801027313539311136336913)
        ·
          refine ⟨404100770485154483352252685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538801027313539311136336913 404100770485154483352252685)
          ·
            refine ⟨151537788931932931257094757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 404100770485154483352252685 151537788931932931257094757)
            ·
              refine ⟨28413335424737424610705267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151537788931932931257094757 28413335424737424610705267)
              ·
                refine ⟨42620003137106136916057901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28413335424737424610705267 42620003137106136916057901)
                ·
                  refine ⟨15982501176414801343521713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42620003137106136916057901 15982501176414801343521713)
                  ·
                    refine ⟨11986875882311101007641285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15982501176414801343521713 11986875882311101007641285)
                    ·
                      refine ⟨2247539227933331438932741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11986875882311101007641285 2247539227933331438932741)
                      ·
                        rfl

theorem cell23_4377067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_4377067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377067 prefixEnd_4377067 := by exact prefixLift 4377067
  have htrace : WordTrace (prefixWord ++ tailWord_4377067) baseStart_4377067 baseEnd_4377067 := by
    simpa [prefixWord, tailWord_4377067, baseEnd_4377067] using wordTrace_append hprefix tailTrace_4377067
  have hstable : (prefixWord ++ tailWord_4377067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377067).length < 2 ^ (prefixWord ++ tailWord_4377067).sum := by decide
  have hdescent : baseEnd_4377067 < baseStart_4377067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377108 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4377108 : Nat := 118140960795 + 4377108 * 2 ^ 59
def prefixEnd_4377108 : Nat := 4983230072969 + 3 ^ 40 * 4377108 * 2
def baseEnd_4377108 : Nat := 2247560280640165778520053

theorem tailTrace_4377108 : CollatzResearch.WordTrace tailWord_4377108 prefixEnd_4377108 2247560280640165778520053 := by
  unfold tailWord_4377108
  simp only [CollatzResearch.WordTrace]
  refine ⟨79823122113246370687985989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106430829484328494250647985 79823122113246370687985989)
  ·
    refine ⟨14966835396233694503997373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79823122113246370687985989 14966835396233694503997373)
    ·
      refine ⟨5612563273587635438999015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14966835396233694503997373 5612563273587635438999015)
      ·
        refine ⟨8418844910381453158498523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5612563273587635438999015 8418844910381453158498523)
        ·
          refine ⟨12628267365572179737747785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8418844910381453158498523 12628267365572179737747785)
          ·
            refine ⟨9471200524179134803310839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12628267365572179737747785 9471200524179134803310839)
            ·
              refine ⟨14206800786268702204966259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9471200524179134803310839 14206800786268702204966259)
              ·
                refine ⟨21310201179403053307449389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14206800786268702204966259 21310201179403053307449389)
                ·
                  refine ⟨7991325442276144990293521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21310201179403053307449389 7991325442276144990293521)
                  ·
                    refine ⟨5993494081707108742720141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7991325442276144990293521 5993494081707108742720141)
                    ·
                      refine ⟨2247560280640165778520053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993494081707108742720141 2247560280640165778520053)
                      ·
                        rfl

theorem cell23_4377108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4377108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377108 prefixEnd_4377108 := by exact prefixLift 4377108
  have htrace : WordTrace (prefixWord ++ tailWord_4377108) baseStart_4377108 baseEnd_4377108 := by
    simpa [prefixWord, tailWord_4377108, baseEnd_4377108] using wordTrace_append hprefix tailTrace_4377108
  have hstable : (prefixWord ++ tailWord_4377108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377108).length < 2 ^ (prefixWord ++ tailWord_4377108).sum := by decide
  have hdescent : baseEnd_4377108 < baseStart_4377108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377131 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 1, 3, 2]
def baseStart_4377131 : Nat := 118140960795 + 4377131 * 2 ^ 59
def prefixEnd_4377131 : Nat := 4983230072969 + 3 ^ 40 * 4377131 * 2
def baseEnd_4377131 : Nat := 2247572090695219188532447

theorem tailTrace_4377131 : CollatzResearch.WordTrace tailWord_4377131 prefixEnd_4377131 2247572090695219188532447 := by
  unfold tailWord_4377131
  simp only [CollatzResearch.WordTrace]
  refine ⟨159647083105409416304059247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106431388736939610869372831 159647083105409416304059247)
  ·
    refine ⟨239470624658114124456088871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159647083105409416304059247 239470624658114124456088871)
    ·
      refine ⟨359205936987171186684133307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239470624658114124456088871 359205936987171186684133307)
      ·
        refine ⟨538808905480756780026199961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359205936987171186684133307 538808905480756780026199961)
        ·
          refine ⟨404106679110567585019649971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538808905480756780026199961 404106679110567585019649971)
          ·
            refine ⟨606160018665851377529474957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404106679110567585019649971 606160018665851377529474957)
            ·
              refine ⟨227310006999694266573553109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606160018665851377529474957 227310006999694266573553109)
              ·
                refine ⟨5327578289055334372817651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 227310006999694266573553109 5327578289055334372817651)
                ·
                  refine ⟨7991367433583001559226477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5327578289055334372817651 7991367433583001559226477)
                  ·
                    refine ⟨2996762787593625584709929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7991367433583001559226477 2996762787593625584709929)
                    ·
                      refine ⟨2247572090695219188532447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996762787593625584709929 2247572090695219188532447)
                      ·
                        rfl

theorem cell23_4377131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 3, 2].length) (baseStart_4377131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377131 prefixEnd_4377131 := by exact prefixLift 4377131
  have htrace : WordTrace (prefixWord ++ tailWord_4377131) baseStart_4377131 baseEnd_4377131 := by
    simpa [prefixWord, tailWord_4377131, baseEnd_4377131] using wordTrace_append hprefix tailTrace_4377131
  have hstable : (prefixWord ++ tailWord_4377131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377131).length < 2 ^ (prefixWord ++ tailWord_4377131).sum := by decide
  have hdescent : baseEnd_4377131 < baseStart_4377131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377133 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4377133 : Nat := 118140960795 + 4377133 * 2 ^ 59
def prefixEnd_4377133 : Nat := 4983230072969 + 3 ^ 40 * 4377133 * 2
def baseEnd_4377133 : Nat := 2247573117656528180707439

theorem tailTrace_4377133 : CollatzResearch.WordTrace tailWord_4377133 prefixEnd_4377133 2247573117656528180707439 := by
  unfold tailWord_4377133
  simp only [CollatzResearch.WordTrace]
  refine ⟨159647156051402170645632053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106431437367601447097088035 159647156051402170645632053)
  ·
    refine ⟨14966920879818953498028005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159647156051402170645632053 14966920879818953498028005)
    ·
      refine ⟨2806297664966053780880251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14966920879818953498028005 2806297664966053780880251)
      ·
        refine ⟨4209446497449080671320377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806297664966053780880251 4209446497449080671320377)
        ·
          refine ⟨3157084873086810503490283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4209446497449080671320377 3157084873086810503490283)
          ·
            refine ⟨4735627309630215755235425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157084873086810503490283 4735627309630215755235425)
            ·
              refine ⟨3551720482222661816426569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4735627309630215755235425 3551720482222661816426569)
              ·
                refine ⟨2663790361666996362319927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3551720482222661816426569 2663790361666996362319927)
                ·
                  refine ⟨3995685542500494543479891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663790361666996362319927 3995685542500494543479891)
                  ·
                    refine ⟨5993528313750741815219837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3995685542500494543479891 5993528313750741815219837)
                    ·
                      refine ⟨2247573117656528180707439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993528313750741815219837 2247573117656528180707439)
                      ·
                        rfl

theorem cell23_4377133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4377133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377133 prefixEnd_4377133 := by exact prefixLift 4377133
  have htrace : WordTrace (prefixWord ++ tailWord_4377133) baseStart_4377133 baseEnd_4377133 := by
    simpa [prefixWord, tailWord_4377133, baseEnd_4377133] using wordTrace_append hprefix tailTrace_4377133
  have hstable : (prefixWord ++ tailWord_4377133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377133).length < 2 ^ (prefixWord ++ tailWord_4377133).sum := by decide
  have hdescent : baseEnd_4377133 < baseStart_4377133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377161 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 8, 2, 2]
def baseStart_4377161 : Nat := 118140960795 + 4377161 * 2 ^ 59
def prefixEnd_4377161 : Nat := 4983230072969 + 3 ^ 40 * 4377161 * 2
def baseEnd_4377161 : Nat := 2247587495114854071157309

theorem tailTrace_4377161 : CollatzResearch.WordTrace tailWord_4377161 prefixEnd_4377161 2247587495114854071157309 := by
  unfold tailWord_4377161
  simp only [CollatzResearch.WordTrace]
  refine ⟨159648177295300731427651337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106432118196867154285100891 159648177295300731427651337)
  ·
    refine ⟨119736132971475548570738503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159648177295300731427651337 119736132971475548570738503)
    ·
      refine ⟨179604199457213322856107755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119736132971475548570738503 179604199457213322856107755)
      ·
        refine ⟨269406299185819984284161633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179604199457213322856107755 269406299185819984284161633)
        ·
          refine ⟨202054724389364988213121225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269406299185819984284161633 202054724389364988213121225)
          ·
            refine ⟨151541043292023741159840919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202054724389364988213121225 151541043292023741159840919)
            ·
              refine ⟨227311564938035611739761379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151541043292023741159840919 227311564938035611739761379)
              ·
                refine ⟨340967347407053417609642069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227311564938035611739761379 340967347407053417609642069)
                ·
                  refine ⟨3995711102426407237612993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 340967347407053417609642069 3995711102426407237612993)
                  ·
                    refine ⟨2996783326819805428209745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3995711102426407237612993 2996783326819805428209745)
                    ·
                      refine ⟨2247587495114854071157309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996783326819805428209745 2247587495114854071157309)
                      ·
                        rfl

theorem cell23_4377161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 2, 2].length) (baseStart_4377161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377161 prefixEnd_4377161 := by exact prefixLift 4377161
  have htrace : WordTrace (prefixWord ++ tailWord_4377161) baseStart_4377161 baseEnd_4377161 := by
    simpa [prefixWord, tailWord_4377161, baseEnd_4377161] using wordTrace_append hprefix tailTrace_4377161
  have hstable : (prefixWord ++ tailWord_4377161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377161).length < 2 ^ (prefixWord ++ tailWord_4377161).sum := by decide
  have hdescent : baseEnd_4377161 < baseStart_4377161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377164 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4377164 : Nat := 118140960795 + 4377164 * 2 ^ 59
def prefixEnd_4377164 : Nat := 4983230072969 + 3 ^ 40 * 4377164 * 2
def baseEnd_4377164 : Nat := 2247589035556817559419795

theorem tailTrace_4377164 : CollatzResearch.WordTrace tailWord_4377164 prefixEnd_4377164 2247589035556817559419795 := by
  unfold tailWord_4377164
  simp only [CollatzResearch.WordTrace]
  refine ⟨79824143357144931470005273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106432191142859908626673697 79824143357144931470005273)
  ·
    refine ⟨59868107517858698602503955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79824143357144931470005273 59868107517858698602503955)
    ·
      refine ⟨89802161276788047903755933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59868107517858698602503955 89802161276788047903755933)
      ·
        refine ⟨33675810478795517963908475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89802161276788047903755933 33675810478795517963908475)
        ·
          refine ⟨50513715718193276945862713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33675810478795517963908475 50513715718193276945862713)
          ·
            refine ⟨37885286788644957709397035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50513715718193276945862713 37885286788644957709397035)
            ·
              refine ⟨56827930182967436564095553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37885286788644957709397035 56827930182967436564095553)
              ·
                refine ⟨42620947637225577423071665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56827930182967436564095553 42620947637225577423071665)
                ·
                  refine ⟨31965710727919183067303749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42620947637225577423071665 31965710727919183067303749)
                  ·
                    refine ⟨5993570761484846825119453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31965710727919183067303749 5993570761484846825119453)
                    ·
                      refine ⟨2247589035556817559419795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993570761484846825119453 2247589035556817559419795)
                      ·
                        rfl

theorem cell23_4377164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4377164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377164 prefixEnd_4377164 := by exact prefixLift 4377164
  have htrace : WordTrace (prefixWord ++ tailWord_4377164) baseStart_4377164 baseEnd_4377164 := by
    simpa [prefixWord, tailWord_4377164, baseEnd_4377164] using wordTrace_append hprefix tailTrace_4377164
  have hstable : (prefixWord ++ tailWord_4377164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377164).length < 2 ^ (prefixWord ++ tailWord_4377164).sum := by decide
  have hdescent : baseEnd_4377164 < baseStart_4377164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377167 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 9]
def baseStart_4377167 : Nat := 118140960795 + 4377167 * 2 ^ 59
def prefixEnd_4377167 : Nat := 4983230072969 + 3 ^ 40 * 4377167 * 2
def baseEnd_4377167 : Nat := 249732286222086783075809

theorem tailTrace_4377167 : CollatzResearch.WordTrace tailWord_4377167 prefixEnd_4377167 249732286222086783075809 := by
  unfold tailWord_4377167
  simp only [CollatzResearch.WordTrace]
  refine ⟨159648396133278994452369755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106432264088852662968246503 159648396133278994452369755)
  ·
    refine ⟨239472594199918491678554633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159648396133278994452369755 239472594199918491678554633)
    ·
      refine ⟨179604445649938868758915975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239472594199918491678554633 179604445649938868758915975)
      ·
        refine ⟨269406668474908303138373963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179604445649938868758915975 269406668474908303138373963)
        ·
          refine ⟨404110002712362454707560945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269406668474908303138373963 404110002712362454707560945)
          ·
            refine ⟨303082502034271841030670709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404110002712362454707560945 303082502034271841030670709)
            ·
              refine ⟨28413984565712985096625379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 303082502034271841030670709 28413984565712985096625379)
              ·
                refine ⟨42620976848569477644938069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28413984565712985096625379 42620976848569477644938069)
                ·
                  refine ⟨249732286222086783075809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42620976848569477644938069 249732286222086783075809)
                  ·
                    rfl

theorem cell23_4377167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 9].length) (baseStart_4377167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377167 prefixEnd_4377167 := by exact prefixLift 4377167
  have htrace : WordTrace (prefixWord ++ tailWord_4377167) baseStart_4377167 baseEnd_4377167 := by
    simpa [prefixWord, tailWord_4377167, baseEnd_4377167] using wordTrace_append hprefix tailTrace_4377167
  have hstable : (prefixWord ++ tailWord_4377167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377167).length < 2 ^ (prefixWord ++ tailWord_4377167).sum := by decide
  have hdescent : baseEnd_4377167 < baseStart_4377167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377177 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_4377177 : Nat := 118140960795 + 4377177 * 2 ^ 59
def prefixEnd_4377177 : Nat := 4983230072969 + 3 ^ 40 * 4377177 * 2
def baseEnd_4377177 : Nat := 2247595710805326008557235

theorem tailTrace_4377177 : CollatzResearch.WordTrace tailWord_4377177 prefixEnd_4377177 2247595710805326008557235 := by
  unfold tailWord_4377177
  simp only [CollatzResearch.WordTrace]
  refine ⟨159648760863242766160233785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106432507242161844106822523 159648760863242766160233785)
  ·
    refine ⟨119736570647432074620175339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159648760863242766160233785 119736570647432074620175339)
    ·
      refine ⟨179604855971148111930263009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119736570647432074620175339 179604855971148111930263009)
      ·
        refine ⟨134703641978361083947697257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179604855971148111930263009 134703641978361083947697257)
        ·
          refine ⟨101027731483770812960772943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134703641978361083947697257 101027731483770812960772943)
          ·
            refine ⟨151541597225656219441159415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101027731483770812960772943 151541597225656219441159415)
            ·
              refine ⟨227312395838484329161739123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151541597225656219441159415 227312395838484329161739123)
              ·
                refine ⟨340968593757726493742608685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227312395838484329161739123 340968593757726493742608685)
                ·
                  refine ⟨127863222659147435153478257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340968593757726493742608685 127863222659147435153478257)
                  ·
                    refine ⟨95897416994360576365108693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127863222659147435153478257 95897416994360576365108693)
                    ·
                      refine ⟨2247595710805326008557235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95897416994360576365108693 2247595710805326008557235)
                      ·
                        rfl

theorem cell23_4377177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_4377177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377177 prefixEnd_4377177 := by exact prefixLift 4377177
  have htrace : WordTrace (prefixWord ++ tailWord_4377177) baseStart_4377177 baseEnd_4377177 := by
    simpa [prefixWord, tailWord_4377177, baseEnd_4377177] using wordTrace_append hprefix tailTrace_4377177
  have hstable : (prefixWord ++ tailWord_4377177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377177).length < 2 ^ (prefixWord ++ tailWord_4377177).sum := by decide
  have hdescent : baseEnd_4377177 < baseStart_4377177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377251 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 2, 4, 2]
def baseStart_4377251 : Nat := 118140960795 + 4377251 * 2 ^ 59
def prefixEnd_4377251 : Nat := 4983230072969 + 3 ^ 40 * 4377251 * 2
def baseEnd_4377251 : Nat := 2247633708373758719031895

theorem tailTrace_4377251 : CollatzResearch.WordTrace tailWord_4377251 prefixEnd_4377251 2247633708373758719031895 := by
  unfold tailWord_4377251
  simp only [CollatzResearch.WordTrace]
  refine ⟨159651459864974676798427607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106434306576649784532285071 159651459864974676798427607)
  ·
    refine ⟨239477189797462015197641411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159651459864974676798427607 239477189797462015197641411)
    ·
      refine ⟨359215784696193022796462117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239477189797462015197641411 359215784696193022796462117)
      ·
        refine ⟨67352959630536191774336647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 359215784696193022796462117 67352959630536191774336647)
        ·
          refine ⟨101029439445804287661504971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67352959630536191774336647 101029439445804287661504971)
          ·
            refine ⟨151544159168706431492257457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101029439445804287661504971 151544159168706431492257457)
            ·
              refine ⟨113658119376529823619193093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151544159168706431492257457 113658119376529823619193093)
              ·
                refine ⟨21310897383099341928598705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113658119376529823619193093 21310897383099341928598705)
                ·
                  refine ⟨15983173037324506446449029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21310897383099341928598705 15983173037324506446449029)
                  ·
                    refine ⟨2996844944498344958709193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15983173037324506446449029 2996844944498344958709193)
                    ·
                      refine ⟨2247633708373758719031895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996844944498344958709193 2247633708373758719031895)
                      ·
                        rfl

theorem cell23_4377251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_4377251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377251 prefixEnd_4377251 := by exact prefixLift 4377251
  have htrace : WordTrace (prefixWord ++ tailWord_4377251) baseStart_4377251 baseEnd_4377251 := by
    simpa [prefixWord, tailWord_4377251, baseEnd_4377251] using wordTrace_append hprefix tailTrace_4377251
  have hstable : (prefixWord ++ tailWord_4377251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377251).length < 2 ^ (prefixWord ++ tailWord_4377251).sum := by decide
  have hdescent : baseEnd_4377251 < baseStart_4377251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377288 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_4377288 : Nat := 118140960795 + 4377288 * 2 ^ 59
def prefixEnd_4377288 : Nat := 4983230072969 + 3 ^ 40 * 4377288 * 2
def baseEnd_4377288 : Nat := 2247652707157975074269225

theorem tailTrace_4377288 : CollatzResearch.WordTrace tailWord_4377288 prefixEnd_4377288 2247652707157975074269225 := by
  unfold tailWord_4377288
  simp only [CollatzResearch.WordTrace]
  refine ⟨79826404682920316058762259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106435206243893754745016345 79826404682920316058762259)
  ·
    refine ⟨119739607024380474088143389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79826404682920316058762259 119739607024380474088143389)
    ·
      refine ⟨44902352634142677783053771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119739607024380474088143389 44902352634142677783053771)
      ·
        refine ⟨67353528951214016674580657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44902352634142677783053771 67353528951214016674580657)
        ·
          refine ⟨50515146713410512505935493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67353528951214016674580657 50515146713410512505935493)
          ·
            refine ⟨9471590008764471094862905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50515146713410512505935493 9471590008764471094862905)
            ·
              refine ⟨7103692506573353321147179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471590008764471094862905 7103692506573353321147179)
              ·
                refine ⟨10655538759860029981720769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7103692506573353321147179 10655538759860029981720769)
                ·
                  refine ⟨7991654069895022486290577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10655538759860029981720769 7991654069895022486290577)
                  ·
                    refine ⟨5993740552421266864717933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7991654069895022486290577 5993740552421266864717933)
                    ·
                      refine ⟨2247652707157975074269225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993740552421266864717933 2247652707157975074269225)
                      ·
                        rfl

theorem cell23_4377288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_4377288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377288 prefixEnd_4377288 := by exact prefixLift 4377288
  have htrace : WordTrace (prefixWord ++ tailWord_4377288) baseStart_4377288 baseEnd_4377288 := by
    simpa [prefixWord, tailWord_4377288, baseEnd_4377288] using wordTrace_append hprefix tailTrace_4377288
  have hstable : (prefixWord ++ tailWord_4377288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377288).length < 2 ^ (prefixWord ++ tailWord_4377288).sum := by decide
  have hdescent : baseEnd_4377288 < baseStart_4377288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377308 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 6]
def baseStart_4377308 : Nat := 118140960795 + 4377308 * 2 ^ 59
def prefixEnd_4377308 : Nat := 4983230072969 + 3 ^ 40 * 4377308 * 2
def baseEnd_4377308 : Nat := 249740330752340555113237

theorem tailTrace_4377308 : CollatzResearch.WordTrace tailWord_4377308 prefixEnd_4377308 249740330752340555113237 := by
  unfold tailWord_4377308
  simp only [CollatzResearch.WordTrace]
  refine ⟨79826769412884087766626289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106435692550512117022168385 79826769412884087766626289)
  ·
    refine ⟨59870077059663065824969717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79826769412884087766626289 59870077059663065824969717)
    ·
      refine ⟨5612819724343412421090911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59870077059663065824969717 5612819724343412421090911)
      ·
        refine ⟨8419229586515118631636367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5612819724343412421090911 8419229586515118631636367)
        ·
          refine ⟨12628844379772677947454551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8419229586515118631636367 12628844379772677947454551)
          ·
            refine ⟨18943266569659016921181827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12628844379772677947454551 18943266569659016921181827)
            ·
              refine ⟨28414899854488525381772741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18943266569659016921181827 28414899854488525381772741)
              ·
                refine ⟨5327793722716598509082389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28414899854488525381772741 5327793722716598509082389)
                ·
                  refine ⟨249740330752340555113237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5327793722716598509082389 249740330752340555113237)
                  ·
                    rfl

theorem cell23_4377308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_4377308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377308 prefixEnd_4377308 := by exact prefixLift 4377308
  have htrace : WordTrace (prefixWord ++ tailWord_4377308) baseStart_4377308 baseEnd_4377308 := by
    simpa [prefixWord, tailWord_4377308, baseEnd_4377308] using wordTrace_append hprefix tailTrace_4377308
  have hstable : (prefixWord ++ tailWord_4377308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377308).length < 2 ^ (prefixWord ++ tailWord_4377308).sum := by decide
  have hdescent : baseEnd_4377308 < baseStart_4377308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377341 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_4377341 : Nat := 118140960795 + 4377341 * 2 ^ 59
def prefixEnd_4377341 : Nat := 4983230072969 + 3 ^ 40 * 4377341 * 2
def baseEnd_4377341 : Nat := 2247679921632663366906481

theorem tailTrace_4377341 : CollatzResearch.WordTrace tailWord_4377341 prefixEnd_4377341 2247679921632663366906481 := by
  unfold tailWord_4377341
  simp only [CollatzResearch.WordTrace]
  refine ⟨159654742434648622169203877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106436494956432414779469251 159654742434648622169203877)
  ·
    refine ⟨29935264206496616656725727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159654742434648622169203877 29935264206496616656725727)
    ·
      refine ⟨44902896309744924985088591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29935264206496616656725727 44902896309744924985088591)
      ·
        refine ⟨67354344464617387477632887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44902896309744924985088591 67354344464617387477632887)
        ·
          refine ⟨101031516696926081216449331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67354344464617387477632887 101031516696926081216449331)
          ·
            refine ⟨151547275045389121824673997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101031516696926081216449331 151547275045389121824673997)
            ·
              refine ⟨56830228142020920684252749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151547275045389121824673997 56830228142020920684252749)
              ·
                refine ⟨21311335553257845256594781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56830228142020920684252749 21311335553257845256594781)
                ·
                  refine ⟨7991750832471691971223043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21311335553257845256594781 7991750832471691971223043)
                  ·
                    refine ⟨11987626248707537956834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7991750832471691971223043 11987626248707537956834565)
                    ·
                      refine ⟨2247679921632663366906481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11987626248707537956834565 2247679921632663366906481)
                      ·
                        rfl

theorem cell23_4377341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_4377341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377341 prefixEnd_4377341 := by exact prefixLift 4377341
  have htrace : WordTrace (prefixWord ++ tailWord_4377341) baseStart_4377341 baseEnd_4377341 := by
    simpa [prefixWord, tailWord_4377341, baseEnd_4377341] using wordTrace_append hprefix tailTrace_4377341
  have hstable : (prefixWord ++ tailWord_4377341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377341).length < 2 ^ (prefixWord ++ tailWord_4377341).sum := by decide
  have hdescent : baseEnd_4377341 < baseStart_4377341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377344 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_4377344 : Nat := 118140960795 + 4377344 * 2 ^ 59
def prefixEnd_4377344 : Nat := 4983230072969 + 3 ^ 40 * 4377344 * 2
def baseEnd_4377344 : Nat := 2247681462074626855168967

theorem tailTrace_4377344 : CollatzResearch.WordTrace tailWord_4377344 prefixEnd_4377344 2247681462074626855168967 := by
  unfold tailWord_4377344
  simp only [CollatzResearch.WordTrace]
  refine ⟨79827425926818876840781543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106436567902425169121042057 79827425926818876840781543)
  ·
    refine ⟨119741138890228315261172315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79827425926818876840781543 119741138890228315261172315)
    ·
      refine ⟨179611708335342472891758473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119741138890228315261172315 179611708335342472891758473)
      ·
        refine ⟨134708781251506854668818855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179611708335342472891758473 134708781251506854668818855)
        ·
          refine ⟨202063171877260282003228283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134708781251506854668818855 202063171877260282003228283)
          ·
            refine ⟨303094757815890423004842425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202063171877260282003228283 303094757815890423004842425)
            ·
              refine ⟨227321068361917817253631819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303094757815890423004842425 227321068361917817253631819)
              ·
                refine ⟨340981602542876725880447729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227321068361917817253631819 340981602542876725880447729)
                ·
                  refine ⟨255736201907157544410335797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340981602542876725880447729 255736201907157544410335797)
                  ·
                    refine ⟨23975268928796019788468981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255736201907157544410335797 23975268928796019788468981)
                    ·
                      refine ⟨2247681462074626855168967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23975268928796019788468981 2247681462074626855168967)
                      ·
                        rfl

theorem cell23_4377344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_4377344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377344 prefixEnd_4377344 := by exact prefixLift 4377344
  have htrace : WordTrace (prefixWord ++ tailWord_4377344) baseStart_4377344 baseEnd_4377344 := by
    simpa [prefixWord, tailWord_4377344, baseEnd_4377344] using wordTrace_append hprefix tailTrace_4377344
  have hstable : (prefixWord ++ tailWord_4377344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377344).length < 2 ^ (prefixWord ++ tailWord_4377344).sum := by decide
  have hdescent : baseEnd_4377344 < baseStart_4377344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377352 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_4377352 : Nat := 118140960795 + 4377352 * 2 ^ 59
def prefixEnd_4377352 : Nat := 4983230072969 + 3 ^ 40 * 4377352 * 2
def baseEnd_4377352 : Nat := 2247685569919862823868931

theorem tailTrace_4377352 : CollatzResearch.WordTrace tailWord_4377352 prefixEnd_4377352 2247685569919862823868931 := by
  unfold tailWord_4377352
  simp only [CollatzResearch.WordTrace]
  refine ⟨79827571818804385523927155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106436762425072514031902873 79827571818804385523927155)
  ·
    refine ⟨119741357728206578285890733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79827571818804385523927155 119741357728206578285890733)
    ·
      refine ⟨44903009148077466857209025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119741357728206578285890733 44903009148077466857209025)
      ·
        refine ⟨33677256861058100142906769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44903009148077466857209025 33677256861058100142906769)
        ·
          refine ⟨25257942645793575107180077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33677256861058100142906769 25257942645793575107180077)
          ·
            refine ⟨9471728492172590665192529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25257942645793575107180077 9471728492172590665192529)
            ·
              refine ⟨7103796369129442998894397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471728492172590665192529 7103796369129442998894397)
              ·
                refine ⟨2663923638423541124585399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7103796369129442998894397 2663923638423541124585399)
                ·
                  refine ⟨3995885457635311686878099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663923638423541124585399 3995885457635311686878099)
                  ·
                    refine ⟨5993828186452967530317149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3995885457635311686878099 5993828186452967530317149)
                    ·
                      refine ⟨2247685569919862823868931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993828186452967530317149 2247685569919862823868931)
                      ·
                        rfl

theorem cell23_4377352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_4377352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377352 prefixEnd_4377352 := by exact prefixLift 4377352
  have htrace : WordTrace (prefixWord ++ tailWord_4377352) baseStart_4377352 baseEnd_4377352 := by
    simpa [prefixWord, tailWord_4377352, baseEnd_4377352] using wordTrace_append hprefix tailTrace_4377352
  have hstable : (prefixWord ++ tailWord_4377352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377352).length < 2 ^ (prefixWord ++ tailWord_4377352).sum := by decide
  have hdescent : baseEnd_4377352 < baseStart_4377352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377375 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 3, 2, 2]
def baseStart_4377375 : Nat := 118140960795 + 4377375 * 2 ^ 59
def prefixEnd_4377375 : Nat := 4983230072969 + 3 ^ 40 * 4377375 * 2
def baseEnd_4377375 : Nat := 2247697379974916233881325

theorem tailTrace_4377375 : CollatzResearch.WordTrace tailWord_4377375 prefixEnd_4377375 2247697379974916233881325 := by
  unfold tailWord_4377375
  simp only [CollatzResearch.WordTrace]
  refine ⟨159655982516525445975941579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106437321677683630650627719 159655982516525445975941579)
  ·
    refine ⟨239483973774788168963912369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159655982516525445975941579 239483973774788168963912369)
    ·
      refine ⟨179612980331091126722934277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239483973774788168963912369 179612980331091126722934277)
      ·
        refine ⟨33677433812079586260550177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179612980331091126722934277 33677433812079586260550177)
        ·
          refine ⟨25258075359059689695412633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33677433812079586260550177 25258075359059689695412633)
          ·
            refine ⟨18943556519294767271559475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25258075359059689695412633 18943556519294767271559475)
            ·
              refine ⟨28415334778942150907339213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18943556519294767271559475 28415334778942150907339213)
              ·
                refine ⟨10655750542103306590252205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28415334778942150907339213 10655750542103306590252205)
                ·
                  refine ⟨3995906453288739971344577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10655750542103306590252205 3995906453288739971344577)
                  ·
                    refine ⟨2996929839966554978508433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3995906453288739971344577 2996929839966554978508433)
                    ·
                      refine ⟨2247697379974916233881325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996929839966554978508433 2247697379974916233881325)
                      ·
                        rfl

theorem cell23_4377375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_4377375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377375 prefixEnd_4377375 := by exact prefixLift 4377375
  have htrace : WordTrace (prefixWord ++ tailWord_4377375) baseStart_4377375 baseEnd_4377375 := by
    simpa [prefixWord, tailWord_4377375, baseEnd_4377375] using wordTrace_append hprefix tailTrace_4377375
  have hstable : (prefixWord ++ tailWord_4377375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377375).length < 2 ^ (prefixWord ++ tailWord_4377375).sum := by decide
  have hdescent : baseEnd_4377375 < baseStart_4377375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377378 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4377378 : Nat := 118140960795 + 4377378 * 2 ^ 59
def prefixEnd_4377378 : Nat := 4983230072969 + 3 ^ 40 * 4377378 * 2
def baseEnd_4377378 : Nat := 2247698920416879722143811

theorem tailTrace_4377378 : CollatzResearch.WordTrace tailWord_4377378 prefixEnd_4377378 2247698920416879722143811 := by
  unfold tailWord_4377378
  simp only [CollatzResearch.WordTrace]
  refine ⟨39914022983878644372075197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106437394623676384992200525 39914022983878644372075197)
  ·
    refine ⟨14967758618954491639528199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39914022983878644372075197 14967758618954491639528199)
    ·
      refine ⟨22451637928431737459292299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14967758618954491639528199 22451637928431737459292299)
      ·
        refine ⟨33677456892647606188938449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22451637928431737459292299 33677456892647606188938449)
        ·
          refine ⟨25258092669485704641703837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33677456892647606188938449 25258092669485704641703837)
          ·
            refine ⟨9471784751057139240638939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25258092669485704641703837 9471784751057139240638939)
            ·
              refine ⟨14207677126585708860958409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9471784751057139240638939 14207677126585708860958409)
              ·
                refine ⟨10655757844939281645718807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14207677126585708860958409 10655757844939281645718807)
                ·
                  refine ⟨15983636767408922468578211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10655757844939281645718807 15983636767408922468578211)
                  ·
                    refine ⟨23975455151113383702867317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15983636767408922468578211 23975455151113383702867317)
                    ·
                      refine ⟨2247698920416879722143811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23975455151113383702867317 2247698920416879722143811)
                      ·
                        rfl

theorem cell23_4377378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4377378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377378 prefixEnd_4377378 := by exact prefixLift 4377378
  have htrace : WordTrace (prefixWord ++ tailWord_4377378) baseStart_4377378 baseEnd_4377378 := by
    simpa [prefixWord, tailWord_4377378, baseEnd_4377378] using wordTrace_append hprefix tailTrace_4377378
  have hstable : (prefixWord ++ tailWord_4377378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377378).length < 2 ^ (prefixWord ++ tailWord_4377378).sum := by decide
  have hdescent : baseEnd_4377378 < baseStart_4377378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377395 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 3]
def baseStart_4377395 : Nat := 118140960795 + 4377395 * 2 ^ 59
def prefixEnd_4377395 : Nat := 4983230072969 + 3 ^ 40 * 4377395 * 2
def baseEnd_4377395 : Nat := 2247707649588006155631233

theorem tailTrace_4377395 : CollatzResearch.WordTrace tailWord_4377395 prefixEnd_4377395 2247707649588006155631233 := by
  unfold tailWord_4377395
  simp only [CollatzResearch.WordTrace]
  refine ⟨159656711976452989391669639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106437807984301992927779759 159656711976452989391669639)
  ·
    refine ⟨239485067964679484087504459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159656711976452989391669639 239485067964679484087504459)
    ·
      refine ⟨359227601947019226131256689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239485067964679484087504459 359227601947019226131256689)
      ·
        refine ⟨269420701460264419598442517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359227601947019226131256689 269420701460264419598442517)
        ·
          refine ⟨12629095380949894668676993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 269420701460264419598442517 12629095380949894668676993)
          ·
            refine ⟨9471821535712421001507745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12629095380949894668676993 9471821535712421001507745)
            ·
              refine ⟨7103866151784315751130809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471821535712421001507745 7103866151784315751130809)
              ·
                refine ⟨5327899613838236813348107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7103866151784315751130809 5327899613838236813348107)
                ·
                  refine ⟨7991849420757355220022161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5327899613838236813348107 7991849420757355220022161)
                  ·
                    refine ⟨5993887065568016415016621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7991849420757355220022161 5993887065568016415016621)
                    ·
                      refine ⟨2247707649588006155631233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5993887065568016415016621 2247707649588006155631233)
                      ·
                        rfl

theorem cell23_4377395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_4377395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377395 prefixEnd_4377395 := by exact prefixLift 4377395
  have htrace : WordTrace (prefixWord ++ tailWord_4377395) baseStart_4377395 baseEnd_4377395 := by
    simpa [prefixWord, tailWord_4377395, baseEnd_4377395] using wordTrace_append hprefix tailTrace_4377395
  have hstable : (prefixWord ++ tailWord_4377395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377395).length < 2 ^ (prefixWord ++ tailWord_4377395).sum := by decide
  have hdescent : baseEnd_4377395 < baseStart_4377395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377412 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4377412 : Nat := 118140960795 + 4377412 * 2 ^ 59
def prefixEnd_4377412 : Nat := 4983230072969 + 3 ^ 40 * 4377412 * 2
def baseEnd_4377412 : Nat := 2247716378759132589118655

theorem tailTrace_4377412 : CollatzResearch.WordTrace tailWord_4377412 prefixEnd_4377412 2247716378759132589118655 := by
  unfold tailWord_4377412
  simp only [CollatzResearch.WordTrace]
  refine ⟨79828666008695700647519245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106438221344927600863358993 79828666008695700647519245)
  ·
    refine ⟨29935749753260887742819717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79828666008695700647519245 29935749753260887742819717)
    ·
      refine ⟨5612953078736416451778697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29935749753260887742819717 5612953078736416451778697)
      ·
        refine ⟨4209714809052312338834023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5612953078736416451778697 4209714809052312338834023)
        ·
          refine ⟨6314572213578468508251035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209714809052312338834023 6314572213578468508251035)
          ·
            refine ⟨9471858320367702762376553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6314572213578468508251035 9471858320367702762376553)
            ·
              refine ⟨7103893740275777071782415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471858320367702762376553 7103893740275777071782415)
              ·
                refine ⟨10655840610413665607673623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7103893740275777071782415 10655840610413665607673623)
                ·
                  refine ⟨15983760915620498411510435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10655840610413665607673623 15983760915620498411510435)
                  ·
                    refine ⟨23975641373430747617265653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15983760915620498411510435 23975641373430747617265653)
                    ·
                      refine ⟨2247716378759132589118655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23975641373430747617265653 2247716378759132589118655)
                      ·
                        rfl

theorem cell23_4377412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4377412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377412 prefixEnd_4377412 := by exact prefixLift 4377412
  have htrace : WordTrace (prefixWord ++ tailWord_4377412) baseStart_4377412 baseEnd_4377412 := by
    simpa [prefixWord, tailWord_4377412, baseEnd_4377412] using wordTrace_append hprefix tailTrace_4377412
  have hstable : (prefixWord ++ tailWord_4377412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377412).length < 2 ^ (prefixWord ++ tailWord_4377412).sum := by decide
  have hdescent : baseEnd_4377412 < baseStart_4377412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377451 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5]
def baseStart_4377451 : Nat := 118140960795 + 4377451 * 2 ^ 59
def prefixEnd_4377451 : Nat := 4983230072969 + 3 ^ 40 * 4377451 * 2
def baseEnd_4377451 : Nat := 2247736404504657936530975

theorem tailTrace_4377451 : CollatzResearch.WordTrace tailWord_4377451 prefixEnd_4377451 2247736404504657936530975 := by
  unfold tailWord_4377451
  simp only [CollatzResearch.WordTrace]
  refine ⟨159658754464250110955708207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106439169642833407303805471 159658754464250110955708207)
  ·
    refine ⟨239488131696375166433562311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159658754464250110955708207 239488131696375166433562311)
    ·
      refine ⟨359232197544562749650343467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239488131696375166433562311 359232197544562749650343467)
      ·
        refine ⟨538848296316844124475515201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359232197544562749650343467 538848296316844124475515201)
        ·
          refine ⟨404136222237633093356636401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538848296316844124475515201 404136222237633093356636401)
          ·
            refine ⟨303102166678224820017477301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404136222237633093356636401 303102166678224820017477301)
            ·
              refine ⟨28415828126083576876638497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 303102166678224820017477301 28415828126083576876638497)
              ·
                refine ⟨21311871094562682657478873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28415828126083576876638497 21311871094562682657478873)
                ·
                  refine ⟨15983903320922011993109155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21311871094562682657478873 15983903320922011993109155)
                  ·
                    refine ⟨23975854981383017989663733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15983903320922011993109155 23975854981383017989663733)
                    ·
                      refine ⟨2247736404504657936530975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23975854981383017989663733 2247736404504657936530975)
                      ·
                        rfl

theorem cell23_4377451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_4377451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377451 prefixEnd_4377451 := by exact prefixLift 4377451
  have htrace : WordTrace (prefixWord ++ tailWord_4377451) baseStart_4377451 baseEnd_4377451 := by
    simpa [prefixWord, tailWord_4377451, baseEnd_4377451] using wordTrace_append hprefix tailTrace_4377451
  have hstable : (prefixWord ++ tailWord_4377451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377451).length < 2 ^ (prefixWord ++ tailWord_4377451).sum := by decide
  have hdescent : baseEnd_4377451 < baseStart_4377451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377465 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 1, 4, 2]
def baseStart_4377465 : Nat := 118140960795 + 4377465 * 2 ^ 59
def prefixEnd_4377465 : Nat := 4983230072969 + 3 ^ 40 * 4377465 * 2
def baseEnd_4377465 : Nat := 2247743593233820881755911

theorem tailTrace_4377465 : CollatzResearch.WordTrace tailWord_4377465 prefixEnd_4377465 2247743593233820881755911 := by
  unfold tailWord_4377465
  simp only [CollatzResearch.WordTrace]
  refine ⟨159659265086199391346717849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106439510057466260897811899 159659265086199391346717849)
  ·
    refine ⟨119744448814649543510038387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159659265086199391346717849 119744448814649543510038387)
    ·
      refine ⟨179616673221974315265057581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119744448814649543510038387 179616673221974315265057581)
      ·
        refine ⟨67356252458240368224396593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179616673221974315265057581 67356252458240368224396593)
        ·
          refine ⟨50517189343680276168297445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67356252458240368224396593 50517189343680276168297445)
          ·
            refine ⟨9471973001940051781555771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50517189343680276168297445 9471973001940051781555771)
            ·
              refine ⟨14207959502910077672333657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9471973001940051781555771 14207959502910077672333657)
              ·
                refine ⟨10655969627182558254250243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14207959502910077672333657 10655969627182558254250243)
                ·
                  refine ⟨15983954440773837381375365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10655969627182558254250243 15983954440773837381375365)
                  ·
                    refine ⟨2996991457645094509007881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15983954440773837381375365 2996991457645094509007881)
                    ·
                      refine ⟨2247743593233820881755911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2996991457645094509007881 2247743593233820881755911)
                      ·
                        rfl

theorem cell23_4377465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_4377465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377465 prefixEnd_4377465 := by exact prefixLift 4377465
  have htrace : WordTrace (prefixWord ++ tailWord_4377465) baseStart_4377465 baseEnd_4377465 := by
    simpa [prefixWord, tailWord_4377465, baseEnd_4377465] using wordTrace_append hprefix tailTrace_4377465
  have hstable : (prefixWord ++ tailWord_4377465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377465).length < 2 ^ (prefixWord ++ tailWord_4377465).sum := by decide
  have hdescent : baseEnd_4377465 < baseStart_4377465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377575 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4377575 : Nat := 118140960795 + 4377575 * 2 ^ 59
def prefixEnd_4377575 : Nat := 4983230072969 + 3 ^ 40 * 4377575 * 2
def baseEnd_4377575 : Nat := 2247800076105815451380405

theorem tailTrace_4377575 : CollatzResearch.WordTrace tailWord_4377575 prefixEnd_4377575 2247800076105815451380405 := by
  unfold tailWord_4377575
  simp only [CollatzResearch.WordTrace]
  refine ⟨159663277115800880133222179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106442184743867253422148119 159663277115800880133222179)
  ·
    refine ⟨239494915673701320199833269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159663277115800880133222179 239494915673701320199833269)
    ·
      refine ⟨22452648344409498768734369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239494915673701320199833269 22452648344409498768734369)
      ·
        refine ⟨16839486258307124076550777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22452648344409498768734369 16839486258307124076550777)
        ·
          refine ⟨12629614693730343057413083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16839486258307124076550777 12629614693730343057413083)
          ·
            refine ⟨18944422040595514586119625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12629614693730343057413083 18944422040595514586119625)
            ·
              refine ⟨14208316530446635939589719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18944422040595514586119625 14208316530446635939589719)
              ·
                refine ⟨21312474795669953909384579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14208316530446635939589719 21312474795669953909384579)
                ·
                  refine ⟨31968712193504930864076869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21312474795669953909384579 31968712193504930864076869)
                  ·
                    refine ⟨5994133536282174537014413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31968712193504930864076869 5994133536282174537014413)
                    ·
                      refine ⟨2247800076105815451380405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994133536282174537014413 2247800076105815451380405)
                      ·
                        rfl

theorem cell23_4377575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4377575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377575 prefixEnd_4377575 := by exact prefixLift 4377575
  have htrace : WordTrace (prefixWord ++ tailWord_4377575) baseStart_4377575 baseEnd_4377575 := by
    simpa [prefixWord, tailWord_4377575, baseEnd_4377575] using wordTrace_append hprefix tailTrace_4377575
  have hstable : (prefixWord ++ tailWord_4377575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377575).length < 2 ^ (prefixWord ++ tailWord_4377575).sum := by decide
  have hdescent : baseEnd_4377575 < baseStart_4377575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377578 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_4377578 : Nat := 118140960795 + 4377578 * 2 ^ 59
def prefixEnd_4377578 : Nat := 4983230072969 + 3 ^ 40 * 4377578 * 2
def baseEnd_4377578 : Nat := 249755735171975437738099

theorem tailTrace_4377578 : CollatzResearch.WordTrace tailWord_4377578 prefixEnd_4377578 249755735171975437738099 := by
  unfold tailWord_4377578
  simp only [CollatzResearch.WordTrace]
  refine ⟨39915846633697502911395347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106442257689860007763720925 39915846633697502911395347)
  ·
    refine ⟨59873769950546254367093021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39915846633697502911395347 59873769950546254367093021)
    ·
      refine ⟨22452663731454845387659883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59873769950546254367093021 22452663731454845387659883)
      ·
        refine ⟨33678995597182268081489825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22452663731454845387659883 33678995597182268081489825)
        ·
          refine ⟨25259246697886701061117369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33678995597182268081489825 25259246697886701061117369)
          ·
            refine ⟨18944435023415025795838027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25259246697886701061117369 18944435023415025795838027)
            ·
              refine ⟨28416652535122538693757041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18944435023415025795838027 28416652535122538693757041)
              ·
                refine ⟨21312489401341904020317781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28416652535122538693757041 21312489401341904020317781)
                ·
                  refine ⟨249755735171975437738099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21312489401341904020317781 249755735171975437738099)
                  ·
                    rfl

theorem cell23_4377578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_4377578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377578 prefixEnd_4377578 := by exact prefixLift 4377578
  have htrace : WordTrace (prefixWord ++ tailWord_4377578) baseStart_4377578 baseEnd_4377578 := by
    simpa [prefixWord, tailWord_4377578, baseEnd_4377578] using wordTrace_append hprefix tailTrace_4377578
  have hstable : (prefixWord ++ tailWord_4377578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377578).length < 2 ^ (prefixWord ++ tailWord_4377578).sum := by decide
  have hdescent : baseEnd_4377578 < baseStart_4377578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377589 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4377589 : Nat := 118140960795 + 4377589 * 2 ^ 59
def prefixEnd_4377589 : Nat := 4983230072969 + 3 ^ 40 * 4377589 * 2
def baseEnd_4377589 : Nat := 2247807264834978396605341

theorem tailTrace_4377589 : CollatzResearch.WordTrace tailWord_4377589 prefixEnd_4377589 2247807264834978396605341 := by
  unfold tailWord_4377589
  simp only [CollatzResearch.WordTrace]
  refine ⟨159663787737750160524231821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106442525158500107016154547 159663787737750160524231821)
  ·
    refine ⟨59873920401656310196586933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159663787737750160524231821 59873920401656310196586933)
    ·
      refine ⟨5613180037655279080930025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59873920401656310196586933 5613180037655279080930025)
      ·
        refine ⟨4209885028241459310697519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5613180037655279080930025 4209885028241459310697519)
        ·
          refine ⟨6314827542362188966046279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209885028241459310697519 6314827542362188966046279)
          ·
            refine ⟨9472241313543283449069419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6314827542362188966046279 9472241313543283449069419)
            ·
              refine ⟨14208361970314925173604129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9472241313543283449069419 14208361970314925173604129)
              ·
                refine ⟨10656271477736193880203097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14208361970314925173604129 10656271477736193880203097)
                ·
                  refine ⟨7992203608302145410152323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10656271477736193880203097 7992203608302145410152323)
                  ·
                    refine ⟨11988305412453218115228485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7992203608302145410152323 11988305412453218115228485)
                    ·
                      refine ⟨2247807264834978396605341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11988305412453218115228485 2247807264834978396605341)
                      ·
                        rfl

theorem cell23_4377589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4377589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377589 prefixEnd_4377589 := by exact prefixLift 4377589
  have htrace : WordTrace (prefixWord ++ tailWord_4377589) baseStart_4377589 baseEnd_4377589 := by
    simpa [prefixWord, tailWord_4377589, baseEnd_4377589] using wordTrace_append hprefix tailTrace_4377589
  have hstable : (prefixWord ++ tailWord_4377589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377589).length < 2 ^ (prefixWord ++ tailWord_4377589).sum := by decide
  have hdescent : baseEnd_4377589 < baseStart_4377589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377612 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 6]
def baseStart_4377612 : Nat := 118140960795 + 4377612 * 2 ^ 59
def prefixEnd_4377612 : Nat := 4983230072969 + 3 ^ 40 * 4377612 * 2
def baseEnd_4377612 : Nat := 249757674987781311846415

theorem tailTrace_4377612 : CollatzResearch.WordTrace tailWord_4377612 prefixEnd_4377612 249757674987781311846415 := by
  unfold tailWord_4377612
  simp only [CollatzResearch.WordTrace]
  refine ⟨79832313308333417726159545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106443084411111223634879393 79832313308333417726159545)
  ·
    refine ⟨59874234981250063294619659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79832313308333417726159545 59874234981250063294619659)
    ·
      refine ⟨89811352471875094941929489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59874234981250063294619659 89811352471875094941929489)
      ·
        refine ⟨67358514353906321206447117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89811352471875094941929489 67358514353906321206447117)
        ·
          refine ⟨25259442882714870452417669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67358514353906321206447117 25259442882714870452417669)
          ·
            refine ⟨4736145540509038209828313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25259442882714870452417669 4736145540509038209828313)
            ·
              refine ⟨3552109155381778657371235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736145540509038209828313 3552109155381778657371235)
              ·
                refine ⟨5328163733072667986056853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552109155381778657371235 5328163733072667986056853)
                ·
                  refine ⟨249757674987781311846415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5328163733072667986056853 249757674987781311846415)
                  ·
                    rfl

theorem cell23_4377612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_4377612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377612 prefixEnd_4377612 := by exact prefixLift 4377612
  have htrace : WordTrace (prefixWord ++ tailWord_4377612) baseStart_4377612 baseEnd_4377612 := by
    simpa [prefixWord, tailWord_4377612, baseEnd_4377612] using wordTrace_append hprefix tailTrace_4377612
  have hstable : (prefixWord ++ tailWord_4377612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377612).length < 2 ^ (prefixWord ++ tailWord_4377612).sum := by decide
  have hdescent : baseEnd_4377612 < baseStart_4377612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377625 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 1, 5]
def baseStart_4377625 : Nat := 118140960795 + 4377625 * 2 ^ 59
def prefixEnd_4377625 : Nat := 4983230072969 + 3 ^ 40 * 4377625 * 2
def baseEnd_4377625 : Nat := 749275250046180085251725

theorem tailTrace_4377625 : CollatzResearch.WordTrace tailWord_4377625 prefixEnd_4377625 749275250046180085251725 := by
  unfold tailWord_4377625
  simp only [CollatzResearch.WordTrace]
  refine ⟨159665100765619738672542329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106443400510413159115028219 159665100765619738672542329)
  ·
    refine ⟨119748825574214804004406747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159665100765619738672542329 119748825574214804004406747)
    ·
      refine ⟨179623238361322206006610121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119748825574214804004406747 179623238361322206006610121)
      ·
        refine ⟨134717428770991654504957591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179623238361322206006610121 134717428770991654504957591)
        ·
          refine ⟨202076143156487481757436387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134717428770991654504957591 202076143156487481757436387)
          ·
            refine ⟨303114214734731222636154581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202076143156487481757436387 303114214734731222636154581)
            ·
              refine ⟨7104239407845263030534873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 303114214734731222636154581 7104239407845263030534873)
              ·
                refine ⟨5328179555883947272901155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7104239407845263030534873 5328179555883947272901155)
                ·
                  refine ⟨7992269333825920909351733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5328179555883947272901155 7992269333825920909351733)
                  ·
                    refine ⟨749275250046180085251725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7992269333825920909351733 749275250046180085251725)
                    ·
                      rfl

theorem cell23_4377625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_4377625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377625 prefixEnd_4377625 := by exact prefixLift 4377625
  have htrace : WordTrace (prefixWord ++ tailWord_4377625) baseStart_4377625 baseEnd_4377625 := by
    simpa [prefixWord, tailWord_4377625, baseEnd_4377625] using wordTrace_append hprefix tailTrace_4377625
  have hstable : (prefixWord ++ tailWord_4377625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377625).length < 2 ^ (prefixWord ++ tailWord_4377625).sum := by decide
  have hdescent : baseEnd_4377625 < baseStart_4377625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377656 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 1, 1, 3]
def baseStart_4377656 : Nat := 118140960795 + 4377656 * 2 ^ 59
def prefixEnd_4377656 : Nat := 4983230072969 + 3 ^ 40 * 4377656 * 2
def baseEnd_4377656 : Nat := 2247841668038829634467533

theorem tailTrace_4377656 : CollatzResearch.WordTrace tailWord_4377656 prefixEnd_4377656 2247841668038829634467533 := by
  unfold tailWord_4377656
  simp only [CollatzResearch.WordTrace]
  refine ⟨79833115714253715483460411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106444154285671620644613881 79833115714253715483460411)
  ·
    refine ⟨119749673571380573225190617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79833115714253715483460411 119749673571380573225190617)
    ·
      refine ⟨89812255178535429918892963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119749673571380573225190617 89812255178535429918892963)
      ·
        refine ⟨134718382767803144878339445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89812255178535429918892963 134718382767803144878339445)
        ·
          refine ⟨12629848384481544832344323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134718382767803144878339445 12629848384481544832344323)
          ·
            refine ⟨18944772576722317248516485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12629848384481544832344323 18944772576722317248516485)
            ·
              refine ⟨3552144858135434484096841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18944772576722317248516485 3552144858135434484096841)
              ·
                refine ⟨2664108643601575863072631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3552144858135434484096841 2664108643601575863072631)
                ·
                  refine ⟨3996162965402363794608947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664108643601575863072631 3996162965402363794608947)
                  ·
                    refine ⟨5994244448103545691913421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3996162965402363794608947 5994244448103545691913421)
                    ·
                      refine ⟨2247841668038829634467533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994244448103545691913421 2247841668038829634467533)
                      ·
                        rfl

theorem cell23_4377656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_4377656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377656 prefixEnd_4377656 := by exact prefixLift 4377656
  have htrace : WordTrace (prefixWord ++ tailWord_4377656) baseStart_4377656 baseEnd_4377656 := by
    simpa [prefixWord, tailWord_4377656, baseEnd_4377656] using wordTrace_append hprefix tailTrace_4377656
  have hstable : (prefixWord ++ tailWord_4377656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377656).length < 2 ^ (prefixWord ++ tailWord_4377656).sum := by decide
  have hdescent : baseEnd_4377656 < baseStart_4377656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377658 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_4377658 : Nat := 118140960795 + 4377658 * 2 ^ 59
def prefixEnd_4377658 : Nat := 4983230072969 + 3 ^ 40 * 4377658 * 2
def baseEnd_4377658 : Nat := 2247842695000138626642523

theorem tailTrace_4377658 : CollatzResearch.WordTrace tailWord_4377658 prefixEnd_4377658 2247842695000138626642523 := by
  unfold tailWord_4377658
  simp only [CollatzResearch.WordTrace]
  refine ⟨39916576093625046327123407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106444202916333456872329085 39916576093625046327123407)
  ·
    refine ⟨59874864140437569490685111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39916576093625046327123407 59874864140437569490685111)
    ·
      refine ⟨89812296210656354236027667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59874864140437569490685111 89812296210656354236027667)
      ·
        refine ⟨134718444315984531354041501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89812296210656354236027667 134718444315984531354041501)
        ·
          refine ⟨50519416618494199257765563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134718444315984531354041501 50519416618494199257765563)
          ·
            refine ⟨75779124927741298886648345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50519416618494199257765563 75779124927741298886648345)
            ·
              refine ⟨56834343695805974164986259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75779124927741298886648345 56834343695805974164986259)
              ·
                refine ⟨85251515543708961247479389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56834343695805974164986259 85251515543708961247479389)
                ·
                  refine ⟨31969318328890860467804771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85251515543708961247479389 31969318328890860467804771)
                  ·
                    refine ⟨47953977493336290701707157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31969318328890860467804771 47953977493336290701707157)
                    ·
                      refine ⟨2247842695000138626642523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47953977493336290701707157 2247842695000138626642523)
                      ·
                        rfl

theorem cell23_4377658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_4377658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377658 prefixEnd_4377658 := by exact prefixLift 4377658
  have htrace : WordTrace (prefixWord ++ tailWord_4377658) baseStart_4377658 baseEnd_4377658 := by
    simpa [prefixWord, tailWord_4377658, baseEnd_4377658] using wordTrace_append hprefix tailTrace_4377658
  have hstable : (prefixWord ++ tailWord_4377658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377658).length < 2 ^ (prefixWord ++ tailWord_4377658).sum := by decide
  have hdescent : baseEnd_4377658 < baseStart_4377658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377662 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4377662 : Nat := 118140960795 + 4377662 * 2 ^ 59
def prefixEnd_4377662 : Nat := 4983230072969 + 3 ^ 40 * 4377662 * 2
def baseEnd_4377662 : Nat := 2247844748922756610992505

theorem tailTrace_4377662 : CollatzResearch.WordTrace tailWord_4377662 prefixEnd_4377662 2247844748922756610992505 := by
  unfold tailWord_4377662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19958306283310711748954905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106444300177657129327759493 19958306283310711748954905)
  ·
    refine ⟨14968729712483033811716179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19958306283310711748954905 14968729712483033811716179)
    ·
      refine ⟨22453094568724550717574269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14968729712483033811716179 22453094568724550717574269)
      ·
        refine ⟨8419910463271706519090351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22453094568724550717574269 8419910463271706519090351)
        ·
          refine ⟨12629865694907559778635527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8419910463271706519090351 12629865694907559778635527)
          ·
            refine ⟨18944798542361339667953291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12629865694907559778635527 18944798542361339667953291)
            ·
              refine ⟨28417197813542009501929937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18944798542361339667953291 28417197813542009501929937)
              ·
                refine ⟨21312898360156507126447453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28417197813542009501929937 21312898360156507126447453)
                ·
                  refine ⟨7992336885058690172417795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21312898360156507126447453 7992336885058690172417795)
                  ·
                    refine ⟨11988505327588035258626693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7992336885058690172417795 11988505327588035258626693)
                    ·
                      refine ⟨2247844748922756610992505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11988505327588035258626693 2247844748922756610992505)
                      ·
                        rfl

theorem cell23_4377662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4377662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377662 prefixEnd_4377662 := by exact prefixLift 4377662
  have htrace : WordTrace (prefixWord ++ tailWord_4377662) baseStart_4377662 baseEnd_4377662 := by
    simpa [prefixWord, tailWord_4377662, baseEnd_4377662] using wordTrace_append hprefix tailTrace_4377662
  have hstable : (prefixWord ++ tailWord_4377662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377662).length < 2 ^ (prefixWord ++ tailWord_4377662).sum := by decide
  have hdescent : baseEnd_4377662 < baseStart_4377662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377682 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_4377682 : Nat := 118140960795 + 4377682 * 2 ^ 59
def prefixEnd_4377682 : Nat := 4983230072969 + 3 ^ 40 * 4377682 * 2
def baseEnd_4377682 : Nat := 2247855018535846532742413

theorem tailTrace_4377682 : CollatzResearch.WordTrace tailWord_4377682 prefixEnd_4377682 2247855018535846532742413 := by
  unfold tailWord_4377682
  simp only [CollatzResearch.WordTrace]
  refine ⟨39916794931603309351841825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106444786484275491604911533 39916794931603309351841825)
  ·
    refine ⟨29937596198702482013881369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39916794931603309351841825 29937596198702482013881369)
    ·
      refine ⟨22453197149026861510411027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29937596198702482013881369 22453197149026861510411027)
      ·
        refine ⟨33679795723540292265616541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22453197149026861510411027 33679795723540292265616541)
        ·
          refine ⟨12629923396327609599606203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33679795723540292265616541 12629923396327609599606203)
          ·
            refine ⟨18944885094491414399409305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12629923396327609599606203 18944885094491414399409305)
            ·
              refine ⟨14208663820868560799556979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18944885094491414399409305 14208663820868560799556979)
              ·
                refine ⟨21312995731302841199335469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14208663820868560799556979 21312995731302841199335469)
                ·
                  refine ⟨7992373399238565449750801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21312995731302841199335469 7992373399238565449750801)
                  ·
                    refine ⟨5994280049428924087313101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7992373399238565449750801 5994280049428924087313101)
                    ·
                      refine ⟨2247855018535846532742413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994280049428924087313101 2247855018535846532742413)
                      ·
                        rfl

theorem cell23_4377682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_4377682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377682 prefixEnd_4377682 := by exact prefixLift 4377682
  have htrace : WordTrace (prefixWord ++ tailWord_4377682) baseStart_4377682 baseEnd_4377682 := by
    simpa [prefixWord, tailWord_4377682, baseEnd_4377682] using wordTrace_append hprefix tailTrace_4377682
  have hstable : (prefixWord ++ tailWord_4377682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377682).length < 2 ^ (prefixWord ++ tailWord_4377682).sum := by decide
  have hdescent : baseEnd_4377682 < baseStart_4377682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377685 : List Nat := [1, 3, 2, 2, 1, 2, 5, 7]
def baseStart_4377685 : Nat := 118140960795 + 4377685 * 2 ^ 59
def prefixEnd_4377685 : Nat := 4983230072969 + 3 ^ 40 * 4377685 * 2
def baseEnd_4377685 : Nat := 83253946628807778555737

theorem tailTrace_4377685 : CollatzResearch.WordTrace tailWord_4377685 prefixEnd_4377685 83253946628807778555737 := by
  unfold tailWord_4377685
  simp only [CollatzResearch.WordTrace]
  refine ⟨159667289145402368919726509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106444859430268245946484339 159667289145402368919726509)
  ·
    refine ⟨59875233429525888344897441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159667289145402368919726509 59875233429525888344897441)
    ·
      refine ⟨44906425072144416258673081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59875233429525888344897441 44906425072144416258673081)
      ·
        refine ⟨33679818804108312194004811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44906425072144416258673081 33679818804108312194004811)
        ·
          refine ⟨50519728206162468291007217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33679818804108312194004811 50519728206162468291007217)
          ·
            refine ⟨37889796154621851218255413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50519728206162468291007217 37889796154621851218255413)
            ·
              refine ⟨3552168389495798551711445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37889796154621851218255413 3552168389495798551711445)
              ·
                refine ⟨83253946628807778555737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3552168389495798551711445 83253946628807778555737)
                ·
                  rfl

theorem cell23_4377685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 7].length) (baseStart_4377685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377685 prefixEnd_4377685 := by exact prefixLift 4377685
  have htrace : WordTrace (prefixWord ++ tailWord_4377685) baseStart_4377685 baseEnd_4377685 := by
    simpa [prefixWord, tailWord_4377685, baseEnd_4377685] using wordTrace_append hprefix tailTrace_4377685
  have hstable : (prefixWord ++ tailWord_4377685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377685).length < 2 ^ (prefixWord ++ tailWord_4377685).sum := by decide
  have hdescent : baseEnd_4377685 < baseStart_4377685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377693 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4377693 : Nat := 118140960795 + 4377693 * 2 ^ 59
def prefixEnd_4377693 : Nat := 4983230072969 + 3 ^ 40 * 4377693 * 2
def baseEnd_4377693 : Nat := 749286888941015329901621

theorem tailTrace_4377693 : CollatzResearch.WordTrace tailWord_4377693 prefixEnd_4377693 749286888941015329901621 := by
  unfold tailWord_4377693
  simp only [CollatzResearch.WordTrace]
  refine ⟨159667580929373386286017733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106445053952915590857345155 159667580929373386286017733)
  ·
    refine ⟨29937671424257509928628325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159667580929373386286017733 29937671424257509928628325)
    ·
      refine ⟨5613313392048283111617811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29937671424257509928628325 5613313392048283111617811)
      ·
        refine ⟨8419970088072424667426717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613313392048283111617811 8419970088072424667426717)
        ·
          refine ⟨3157488783027159250285019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8419970088072424667426717 3157488783027159250285019)
          ·
            refine ⟨4736233174540738875427529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157488783027159250285019 4736233174540738875427529)
            ·
              refine ⟨3552174880905554156570647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736233174540738875427529 3552174880905554156570647)
              ·
                refine ⟨5328262321358331234855971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552174880905554156570647 5328262321358331234855971)
                ·
                  refine ⟨7992393482037496852283957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5328262321358331234855971 7992393482037496852283957)
                  ·
                    refine ⟨749286888941015329901621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7992393482037496852283957 749286888941015329901621)
                    ·
                      rfl

theorem cell23_4377693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4377693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377693 prefixEnd_4377693 := by exact prefixLift 4377693
  have htrace : WordTrace (prefixWord ++ tailWord_4377693) baseStart_4377693 baseEnd_4377693 := by
    simpa [prefixWord, tailWord_4377693, baseEnd_4377693] using wordTrace_append hprefix tailTrace_4377693
  have hstable : (prefixWord ++ tailWord_4377693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377693).length < 2 ^ (prefixWord ++ tailWord_4377693).sum := by decide
  have hdescent : baseEnd_4377693 < baseStart_4377693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377695 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_4377695 : Nat := 118140960795 + 4377695 * 2 ^ 59
def prefixEnd_4377695 : Nat := 4983230072969 + 3 ^ 40 * 4377695 * 2
def baseEnd_4377695 : Nat := 2247861693784354981879853

theorem tailTrace_4377695 : CollatzResearch.WordTrace tailWord_4377695 prefixEnd_4377695 2247861693784354981879853 := by
  unfold tailWord_4377695
  simp only [CollatzResearch.WordTrace]
  refine ⟨159667653875366140627590539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106445102583577427085060359 159667653875366140627590539)
  ·
    refine ⟨239501480813049210941385809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159667653875366140627590539 239501480813049210941385809)
    ·
      refine ⟨179626110609786908206039357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239501480813049210941385809 179626110609786908206039357)
      ·
        refine ⟨67359791478670090577264759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179626110609786908206039357 67359791478670090577264759)
        ·
          refine ⟨101039687218005135865897139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67359791478670090577264759 101039687218005135865897139)
          ·
            refine ⟨151559530827007703798845709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101039687218005135865897139 151559530827007703798845709)
            ·
              refine ⟨56834824060127888924567141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151559530827007703798845709 56834824060127888924567141)
              ·
                refine ⟨10656529511273979173356339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56834824060127888924567141 10656529511273979173356339)
                ·
                  refine ⟨15984794266910968760034509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10656529511273979173356339 15984794266910968760034509)
                  ·
                    refine ⟨5994297850091613285012941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15984794266910968760034509 5994297850091613285012941)
                    ·
                      refine ⟨2247861693784354981879853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994297850091613285012941 2247861693784354981879853)
                      ·
                        rfl

theorem cell23_4377695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_4377695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377695 prefixEnd_4377695 := by exact prefixLift 4377695
  have htrace : WordTrace (prefixWord ++ tailWord_4377695) baseStart_4377695 baseEnd_4377695 := by
    simpa [prefixWord, tailWord_4377695, baseEnd_4377695] using wordTrace_append hprefix tailTrace_4377695
  have hstable : (prefixWord ++ tailWord_4377695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377695).length < 2 ^ (prefixWord ++ tailWord_4377695).sum := by decide
  have hdescent : baseEnd_4377695 < baseStart_4377695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377696 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 1, 2, 2]
def baseStart_4377696 : Nat := 118140960795 + 4377696 * 2 ^ 59
def prefixEnd_4377696 : Nat := 4983230072969 + 3 ^ 40 * 4377696 * 2
def baseEnd_4377696 : Nat := 2247862207265009477967349

theorem tailTrace_4377696 : CollatzResearch.WordTrace tailWord_4377696 prefixEnd_4377696 2247862207265009477967349 := by
  unfold tailWord_4377696
  simp only [CollatzResearch.WordTrace]
  refine ⟨79833845174181258899188471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106445126898908345198917961 79833845174181258899188471)
  ·
    refine ⟨119750767761271888348782707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79833845174181258899188471 119750767761271888348782707)
    ·
      refine ⟨179626151641907832523174061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119750767761271888348782707 179626151641907832523174061)
      ·
        refine ⟨67359806865715437196190273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179626151641907832523174061 67359806865715437196190273)
        ·
          refine ⟨50519855149286577897142705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67359806865715437196190273 50519855149286577897142705)
          ·
            refine ⟨37889891361964933422857029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50519855149286577897142705 37889891361964933422857029)
            ·
              refine ⟨7104354630368425016785693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37889891361964933422857029 7104354630368425016785693)
              ·
                refine ⟨2664132986388159381294635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7104354630368425016785693 2664132986388159381294635)
                ·
                  refine ⟨3996199479582239071941953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664132986388159381294635 3996199479582239071941953)
                  ·
                    refine ⟨2997149609686679303956465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3996199479582239071941953 2997149609686679303956465)
                    ·
                      refine ⟨2247862207265009477967349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997149609686679303956465 2247862207265009477967349)
                      ·
                        rfl

theorem cell23_4377696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_4377696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377696 prefixEnd_4377696 := by exact prefixLift 4377696
  have htrace : WordTrace (prefixWord ++ tailWord_4377696) baseStart_4377696 baseEnd_4377696 := by
    simpa [prefixWord, tailWord_4377696, baseEnd_4377696] using wordTrace_append hprefix tailTrace_4377696
  have hstable : (prefixWord ++ tailWord_4377696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377696).length < 2 ^ (prefixWord ++ tailWord_4377696).sum := by decide
  have hdescent : baseEnd_4377696 < baseStart_4377696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377712 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 4, 1, 3]
def baseStart_4377712 : Nat := 118140960795 + 4377712 * 2 ^ 59
def prefixEnd_4377712 : Nat := 4983230072969 + 3 ^ 40 * 4377712 * 2
def baseEnd_4377712 : Nat := 2247870422955481415367275

theorem tailTrace_4377712 : CollatzResearch.WordTrace tailWord_4377712 prefixEnd_4377712 2247870422955481415367275 := by
  unfold tailWord_4377712
  simp only [CollatzResearch.WordTrace]
  refine ⟨79834136958152276265479695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106445515944203035020639593 79834136958152276265479695)
  ·
    refine ⟨119751205437228414398219543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79834136958152276265479695 119751205437228414398219543)
    ·
      refine ⟨179626808155842621597329315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119751205437228414398219543 179626808155842621597329315)
      ·
        refine ⟨269440212233763932395993973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179626808155842621597329315 269440212233763932395993973)
        ·
          refine ⟨25260019896915368662124435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 269440212233763932395993973 25260019896915368662124435)
          ·
            refine ⟨37890029845373052993186653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25260019896915368662124435 37890029845373052993186653)
            ·
              refine ⟨14208761192014894872444995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37890029845373052993186653 14208761192014894872444995)
              ·
                refine ⟨21313141788022342308667493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14208761192014894872444995 21313141788022342308667493)
                ·
                  refine ⟨3996214085254189182875155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21313141788022342308667493 3996214085254189182875155)
                  ·
                    refine ⟨5994321127881283774312733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3996214085254189182875155 5994321127881283774312733)
                    ·
                      refine ⟨2247870422955481415367275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994321127881283774312733 2247870422955481415367275)
                      ·
                        rfl

theorem cell23_4377712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_4377712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377712 prefixEnd_4377712 := by exact prefixLift 4377712
  have htrace : WordTrace (prefixWord ++ tailWord_4377712) baseStart_4377712 baseEnd_4377712 := by
    simpa [prefixWord, tailWord_4377712, baseEnd_4377712] using wordTrace_append hprefix tailTrace_4377712
  have hstable : (prefixWord ++ tailWord_4377712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377712).length < 2 ^ (prefixWord ++ tailWord_4377712).sum := by decide
  have hdescent : baseEnd_4377712 < baseStart_4377712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377726 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4377726 : Nat := 118140960795 + 4377726 * 2 ^ 59
def prefixEnd_4377726 : Nat := 4983230072969 + 3 ^ 40 * 4377726 * 2
def baseEnd_4377726 : Nat := 2247877611684644360592211

theorem tailTrace_4377726 : CollatzResearch.WordTrace tailWord_4377726 prefixEnd_4377726 2247877611684644360592211 := by
  unfold tailWord_4377726
  simp only [CollatzResearch.WordTrace]
  refine ⟨19958598067281729115246129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106445856358835888614646021 19958598067281729115246129)
  ·
    refine ⟨14968948550461296836434597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19958598067281729115246129 14968948550461296836434597)
    ·
      refine ⟨2806677853211493156831487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14968948550461296836434597 2806677853211493156831487)
      ·
        refine ⟨4210016779817239735247231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806677853211493156831487 4210016779817239735247231)
        ·
          refine ⟨6315025169725859602870847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210016779817239735247231 6315025169725859602870847)
          ·
            refine ⟨9472537754588789404306271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6315025169725859602870847 9472537754588789404306271)
            ·
              refine ⟨14208806631883184106459407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9472537754588789404306271 14208806631883184106459407)
              ·
                refine ⟨21313209947824776159689111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14208806631883184106459407 21313209947824776159689111)
                ·
                  refine ⟨31969814921737164239533667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21313209947824776159689111 31969814921737164239533667)
                  ·
                    refine ⟨47954722382605746359300501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31969814921737164239533667 47954722382605746359300501)
                    ·
                      refine ⟨2247877611684644360592211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47954722382605746359300501 2247877611684644360592211)
                      ·
                        rfl

theorem cell23_4377726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4377726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377726 prefixEnd_4377726 := by exact prefixLift 4377726
  have htrace : WordTrace (prefixWord ++ tailWord_4377726) baseStart_4377726 baseEnd_4377726 := by
    simpa [prefixWord, tailWord_4377726, baseEnd_4377726] using wordTrace_append hprefix tailTrace_4377726
  have hstable : (prefixWord ++ tailWord_4377726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377726).length < 2 ^ (prefixWord ++ tailWord_4377726).sum := by decide
  have hdescent : baseEnd_4377726 < baseStart_4377726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377729 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_4377729 : Nat := 118140960795 + 4377729 * 2 ^ 59
def prefixEnd_4377729 : Nat := 4983230072969 + 3 ^ 40 * 4377729 * 2
def baseEnd_4377729 : Nat := 2247879152126607848854697

theorem tailTrace_4377729 : CollatzResearch.WordTrace tailWord_4377729 prefixEnd_4377729 2247879152126607848854697 := by
  unfold tailWord_4377729
  simp only [CollatzResearch.WordTrace]
  refine ⟨159668893957242964434328241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106445929304828642956218827 159668893957242964434328241)
  ·
    refine ⟨119751670467932223325746181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159668893957242964434328241 119751670467932223325746181)
    ·
      refine ⟨22453438212737291873577409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119751670467932223325746181 22453438212737291873577409)
      ·
        refine ⟨16840078659552968905183057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22453438212737291873577409 16840078659552968905183057)
        ·
          refine ⟨12630058994664726678887293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16840078659552968905183057 12630058994664726678887293)
          ·
            refine ⟨4736272122999272504582735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12630058994664726678887293 4736272122999272504582735)
            ·
              refine ⟨7104408184498908756874103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736272122999272504582735 7104408184498908756874103)
              ·
                refine ⟨10656612276748363135311155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104408184498908756874103 10656612276748363135311155)
                ·
                  refine ⟨15984918415122544702966733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10656612276748363135311155 15984918415122544702966733)
                  ·
                    refine ⟨5994344405670954263612525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15984918415122544702966733 5994344405670954263612525)
                    ·
                      refine ⟨2247879152126607848854697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994344405670954263612525 2247879152126607848854697)
                      ·
                        rfl

theorem cell23_4377729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_4377729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377729 prefixEnd_4377729 := by exact prefixLift 4377729
  have htrace : WordTrace (prefixWord ++ tailWord_4377729) baseStart_4377729 baseEnd_4377729 := by
    simpa [prefixWord, tailWord_4377729, baseEnd_4377729] using wordTrace_append hprefix tailTrace_4377729
  have hstable : (prefixWord ++ tailWord_4377729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377729).length < 2 ^ (prefixWord ++ tailWord_4377729).sum := by decide
  have hdescent : baseEnd_4377729 < baseStart_4377729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377775 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 7]
def baseStart_4377775 : Nat := 118140960795 + 4377775 * 2 ^ 59
def prefixEnd_4377775 : Nat := 4983230072969 + 3 ^ 40 * 4377775 * 2
def baseEnd_4377775 : Nat := 249766974692968296542165

theorem tailTrace_4377775 : CollatzResearch.WordTrace tailWord_4377775 prefixEnd_4377775 249766974692968296542165 := by
  unfold tailWord_4377775
  simp only [CollatzResearch.WordTrace]
  refine ⟨159670571715076314290502779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106447047810050876193668519 159670571715076314290502779)
  ·
    refine ⟨239505857572614471435754169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159670571715076314290502779 239505857572614471435754169)
    ·
      refine ⟨179629393179460853576815627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239505857572614471435754169 179629393179460853576815627)
      ·
        refine ⟨269444089769191280365223441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179629393179460853576815627 269444089769191280365223441)
        ·
          refine ⟨202083067326893460273917581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269444089769191280365223441 202083067326893460273917581)
          ·
            refine ⟨75781150247585047602719093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202083067326893460273917581 75781150247585047602719093)
            ·
              refine ⟨7104482835711098212754915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75781150247585047602719093 7104482835711098212754915)
              ·
                refine ⟨10656724253566647319132373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104482835711098212754915 10656724253566647319132373)
                ·
                  refine ⟨249766974692968296542165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10656724253566647319132373 249766974692968296542165)
                  ·
                    rfl

theorem cell23_4377775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 7].length) (baseStart_4377775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377775 prefixEnd_4377775 := by exact prefixLift 4377775
  have htrace : WordTrace (prefixWord ++ tailWord_4377775) baseStart_4377775 baseEnd_4377775 := by
    simpa [prefixWord, tailWord_4377775, baseEnd_4377775] using wordTrace_append hprefix tailTrace_4377775
  have hstable : (prefixWord ++ tailWord_4377775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377775).length < 2 ^ (prefixWord ++ tailWord_4377775).sum := by decide
  have hdescent : baseEnd_4377775 < baseStart_4377775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377815 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_4377815 : Nat := 118140960795 + 4377815 * 2 ^ 59
def prefixEnd_4377815 : Nat := 4983230072969 + 3 ^ 40 * 4377815 * 2
def baseEnd_4377815 : Nat := 2247923311462894512379301

theorem tailTrace_4377815 : CollatzResearch.WordTrace tailWord_4377815 prefixEnd_4377815 2247923311462894512379301 := by
  unfold tailWord_4377815
  simp only [CollatzResearch.WordTrace]
  refine ⟨159672030634931401121958899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106448020423287600747972599 159672030634931401121958899)
  ·
    refine ⟨239508045952397101682938349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159672030634931401121958899 239508045952397101682938349)
    ·
      refine ⟨89815517232148913131101881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239508045952397101682938349 89815517232148913131101881)
      ·
        refine ⟨67361637924111684848326411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89815517232148913131101881 67361637924111684848326411)
        ·
          refine ⟨101042456886167527272489617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67361637924111684848326411 101042456886167527272489617)
          ·
            refine ⟨75781842664625645454367213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101042456886167527272489617 75781842664625645454367213)
            ·
              refine ⟨28418190999234617045387705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75781842664625645454367213 28418190999234617045387705)
              ·
                refine ⟨21313643249425962784040779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28418190999234617045387705 21313643249425962784040779)
                ·
                  refine ⟨31970464874138944176061169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21313643249425962784040779 31970464874138944176061169)
                  ·
                    refine ⟨23977848655604208132045877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31970464874138944176061169 23977848655604208132045877)
                    ·
                      refine ⟨2247923311462894512379301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23977848655604208132045877 2247923311462894512379301)
                      ·
                        rfl

theorem cell23_4377815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_4377815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377815 prefixEnd_4377815 := by exact prefixLift 4377815
  have htrace : WordTrace (prefixWord ++ tailWord_4377815) baseStart_4377815 baseEnd_4377815 := by
    simpa [prefixWord, tailWord_4377815, baseEnd_4377815] using wordTrace_append hprefix tailTrace_4377815
  have hstable : (prefixWord ++ tailWord_4377815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377815).length < 2 ^ (prefixWord ++ tailWord_4377815).sum := by decide
  have hdescent : baseEnd_4377815 < baseStart_4377815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377859 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 4]
def baseStart_4377859 : Nat := 118140960795 + 4377859 * 2 ^ 59
def prefixEnd_4377859 : Nat := 4983230072969 + 3 ^ 40 * 4377859 * 2
def baseEnd_4377859 : Nat := 2247945904611692340229099

theorem tailTrace_4377859 : CollatzResearch.WordTrace tailWord_4377859 prefixEnd_4377859 2247945904611692340229099 := by
  unfold tailWord_4377859
  simp only [CollatzResearch.WordTrace]
  refine ⟨159673635446771996636560631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106449090297847997757707087 159673635446771996636560631)
  ·
    refine ⟨239510453170157994954840947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159673635446771996636560631 239510453170157994954840947)
    ·
      refine ⟨359265679755236992432261421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239510453170157994954840947 359265679755236992432261421)
      ·
        refine ⟨134724629908213872162098033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359265679755236992432261421 134724629908213872162098033)
        ·
          refine ⟨101043472431160404121573525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134724629908213872162098033 101043472431160404121573525)
          ·
            refine ⟨4736412770210643943198759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101043472431160404121573525 4736412770210643943198759)
            ·
              refine ⟨7104619155315965914798139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736412770210643943198759 7104619155315965914798139)
              ·
                refine ⟨10656928732973948872197209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104619155315965914798139 10656928732973948872197209)
                ·
                  refine ⟨7992696549730461654147907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10656928732973948872197209 7992696549730461654147907)
                  ·
                    refine ⟨11989044824595692481221861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7992696549730461654147907 11989044824595692481221861)
                    ·
                      refine ⟨2247945904611692340229099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11989044824595692481221861 2247945904611692340229099)
                      ·
                        rfl

theorem cell23_4377859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_4377859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377859 prefixEnd_4377859 := by exact prefixLift 4377859
  have htrace : WordTrace (prefixWord ++ tailWord_4377859) baseStart_4377859 baseEnd_4377859 := by
    simpa [prefixWord, tailWord_4377859, baseEnd_4377859] using wordTrace_append hprefix tailTrace_4377859
  have hstable : (prefixWord ++ tailWord_4377859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377859).length < 2 ^ (prefixWord ++ tailWord_4377859).sum := by decide
  have hdescent : baseEnd_4377859 < baseStart_4377859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377865 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 8]
def baseStart_4377865 : Nat := 118140960795 + 4377865 * 2 ^ 59
def prefixEnd_4377865 : Nat := 4983230072969 + 3 ^ 40 * 4377865 * 2
def baseEnd_4377865 : Nat := 249772109499513257417119

theorem tailTrace_4377865 : CollatzResearch.WordTrace tailWord_4377865 prefixEnd_4377865 249772109499513257417119 := by
  unfold tailWord_4377865
  simp only [CollatzResearch.WordTrace]
  refine ⟨159673854284750259661279049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106449236189833506440852699 159673854284750259661279049)
  ·
    refine ⟨119755390713562694745959287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159673854284750259661279049 119755390713562694745959287)
    ·
      refine ⟨179633086070344042118938931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119755390713562694745959287 179633086070344042118938931)
      ·
        refine ⟨269449629105516063178408397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179633086070344042118938931 269449629105516063178408397)
        ·
          refine ⟨101043610914568523691903149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269449629105516063178408397 101043610914568523691903149)
          ·
            refine ⟨37891354092963196384463681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101043610914568523691903149 37891354092963196384463681)
            ·
              refine ⟨28418515569722397288347761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37891354092963196384463681 28418515569722397288347761)
              ·
                refine ⟨21313886677291797966260821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28418515569722397288347761 21313886677291797966260821)
                ·
                  refine ⟨249772109499513257417119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21313886677291797966260821 249772109499513257417119)
                  ·
                    rfl

theorem cell23_4377865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_4377865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377865 prefixEnd_4377865 := by exact prefixLift 4377865
  have htrace : WordTrace (prefixWord ++ tailWord_4377865) baseStart_4377865 baseEnd_4377865 := by
    simpa [prefixWord, tailWord_4377865, baseEnd_4377865] using wordTrace_append hprefix tailTrace_4377865
  have hstable : (prefixWord ++ tailWord_4377865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377865).length < 2 ^ (prefixWord ++ tailWord_4377865).sum := by decide
  have hdescent : baseEnd_4377865 < baseStart_4377865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377882 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_4377882 : Nat := 118140960795 + 4377882 * 2 ^ 59
def prefixEnd_4377882 : Nat := 4983230072969 + 3 ^ 40 * 4377882 * 2
def baseEnd_4377882 : Nat := 249773079407416194471277

theorem tailTrace_4377882 : CollatzResearch.WordTrace tailWord_4377882 prefixEnd_4377882 249773079407416194471277 := by
  unfold tailWord_4377882
  simp only [CollatzResearch.WordTrace]
  refine ⟨39918618581422167891161975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106449649550459114376431933 39918618581422167891161975)
  ·
    refine ⟨59877927872133251836742963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39918618581422167891161975 59877927872133251836742963)
    ·
      refine ⟨89816891808199877755114445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59877927872133251836742963 89816891808199877755114445)
      ·
        refine ⟨33681334428074954158167917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89816891808199877755114445 33681334428074954158167917)
        ·
          refine ⟨12630500410528107809312969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33681334428074954158167917 12630500410528107809312969)
          ·
            refine ⟨9472875307896080856984727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12630500410528107809312969 9472875307896080856984727)
            ·
              refine ⟨14209312961844121285477091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9472875307896080856984727 14209312961844121285477091)
              ·
                refine ⟨21313969442766181928215637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14209312961844121285477091 21313969442766181928215637)
                ·
                  refine ⟨249773079407416194471277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21313969442766181928215637 249773079407416194471277)
                  ·
                    rfl

theorem cell23_4377882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_4377882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377882 prefixEnd_4377882 := by exact prefixLift 4377882
  have htrace : WordTrace (prefixWord ++ tailWord_4377882) baseStart_4377882 baseEnd_4377882 := by
    simpa [prefixWord, tailWord_4377882, baseEnd_4377882] using wordTrace_append hprefix tailTrace_4377882
  have hstable : (prefixWord ++ tailWord_4377882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377882).length < 2 ^ (prefixWord ++ tailWord_4377882).sum := by decide
  have hdescent : baseEnd_4377882 < baseStart_4377882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4377919 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 1, 5, 2]
def baseStart_4377919 : Nat := 118140960795 + 4377919 * 2 ^ 59
def prefixEnd_4377919 : Nat := 4983230072969 + 3 ^ 40 * 4377919 * 2
def baseEnd_4377919 : Nat := 2247976713450962105478823

theorem tailTrace_4377919 : CollatzResearch.WordTrace tailWord_4377919 prefixEnd_4377919 2247976713450962105478823 := by
  unfold tailWord_4377919
  simp only [CollatzResearch.WordTrace]
  refine ⟨159675823826554626883744811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106450549217703084589163207 159675823826554626883744811)
  ·
    refine ⟨239513735739831940325617217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159675823826554626883744811 239513735739831940325617217)
    ·
      refine ⟨179635301804873955244212913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239513735739831940325617217 179635301804873955244212913)
      ·
        refine ⟨134726476353655466433159685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179635301804873955244212913 134726476353655466433159685)
        ·
          refine ⟨25261214316310399956217441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134726476353655466433159685 25261214316310399956217441)
          ·
            refine ⟨18945910737232799967163081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25261214316310399956217441 18945910737232799967163081)
            ·
              refine ⟨14209433052924599975372311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18945910737232799967163081 14209433052924599975372311)
              ·
                refine ⟨21314149579386899963058467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14209433052924599975372311 21314149579386899963058467)
                ·
                  refine ⟨31971224369080349944587701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21314149579386899963058467 31971224369080349944587701)
                  ·
                    refine ⟨2997302284601282807305097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31971224369080349944587701 2997302284601282807305097)
                    ·
                      refine ⟨2247976713450962105478823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997302284601282807305097 2247976713450962105478823)
                      ·
                        rfl

theorem cell23_4377919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_4377919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4377919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4377919 prefixEnd_4377919 := by exact prefixLift 4377919
  have htrace : WordTrace (prefixWord ++ tailWord_4377919) baseStart_4377919 baseEnd_4377919 := by
    simpa [prefixWord, tailWord_4377919, baseEnd_4377919] using wordTrace_append hprefix tailTrace_4377919
  have hstable : (prefixWord ++ tailWord_4377919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4377919).length < 2 ^ (prefixWord ++ tailWord_4377919).sum := by decide
  have hdescent : baseEnd_4377919 < baseStart_4377919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4377919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378016 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 2, 1, 3]
def baseStart_4378016 : Nat := 118140960795 + 4378016 * 2 ^ 59
def prefixEnd_4378016 : Nat := 4983230072969 + 3 ^ 40 * 4378016 * 2
def baseEnd_4378016 : Nat := 2248026521074448225965877

theorem tailTrace_4378016 : CollatzResearch.WordTrace tailWord_4378016 prefixEnd_4378016 2248026521074448225965877 := by
  unfold tailWord_4378016
  simp only [CollatzResearch.WordTrace]
  refine ⟨79839680853601606225012951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106452907804802141633350601 79839680853601606225012951)
  ·
    refine ⟨119759521280402409337519427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79839680853601606225012951 119759521280402409337519427)
    ·
      refine ⟨179639281920603614006279141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119759521280402409337519427 179639281920603614006279141)
      ·
        refine ⟨33682365360113177626177339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179639281920603614006279141 33682365360113177626177339)
        ·
          refine ⟨50523548040169766439266009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33682365360113177626177339 50523548040169766439266009)
          ·
            refine ⟨37892661030127324829449507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50523548040169766439266009 37892661030127324829449507)
            ·
              refine ⟨56838991545190987244174261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37892661030127324829449507 56838991545190987244174261)
              ·
                refine ⟨5328655457361655054141337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56838991545190987244174261 5328655457361655054141337)
                ·
                  refine ⟨3996491593021241290606003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5328655457361655054141337 3996491593021241290606003)
                  ·
                    refine ⟨5994737389531861935909005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3996491593021241290606003 5994737389531861935909005)
                    ·
                      refine ⟨2248026521074448225965877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994737389531861935909005 2248026521074448225965877)
                      ·
                        rfl

theorem cell23_4378016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_4378016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378016 prefixEnd_4378016 := by exact prefixLift 4378016
  have htrace : WordTrace (prefixWord ++ tailWord_4378016) baseStart_4378016 baseEnd_4378016 := by
    simpa [prefixWord, tailWord_4378016, baseEnd_4378016] using wordTrace_append hprefix tailTrace_4378016
  have hstable : (prefixWord ++ tailWord_4378016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378016).length < 2 ^ (prefixWord ++ tailWord_4378016).sum := by decide
  have hdescent : baseEnd_4378016 < baseStart_4378016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378069 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4378069 : Nat := 118140960795 + 4378069 * 2 ^ 59
def prefixEnd_4378069 : Nat := 4983230072969 + 3 ^ 40 * 4378069 * 2
def baseEnd_4378069 : Nat := 2248053735549136518603133

theorem tailTrace_4378069 : CollatzResearch.WordTrace tailWord_4378069 prefixEnd_4378069 2248053735549136518603133 := by
  unfold tailWord_4378069
  simp only [CollatzResearch.WordTrace]
  refine ⟨159681294776011202501705261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106454196517340801667803507 159681294776011202501705261)
  ·
    refine ⟨59880485541004200938139473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159681294776011202501705261 59880485541004200938139473)
    ·
      refine ⟨44910364155753150703604605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59880485541004200938139473 44910364155753150703604605)
      ·
        refine ⟨16841386558407431513851727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44910364155753150703604605 16841386558407431513851727)
        ·
          refine ⟨25262079837611147270777591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16841386558407431513851727 25262079837611147270777591)
          ·
            refine ⟨37893119756416720906166387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25262079837611147270777591 37893119756416720906166387)
            ·
              refine ⟨56839679634625081359249581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37893119756416720906166387 56839679634625081359249581)
              ·
                refine ⟨21314879862984405509718593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56839679634625081359249581 21314879862984405509718593)
                ·
                  refine ⟨15986159897238304132288945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21314879862984405509718593 15986159897238304132288945)
                  ·
                    refine ⟨11989619922928728099216709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15986159897238304132288945 11989619922928728099216709)
                    ·
                      refine ⟨2248053735549136518603133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11989619922928728099216709 2248053735549136518603133)
                      ·
                        rfl

theorem cell23_4378069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4378069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378069 prefixEnd_4378069 := by exact prefixLift 4378069
  have htrace : WordTrace (prefixWord ++ tailWord_4378069) baseStart_4378069 baseEnd_4378069 := by
    simpa [prefixWord, tailWord_4378069, baseEnd_4378069] using wordTrace_append hprefix tailTrace_4378069
  have hstable : (prefixWord ++ tailWord_4378069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378069).length < 2 ^ (prefixWord ++ tailWord_4378069).sum := by decide
  have hdescent : baseEnd_4378069 < baseStart_4378069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378073 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 1, 4, 2]
def baseStart_4378073 : Nat := 118140960795 + 4378073 * 2 ^ 59
def prefixEnd_4378073 : Nat := 4983230072969 + 3 ^ 40 * 4378073 * 2
def baseEnd_4378073 : Nat := 2248055789471754502953115

theorem tailTrace_4378073 : CollatzResearch.WordTrace tailWord_4378073 prefixEnd_4378073 2248055789471754502953115 := by
  unfold tailWord_4378073
  simp only [CollatzResearch.WordTrace]
  refine ⟨159681440667996711184850873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106454293778664474123233915 159681440667996711184850873)
  ·
    refine ⟨119761080500997533388638155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159681440667996711184850873 119761080500997533388638155)
    ·
      refine ⟨179641620751496300082957233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119761080500997533388638155 179641620751496300082957233)
      ·
        refine ⟨134731215563622225062217925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179641620751496300082957233 134731215563622225062217925)
        ·
          refine ⟨25262102918179167199165861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134731215563622225062217925 25262102918179167199165861)
          ·
            refine ⟨4736644297158593849843599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25262102918179167199165861 4736644297158593849843599)
            ·
              refine ⟨7104966445737890774765399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736644297158593849843599 7104966445737890774765399)
              ·
                refine ⟨10657449668606836162148099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7104966445737890774765399 10657449668606836162148099)
                ·
                  refine ⟨15986174502910254243222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10657449668606836162148099 15986174502910254243222149)
                  ·
                    refine ⟨2997407719295672670604153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15986174502910254243222149 2997407719295672670604153)
                    ·
                      refine ⟨2248055789471754502953115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997407719295672670604153 2248055789471754502953115)
                      ·
                        rfl

theorem cell23_4378073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_4378073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378073 prefixEnd_4378073 := by exact prefixLift 4378073
  have htrace : WordTrace (prefixWord ++ tailWord_4378073) baseStart_4378073 baseEnd_4378073 := by
    simpa [prefixWord, tailWord_4378073, baseEnd_4378073] using wordTrace_append hprefix tailTrace_4378073
  have hstable : (prefixWord ++ tailWord_4378073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378073).length < 2 ^ (prefixWord ++ tailWord_4378073).sum := by decide
  have hdescent : baseEnd_4378073 < baseStart_4378073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378096 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 5]
def baseStart_4378096 : Nat := 118140960795 + 4378096 * 2 ^ 59
def prefixEnd_4378096 : Nat := 4983230072969 + 3 ^ 40 * 4378096 * 2
def baseEnd_4378096 : Nat := 249785288836311990329501

theorem tailTrace_4378096 : CollatzResearch.WordTrace tailWord_4378096 prefixEnd_4378096 249785288836311990329501 := by
  unfold tailWord_4378096
  simp only [CollatzResearch.WordTrace]
  refine ⟨79841139773456693056469071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106454853031275590741958761 79841139773456693056469071)
  ·
    refine ⟨119761709660185039584703607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79841139773456693056469071 119761709660185039584703607)
    ·
      refine ⟨179642564490277559377055411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119761709660185039584703607 179642564490277559377055411)
      ·
        refine ⟨269463846735416339065583117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179642564490277559377055411 269463846735416339065583117)
        ·
          refine ⟨101048942525781127149593669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269463846735416339065583117 101048942525781127149593669)
          ·
            refine ⟨18946676723583961340548813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101048942525781127149593669 18946676723583961340548813)
            ·
              refine ⟨7105003771343985502705805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18946676723583961340548813 7105003771343985502705805)
              ·
                refine ⟨2664376414253994563514677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7105003771343985502705805 2664376414253994563514677)
                ·
                  refine ⟨249785288836311990329501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2664376414253994563514677 249785288836311990329501)
                  ·
                    rfl

theorem cell23_4378096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 5].length) (baseStart_4378096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378096 prefixEnd_4378096 := by exact prefixLift 4378096
  have htrace : WordTrace (prefixWord ++ tailWord_4378096) baseStart_4378096 baseEnd_4378096 := by
    simpa [prefixWord, tailWord_4378096, baseEnd_4378096] using wordTrace_append hprefix tailTrace_4378096
  have hstable : (prefixWord ++ tailWord_4378096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378096).length < 2 ^ (prefixWord ++ tailWord_4378096).sum := by decide
  have hdescent : baseEnd_4378096 < baseStart_4378096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378109 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_4378109 : Nat := 118140960795 + 4378109 * 2 ^ 59
def prefixEnd_4378109 : Nat := 4983230072969 + 3 ^ 40 * 4378109 * 2
def baseEnd_4378109 : Nat := 749358091591772120700983

theorem tailTrace_4378109 : CollatzResearch.WordTrace tailWord_4378109 prefixEnd_4378109 749358091591772120700983 := by
  unfold tailWord_4378109
  simp only [CollatzResearch.WordTrace]
  refine ⟨159682753695866289333161381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106455169130577526222107587 159682753695866289333161381)
  ·
    refine ⟨29940516317974929249967759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159682753695866289333161381 29940516317974929249967759)
    ·
      refine ⟨44910774476962393874951639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29940516317974929249967759 44910774476962393874951639)
      ·
        refine ⟨67366161715443590812427459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44910774476962393874951639 67366161715443590812427459)
        ·
          refine ⟨101049242573165386218641189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67366161715443590812427459 101049242573165386218641189)
          ·
            refine ⟨18946732982468509915995223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101049242573165386218641189 18946732982468509915995223)
            ·
              refine ⟨28420099473702764873992835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18946732982468509915995223 28420099473702764873992835)
              ·
                refine ⟨42630149210554147310989253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28420099473702764873992835 42630149210554147310989253)
                ·
                  refine ⟨7993152976978902620810485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42630149210554147310989253 7993152976978902620810485)
                  ·
                    refine ⟨749358091591772120700983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7993152976978902620810485 749358091591772120700983)
                    ·
                      rfl

theorem cell23_4378109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_4378109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378109 prefixEnd_4378109 := by exact prefixLift 4378109
  have htrace : WordTrace (prefixWord ++ tailWord_4378109) baseStart_4378109 baseEnd_4378109 := by
    simpa [prefixWord, tailWord_4378109, baseEnd_4378109] using wordTrace_append hprefix tailTrace_4378109
  have hstable : (prefixWord ++ tailWord_4378109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378109).length < 2 ^ (prefixWord ++ tailWord_4378109).sum := by decide
  have hdescent : baseEnd_4378109 < baseStart_4378109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378112 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_4378112 : Nat := 118140960795 + 4378112 * 2 ^ 59
def prefixEnd_4378112 : Nat := 4983230072969 + 3 ^ 40 * 4378112 * 2
def baseEnd_4378112 : Nat := 2248075815217279850365435

theorem tailTrace_4378112 : CollatzResearch.WordTrace tailWord_4378112 prefixEnd_4378112 2248075815217279850365435 := by
  unfold tailWord_4378112
  simp only [CollatzResearch.WordTrace]
  refine ⟨79841431557427710422760295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106455242076570280563680393 79841431557427710422760295)
  ·
    refine ⟨119762147336141565634140443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79841431557427710422760295 119762147336141565634140443)
    ·
      refine ⟨179643221004212348451210665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119762147336141565634140443 179643221004212348451210665)
      ·
        refine ⟨134732415753159261338407999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179643221004212348451210665 134732415753159261338407999)
        ·
          refine ⟨202098623629738892007611999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134732415753159261338407999 202098623629738892007611999)
          ·
            refine ⟨303147935444608338011417999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202098623629738892007611999 303147935444608338011417999)
            ·
              refine ⟨454721903166912507017126999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303147935444608338011417999 454721903166912507017126999)
              ·
                refine ⟨682082854750368760525690499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454721903166912507017126999 682082854750368760525690499)
                ·
                  refine ⟨1023124282125553140788535749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682082854750368760525690499 1023124282125553140788535749)
                  ·
                    refine ⟨191835802898541213897850453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1023124282125553140788535749 191835802898541213897850453)
                    ·
                      refine ⟨2248075815217279850365435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191835802898541213897850453 2248075815217279850365435)
                      ·
                        rfl

theorem cell23_4378112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_4378112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378112 prefixEnd_4378112 := by exact prefixLift 4378112
  have htrace : WordTrace (prefixWord ++ tailWord_4378112) baseStart_4378112 baseEnd_4378112 := by
    simpa [prefixWord, tailWord_4378112, baseEnd_4378112] using wordTrace_append hprefix tailTrace_4378112
  have hstable : (prefixWord ++ tailWord_4378112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378112).length < 2 ^ (prefixWord ++ tailWord_4378112).sum := by decide
  have hdescent : baseEnd_4378112 < baseStart_4378112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378113 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 7]
def baseStart_4378113 : Nat := 118140960795 + 4378113 * 2 ^ 59
def prefixEnd_4378113 : Nat := 4983230072969 + 3 ^ 40 * 4378113 * 2
def baseEnd_4378113 : Nat := 249786258744214927383659

theorem tailTrace_4378113 : CollatzResearch.WordTrace tailWord_4378113 prefixEnd_4378113 249786258744214927383659 := by
  unfold tailWord_4378113
  simp only [CollatzResearch.WordTrace]
  refine ⟨159682899587851798016306993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106455266391901198677537995 159682899587851798016306993)
  ·
    refine ⟨119762174690888848512230245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159682899587851798016306993 119762174690888848512230245)
    ·
      refine ⟨22455407754541659096043171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119762174690888848512230245 22455407754541659096043171)
      ·
        refine ⟨33683111631812488644064757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22455407754541659096043171 33683111631812488644064757)
        ·
          refine ⟨3157791715482420810381071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33683111631812488644064757 3157791715482420810381071)
          ·
            refine ⟨4736687573223631215571607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157791715482420810381071 4736687573223631215571607)
            ·
              refine ⟨7105031359835446823357411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736687573223631215571607 7105031359835446823357411)
              ·
                refine ⟨10657547039753170235036117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7105031359835446823357411 10657547039753170235036117)
                ·
                  refine ⟨249786258744214927383659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10657547039753170235036117 249786258744214927383659)
                  ·
                    rfl

theorem cell23_4378113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 7].length) (baseStart_4378113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378113 prefixEnd_4378113 := by exact prefixLift 4378113
  have htrace : WordTrace (prefixWord ++ tailWord_4378113) baseStart_4378113 baseEnd_4378113 := by
    simpa [prefixWord, tailWord_4378113, baseEnd_4378113] using wordTrace_append hprefix tailTrace_4378113
  have hstable : (prefixWord ++ tailWord_4378113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378113).length < 2 ^ (prefixWord ++ tailWord_4378113).sum := by decide
  have hdescent : baseEnd_4378113 < baseStart_4378113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378118 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4378118 : Nat := 118140960795 + 4378118 * 2 ^ 59
def prefixEnd_4378118 : Nat := 4983230072969 + 3 ^ 40 * 4378118 * 2
def baseEnd_4378118 : Nat := 2248078896101206826890409

theorem tailTrace_4378118 : CollatzResearch.WordTrace tailWord_4378118 prefixEnd_4378118 2248078896101206826890409 := by
  unfold tailWord_4378118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990096311026052620944969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106455387968555789246826005 4990096311026052620944969)
  ·
    refine ⟨3742572233269539465708727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4990096311026052620944969 3742572233269539465708727)
    ·
      refine ⟨5613858349904309198563091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742572233269539465708727 5613858349904309198563091)
      ·
        refine ⟨8420787524856463797844637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613858349904309198563091 8420787524856463797844637)
        ·
          refine ⟨3157795321821173924191739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8420787524856463797844637 3157795321821173924191739)
          ·
            refine ⟨4736692982731760886287609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157795321821173924191739 4736692982731760886287609)
            ·
              refine ⟨3552519737048820664715707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736692982731760886287609 3552519737048820664715707)
              ·
                refine ⟨5328779605573230997073561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552519737048820664715707 5328779605573230997073561)
                ·
                  refine ⟨3996584704179923247805171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5328779605573230997073561 3996584704179923247805171)
                  ·
                    refine ⟨5994877056269884871707757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3996584704179923247805171 5994877056269884871707757)
                    ·
                      refine ⟨2248078896101206826890409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994877056269884871707757 2248078896101206826890409)
                      ·
                        rfl

theorem cell23_4378118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4378118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378118 prefixEnd_4378118 := by exact prefixLift 4378118
  have htrace : WordTrace (prefixWord ++ tailWord_4378118) baseStart_4378118 baseEnd_4378118 := by
    simpa [prefixWord, tailWord_4378118, baseEnd_4378118] using wordTrace_append hprefix tailTrace_4378118
  have hstable : (prefixWord ++ tailWord_4378118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378118).length < 2 ^ (prefixWord ++ tailWord_4378118).sum := by decide
  have hdescent : baseEnd_4378118 < baseStart_4378118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378119 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4378119 : Nat := 118140960795 + 4378119 * 2 ^ 59
def prefixEnd_4378119 : Nat := 4983230072969 + 3 ^ 40 * 4378119 * 2
def baseEnd_4378119 : Nat := 2248079409581861322977903

theorem tailTrace_4378119 : CollatzResearch.WordTrace tailWord_4378119 prefixEnd_4378119 2248079409581861322977903 := by
  unfold tailWord_4378119
  simp only [CollatzResearch.WordTrace]
  refine ⟨159683118425830061041025411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106455412283886707360683607 159683118425830061041025411)
  ·
    refine ⟨239524677638745091561538117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159683118425830061041025411 239524677638745091561538117)
    ·
      refine ⟨44910877057264704667788397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239524677638745091561538117 44910877057264704667788397)
      ·
        refine ⟨16841578896474264250420649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44910877057264704667788397 16841578896474264250420649)
        ·
          refine ⟨12631184172355698187815487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16841578896474264250420649 12631184172355698187815487)
          ·
            refine ⟨18946776258533547281723231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12631184172355698187815487 18946776258533547281723231)
            ·
              refine ⟨28420164387800320922584847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18946776258533547281723231 28420164387800320922584847)
              ·
                refine ⟨42630246581700481383877271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28420164387800320922584847 42630246581700481383877271)
                ·
                  refine ⟨63945369872550722075815907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42630246581700481383877271 63945369872550722075815907)
                  ·
                    refine ⟨95918054808826083113723861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63945369872550722075815907 95918054808826083113723861)
                    ·
                      refine ⟨2248079409581861322977903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95918054808826083113723861 2248079409581861322977903)
                      ·
                        rfl

theorem cell23_4378119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4378119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378119 prefixEnd_4378119 := by exact prefixLift 4378119
  have htrace : WordTrace (prefixWord ++ tailWord_4378119) baseStart_4378119 baseEnd_4378119 := by
    simpa [prefixWord, tailWord_4378119, baseEnd_4378119] using wordTrace_append hprefix tailTrace_4378119
  have hstable : (prefixWord ++ tailWord_4378119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378119).length < 2 ^ (prefixWord ++ tailWord_4378119).sum := by decide
  have hdescent : baseEnd_4378119 < baseStart_4378119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378124 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 2, 2, 2]
def baseStart_4378124 : Nat := 118140960795 + 4378124 * 2 ^ 59
def prefixEnd_4378124 : Nat := 4983230072969 + 3 ^ 40 * 4378124 * 2
def baseEnd_4378124 : Nat := 2248081976985133803415381

theorem tailTrace_4378124 : CollatzResearch.WordTrace tailWord_4378124 prefixEnd_4378124 2248081976985133803415381 := by
  unfold tailWord_4378124
  simp only [CollatzResearch.WordTrace]
  refine ⟨79841650395405973447478713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106455533860541297929971617 79841650395405973447478713)
  ·
    refine ⟨59881237796554480085609035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79841650395405973447478713 59881237796554480085609035)
    ·
      refine ⟨89821856694831720128413553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59881237796554480085609035 89821856694831720128413553)
      ·
        refine ⟨67366392521123790096310165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89821856694831720128413553 67366392521123790096310165)
        ·
          refine ⟨3157799649427677660764539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67366392521123790096310165 3157799649427677660764539)
          ·
            refine ⟨4736699474141516491146809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157799649427677660764539 4736699474141516491146809)
            ·
              refine ⟨3552524605606137368360107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736699474141516491146809 3552524605606137368360107)
              ·
                refine ⟨5328786908409206052540161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3552524605606137368360107 5328786908409206052540161)
                ·
                  refine ⟨3996590181306904539405121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5328786908409206052540161 3996590181306904539405121)
                  ·
                    refine ⟨2997442635980178404553841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3996590181306904539405121 2997442635980178404553841)
                    ·
                      refine ⟨2248081976985133803415381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997442635980178404553841 2248081976985133803415381)
                      ·
                        rfl

theorem cell23_4378124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_4378124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378124 prefixEnd_4378124 := by exact prefixLift 4378124
  have htrace : WordTrace (prefixWord ++ tailWord_4378124) baseStart_4378124 baseEnd_4378124 := by
    simpa [prefixWord, tailWord_4378124, baseEnd_4378124] using wordTrace_append hprefix tailTrace_4378124
  have hstable : (prefixWord ++ tailWord_4378124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378124).length < 2 ^ (prefixWord ++ tailWord_4378124).sum := by decide
  have hdescent : baseEnd_4378124 < baseStart_4378124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378129 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_4378129 : Nat := 118140960795 + 4378129 * 2 ^ 59
def prefixEnd_4378129 : Nat := 4983230072969 + 3 ^ 40 * 4378129 * 2
def baseEnd_4378129 : Nat := 2248084544388406283852857

theorem tailTrace_4378129 : CollatzResearch.WordTrace tailWord_4378129 prefixEnd_4378129 2248084544388406283852857 := by
  unfold tailWord_4378129
  simp only [CollatzResearch.WordTrace]
  refine ⟨159683483155793832748889441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106455655437195888499259627 159683483155793832748889441)
  ·
    refine ⟨119762612366845374561667081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159683483155793832748889441 119762612366845374561667081)
    ·
      refine ⟨89821959275134030921250311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119762612366845374561667081 89821959275134030921250311)
      ·
        refine ⟨134732938912701046381875467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89821959275134030921250311 134732938912701046381875467)
        ·
          refine ⟨202099408369051569572813201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134732938912701046381875467 202099408369051569572813201)
          ·
            refine ⟨151574556276788677179609901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202099408369051569572813201 151574556276788677179609901)
            ·
              refine ⟨56840458603795753942353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151574556276788677179609901 56840458603795753942353713)
              ·
                refine ⟨42630343952846815456765285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56840458603795753942353713 42630343952846815456765285)
                ·
                  refine ⟨7993189491158777898143491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42630343952846815456765285 7993189491158777898143491)
                  ·
                    refine ⟨11989784236738166847215237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7993189491158777898143491 11989784236738166847215237)
                    ·
                      refine ⟨2248084544388406283852857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11989784236738166847215237 2248084544388406283852857)
                      ·
                        rfl

theorem cell23_4378129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_4378129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378129 prefixEnd_4378129 := by exact prefixLift 4378129
  have htrace : WordTrace (prefixWord ++ tailWord_4378129) baseStart_4378129 baseEnd_4378129 := by
    simpa [prefixWord, tailWord_4378129, baseEnd_4378129] using wordTrace_append hprefix tailTrace_4378129
  have hstable : (prefixWord ++ tailWord_4378129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378129).length < 2 ^ (prefixWord ++ tailWord_4378129).sum := by decide
  have hdescent : baseEnd_4378129 < baseStart_4378129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378146 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4378146 : Nat := 118140960795 + 4378146 * 2 ^ 59
def prefixEnd_4378146 : Nat := 4983230072969 + 3 ^ 40 * 4378146 * 2
def baseEnd_4378146 : Nat := 2248093273559532717340279

theorem tailTrace_4378146 : CollatzResearch.WordTrace tailWord_4378146 prefixEnd_4378146 2248093273559532717340279 := by
  unfold tailWord_4378146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39921025799183061163064573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106456068797821496434838861 39921025799183061163064573)
  ·
    refine ⟨14970384674693647936149215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39921025799183061163064573 14970384674693647936149215)
    ·
      refine ⟨22455577012040471904223823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14970384674693647936149215 22455577012040471904223823)
      ·
        refine ⟨33683365518060707856335735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22455577012040471904223823 33683365518060707856335735)
        ·
          refine ⟨50525048277091061784503603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33683365518060707856335735 50525048277091061784503603)
          ·
            refine ⟨75787572415636592676755405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50525048277091061784503603 75787572415636592676755405)
            ·
              refine ⟨28420339655863722253783277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75787572415636592676755405 28420339655863722253783277)
              ·
                refine ⟨10657627370948895845168729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28420339655863722253783277 10657627370948895845168729)
                ·
                  refine ⟨7993220528211671883876547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10657627370948895845168729 7993220528211671883876547)
                  ·
                    refine ⟨11989830792317507825814821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7993220528211671883876547 11989830792317507825814821)
                    ·
                      refine ⟨2248093273559532717340279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11989830792317507825814821 2248093273559532717340279)
                      ·
                        rfl

theorem cell23_4378146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4378146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378146 prefixEnd_4378146 := by exact prefixLift 4378146
  have htrace : WordTrace (prefixWord ++ tailWord_4378146) baseStart_4378146 baseEnd_4378146 := by
    simpa [prefixWord, tailWord_4378146, baseEnd_4378146] using wordTrace_append hprefix tailTrace_4378146
  have hstable : (prefixWord ++ tailWord_4378146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378146).length < 2 ^ (prefixWord ++ tailWord_4378146).sum := by decide
  have hdescent : baseEnd_4378146 < baseStart_4378146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378179 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 3]
def baseStart_4378179 : Nat := 118140960795 + 4378179 * 2 ^ 59
def prefixEnd_4378179 : Nat := 4983230072969 + 3 ^ 40 * 4378179 * 2
def baseEnd_4378179 : Nat := 2248110218421131088227627

theorem tailTrace_4378179 : CollatzResearch.WordTrace tailWord_4378179 prefixEnd_4378179 2248110218421131088227627 := by
  unfold tailWord_4378179
  simp only [CollatzResearch.WordTrace]
  refine ⟨159685306805612691288209591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106456871203741794192139727 159685306805612691288209591)
  ·
    refine ⟨239527960208419036932314387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159685306805612691288209591 239527960208419036932314387)
    ·
      refine ⟨359291940312628555398471581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239527960208419036932314387 359291940312628555398471581)
      ·
        refine ⟨134734477617235708274426843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359291940312628555398471581 134734477617235708274426843)
        ·
          refine ⟨202101716425853562411640265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134734477617235708274426843 202101716425853562411640265)
          ·
            refine ⟨151576287319390171808730199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202101716425853562411640265 151576287319390171808730199)
            ·
              refine ⟨227364430979085257713095299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151576287319390171808730199 227364430979085257713095299)
              ·
                refine ⟨341046646468627886569642949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227364430979085257713095299 341046646468627886569642949)
                ·
                  refine ⟨63946246212867728731808053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341046646468627886569642949 63946246212867728731808053)
                  ·
                    refine ⟨5994960582456349568607005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63946246212867728731808053 5994960582456349568607005)
                    ·
                      refine ⟨2248110218421131088227627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5994960582456349568607005 2248110218421131088227627)
                      ·
                        rfl

theorem cell23_4378179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_4378179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378179 prefixEnd_4378179 := by exact prefixLift 4378179
  have htrace : WordTrace (prefixWord ++ tailWord_4378179) baseStart_4378179 baseEnd_4378179 := by
    simpa [prefixWord, tailWord_4378179, baseEnd_4378179] using wordTrace_append hprefix tailTrace_4378179
  have hstable : (prefixWord ++ tailWord_4378179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378179).length < 2 ^ (prefixWord ++ tailWord_4378179).sum := by decide
  have hdescent : baseEnd_4378179 < baseStart_4378179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378230 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4378230 : Nat := 118140960795 + 4378230 * 2 ^ 59
def prefixEnd_4378230 : Nat := 4983230072969 + 3 ^ 40 * 4378230 * 2
def baseEnd_4378230 : Nat := 2248136405934510388689893

theorem tailTrace_4378230 : CollatzResearch.WordTrace tailWord_4378230 prefixEnd_4378230 2248136405934510388689893 := by
  unfold tailWord_4378230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980447933026745437394759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106458111285618617998877429 9980447933026745437394759)
  ·
    refine ⟨14970671899540118156092139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9980447933026745437394759 14970671899540118156092139)
    ·
      refine ⟨22456007849310177234138209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14970671899540118156092139 22456007849310177234138209)
      ·
        refine ⟨16842005886982632925603657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22456007849310177234138209 16842005886982632925603657)
        ·
          refine ⟨12631504415236974694202743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16842005886982632925603657 12631504415236974694202743)
          ·
            refine ⟨18947256622855462041304115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12631504415236974694202743 18947256622855462041304115)
            ·
              refine ⟨28420884934283193061956173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18947256622855462041304115 28420884934283193061956173)
              ·
                refine ⟨10657831850356197398233565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28420884934283193061956173 10657831850356197398233565)
                ·
                  refine ⟨3996686943883574024337587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10657831850356197398233565 3996686943883574024337587)
                  ·
                    refine ⟨5995030415825361036506381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3996686943883574024337587 5995030415825361036506381)
                    ·
                      refine ⟨2248136405934510388689893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995030415825361036506381 2248136405934510388689893)
                      ·
                        rfl

theorem cell23_4378230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4378230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378230 prefixEnd_4378230 := by exact prefixLift 4378230
  have htrace : WordTrace (prefixWord ++ tailWord_4378230) baseStart_4378230 baseEnd_4378230 := by
    simpa [prefixWord, tailWord_4378230, baseEnd_4378230] using wordTrace_append hprefix tailTrace_4378230
  have hstable : (prefixWord ++ tailWord_4378230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378230).length < 2 ^ (prefixWord ++ tailWord_4378230).sum := by decide
  have hdescent : baseEnd_4378230 < baseStart_4378230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378256 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_4378256 : Nat := 118140960795 + 4378256 * 2 ^ 59
def prefixEnd_4378256 : Nat := 4983230072969 + 3 ^ 40 * 4378256 * 2
def baseEnd_4378256 : Nat := 2248149756431527286964773

theorem tailTrace_4378256 : CollatzResearch.WordTrace tailWord_4378256 prefixEnd_4378256 2248149756431527286964773 := by
  unfold tailWord_4378256
  simp only [CollatzResearch.WordTrace]
  refine ⟨79844057613166866719381311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106458743484222488959175081 79844057613166866719381311)
  ·
    refine ⟨119766086419750300079071967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79844057613166866719381311 119766086419750300079071967)
    ·
      refine ⟨179649129629625450118607951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119766086419750300079071967 179649129629625450118607951)
      ·
        refine ⟨269473694444438175177911927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179649129629625450118607951 269473694444438175177911927)
        ·
          refine ⟨404210541666657262766867891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269473694444438175177911927 404210541666657262766867891)
          ·
            refine ⟨606315812499985894150301837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404210541666657262766867891 606315812499985894150301837)
            ·
              refine ⟨227368429687494710306363189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606315812499985894150301837 227368429687494710306363189)
              ·
                refine ⟨21315790283202629091221549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227368429687494710306363189 21315790283202629091221549)
                ·
                  refine ⟨7993421356200985909208081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21315790283202629091221549 7993421356200985909208081)
                  ·
                    refine ⟨5995066017150739431906061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7993421356200985909208081 5995066017150739431906061)
                    ·
                      refine ⟨2248149756431527286964773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995066017150739431906061 2248149756431527286964773)
                      ·
                        rfl

theorem cell23_4378256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_4378256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378256 prefixEnd_4378256 := by exact prefixLift 4378256
  have htrace : WordTrace (prefixWord ++ tailWord_4378256) baseStart_4378256 baseEnd_4378256 := by
    simpa [prefixWord, tailWord_4378256, baseEnd_4378256] using wordTrace_append hprefix tailTrace_4378256
  have hstable : (prefixWord ++ tailWord_4378256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378256).length < 2 ^ (prefixWord ++ tailWord_4378256).sum := by decide
  have hdescent : baseEnd_4378256 < baseStart_4378256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378270 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_4378270 : Nat := 118140960795 + 4378270 * 2 ^ 59
def prefixEnd_4378270 : Nat := 4983230072969 + 3 ^ 40 * 4378270 * 2
def baseEnd_4378270 : Nat := 2248156945160690232189709

theorem tailTrace_4378270 : CollatzResearch.WordTrace tailWord_4378270 prefixEnd_4378270 2248156945160690232189709 := by
  unfold tailWord_4378270
  simp only [CollatzResearch.WordTrace]
  refine ⟨19961078231035376728721533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106459083898855342553181509 19961078231035376728721533)
  ·
    refine ⟨7485404336638266273270575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19961078231035376728721533 7485404336638266273270575)
    ·
      refine ⟨11228106504957399409905863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7485404336638266273270575 11228106504957399409905863)
      ·
        refine ⟨16842159757436099114858795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11228106504957399409905863 16842159757436099114858795)
        ·
          refine ⟨25263239636154148672288193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16842159757436099114858795 25263239636154148672288193)
          ·
            refine ⟨18947429727115611504216145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25263239636154148672288193 18947429727115611504216145)
            ·
              refine ⟨14210572295336708628162109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18947429727115611504216145 14210572295336708628162109)
              ·
                refine ⟨5328964610751265735560791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14210572295336708628162109 5328964610751265735560791)
                ·
                  refine ⟨7993446916126898603341187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5328964610751265735560791 7993446916126898603341187)
                  ·
                    refine ⟨11990170374190347905011781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7993446916126898603341187 11990170374190347905011781)
                    ·
                      refine ⟨2248156945160690232189709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11990170374190347905011781 2248156945160690232189709)
                      ·
                        rfl

theorem cell23_4378270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_4378270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378270 prefixEnd_4378270 := by exact prefixLift 4378270
  have htrace : WordTrace (prefixWord ++ tailWord_4378270) baseStart_4378270 baseEnd_4378270 := by
    simpa [prefixWord, tailWord_4378270, baseEnd_4378270] using wordTrace_append hprefix tailTrace_4378270
  have hstable : (prefixWord ++ tailWord_4378270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378270).length < 2 ^ (prefixWord ++ tailWord_4378270).sum := by decide
  have hdescent : baseEnd_4378270 < baseStart_4378270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378273 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4378273 : Nat := 118140960795 + 4378273 * 2 ^ 59
def prefixEnd_4378273 : Nat := 4983230072969 + 3 ^ 40 * 4378273 * 2
def baseEnd_4378273 : Nat := 2248158485602653720452195

theorem tailTrace_4378273 : CollatzResearch.WordTrace tailWord_4378273 prefixEnd_4378273 2248158485602653720452195 := by
  unfold tailWord_4378273
  simp only [CollatzResearch.WordTrace]
  refine ⟨159688735267272145342131473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106459156844848096894754315 159688735267272145342131473)
  ·
    refine ⟨119766551450454109006598605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159688735267272145342131473 119766551450454109006598605)
    ·
      refine ⟨44912456793920290877474477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119766551450454109006598605 44912456793920290877474477)
      ·
        refine ⟨16842171297720109079052929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44912456793920290877474477 16842171297720109079052929)
        ·
          refine ⟨12631628473290081809289697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16842171297720109079052929 12631628473290081809289697)
          ·
            refine ⟨9473721354967561356967273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12631628473290081809289697 9473721354967561356967273)
            ·
              refine ⟨7105291016225671017725455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9473721354967561356967273 7105291016225671017725455)
              ·
                refine ⟨10657936524338506526588183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7105291016225671017725455 10657936524338506526588183)
                ·
                  refine ⟨15986904786507759789882275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10657936524338506526588183 15986904786507759789882275)
                  ·
                    refine ⟨23980357179761639684823413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15986904786507759789882275 23980357179761639684823413)
                    ·
                      refine ⟨2248158485602653720452195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23980357179761639684823413 2248158485602653720452195)
                      ·
                        rfl

theorem cell23_4378273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4378273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378273 prefixEnd_4378273 := by exact prefixLift 4378273
  have htrace : WordTrace (prefixWord ++ tailWord_4378273) baseStart_4378273 baseEnd_4378273 := by
    simpa [prefixWord, tailWord_4378273, baseEnd_4378273] using wordTrace_append hprefix tailTrace_4378273
  have hstable : (prefixWord ++ tailWord_4378273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378273).length < 2 ^ (prefixWord ++ tailWord_4378273).sum := by decide
  have hdescent : baseEnd_4378273 < baseStart_4378273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378276 : List Nat := [2, 3, 1, 2, 2, 4, 9]
def baseStart_4378276 : Nat := 118140960795 + 4378276 * 2 ^ 59
def prefixEnd_4378276 : Nat := 4983230072969 + 3 ^ 40 * 4378276 * 2
def baseEnd_4378276 : Nat := 27755062049933545786601

theorem tailTrace_4378276 : CollatzResearch.WordTrace tailWord_4378276 prefixEnd_4378276 27755062049933545786601 := by
  unfold tailWord_4378276
  simp only [CollatzResearch.WordTrace]
  refine ⟨79844422343130638427245341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106459229790840851236327121 79844422343130638427245341)
  ·
    refine ⟨29941658378673989410217003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79844422343130638427245341 29941658378673989410217003)
    ·
      refine ⟨44912487568010984115325505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29941658378673989410217003 44912487568010984115325505)
      ·
        refine ⟨33684365676008238086494129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44912487568010984115325505 33684365676008238086494129)
        ·
          refine ⟨25263274257006178564870597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33684365676008238086494129 25263274257006178564870597)
          ·
            refine ⟨4736863923188658480913237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25263274257006178564870597 4736863923188658480913237)
            ·
              refine ⟨27755062049933545786601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4736863923188658480913237 27755062049933545786601)
              ·
                rfl

theorem cell23_4378276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 9].length) (baseStart_4378276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378276 prefixEnd_4378276 := by exact prefixLift 4378276
  have htrace : WordTrace (prefixWord ++ tailWord_4378276) baseStart_4378276 baseEnd_4378276 := by
    simpa [prefixWord, tailWord_4378276, baseEnd_4378276] using wordTrace_append hprefix tailTrace_4378276
  have hstable : (prefixWord ++ tailWord_4378276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378276).length < 2 ^ (prefixWord ++ tailWord_4378276).sum := by decide
  have hdescent : baseEnd_4378276 < baseStart_4378276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378293 : List Nat := [1, 3, 3, 3, 2, 1, 2, 8]
def baseStart_4378293 : Nat := 118140960795 + 4378293 * 2 ^ 59
def prefixEnd_4378293 : Nat := 4983230072969 + 3 ^ 40 * 4378293 * 2
def baseEnd_4378293 : Nat := 83265509452434949711189

theorem tailTrace_4378293 : CollatzResearch.WordTrace tailWord_4378293 prefixEnd_4378293 83265509452434949711189 := by
  unfold tailWord_4378293
  simp only [CollatzResearch.WordTrace]
  refine ⟨159689464727199688757859533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106459643151466459171906355 159689464727199688757859533)
  ·
    refine ⟨59883549272699883284197325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159689464727199688757859533 59883549272699883284197325)
    ·
      refine ⟨22456330977262456231573997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59883549272699883284197325 22456330977262456231573997)
      ·
        refine ⟨8421124116473421086840249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22456330977262456231573997 8421124116473421086840249)
        ·
          refine ⟨6315843087355065815130187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8421124116473421086840249 6315843087355065815130187)
          ·
            refine ⟨9473764631032598722695281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6315843087355065815130187 9473764631032598722695281)
            ·
              refine ⟨7105323473274449042021461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9473764631032598722695281 7105323473274449042021461)
              ·
                refine ⟨83265509452434949711189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7105323473274449042021461 83265509452434949711189)
                ·
                  rfl

theorem cell23_4378293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 8].length) (baseStart_4378293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378293 prefixEnd_4378293 := by exact prefixLift 4378293
  have htrace : WordTrace (prefixWord ++ tailWord_4378293) baseStart_4378293 baseEnd_4378293 := by
    simpa [prefixWord, tailWord_4378293, baseEnd_4378293] using wordTrace_append hprefix tailTrace_4378293
  have hstable : (prefixWord ++ tailWord_4378293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378293).length < 2 ^ (prefixWord ++ tailWord_4378293).sum := by decide
  have hdescent : baseEnd_4378293 < baseStart_4378293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378310 : List Nat := [6, 1, 2, 1, 1, 1, 2, 9]
def baseStart_4378310 : Nat := 118140960795 + 4378310 * 2 ^ 59
def prefixEnd_4378310 : Nat := 4983230072969 + 3 ^ 40 * 4378310 * 2
def baseEnd_4378310 : Nat := 83265832755069262062575

theorem tailTrace_4378310 : CollatzResearch.WordTrace tailWord_4378310 prefixEnd_4378310 83265832755069262062575 := by
  unfold tailWord_4378310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990315149004315645663387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106460056512092067107485589 4990315149004315645663387)
  ·
    refine ⟨7485472723506473468495081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4990315149004315645663387 7485472723506473468495081)
    ·
      refine ⟨5614104542629855101371311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7485472723506473468495081 5614104542629855101371311)
      ·
        refine ⟨8421156813944782652056967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5614104542629855101371311 8421156813944782652056967)
        ·
          refine ⟨12631735220917173978085451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8421156813944782652056967 12631735220917173978085451)
          ·
            refine ⟨18947602831375760967128177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12631735220917173978085451 18947602831375760967128177)
            ·
              refine ⟨14210702123531820725346133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18947602831375760967128177 14210702123531820725346133)
              ·
                refine ⟨83265832755069262062575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14210702123531820725346133 83265832755069262062575)
                ·
                  rfl

theorem cell23_4378310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_4378310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378310 prefixEnd_4378310 := by exact prefixLift 4378310
  have htrace : WordTrace (prefixWord ++ tailWord_4378310) baseStart_4378310 baseEnd_4378310 := by
    simpa [prefixWord, tailWord_4378310, baseEnd_4378310] using wordTrace_append hprefix tailTrace_4378310
  have hstable : (prefixWord ++ tailWord_4378310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378310).length < 2 ^ (prefixWord ++ tailWord_4378310).sum := by decide
  have hdescent : baseEnd_4378310 < baseStart_4378310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378337 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_4378337 : Nat := 118140960795 + 4378337 * 2 ^ 59
def prefixEnd_4378337 : Nat := 4983230072969 + 3 ^ 40 * 4378337 * 2
def baseEnd_4378337 : Nat := 2248191348364541470051901

theorem tailTrace_4378337 : CollatzResearch.WordTrace tailWord_4378337 prefixEnd_4378337 2248191348364541470051901 := by
  unfold tailWord_4378337
  simp only [CollatzResearch.WordTrace]
  refine ⟨159691069539040284272461265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106460713026026856181640843 159691069539040284272461265)
  ·
    refine ⟨119768302154280213204345949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159691069539040284272461265 119768302154280213204345949)
    ·
      refine ⟨44913113307855079951629731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119768302154280213204345949 44913113307855079951629731)
      ·
        refine ⟨67369669961782619927444597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44913113307855079951629731 67369669961782619927444597)
        ·
          refine ⟨6315906558917120618197931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67369669961782619927444597 6315906558917120618197931)
          ·
            refine ⟨9473859838375680927296897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6315906558917120618197931 9473859838375680927296897)
            ·
              refine ⟨7105394878781760695472673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9473859838375680927296897 7105394878781760695472673)
              ·
                refine ⟨5329046159086320521604505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7105394878781760695472673 5329046159086320521604505)
                ·
                  refine ⟨3996784619314740391203379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5329046159086320521604505 3996784619314740391203379)
                  ·
                    refine ⟨5995176928972110586805069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3996784619314740391203379 5995176928972110586805069)
                    ·
                      refine ⟨2248191348364541470051901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995176928972110586805069 2248191348364541470051901)
                      ·
                        rfl

theorem cell23_4378337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_4378337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378337 prefixEnd_4378337 := by exact prefixLift 4378337
  have htrace : WordTrace (prefixWord ++ tailWord_4378337) baseStart_4378337 baseEnd_4378337 := by
    simpa [prefixWord, tailWord_4378337, baseEnd_4378337] using wordTrace_append hprefix tailTrace_4378337
  have hstable : (prefixWord ++ tailWord_4378337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378337).length < 2 ^ (prefixWord ++ tailWord_4378337).sum := by decide
  have hdescent : baseEnd_4378337 < baseStart_4378337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378346 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_4378346 : Nat := 118140960795 + 4378346 * 2 ^ 59
def prefixEnd_4378346 : Nat := 4983230072969 + 3 ^ 40 * 4378346 * 2
def baseEnd_4378346 : Nat := 2248195969690431934839359

theorem tailTrace_4378346 : CollatzResearch.WordTrace tailWord_4378346 prefixEnd_4378346 2248195969690431934839359 := by
  unfold tailWord_4378346
  simp only [CollatzResearch.WordTrace]
  refine ⟨39922849449001919702384723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106460931864005119206359261 39922849449001919702384723)
  ·
    refine ⟨59884274173502879553577085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39922849449001919702384723 59884274173502879553577085)
    ·
      refine ⟨22456602815063579832591407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59884274173502879553577085 22456602815063579832591407)
      ·
        refine ⟨33684904222595369748887111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22456602815063579832591407 33684904222595369748887111)
        ·
          refine ⟨50527356333893054623330667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33684904222595369748887111 50527356333893054623330667)
          ·
            refine ⟨75791034500839581934996001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50527356333893054623330667 75791034500839581934996001)
            ·
              refine ⟨56843275875629686451247001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75791034500839581934996001 56843275875629686451247001)
              ·
                refine ⟨42632456906722264838435251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56843275875629686451247001 42632456906722264838435251)
                ·
                  refine ⟨63948685360083397257652877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42632456906722264838435251 63948685360083397257652877)
                  ·
                    refine ⟨23980757010031273971619829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63948685360083397257652877 23980757010031273971619829)
                    ·
                      refine ⟨2248195969690431934839359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23980757010031273971619829 2248195969690431934839359)
                      ·
                        rfl

theorem cell23_4378346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_4378346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378346 prefixEnd_4378346 := by exact prefixLift 4378346
  have htrace : WordTrace (prefixWord ++ tailWord_4378346) baseStart_4378346 baseEnd_4378346 := by
    simpa [prefixWord, tailWord_4378346, baseEnd_4378346] using wordTrace_append hprefix tailTrace_4378346
  have hstable : (prefixWord ++ tailWord_4378346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378346).length < 2 ^ (prefixWord ++ tailWord_4378346).sum := by decide
  have hdescent : baseEnd_4378346 < baseStart_4378346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378388 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4378388 : Nat := 118140960795 + 4378388 * 2 ^ 59
def prefixEnd_4378388 : Nat := 4983230072969 + 3 ^ 40 * 4378388 * 2
def baseEnd_4378388 : Nat := 2248217535877920770514167

theorem tailTrace_4378388 : CollatzResearch.WordTrace tailWord_4378388 prefixEnd_4378388 2248217535877920770514167 := by
  unfold tailWord_4378388
  simp only [CollatzResearch.WordTrace]
  refine ⟨79846464830927759991283909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106461953107903679988378545 79846464830927759991283909)
  ·
    refine ⟨14971212155798954998365733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79846464830927759991283909 14971212155798954998365733)
    ·
      refine ⟨2807102279212304062193575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14971212155798954998365733 2807102279212304062193575)
      ·
        refine ⟨4210653418818456093290363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807102279212304062193575 4210653418818456093290363)
        ·
          refine ⟨6315980128227684139935545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210653418818456093290363 6315980128227684139935545)
          ·
            refine ⟨4736985096170763104951659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6315980128227684139935545 4736985096170763104951659)
            ·
              refine ⟨7105477644256144657427489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736985096170763104951659 7105477644256144657427489)
              ·
                refine ⟨5329108233192108493070617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7105477644256144657427489 5329108233192108493070617)
                ·
                  refine ⟨3996831174894081369802963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5329108233192108493070617 3996831174894081369802963)
                  ·
                    refine ⟨5995246762341122054704445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3996831174894081369802963 5995246762341122054704445)
                    ·
                      refine ⟨2248217535877920770514167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995246762341122054704445 2248217535877920770514167)
                      ·
                        rfl

theorem cell23_4378388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4378388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378388 prefixEnd_4378388 := by exact prefixLift 4378388
  have htrace : WordTrace (prefixWord ++ tailWord_4378388) baseStart_4378388 baseEnd_4378388 := by
    simpa [prefixWord, tailWord_4378388, baseEnd_4378388] using wordTrace_append hprefix tailTrace_4378388
  have hstable : (prefixWord ++ tailWord_4378388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378388).length < 2 ^ (prefixWord ++ tailWord_4378388).sum := by decide
  have hdescent : baseEnd_4378388 < baseStart_4378388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378394 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2]
def baseStart_4378394 : Nat := 118140960795 + 4378394 * 2 ^ 59
def prefixEnd_4378394 : Nat := 4983230072969 + 3 ^ 40 * 4378394 * 2
def baseEnd_4378394 : Nat := 2248220616761847747039139

theorem tailTrace_4378394 : CollatzResearch.WordTrace tailWord_4378394 prefixEnd_4378394 2248220616761847747039139 := by
  unfold tailWord_4378394
  simp only [CollatzResearch.WordTrace]
  refine ⟨39923287124958445751821559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106462098999889188671524157 39923287124958445751821559)
  ·
    refine ⟨59884930687437668627732339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39923287124958445751821559 59884930687437668627732339)
    ·
      refine ⟨89827396031156502941598509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59884930687437668627732339 89827396031156502941598509)
      ·
        refine ⟨33685273511683688603099441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89827396031156502941598509 33685273511683688603099441)
        ·
          refine ⟨25263955133762766452324581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33685273511683688603099441 25263955133762766452324581)
          ·
            refine ⟨4736991587580518709810859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25263955133762766452324581 4736991587580518709810859)
            ·
              refine ⟨7105487381370778064716289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4736991587580518709810859 7105487381370778064716289)
              ·
                refine ⟨5329115536028083548537217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7105487381370778064716289 5329115536028083548537217)
                ·
                  refine ⟨3996836652021062661402913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5329115536028083548537217 3996836652021062661402913)
                  ·
                    refine ⟨2997627489015796996052185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3996836652021062661402913 2997627489015796996052185)
                    ·
                      refine ⟨2248220616761847747039139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997627489015796996052185 2248220616761847747039139)
                      ·
                        rfl

theorem cell23_4378394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_4378394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378394 prefixEnd_4378394 := by exact prefixLift 4378394
  have htrace : WordTrace (prefixWord ++ tailWord_4378394) baseStart_4378394 baseEnd_4378394 := by
    simpa [prefixWord, tailWord_4378394, baseEnd_4378394] using wordTrace_append hprefix tailTrace_4378394
  have hstable : (prefixWord ++ tailWord_4378394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378394).length < 2 ^ (prefixWord ++ tailWord_4378394).sum := by decide
  have hdescent : baseEnd_4378394 < baseStart_4378394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378403 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 7, 2]
def baseStart_4378403 : Nat := 118140960795 + 4378403 * 2 ^ 59
def prefixEnd_4378403 : Nat := 4983230072969 + 3 ^ 40 * 4378403 * 2
def baseEnd_4378403 : Nat := 2248225238087738211826597

theorem tailTrace_4378403 : CollatzResearch.WordTrace tailWord_4378403 prefixEnd_4378403 2248225238087738211826597 := by
  unfold tailWord_4378403
  simp only [CollatzResearch.WordTrace]
  refine ⟨159693476756801177544363863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106462317837867451696242575 159693476756801177544363863)
  ·
    refine ⟨239540215135201766316545795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159693476756801177544363863 239540215135201766316545795)
    ·
      refine ⟨359310322702802649474818693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239540215135201766316545795 359310322702802649474818693)
      ·
        refine ⟨67370685506775496776528505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 359310322702802649474818693 67370685506775496776528505)
        ·
          refine ⟨50528014130081622582396379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67370685506775496776528505 50528014130081622582396379)
          ·
            refine ⟨75792021195122433873594569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50528014130081622582396379 75792021195122433873594569)
            ·
              refine ⟨56844015896341825405195927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75792021195122433873594569 56844015896341825405195927)
              ·
                refine ⟨85266023844512738107793891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56844015896341825405195927 85266023844512738107793891)
                ·
                  refine ⟨127899035766769107161690837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85266023844512738107793891 127899035766769107161690837)
                  ·
                    refine ⟨2997633650783650949102129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127899035766769107161690837 2997633650783650949102129)
                    ·
                      refine ⟨2248225238087738211826597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997633650783650949102129 2248225238087738211826597)
                      ·
                        rfl

theorem cell23_4378403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_4378403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378403 prefixEnd_4378403 := by exact prefixLift 4378403
  have htrace : WordTrace (prefixWord ++ tailWord_4378403) baseStart_4378403 baseEnd_4378403 := by
    simpa [prefixWord, tailWord_4378403, baseEnd_4378403] using wordTrace_append hprefix tailTrace_4378403
  have hstable : (prefixWord ++ tailWord_4378403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378403).length < 2 ^ (prefixWord ++ tailWord_4378403).sum := by decide
  have hdescent : baseEnd_4378403 < baseStart_4378403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378450 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_4378450 : Nat := 118140960795 + 4378450 * 2 ^ 59
def prefixEnd_4378450 : Nat := 4983230072969 + 3 ^ 40 * 4378450 * 2
def baseEnd_4378450 : Nat := 2248249371678499527938881

theorem tailTrace_4378450 : CollatzResearch.WordTrace tailWord_4378450 prefixEnd_4378450 2248249371678499527938881 := by
  unfold tailWord_4378450
  simp only [CollatzResearch.WordTrace]
  refine ⟨39923797746907726142831201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106463460658420603047549869 39923797746907726142831201)
  ·
    refine ⟨29942848310180794607123401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39923797746907726142831201 29942848310180794607123401)
    ·
      refine ⟨22457136232635595955342551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29942848310180794607123401 22457136232635595955342551)
      ·
        refine ⟨33685704348953393933013827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22457136232635595955342551 33685704348953393933013827)
        ·
          refine ⟨50528556523430090899520741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33685704348953393933013827 50528556523430090899520741)
          ·
            refine ⟨9474104348143142043660139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50528556523430090899520741 9474104348143142043660139)
            ·
              refine ⟨14211156522214713065490209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9474104348143142043660139 14211156522214713065490209)
              ·
                refine ⟨10658367391661034799117657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14211156522214713065490209 10658367391661034799117657)
                ·
                  refine ⟨7993775543745776099338243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10658367391661034799117657 7993775543745776099338243)
                  ·
                    refine ⟨11990663315618664149007365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7993775543745776099338243 11990663315618664149007365)
                    ·
                      refine ⟨2248249371678499527938881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11990663315618664149007365 2248249371678499527938881)
                      ·
                        rfl

theorem cell23_4378450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_4378450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378450 prefixEnd_4378450 := by exact prefixLift 4378450
  have htrace : WordTrace (prefixWord ++ tailWord_4378450) baseStart_4378450 baseEnd_4378450 := by
    simpa [prefixWord, tailWord_4378450, baseEnd_4378450] using wordTrace_append hprefix tailTrace_4378450
  have hstable : (prefixWord ++ tailWord_4378450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378450).length < 2 ^ (prefixWord ++ tailWord_4378450).sum := by decide
  have hdescent : baseEnd_4378450 < baseStart_4378450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378557 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_4378557 : Nat := 118140960795 + 4378557 * 2 ^ 59
def prefixEnd_4378557 : Nat := 4983230072969 + 3 ^ 40 * 4378557 * 2
def baseEnd_4378557 : Nat := 2248304314108530609300889

theorem tailTrace_4378557 : CollatzResearch.WordTrace tailWord_4378557 prefixEnd_4378557 2248304314108530609300889 := by
  unfold tailWord_4378557
  simp only [CollatzResearch.WordTrace]
  refine ⟨159699093598243261845469925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106466062398828841230313283 159699093598243261845469925)
  ·
    refine ⟨29943580049670611596025611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159699093598243261845469925 29943580049670611596025611)
    ·
      refine ⟨44915370074505917394038417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29943580049670611596025611 44915370074505917394038417)
      ·
        refine ⟨33686527555879438045528813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44915370074505917394038417 33686527555879438045528813)
        ·
          refine ⟨12632447833454789267073305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33686527555879438045528813 12632447833454789267073305)
          ·
            refine ⟨9474335875091091950304979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12632447833454789267073305 9474335875091091950304979)
            ·
              refine ⟨14211503812636637925457469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9474335875091091950304979 14211503812636637925457469)
              ·
                refine ⟨5329313929738739222046551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14211503812636637925457469 5329313929738739222046551)
                ·
                  refine ⟨7993970894608108833069827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5329313929738739222046551 7993970894608108833069827)
                  ·
                    refine ⟨11990956341912163249604741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7993970894608108833069827 11990956341912163249604741)
                    ·
                      refine ⟨2248304314108530609300889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11990956341912163249604741 2248304314108530609300889)
                      ·
                        rfl

theorem cell23_4378557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_4378557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378557 prefixEnd_4378557 := by exact prefixLift 4378557
  have htrace : WordTrace (prefixWord ++ tailWord_4378557) baseStart_4378557 baseEnd_4378557 := by
    simpa [prefixWord, tailWord_4378557, baseEnd_4378557] using wordTrace_append hprefix tailTrace_4378557
  have hstable : (prefixWord ++ tailWord_4378557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378557).length < 2 ^ (prefixWord ++ tailWord_4378557).sum := by decide
  have hdescent : baseEnd_4378557 < baseStart_4378557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378574 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_4378574 : Nat := 118140960795 + 4378574 * 2 ^ 59
def prefixEnd_4378574 : Nat := 4983230072969 + 3 ^ 40 * 4378574 * 2
def baseEnd_4378574 : Nat := 2248313043279657042788311

theorem tailTrace_4378574 : CollatzResearch.WordTrace tailWord_4378574 prefixEnd_4378574 2248313043279657042788311 := by
  unfold tailWord_4378574
  simp only [CollatzResearch.WordTrace]
  refine ⟨19962464204897709218604847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106466475759454449165892517 19962464204897709218604847)
  ·
    refine ⟨29943696307346563827907271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19962464204897709218604847 29943696307346563827907271)
    ·
      refine ⟨44915544461019845741860907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29943696307346563827907271 44915544461019845741860907)
      ·
        refine ⟨67373316691529768612791361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44915544461019845741860907 67373316691529768612791361)
        ·
          refine ⟨50529987518647326459593521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67373316691529768612791361 50529987518647326459593521)
          ·
            refine ⟨37897490638985494844695141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50529987518647326459593521 37897490638985494844695141)
            ·
              refine ⟨7105779494809780283380339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37897490638985494844695141 7105779494809780283380339)
              ·
                refine ⟨10658669242214670425070509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7105779494809780283380339 10658669242214670425070509)
                ·
                  refine ⟨3997000965830501409401441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10658669242214670425070509 3997000965830501409401441)
                  ·
                    refine ⟨2997750724372876057051081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3997000965830501409401441 2997750724372876057051081)
                    ·
                      refine ⟨2248313043279657042788311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997750724372876057051081 2248313043279657042788311)
                      ·
                        rfl

theorem cell23_4378574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_4378574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378574 prefixEnd_4378574 := by exact prefixLift 4378574
  have htrace : WordTrace (prefixWord ++ tailWord_4378574) baseStart_4378574 baseEnd_4378574 := by
    simpa [prefixWord, tailWord_4378574, baseEnd_4378574] using wordTrace_append hprefix tailTrace_4378574
  have hstable : (prefixWord ++ tailWord_4378574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378574).length < 2 ^ (prefixWord ++ tailWord_4378574).sum := by decide
  have hdescent : baseEnd_4378574 < baseStart_4378574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378593 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_4378593 : Nat := 118140960795 + 4378593 * 2 ^ 59
def prefixEnd_4378593 : Nat := 4983230072969 + 3 ^ 40 * 4378593 * 2
def baseEnd_4378593 : Nat := 749440933137364156150241

theorem tailTrace_4378593 : CollatzResearch.WordTrace tailWord_4378593 prefixEnd_4378593 749440933137364156150241 := by
  unfold tailWord_4378593
  simp only [CollatzResearch.WordTrace]
  refine ⟨159700406626112839993780433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106466937750741893329186955 159700406626112839993780433)
  ·
    refine ⟨119775304969584629995335325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159700406626112839993780433 119775304969584629995335325)
    ·
      refine ⟨44915739363594236248250747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119775304969584629995335325 44915739363594236248250747)
      ·
        refine ⟨67373609045391354372376121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44915739363594236248250747 67373609045391354372376121)
        ·
          refine ⟨50530206784043515779282091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67373609045391354372376121 50530206784043515779282091)
          ·
            refine ⟨75795310176065273668923137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50530206784043515779282091 75795310176065273668923137)
            ·
              refine ⟨56846482632048955251692353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75795310176065273668923137 56846482632048955251692353)
              ·
                refine ⟨42634861974036716438769265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56846482632048955251692353 42634861974036716438769265)
                ·
                  refine ⟨31976146480527537329076949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42634861974036716438769265 31976146480527537329076949)
                  ·
                    refine ⟨749440933137364156150241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31976146480527537329076949 749440933137364156150241)
                    ·
                      rfl

theorem cell23_4378593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_4378593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378593 prefixEnd_4378593 := by exact prefixLift 4378593
  have htrace : WordTrace (prefixWord ++ tailWord_4378593) baseStart_4378593 baseEnd_4378593 := by
    simpa [prefixWord, tailWord_4378593, baseEnd_4378593] using wordTrace_append hprefix tailTrace_4378593
  have hstable : (prefixWord ++ tailWord_4378593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378593).length < 2 ^ (prefixWord ++ tailWord_4378593).sum := by decide
  have hdescent : baseEnd_4378593 < baseStart_4378593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378623 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 4, 6]
def baseStart_4378623 : Nat := 118140960795 + 4378623 * 2 ^ 59
def prefixEnd_4378623 : Nat := 4983230072969 + 3 ^ 40 * 4378623 * 2
def baseEnd_4378623 : Nat := 749446067943909117025195

theorem tailTrace_4378623 : CollatzResearch.WordTrace tailWord_4378623 prefixEnd_4378623 749446067943909117025195 := by
  unfold tailWord_4378623
  simp only [CollatzResearch.WordTrace]
  refine ⟨159701500816004155117372523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106467667210669436744915015 159701500816004155117372523)
  ·
    refine ⟨239552251224006232676058785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159701500816004155117372523 239552251224006232676058785)
    ·
      refine ⟨179664188418004674507044089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239552251224006232676058785 179664188418004674507044089)
      ·
        refine ⟨134748141313503505880283067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179664188418004674507044089 134748141313503505880283067)
        ·
          refine ⟨202122211970255258820424601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134748141313503505880283067 202122211970255258820424601)
          ·
            refine ⟨151591658977691444115318451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202122211970255258820424601 151591658977691444115318451)
            ·
              refine ⟨227387488466537166172977677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151591658977691444115318451 227387488466537166172977677)
              ·
                refine ⟨85270308174951437314866629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227387488466537166172977677 85270308174951437314866629)
                ·
                  refine ⟨15988182782803394496537493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85270308174951437314866629 15988182782803394496537493)
                  ·
                    refine ⟨749446067943909117025195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15988182782803394496537493 749446067943909117025195)
                    ·
                      rfl

theorem cell23_4378623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_4378623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378623 prefixEnd_4378623 := by exact prefixLift 4378623
  have htrace : WordTrace (prefixWord ++ tailWord_4378623) baseStart_4378623 baseEnd_4378623 := by
    simpa [prefixWord, tailWord_4378623, baseEnd_4378623] using wordTrace_append hprefix tailTrace_4378623
  have hstable : (prefixWord ++ tailWord_4378623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378623).length < 2 ^ (prefixWord ++ tailWord_4378623).sum := by decide
  have hdescent : baseEnd_4378623 < baseStart_4378623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378650 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4378650 : Nat := 118140960795 + 4378650 * 2 ^ 59
def prefixEnd_4378650 : Nat := 4983230072969 + 3 ^ 40 * 4378650 * 2
def baseEnd_4378650 : Nat := 2248352067809398745437961

theorem tailTrace_4378650 : CollatzResearch.WordTrace tailWord_4378650 prefixEnd_4378650 2248352067809398745437961 := by
  unfold tailWord_4378650
  simp only [CollatzResearch.WordTrace]
  refine ⟨39925621396726584682151351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106468323724604225819070269 39925621396726584682151351)
  ·
    refine ⟨59888432095089877023227027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39925621396726584682151351 59888432095089877023227027)
    ·
      refine ⟨89832648142634815534840541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59888432095089877023227027 89832648142634815534840541)
      ·
        refine ⟨33687243053488055825565203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89832648142634815534840541 33687243053488055825565203)
        ·
          refine ⟨50530864580232083738347805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33687243053488055825565203 50530864580232083738347805)
          ·
            refine ⟨18949074217587031401880427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50530864580232083738347805 18949074217587031401880427)
            ·
              refine ⟨28423611326380547102820641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18949074217587031401880427 28423611326380547102820641)
              ·
                refine ⟨21317708494785410327115481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28423611326380547102820641 21317708494785410327115481)
                ·
                  refine ⟨15988281371089057745336611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21317708494785410327115481 15988281371089057745336611)
                  ·
                    refine ⟨23982422056633586618004917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15988281371089057745336611 23982422056633586618004917)
                    ·
                      refine ⟨2248352067809398745437961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23982422056633586618004917 2248352067809398745437961)
                      ·
                        rfl

theorem cell23_4378650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4378650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378650 prefixEnd_4378650 := by exact prefixLift 4378650
  have htrace : WordTrace (prefixWord ++ tailWord_4378650) baseStart_4378650 baseEnd_4378650 := by
    simpa [prefixWord, tailWord_4378650, baseEnd_4378650] using wordTrace_append hprefix tailTrace_4378650
  have hstable : (prefixWord ++ tailWord_4378650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378650).length < 2 ^ (prefixWord ++ tailWord_4378650).sum := by decide
  have hdescent : baseEnd_4378650 < baseStart_4378650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378694 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4378694 : Nat := 118140960795 + 4378694 * 2 ^ 59
def prefixEnd_4378694 : Nat := 4983230072969 + 3 ^ 40 * 4378694 * 2
def baseEnd_4378694 : Nat := 2248374660958196573287759

theorem tailTrace_4378694 : CollatzResearch.WordTrace tailWord_4378694 prefixEnd_4378694 2248374660958196573287759 := by
  unfold tailWord_4378694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990752824960841695100223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106469393599164622828804757 4990752824960841695100223)
  ·
    refine ⟨7486129237441262542650335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4990752824960841695100223 7486129237441262542650335)
    ·
      refine ⟨11229193856161893813975503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7486129237441262542650335 11229193856161893813975503)
      ·
        refine ⟨16843790784242840720963255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11229193856161893813975503 16843790784242840720963255)
        ·
          refine ⟨25265686176364261081444883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16843790784242840720963255 25265686176364261081444883)
          ·
            refine ⟨37898529264546391622167325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25265686176364261081444883 37898529264546391622167325)
            ·
              refine ⟨14211948474204896858312747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37898529264546391622167325 14211948474204896858312747)
              ·
                refine ⟨21317922711307345287469121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14211948474204896858312747 21317922711307345287469121)
                ·
                  refine ⟨15988442033480508965601841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21317922711307345287469121 15988442033480508965601841)
                  ·
                    refine ⟨11991331525110381724201381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15988442033480508965601841 11991331525110381724201381)
                    ·
                      refine ⟨2248374660958196573287759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11991331525110381724201381 2248374660958196573287759)
                      ·
                        rfl

theorem cell23_4378694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4378694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378694 prefixEnd_4378694 := by exact prefixLift 4378694
  have htrace : WordTrace (prefixWord ++ tailWord_4378694) baseStart_4378694 baseEnd_4378694 := by
    simpa [prefixWord, tailWord_4378694, baseEnd_4378694] using wordTrace_append hprefix tailTrace_4378694
  have hstable : (prefixWord ++ tailWord_4378694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378694).length < 2 ^ (prefixWord ++ tailWord_4378694).sum := by decide
  have hdescent : baseEnd_4378694 < baseStart_4378694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378700 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_4378700 : Nat := 118140960795 + 4378700 * 2 ^ 59
def prefixEnd_4378700 : Nat := 4983230072969 + 3 ^ 40 * 4378700 * 2
def baseEnd_4378700 : Nat := 749459247280707849937577

theorem tailTrace_4378700 : CollatzResearch.WordTrace tailWord_4378700 prefixEnd_4378700 749459247280707849937577 := by
  unfold tailWord_4378700
  simp only [CollatzResearch.WordTrace]
  refine ⟨79852154618362598633962777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106469539491150131511950369 79852154618362598633962777)
  ·
    refine ⟨59889115963771948975472083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79852154618362598633962777 59889115963771948975472083)
    ·
      refine ⟨89833673945657923463208125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59889115963771948975472083 89833673945657923463208125)
      ·
        refine ⟨33687627729621721298703047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89833673945657923463208125 33687627729621721298703047)
        ·
          refine ⟨50531441594432581948054571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33687627729621721298703047 50531441594432581948054571)
          ·
            refine ⟨75797162391648872922081857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50531441594432581948054571 75797162391648872922081857)
            ·
              refine ⟨56847871793736654691561393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75797162391648872922081857 56847871793736654691561393)
              ·
                refine ⟨42635903845302491018671045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56847871793736654691561393 42635903845302491018671045)
                ·
                  refine ⟨7994231970994217066000821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42635903845302491018671045 7994231970994217066000821)
                  ·
                    refine ⟨749459247280707849937577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7994231970994217066000821 749459247280707849937577)
                    ·
                      rfl

theorem cell23_4378700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_4378700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378700 prefixEnd_4378700 := by exact prefixLift 4378700
  have htrace : WordTrace (prefixWord ++ tailWord_4378700) baseStart_4378700 baseEnd_4378700 := by
    simpa [prefixWord, tailWord_4378700, baseEnd_4378700] using wordTrace_append hprefix tailTrace_4378700
  have hstable : (prefixWord ++ tailWord_4378700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378700).length < 2 ^ (prefixWord ++ tailWord_4378700).sum := by decide
  have hdescent : baseEnd_4378700 < baseStart_4378700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378737 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 4, 4, 2]
def baseStart_4378737 : Nat := 118140960795 + 4378737 * 2 ^ 59
def prefixEnd_4378737 : Nat := 4983230072969 + 3 ^ 40 * 4378737 * 2
def baseEnd_4378737 : Nat := 2248396740626339905050061

theorem tailTrace_4378737 : CollatzResearch.WordTrace tailWord_4378737 prefixEnd_4378737 2248396740626339905050061 := by
  unfold tailWord_4378737
  simp only [CollatzResearch.WordTrace]
  refine ⟨159705658737591152587022465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106470439158394101724681643 159705658737591152587022465)
  ·
    refine ⟨119779244053193364440266849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159705658737591152587022465 119779244053193364440266849)
    ·
      refine ⟨89834433039895023330200137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119779244053193364440266849 89834433039895023330200137)
      ·
        refine ⟨67375824779921267497650103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89834433039895023330200137 67375824779921267497650103)
        ·
          refine ⟨101063737169881901246475155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67375824779921267497650103 101063737169881901246475155)
          ·
            refine ⟨151595605754822851869712733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101063737169881901246475155 151595605754822851869712733)
            ·
              refine ⟨56848352158058569451142275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151595605754822851869712733 56848352158058569451142275)
              ·
                refine ⟨85272528237087854176713413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56848352158058569451142275 85272528237087854176713413)
                ·
                  refine ⟨15988599044453972658133765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85272528237087854176713413 15988599044453972658133765)
                  ·
                    refine ⟨2997862320835119873400081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15988599044453972658133765 2997862320835119873400081)
                    ·
                      refine ⟨2248396740626339905050061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997862320835119873400081 2248396740626339905050061)
                      ·
                        rfl

theorem cell23_4378737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_4378737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378737 prefixEnd_4378737 := by exact prefixLift 4378737
  have htrace : WordTrace (prefixWord ++ tailWord_4378737) baseStart_4378737 baseEnd_4378737 := by
    simpa [prefixWord, tailWord_4378737, baseEnd_4378737] using wordTrace_append hprefix tailTrace_4378737
  have hstable : (prefixWord ++ tailWord_4378737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378737).length < 2 ^ (prefixWord ++ tailWord_4378737).sum := by decide
  have hdescent : baseEnd_4378737 < baseStart_4378737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378757 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_4378757 : Nat := 118140960795 + 4378757 * 2 ^ 59
def prefixEnd_4378757 : Nat := 4983230072969 + 3 ^ 40 * 4378757 * 2
def baseEnd_4378757 : Nat := 2248407010239429826799969

theorem tailTrace_4378757 : CollatzResearch.WordTrace tailWord_4378757 prefixEnd_4378757 2248407010239429826799969 := by
  unfold tailWord_4378757
  simp only [CollatzResearch.WordTrace]
  refine ⟨159706388197518696002750525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106470925465012464001833683 159706388197518696002750525)
  ·
    refine ⟨59889895574069511001031447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159706388197518696002750525 59889895574069511001031447)
    ·
      refine ⟨89834843361104266501547171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59889895574069511001031447 89834843361104266501547171)
      ·
        refine ⟨134752265041656399752320757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89834843361104266501547171 134752265041656399752320757)
        ·
          refine ⟨12633024847655287476780071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134752265041656399752320757 12633024847655287476780071)
          ·
            refine ⟨18949537271482931215170107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12633024847655287476780071 18949537271482931215170107)
            ·
              refine ⟨28424305907224396822755161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18949537271482931215170107 28424305907224396822755161)
              ·
                refine ⟨21318229430418297617066371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28424305907224396822755161 21318229430418297617066371)
                ·
                  refine ⟨31977344145627446425599557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21318229430418297617066371 31977344145627446425599557)
                  ·
                    refine ⟨5995752027305146204799917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31977344145627446425599557 5995752027305146204799917)
                    ·
                      refine ⟨2248407010239429826799969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995752027305146204799917 2248407010239429826799969)
                      ·
                        rfl

theorem cell23_4378757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_4378757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378757 prefixEnd_4378757 := by exact prefixLift 4378757
  have htrace : WordTrace (prefixWord ++ tailWord_4378757) baseStart_4378757 baseEnd_4378757 := by
    simpa [prefixWord, tailWord_4378757, baseEnd_4378757] using wordTrace_append hprefix tailTrace_4378757
  have hstable : (prefixWord ++ tailWord_4378757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378757).length < 2 ^ (prefixWord ++ tailWord_4378757).sum := by decide
  have hdescent : baseEnd_4378757 < baseStart_4378757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378781 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_4378781 : Nat := 118140960795 + 4378781 * 2 ^ 59
def prefixEnd_4378781 : Nat := 4983230072969 + 3 ^ 40 * 4378781 * 2
def baseEnd_4378781 : Nat := 749473111258379244299953

theorem tailTrace_4378781 : CollatzResearch.WordTrace tailWord_4378781 prefixEnd_4378781 749473111258379244299953 := by
  unfold tailWord_4378781
  simp only [CollatzResearch.WordTrace]
  refine ⟨159707263549431748101624197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106471509032954498734416131 159707263549431748101624197)
  ·
    refine ⟨29945111915518452769054537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159707263549431748101624197 29945111915518452769054537)
    ·
      refine ⟨22458833936638839576790903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29945111915518452769054537 22458833936638839576790903)
      ·
        refine ⟨33688250904958259365186355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22458833936638839576790903 33688250904958259365186355)
        ·
          refine ⟨50532376357437389047779533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33688250904958259365186355 50532376357437389047779533)
          ·
            refine ⟨18949641134039020892917325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50532376357437389047779533 18949641134039020892917325)
            ·
              refine ⟨7106115425264632834843997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18949641134039020892917325 7106115425264632834843997)
              ·
                refine ⟨2664793284474237313066499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7106115425264632834843997 2664793284474237313066499)
                ·
                  refine ⟨3997189926711355969599749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664793284474237313066499 3997189926711355969599749)
                  ·
                    refine ⟨749473111258379244299953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3997189926711355969599749 749473111258379244299953)
                    ·
                      rfl

theorem cell23_4378781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_4378781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378781 prefixEnd_4378781 := by exact prefixLift 4378781
  have htrace : WordTrace (prefixWord ++ tailWord_4378781) baseStart_4378781 baseEnd_4378781 := by
    simpa [prefixWord, tailWord_4378781, baseEnd_4378781] using wordTrace_append hprefix tailTrace_4378781
  have hstable : (prefixWord ++ tailWord_4378781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378781).length < 2 ^ (prefixWord ++ tailWord_4378781).sum := by decide
  have hdescent : baseEnd_4378781 < baseStart_4378781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378791 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4378791 : Nat := 118140960795 + 4378791 * 2 ^ 59
def prefixEnd_4378791 : Nat := 4983230072969 + 3 ^ 40 * 4378791 * 2
def baseEnd_4378791 : Nat := 2248424468581682693774813

theorem tailTrace_4378791 : CollatzResearch.WordTrace tailWord_4378791 prefixEnd_4378791 2248424468581682693774813 := by
  unfold tailWord_4378791
  simp only [CollatzResearch.WordTrace]
  refine ⟨159707628279395519809488227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106471752186263679872992151 159707628279395519809488227)
  ·
    refine ⟨239561442419093279714232341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159707628279395519809488227 239561442419093279714232341)
    ·
      refine ⟨11229442613394997486604641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 239561442419093279714232341 11229442613394997486604641)
      ·
        refine ⟨8422081960046248114953481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11229442613394997486604641 8422081960046248114953481)
        ·
          refine ⟨6316561470034686086215111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8422081960046248114953481 6316561470034686086215111)
          ·
            refine ⟨9474842205052029129322667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6316561470034686086215111 9474842205052029129322667)
            ·
              refine ⟨14212263307578043693984001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9474842205052029129322667 14212263307578043693984001)
              ·
                refine ⟨10659197480683532770488001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14212263307578043693984001 10659197480683532770488001)
                ·
                  refine ⟨7994398110512649577866001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10659197480683532770488001 7994398110512649577866001)
                  ·
                    refine ⟨5995798582884487183399501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7994398110512649577866001 5995798582884487183399501)
                    ·
                      refine ⟨2248424468581682693774813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995798582884487183399501 2248424468581682693774813)
                      ·
                        rfl

theorem cell23_4378791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4378791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378791 prefixEnd_4378791 := by exact prefixLift 4378791
  have htrace : WordTrace (prefixWord ++ tailWord_4378791) baseStart_4378791 baseEnd_4378791 := by
    simpa [prefixWord, tailWord_4378791, baseEnd_4378791] using wordTrace_append hprefix tailTrace_4378791
  have hstable : (prefixWord ++ tailWord_4378791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378791).length < 2 ^ (prefixWord ++ tailWord_4378791).sum := by decide
  have hdescent : baseEnd_4378791 < baseStart_4378791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378827 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 4]
def baseStart_4378827 : Nat := 118140960795 + 4378827 * 2 ^ 59
def prefixEnd_4378827 : Nat := 4983230072969 + 3 ^ 40 * 4378827 * 2
def baseEnd_4378827 : Nat := 2248442953885244552924647

theorem tailTrace_4378827 : CollatzResearch.WordTrace tailWord_4378827 prefixEnd_4378827 2248442953885244552924647 := by
  unfold tailWord_4378827
  simp only [CollatzResearch.WordTrace]
  refine ⟨159708941307265097957798735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106472627538176731971865823 159708941307265097957798735)
  ·
    refine ⟨239563411960897646936698103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159708941307265097957798735 239563411960897646936698103)
    ·
      refine ⟨359345117941346470405047155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239563411960897646936698103 359345117941346470405047155)
      ·
        refine ⟨539017676912019705607570733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359345117941346470405047155 539017676912019705607570733)
        ·
          refine ⟨202131628842007389602839025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539017676912019705607570733 202131628842007389602839025)
          ·
            refine ⟨151598721631505542202129269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202131628842007389602839025 151598721631505542202129269)
            ·
              refine ⟨14212380152953644581449619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151598721631505542202129269 14212380152953644581449619)
              ·
                refine ⟨21318570229430466872174429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14212380152953644581449619 21318570229430466872174429)
                ·
                  refine ⟨7994463836036425077065411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21318570229430466872174429 7994463836036425077065411)
                  ·
                    refine ⟨11991695754054637615598117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7994463836036425077065411 11991695754054637615598117)
                    ·
                      refine ⟨2248442953885244552924647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11991695754054637615598117 2248442953885244552924647)
                      ·
                        rfl

theorem cell23_4378827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 4].length) (baseStart_4378827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378827 prefixEnd_4378827 := by exact prefixLift 4378827
  have htrace : WordTrace (prefixWord ++ tailWord_4378827) baseStart_4378827 baseEnd_4378827 := by
    simpa [prefixWord, tailWord_4378827, baseEnd_4378827] using wordTrace_append hprefix tailTrace_4378827
  have hstable : (prefixWord ++ tailWord_4378827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378827).length < 2 ^ (prefixWord ++ tailWord_4378827).sum := by decide
  have hdescent : baseEnd_4378827 < baseStart_4378827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378855 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4378855 : Nat := 118140960795 + 4378855 * 2 ^ 59
def prefixEnd_4378855 : Nat := 4983230072969 + 3 ^ 40 * 4378855 * 2
def baseEnd_4378855 : Nat := 2248457331343570443374519

theorem tailTrace_4378855 : CollatzResearch.WordTrace tailWord_4378855 prefixEnd_4378855 2248457331343570443374519 := by
  unfold tailWord_4378855
  simp only [CollatzResearch.WordTrace]
  refine ⟨159709962551163658739818019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106473308367442439159878679 159709962551163658739818019)
  ·
    refine ⟨239564943826745488109727029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159709962551163658739818019 239564943826745488109727029)
    ·
      refine ⟨22459213483757389510286909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239564943826745488109727029 22459213483757389510286909)
      ·
        refine ⟨8422205056409021066357591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22459213483757389510286909 8422205056409021066357591)
        ·
          refine ⟨12633307584613531599536387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8422205056409021066357591 12633307584613531599536387)
          ·
            refine ⟨18949961376920297399304581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12633307584613531599536387 18949961376920297399304581)
            ·
              refine ⟨3553117758172555762369609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18949961376920297399304581 3553117758172555762369609)
              ·
                refine ⟨2664838318629416821777207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3553117758172555762369609 2664838318629416821777207)
                ·
                  refine ⟨3997257477944125232665811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2664838318629416821777207 3997257477944125232665811)
                  ·
                    refine ⟨5995886216916187848998717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3997257477944125232665811 5995886216916187848998717)
                    ·
                      refine ⟨2248457331343570443374519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995886216916187848998717 2248457331343570443374519)
                      ·
                        rfl

theorem cell23_4378855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4378855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378855 prefixEnd_4378855 := by exact prefixLift 4378855
  have htrace : WordTrace (prefixWord ++ tailWord_4378855) baseStart_4378855 baseEnd_4378855 := by
    simpa [prefixWord, tailWord_4378855, baseEnd_4378855] using wordTrace_append hprefix tailTrace_4378855
  have hstable : (prefixWord ++ tailWord_4378855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378855).length < 2 ^ (prefixWord ++ tailWord_4378855).sum := by decide
  have hdescent : baseEnd_4378855 < baseStart_4378855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378874 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_4378874 : Nat := 118140960795 + 4378874 * 2 ^ 59
def prefixEnd_4378874 : Nat := 4983230072969 + 3 ^ 40 * 4378874 * 2
def baseEnd_4378874 : Nat := 2248467087476005869036931

theorem tailTrace_4378874 : CollatzResearch.WordTrace tailWord_4378874 prefixEnd_4378874 2248467087476005869036931 := by
  unfold tailWord_4378874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39927663884523706246189919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106473770358729883323173117 39927663884523706246189919)
  ·
    refine ⟨59891495826785559369284879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39927663884523706246189919 59891495826785559369284879)
    ·
      refine ⟨89837243740178339053927319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59891495826785559369284879 89837243740178339053927319)
      ·
        refine ⟨134755865610267508580890979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89837243740178339053927319 134755865610267508580890979)
        ·
          refine ⟨202133798415401262871336469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134755865610267508580890979 202133798415401262871336469)
          ·
            refine ⟨9475021800721934197093897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 202133798415401262871336469 9475021800721934197093897)
            ·
              refine ⟨7106266350541450647820423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9475021800721934197093897 7106266350541450647820423)
              ·
                refine ⟨10659399525812175971730635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7106266350541450647820423 10659399525812175971730635)
                ·
                  refine ⟨15989099288718263957595953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10659399525812175971730635 15989099288718263957595953)
                  ·
                    refine ⟨11991824466538697968196965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15989099288718263957595953 11991824466538697968196965)
                    ·
                      refine ⟨2248467087476005869036931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11991824466538697968196965 2248467087476005869036931)
                      ·
                        rfl

theorem cell23_4378874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_4378874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378874 prefixEnd_4378874 := by exact prefixLift 4378874
  have htrace : WordTrace (prefixWord ++ tailWord_4378874) baseStart_4378874 baseEnd_4378874 := by
    simpa [prefixWord, tailWord_4378874, baseEnd_4378874] using wordTrace_append hprefix tailTrace_4378874
  have hstable : (prefixWord ++ tailWord_4378874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378874).length < 2 ^ (prefixWord ++ tailWord_4378874).sum := by decide
  have hdescent : baseEnd_4378874 < baseStart_4378874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378878 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_4378878 : Nat := 118140960795 + 4378878 * 2 ^ 59
def prefixEnd_4378878 : Nat := 4983230072969 + 3 ^ 40 * 4378878 * 2
def baseEnd_4378878 : Nat := 2248469141398623853386913

theorem tailTrace_4378878 : CollatzResearch.WordTrace tailWord_4378878 prefixEnd_4378878 2248469141398623853386913 := by
  unfold tailWord_4378878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963850178760041708488161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106473867620053555778603525 19963850178760041708488161)
  ·
    refine ⟨14972887634070031281366121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19963850178760041708488161 14972887634070031281366121)
    ·
      refine ⟨11229665725552523461024591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14972887634070031281366121 11229665725552523461024591)
      ·
        refine ⟨16844498588328785191536887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11229665725552523461024591 16844498588328785191536887)
        ·
          refine ⟨25266747882493177787305331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16844498588328785191536887 25266747882493177787305331)
          ·
            refine ⟨37900121823739766680957997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25266747882493177787305331 37900121823739766680957997)
            ·
              refine ⟨14212545683902412505359249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37900121823739766680957997 14212545683902412505359249)
              ·
                refine ⟨10659409262926809379019437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14212545683902412505359249 10659409262926809379019437)
                ·
                  refine ⟨3997278473597553517132289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10659409262926809379019437 3997278473597553517132289)
                  ·
                    refine ⟨2997958855198165137849217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3997278473597553517132289 2997958855198165137849217)
                    ·
                      refine ⟨2248469141398623853386913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997958855198165137849217 2248469141398623853386913)
                      ·
                        rfl

theorem cell23_4378878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_4378878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378878 prefixEnd_4378878 := by exact prefixLift 4378878
  have htrace : WordTrace (prefixWord ++ tailWord_4378878) baseStart_4378878 baseEnd_4378878 := by
    simpa [prefixWord, tailWord_4378878, baseEnd_4378878] using wordTrace_append hprefix tailTrace_4378878
  have hstable : (prefixWord ++ tailWord_4378878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378878).length < 2 ^ (prefixWord ++ tailWord_4378878).sum := by decide
  have hdescent : baseEnd_4378878 < baseStart_4378878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378894 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4378894 : Nat := 118140960795 + 4378894 * 2 ^ 59
def prefixEnd_4378894 : Nat := 4983230072969 + 3 ^ 40 * 4378894 * 2
def baseEnd_4378894 : Nat := 2248477357089095790786839

theorem tailTrace_4378894 : CollatzResearch.WordTrace tailWord_4378894 prefixEnd_4378894 2248477357089095790786839 := by
  unfold tailWord_4378894
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963923124752796050060967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106474256665348245600325157 19963923124752796050060967)
  ·
    refine ⟨29945884687129194075091451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19963923124752796050060967 29945884687129194075091451)
    ·
      refine ⟨44918827030693791112637177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29945884687129194075091451 44918827030693791112637177)
      ·
        refine ⟨33689120273020343334477883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44918827030693791112637177 33689120273020343334477883)
        ·
          refine ⟨50533680409530515001716825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33689120273020343334477883 50533680409530515001716825)
          ·
            refine ⟨37900260307147886251287619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50533680409530515001716825 37900260307147886251287619)
            ·
              refine ⟨56850390460721829376931429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37900260307147886251287619 56850390460721829376931429)
              ·
                refine ⟨10659448211385343008174643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56850390460721829376931429 10659448211385343008174643)
                ·
                  refine ⟨15989172317078014512261965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10659448211385343008174643 15989172317078014512261965)
                  ·
                    refine ⟨5995939618904255442098237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15989172317078014512261965 5995939618904255442098237)
                    ·
                      refine ⟨2248477357089095790786839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995939618904255442098237 2248477357089095790786839)
                      ·
                        rfl

theorem cell23_4378894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4378894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378894 prefixEnd_4378894 := by exact prefixLift 4378894
  have htrace : WordTrace (prefixWord ++ tailWord_4378894) baseStart_4378894 baseEnd_4378894 := by
    simpa [prefixWord, tailWord_4378894, baseEnd_4378894] using wordTrace_append hprefix tailTrace_4378894
  have hstable : (prefixWord ++ tailWord_4378894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378894).length < 2 ^ (prefixWord ++ tailWord_4378894).sum := by decide
  have hdescent : baseEnd_4378894 < baseStart_4378894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378911 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 3]
def baseStart_4378911 : Nat := 118140960795 + 4378911 * 2 ^ 59
def prefixEnd_4378911 : Nat := 4983230072969 + 3 ^ 40 * 4378911 * 2
def baseEnd_4378911 : Nat := 2248486086260222224274261

theorem tailTrace_4378911 : CollatzResearch.WordTrace tailWord_4378911 prefixEnd_4378911 2248486086260222224274261 := by
  unfold tailWord_4378911
  simp only [CollatzResearch.WordTrace]
  refine ⟨159712005038960780303856587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106474670025973853535904391 159712005038960780303856587)
  ·
    refine ⟨239568007558441170455784881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159712005038960780303856587 239568007558441170455784881)
    ·
      refine ⟨179676005668830877841838661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239568007558441170455784881 179676005668830877841838661)
      ·
        refine ⟨33689251062905789595344749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179676005668830877841838661 33689251062905789595344749)
        ·
          refine ⟨12633469148589671098254281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33689251062905789595344749 12633469148589671098254281)
          ·
            refine ⟨9475101861442253323690711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12633469148589671098254281 9475101861442253323690711)
            ·
              refine ⟨14212652792163379985536067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9475101861442253323690711 14212652792163379985536067)
              ·
                refine ⟨21318979188245069978304101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14212652792163379985536067 21318979188245069978304101)
                ·
                  refine ⟨3997308597795950620932019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21318979188245069978304101 3997308597795950620932019)
                  ·
                    refine ⟨5995962896693925931398029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3997308597795950620932019 5995962896693925931398029)
                    ·
                      refine ⟨2248486086260222224274261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5995962896693925931398029 2248486086260222224274261)
                      ·
                        rfl

theorem cell23_4378911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_4378911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378911 prefixEnd_4378911 := by exact prefixLift 4378911
  have htrace : WordTrace (prefixWord ++ tailWord_4378911) baseStart_4378911 baseEnd_4378911 := by
    simpa [prefixWord, tailWord_4378911, baseEnd_4378911] using wordTrace_append hprefix tailTrace_4378911
  have hstable : (prefixWord ++ tailWord_4378911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378911).length < 2 ^ (prefixWord ++ tailWord_4378911).sum := by decide
  have hdescent : baseEnd_4378911 < baseStart_4378911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378925 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4378925 : Nat := 118140960795 + 4378925 * 2 ^ 59
def prefixEnd_4378925 : Nat := 4983230072969 + 3 ^ 40 * 4378925 * 2
def baseEnd_4378925 : Nat := 2248493274989385169499197

theorem tailTrace_4378925 : CollatzResearch.WordTrace tailWord_4378925 prefixEnd_4378925 2248493274989385169499197 := by
  unfold tailWord_4378925
  simp only [CollatzResearch.WordTrace]
  refine ⟨159712515660910060694866229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106475010440606707129910819 159712515660910060694866229)
  ·
    refine ⟨14973048343210318190143709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159712515660910060694866229 14973048343210318190143709)
    ·
      refine ⟨5614893128703869321303891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14973048343210318190143709 5614893128703869321303891)
      ·
        refine ⟨8422339693055803981955837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5614893128703869321303891 8422339693055803981955837)
        ·
          refine ⟨3158377384895926493233439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8422339693055803981955837 3158377384895926493233439)
          ·
            refine ⟨4737566077343889739850159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158377384895926493233439 4737566077343889739850159)
            ·
              refine ⟨7106349116015834609775239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737566077343889739850159 7106349116015834609775239)
              ·
                refine ⟨10659523674023751914662859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7106349116015834609775239 10659523674023751914662859)
                ·
                  refine ⟨15989285511035627871994289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10659523674023751914662859 15989285511035627871994289)
                  ·
                    refine ⟨11991964133276720903995717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15989285511035627871994289 11991964133276720903995717)
                    ·
                      refine ⟨2248493274989385169499197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11991964133276720903995717 2248493274989385169499197)
                      ·
                        rfl

theorem cell23_4378925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4378925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378925 prefixEnd_4378925 := by exact prefixLift 4378925
  have htrace : WordTrace (prefixWord ++ tailWord_4378925) baseStart_4378925 baseEnd_4378925 := by
    simpa [prefixWord, tailWord_4378925, baseEnd_4378925] using wordTrace_append hprefix tailTrace_4378925
  have hstable : (prefixWord ++ tailWord_4378925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378925).length < 2 ^ (prefixWord ++ tailWord_4378925).sum := by decide
  have hdescent : baseEnd_4378925 < baseStart_4378925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378927 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 2, 6]
def baseStart_4378927 : Nat := 118140960795 + 4378927 * 2 ^ 59
def prefixEnd_4378927 : Nat := 4983230072969 + 3 ^ 40 * 4378927 * 2
def baseEnd_4378927 : Nat := 749498100650231387224729

theorem tailTrace_4378927 : CollatzResearch.WordTrace tailWord_4378927 prefixEnd_4378927 749498100650231387224729 := by
  unfold tailWord_4378927
  simp only [CollatzResearch.WordTrace]
  refine ⟨159712588606902815036439035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106475059071268543357626023 159712588606902815036439035)
  ·
    refine ⟨239568882910354222554658553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159712588606902815036439035 239568882910354222554658553)
    ·
      refine ⟨179676662182765666915993915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239568882910354222554658553 179676662182765666915993915)
      ·
        refine ⟨269514993274148500373990873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179676662182765666915993915 269514993274148500373990873)
        ·
          refine ⟨202136244955611375280493155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269514993274148500373990873 202136244955611375280493155)
          ·
            refine ⟨303204367433417062920739733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202136244955611375280493155 303204367433417062920739733)
            ·
              refine ⟨14212704723441424824409675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 303204367433417062920739733 14212704723441424824409675)
              ·
                refine ⟨21319057085162137236614513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14212704723441424824409675 21319057085162137236614513)
                ·
                  refine ⟨15989292813871602927460885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21319057085162137236614513 15989292813871602927460885)
                  ·
                    refine ⟨749498100650231387224729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15989292813871602927460885 749498100650231387224729)
                    ·
                      rfl

theorem cell23_4378927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_4378927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378927 prefixEnd_4378927 := by exact prefixLift 4378927
  have htrace : WordTrace (prefixWord ++ tailWord_4378927) baseStart_4378927 baseEnd_4378927 := by
    simpa [prefixWord, tailWord_4378927, baseEnd_4378927] using wordTrace_append hprefix tailTrace_4378927
  have hstable : (prefixWord ++ tailWord_4378927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378927).length < 2 ^ (prefixWord ++ tailWord_4378927).sum := by decide
  have hdescent : baseEnd_4378927 < baseStart_4378927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378938 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2]
def baseStart_4378938 : Nat := 118140960795 + 4378938 * 2 ^ 59
def prefixEnd_4378938 : Nat := 4983230072969 + 3 ^ 40 * 4378938 * 2
def baseEnd_4378938 : Nat := 2248499950237893618636637

theorem tailTrace_4378938 : CollatzResearch.WordTrace tailWord_4378938 prefixEnd_4378938 2248499950237893618636637 := by
  unfold tailWord_4378938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39928247452465740978772367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106475326539908642610059645 39928247452465740978772367)
  ·
    refine ⟨59892371178698611468158551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39928247452465740978772367 59892371178698611468158551)
    ·
      refine ⟨89838556768047917202237827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59892371178698611468158551 89838556768047917202237827)
      ·
        refine ⟨134757835152071875803356741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89838556768047917202237827 134757835152071875803356741)
        ·
          refine ⟨25267094091013476713129389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134757835152071875803356741 25267094091013476713129389)
          ·
            refine ⟨9475160284130053767423521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25267094091013476713129389 9475160284130053767423521)
            ·
              refine ⟨7106370213097540325567641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9475160284130053767423521 7106370213097540325567641)
              ·
                refine ⟨5329777659823155244175731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7106370213097540325567641 5329777659823155244175731)
                ·
                  refine ⟨7994666489734732866263597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5329777659823155244175731 7994666489734732866263597)
                  ·
                    refine ⟨2997999933650524824848849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7994666489734732866263597 2997999933650524824848849)
                    ·
                      refine ⟨2248499950237893618636637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2997999933650524824848849 2248499950237893618636637)
                      ·
                        rfl

theorem cell23_4378938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_4378938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378938 prefixEnd_4378938 := by exact prefixLift 4378938
  have htrace : WordTrace (prefixWord ++ tailWord_4378938) baseStart_4378938 baseEnd_4378938 := by
    simpa [prefixWord, tailWord_4378938, baseEnd_4378938] using wordTrace_append hprefix tailTrace_4378938
  have hstable : (prefixWord ++ tailWord_4378938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378938).length < 2 ^ (prefixWord ++ tailWord_4378938).sum := by decide
  have hdescent : baseEnd_4378938 < baseStart_4378938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378947 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4]
def baseStart_4378947 : Nat := 118140960795 + 4378947 * 2 ^ 59
def prefixEnd_4378947 : Nat := 4983230072969 + 3 ^ 40 * 4378947 * 2
def baseEnd_4378947 : Nat := 2248504571563784083424095

theorem tailTrace_4378947 : CollatzResearch.WordTrace tailWord_4378947 prefixEnd_4378947 2248504571563784083424095 := by
  unfold tailWord_4378947
  simp only [CollatzResearch.WordTrace]
  refine ⟨159713318066830358452167095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106475545377886905634778063 159713318066830358452167095)
  ·
    refine ⟨239569977100245537678250643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159713318066830358452167095 239569977100245537678250643)
    ·
      refine ⟨359354965650368306517375965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239569977100245537678250643 359354965650368306517375965)
      ·
        refine ⟨134758112118888114944015987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359354965650368306517375965 134758112118888114944015987)
        ·
          refine ⟨202137168178332172416023981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134758112118888114944015987 202137168178332172416023981)
          ·
            refine ⟨75801438066874564656008993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202137168178332172416023981 75801438066874564656008993)
            ·
              refine ⟨56851078550155923492006745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75801438066874564656008993 56851078550155923492006745)
              ·
                refine ⟨42638308912616942619005059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56851078550155923492006745 42638308912616942619005059)
                ·
                  refine ⟨63957463368925413928507589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42638308912616942619005059 63957463368925413928507589)
                  ·
                    refine ⟨11992024381673515111595173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63957463368925413928507589 11992024381673515111595173)
                    ·
                      refine ⟨2248504571563784083424095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11992024381673515111595173 2248504571563784083424095)
                      ·
                        rfl

theorem cell23_4378947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_4378947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378947 prefixEnd_4378947 := by exact prefixLift 4378947
  have htrace : WordTrace (prefixWord ++ tailWord_4378947) baseStart_4378947 baseEnd_4378947 := by
    simpa [prefixWord, tailWord_4378947, baseEnd_4378947] using wordTrace_append hprefix tailTrace_4378947
  have hstable : (prefixWord ++ tailWord_4378947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378947).length < 2 ^ (prefixWord ++ tailWord_4378947).sum := by decide
  have hdescent : baseEnd_4378947 < baseStart_4378947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378951 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_4378951 : Nat := 118140960795 + 4378951 * 2 ^ 59
def prefixEnd_4378951 : Nat := 4983230072969 + 3 ^ 40 * 4378951 * 2
def baseEnd_4378951 : Nat := 2248506625486402067774077

theorem tailTrace_4378951 : CollatzResearch.WordTrace tailWord_4378951 prefixEnd_4378951 2248506625486402067774077 := by
  unfold tailWord_4378951
  simp only [CollatzResearch.WordTrace]
  refine ⟨159713463958815867135312707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106475642639210578090208471 159713463958815867135312707)
  ·
    refine ⟨239570195938223800702969061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159713463958815867135312707 239570195938223800702969061)
    ·
      refine ⟨44919411738416962631806699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239570195938223800702969061 44919411738416962631806699)
      ·
        refine ⟨67379117607625443947710049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44919411738416962631806699 67379117607625443947710049)
        ·
          refine ⟨50534338205719082960782537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67379117607625443947710049 50534338205719082960782537)
          ·
            refine ⟨37900753654289312220586903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50534338205719082960782537 37900753654289312220586903)
            ·
              refine ⟨56851130481433968330880355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37900753654289312220586903 56851130481433968330880355)
              ·
                refine ⟨85276695722150952496320533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56851130481433968330880355 85276695722150952496320533)
                ·
                  refine ⟨3997345111975825898265025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85276695722150952496320533 3997345111975825898265025)
                  ·
                    refine ⟨2998008833981869423698769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3997345111975825898265025 2998008833981869423698769)
                    ·
                      refine ⟨2248506625486402067774077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2998008833981869423698769 2248506625486402067774077)
                      ·
                        rfl

theorem cell23_4378951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_4378951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378951 prefixEnd_4378951 := by exact prefixLift 4378951
  have htrace : WordTrace (prefixWord ++ tailWord_4378951) baseStart_4378951 baseEnd_4378951 := by
    simpa [prefixWord, tailWord_4378951, baseEnd_4378951] using wordTrace_append hprefix tailTrace_4378951
  have hstable : (prefixWord ++ tailWord_4378951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378951).length < 2 ^ (prefixWord ++ tailWord_4378951).sum := by decide
  have hdescent : baseEnd_4378951 < baseStart_4378951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4378967 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_4378967 : Nat := 118140960795 + 4378967 * 2 ^ 59
def prefixEnd_4378967 : Nat := 4983230072969 + 3 ^ 40 * 4378967 * 2
def baseEnd_4378967 : Nat := 2248514841176874005174003

theorem tailTrace_4378967 : CollatzResearch.WordTrace tailWord_4378967 prefixEnd_4378967 2248514841176874005174003 := by
  unfold tailWord_4378967
  simp only [CollatzResearch.WordTrace]
  refine ⟨159714047526757901867895155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106476031684505267911930103 159714047526757901867895155)
  ·
    refine ⟨239571071290136852801842733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159714047526757901867895155 239571071290136852801842733)
    ·
      refine ⟨89839151733801319800691025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239571071290136852801842733 89839151733801319800691025)
      ·
        refine ⟨67379363800350989850518269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89839151733801319800691025 67379363800350989850518269)
        ·
          refine ⟨25267261425131621193944351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67379363800350989850518269 25267261425131621193944351)
          ·
            refine ⟨37900892137697431790916527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25267261425131621193944351 37900892137697431790916527)
            ·
              refine ⟨56851338206546147686374791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37900892137697431790916527 56851338206546147686374791)
              ·
                refine ⟨85277007309819221529562187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56851338206546147686374791 85277007309819221529562187)
                ·
                  refine ⟨127915510964728832294343281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85277007309819221529562187 127915510964728832294343281)
                  ·
                    refine ⟨95936633223546624220757461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127915510964728832294343281 95936633223546624220757461)
                    ·
                      refine ⟨2248514841176874005174003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95936633223546624220757461 2248514841176874005174003)
                      ·
                        rfl

theorem cell23_4378967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_4378967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4378967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4378967 prefixEnd_4378967 := by exact prefixLift 4378967
  have htrace : WordTrace (prefixWord ++ tailWord_4378967) baseStart_4378967 baseEnd_4378967 := by
    simpa [prefixWord, tailWord_4378967, baseEnd_4378967] using wordTrace_append hprefix tailTrace_4378967
  have hstable : (prefixWord ++ tailWord_4378967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4378967).length < 2 ^ (prefixWord ++ tailWord_4378967).sum := by decide
  have hdescent : baseEnd_4378967 < baseStart_4378967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4378967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379118 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_4379118 : Nat := 118140960795 + 4379118 * 2 ^ 59
def prefixEnd_4379118 : Nat := 4983230072969 + 3 ^ 40 * 4379118 * 2
def baseEnd_4379118 : Nat := 2248592376755702914385809

theorem tailTrace_4379118 : CollatzResearch.WordTrace tailWord_4379118 prefixEnd_4379118 2248592376755702914385809 := by
  unfold tailWord_4379118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19964944368651356832080251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106479703299473903104428005 19964944368651356832080251)
  ·
    refine ⟨29947416552977035248120377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19964944368651356832080251 29947416552977035248120377)
    ·
      refine ⟨22460562414732776436090283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29947416552977035248120377 22460562414732776436090283)
      ·
        refine ⟨33690843622099164654135425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22460562414732776436090283 33690843622099164654135425)
        ·
          refine ⟨25268132716574373490601569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33690843622099164654135425 25268132716574373490601569)
          ·
            refine ⟨18951099537430780117951177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25268132716574373490601569 18951099537430780117951177)
            ·
              refine ⟨14213324653073085088463383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18951099537430780117951177 14213324653073085088463383)
              ·
                refine ⟨21319986979609627632695075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14213324653073085088463383 21319986979609627632695075)
                ·
                  refine ⟨31979980469414441449042613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21319986979609627632695075 31979980469414441449042613)
                  ·
                    refine ⟨2998123169007603885847745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31979980469414441449042613 2998123169007603885847745)
                    ·
                      refine ⟨2248592376755702914385809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2998123169007603885847745 2248592376755702914385809)
                      ·
                        rfl

theorem cell23_4379118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_4379118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379118 prefixEnd_4379118 := by exact prefixLift 4379118
  have htrace : WordTrace (prefixWord ++ tailWord_4379118) baseStart_4379118 baseEnd_4379118 := by
    simpa [prefixWord, tailWord_4379118, baseEnd_4379118] using wordTrace_append hprefix tailTrace_4379118
  have hstable : (prefixWord ++ tailWord_4379118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379118).length < 2 ^ (prefixWord ++ tailWord_4379118).sum := by decide
  have hdescent : baseEnd_4379118 < baseStart_4379118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379141 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_4379141 : Nat := 118140960795 + 4379141 * 2 ^ 59
def prefixEnd_4379141 : Nat := 4983230072969 + 3 ^ 40 * 4379141 * 2
def baseEnd_4379141 : Nat := 749534728936918774799401

theorem tailTrace_4379141 : CollatzResearch.WordTrace tailWord_4379141 prefixEnd_4379141 749534728936918774799401 := by
  unfold tailWord_4379141
  simp only [CollatzResearch.WordTrace]
  refine ⟨159720393828127529584729277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106480262552085019723152851 159720393828127529584729277)
  ·
    refine ⟨59895147685547823594273479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159720393828127529584729277 59895147685547823594273479)
    ·
      refine ⟨89842721528321735391410219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59895147685547823594273479 89842721528321735391410219)
      ·
        refine ⟨134764082292482603087115329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89842721528321735391410219 134764082292482603087115329)
        ·
          refine ⟨101073061719361952315336497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134764082292482603087115329 101073061719361952315336497)
          ·
            refine ⟨75804796289521464236502373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101073061719361952315336497 75804796289521464236502373)
            ·
              refine ⟨14213399304285274544344195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75804796289521464236502373 14213399304285274544344195)
              ·
                refine ⟨21320098956427911816516293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14213399304285274544344195 21320098956427911816516293)
                ·
                  refine ⟨3997518554330233465596805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21320098956427911816516293 3997518554330233465596805)
                  ·
                    refine ⟨749534728936918774799401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3997518554330233465596805 749534728936918774799401)
                    ·
                      rfl

theorem cell23_4379141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_4379141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379141 prefixEnd_4379141 := by exact prefixLift 4379141
  have htrace : WordTrace (prefixWord ++ tailWord_4379141) baseStart_4379141 baseEnd_4379141 := by
    simpa [prefixWord, tailWord_4379141, baseEnd_4379141] using wordTrace_append hprefix tailTrace_4379141
  have hstable : (prefixWord ++ tailWord_4379141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379141).length < 2 ^ (prefixWord ++ tailWord_4379141).sum := by decide
  have hdescent : baseEnd_4379141 < baseStart_4379141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379165 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_4379165 : Nat := 118140960795 + 4379165 * 2 ^ 59
def prefixEnd_4379165 : Nat := 4983230072969 + 3 ^ 40 * 4379165 * 2
def baseEnd_4379165 : Nat := 2248616510346464230498093

theorem tailTrace_4379165 : CollatzResearch.WordTrace tailWord_4379165 prefixEnd_4379165 2248616510346464230498093 := by
  unfold tailWord_4379165
  simp only [CollatzResearch.WordTrace]
  refine ⟨159721269180040581683602949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106480846120027054455735299 159721269180040581683602949)
  ·
    refine ⟨29947737971257609065675553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159721269180040581683602949 29947737971257609065675553)
    ·
      refine ⟨22460803478443206799256665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29947737971257609065675553 22460803478443206799256665)
      ·
        refine ⟨16845602608832405099442499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22460803478443206799256665 16845602608832405099442499)
        ·
          refine ⟨25268403913248607649163749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16845602608832405099442499 25268403913248607649163749)
          ·
            refine ⟨4737825733734113934218203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25268403913248607649163749 4737825733734113934218203)
            ·
              refine ⟨7106738600601170901327305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737825733734113934218203 7106738600601170901327305)
              ·
                refine ⟨5330053950450878175995479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7106738600601170901327305 5330053950450878175995479)
                ·
                  refine ⟨7995080925676317263993219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5330053950450878175995479 7995080925676317263993219)
                  ·
                    refine ⟨11992621388514475895989829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7995080925676317263993219 11992621388514475895989829)
                    ·
                      refine ⟨2248616510346464230498093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11992621388514475895989829 2248616510346464230498093)
                      ·
                        rfl

theorem cell23_4379165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_4379165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379165 prefixEnd_4379165 := by exact prefixLift 4379165
  have htrace : WordTrace (prefixWord ++ tailWord_4379165) baseStart_4379165 baseEnd_4379165 := by
    simpa [prefixWord, tailWord_4379165, baseEnd_4379165] using wordTrace_append hprefix tailTrace_4379165
  have hstable : (prefixWord ++ tailWord_4379165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379165).length < 2 ^ (prefixWord ++ tailWord_4379165).sum := by decide
  have hdescent : baseEnd_4379165 < baseStart_4379165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379175 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 1, 6]
def baseStart_4379175 : Nat := 118140960795 + 4379175 * 2 ^ 59
def prefixEnd_4379175 : Nat := 4983230072969 + 3 ^ 40 * 4379175 * 2
def baseEnd_4379175 : Nat := 749540548384336397124349

theorem tailTrace_4379175 : CollatzResearch.WordTrace tailWord_4379175 prefixEnd_4379175 749540548384336397124349 := by
  unfold tailWord_4379175
  simp only [CollatzResearch.WordTrace]
  refine ⟨159721633910004353391466979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106481089273336235594311319 159721633910004353391466979)
  ·
    refine ⟨239582450865006530087200469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159721633910004353391466979 239582450865006530087200469)
    ·
      refine ⟨5615213692148590548918761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 239582450865006530087200469 5615213692148590548918761)
      ·
        refine ⟨4211410269111442911689071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5615213692148590548918761 4211410269111442911689071)
        ·
          refine ⟨6317115403667164367533607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211410269111442911689071 6317115403667164367533607)
          ·
            refine ⟨9475673105500746551300411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6317115403667164367533607 9475673105500746551300411)
            ·
              refine ⟨14213509658251119826950617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9475673105500746551300411 14213509658251119826950617)
              ·
                refine ⟨10660132243688339870212963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14213509658251119826950617 10660132243688339870212963)
                ·
                  refine ⟨15990198365532509805319445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10660132243688339870212963 15990198365532509805319445)
                  ·
                    refine ⟨749540548384336397124349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15990198365532509805319445 749540548384336397124349)
                    ·
                      rfl

theorem cell23_4379175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_4379175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379175 prefixEnd_4379175 := by exact prefixLift 4379175
  have htrace : WordTrace (prefixWord ++ tailWord_4379175) baseStart_4379175 baseEnd_4379175 := by
    simpa [prefixWord, tailWord_4379175, baseEnd_4379175] using wordTrace_append hprefix tailTrace_4379175
  have hstable : (prefixWord ++ tailWord_4379175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379175).length < 2 ^ (prefixWord ++ tailWord_4379175).sum := by decide
  have hdescent : baseEnd_4379175 < baseStart_4379175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379178 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4379178 : Nat := 118140960795 + 4379178 * 2 ^ 59
def prefixEnd_4379178 : Nat := 4983230072969 + 3 ^ 40 * 4379178 * 2
def baseEnd_4379178 : Nat := 2248623185594972679635533

theorem tailTrace_4379178 : CollatzResearch.WordTrace tailWord_4379178 prefixEnd_4379178 2248623185594972679635533 := by
  unfold tailWord_4379178
  simp only [CollatzResearch.WordTrace]
  refine ⟨39930435832248371225956547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106481162219328989935884125 39930435832248371225956547)
  ·
    refine ⟨59895653748372556838934821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39930435832248371225956547 59895653748372556838934821)
    ·
      refine ⟨11230435077819854407300279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59895653748372556838934821 11230435077819854407300279)
      ·
        refine ⟨16845652616729781610950419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11230435077819854407300279 16845652616729781610950419)
        ·
          refine ⟨25268478925094672416425629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16845652616729781610950419 25268478925094672416425629)
          ·
            refine ⟨9475679596910502156159611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25268478925094672416425629 9475679596910502156159611)
            ·
              refine ⟨14213519395365753234239417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9475679596910502156159611 14213519395365753234239417)
              ·
                refine ⟨10660139546524314925679563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14213519395365753234239417 10660139546524314925679563)
                ·
                  refine ⟨15990209319786472388519345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10660139546524314925679563 15990209319786472388519345)
                  ·
                    refine ⟨11992656989839854291389509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15990209319786472388519345 11992656989839854291389509)
                    ·
                      refine ⟨2248623185594972679635533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11992656989839854291389509 2248623185594972679635533)
                      ·
                        rfl

theorem cell23_4379178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4379178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379178 prefixEnd_4379178 := by exact prefixLift 4379178
  have htrace : WordTrace (prefixWord ++ tailWord_4379178) baseStart_4379178 baseEnd_4379178 := by
    simpa [prefixWord, tailWord_4379178, baseEnd_4379178] using wordTrace_append hprefix tailTrace_4379178
  have hstable : (prefixWord ++ tailWord_4379178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379178).length < 2 ^ (prefixWord ++ tailWord_4379178).sum := by decide
  have hdescent : baseEnd_4379178 < baseStart_4379178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379182 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_4379182 : Nat := 118140960795 + 4379182 * 2 ^ 59
def prefixEnd_4379182 : Nat := 4983230072969 + 3 ^ 40 * 4379182 * 2
def baseEnd_4379182 : Nat := 2248625239517590663985515

theorem tailTrace_4379182 : CollatzResearch.WordTrace tailWord_4379182 prefixEnd_4379182 2248625239517590663985515 := by
  unfold tailWord_4379182
  simp only [CollatzResearch.WordTrace]
  refine ⟨19965236152622374198371475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106481259480652662391314533 19965236152622374198371475)
  ·
    refine ⟨29947854228933561297557213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19965236152622374198371475 29947854228933561297557213)
    ·
      refine ⟨11230445335850085486583955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29947854228933561297557213 11230445335850085486583955)
      ·
        refine ⟨16845668003775128229875933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11230445335850085486583955 16845668003775128229875933)
        ·
          refine ⟨6317125501415673086203475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16845668003775128229875933 6317125501415673086203475)
          ·
            refine ⟨9475688252123509629305213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6317125501415673086203475 9475688252123509629305213)
            ·
              refine ⟨3553383094546316110989455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9475688252123509629305213 3553383094546316110989455)
              ·
                refine ⟨5330074641819474166484183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553383094546316110989455 5330074641819474166484183)
                ·
                  refine ⟨7995111962729211249726275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5330074641819474166484183 7995111962729211249726275)
                  ·
                    refine ⟨11992667944093816874589413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7995111962729211249726275 11992667944093816874589413)
                    ·
                      refine ⟨2248625239517590663985515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11992667944093816874589413 2248625239517590663985515)
                      ·
                        rfl

theorem cell23_4379182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_4379182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379182 prefixEnd_4379182 := by exact prefixLift 4379182
  have htrace : WordTrace (prefixWord ++ tailWord_4379182) baseStart_4379182 baseEnd_4379182 := by
    simpa [prefixWord, tailWord_4379182, baseEnd_4379182] using wordTrace_append hprefix tailTrace_4379182
  have hstable : (prefixWord ++ tailWord_4379182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379182).length < 2 ^ (prefixWord ++ tailWord_4379182).sum := by decide
  have hdescent : baseEnd_4379182 < baseStart_4379182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379188 : List Nat := [2, 5, 1, 3, 1, 11]
def baseStart_4379188 : Nat := 118140960795 + 4379188 * 2 ^ 59
def prefixEnd_4379188 : Nat := 4983230072969 + 3 ^ 40 * 4379188 * 2
def baseEnd_4379188 : Nat := 9253614487249043788109

theorem tailTrace_4379188 : CollatzResearch.WordTrace tailWord_4379188 prefixEnd_4379188 9253614487249043788109 := by
  unfold tailWord_4379188
  simp only [CollatzResearch.WordTrace]
  refine ⟨79861054029478628305845109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106481405372638171074460145 79861054029478628305845109)
  ·
    refine ⟨7486973815263621403672979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79861054029478628305845109 7486973815263621403672979)
    ·
      refine ⟨11230460722895432105509469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7486973815263621403672979 11230460722895432105509469)
      ·
        refine ⟨4211422771085787039566051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11230460722895432105509469 4211422771085787039566051)
        ·
          refine ⟨6317134156628680559349077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211422771085787039566051 6317134156628680559349077)
          ·
            refine ⟨9253614487249043788109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6317134156628680559349077 9253614487249043788109)
            ·
              rfl

theorem cell23_4379188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 11].length) (baseStart_4379188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379188 prefixEnd_4379188 := by exact prefixLift 4379188
  have htrace : WordTrace (prefixWord ++ tailWord_4379188) baseStart_4379188 baseEnd_4379188 := by
    simpa [prefixWord, tailWord_4379188, baseEnd_4379188] using wordTrace_append hprefix tailTrace_4379188
  have hstable : (prefixWord ++ tailWord_4379188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379188).length < 2 ^ (prefixWord ++ tailWord_4379188).sum := by decide
  have hdescent : baseEnd_4379188 < baseStart_4379188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379201 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4379201 : Nat := 118140960795 + 4379201 * 2 ^ 59
def prefixEnd_4379201 : Nat := 4983230072969 + 3 ^ 40 * 4379201 * 2
def baseEnd_4379201 : Nat := 749544998550008696549309

theorem tailTrace_4379201 : CollatzResearch.WordTrace tailWord_4379201 prefixEnd_4379201 749544998550008696549309 := by
  unfold tailWord_4379201
  simp only [CollatzResearch.WordTrace]
  refine ⟨159722582207910159831913457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106481721471940106554608971 159722582207910159831913457)
  ·
    refine ⟨119791936655932619873935093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159722582207910159831913457 119791936655932619873935093)
    ·
      refine ⟨11230494061493683113181415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119791936655932619873935093 11230494061493683113181415)
      ·
        refine ⟨16845741092240524669772123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11230494061493683113181415 16845741092240524669772123)
        ·
          refine ⟨25268611638360787004658185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16845741092240524669772123 25268611638360787004658185)
          ·
            refine ⟨18951458728770590253493639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25268611638360787004658185 18951458728770590253493639)
            ·
              refine ⟨28427188093155885380240459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18951458728770590253493639 28427188093155885380240459)
              ·
                refine ⟨42640782139733828070360689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28427188093155885380240459 42640782139733828070360689)
                ·
                  refine ⟨31980586604800371052770517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42640782139733828070360689 31980586604800371052770517)
                  ·
                    refine ⟨749544998550008696549309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31980586604800371052770517 749544998550008696549309)
                    ·
                      rfl

theorem cell23_4379201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4379201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379201 prefixEnd_4379201 := by exact prefixLift 4379201
  have htrace : WordTrace (prefixWord ++ tailWord_4379201) baseStart_4379201 baseEnd_4379201 := by
    simpa [prefixWord, tailWord_4379201, baseEnd_4379201] using wordTrace_append hprefix tailTrace_4379201
  have hstable : (prefixWord ++ tailWord_4379201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379201).length < 2 ^ (prefixWord ++ tailWord_4379201).sum := by decide
  have hdescent : baseEnd_4379201 < baseStart_4379201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379266 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4379266 : Nat := 118140960795 + 4379266 * 2 ^ 59
def prefixEnd_4379266 : Nat := 4983230072969 + 3 ^ 40 * 4379266 * 2
def baseEnd_4379266 : Nat := 2248668371892568335335129

theorem tailTrace_4379266 : CollatzResearch.WordTrace tailWord_4379266 prefixEnd_4379266 2248668371892568335335129 := by
  unfold tailWord_4379266
  simp only [CollatzResearch.WordTrace]
  refine ⟨39931238238168668983257413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106483301968449783955353101 39931238238168668983257413)
  ·
    refine ⟨7487107169656625434360765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39931238238168668983257413 7487107169656625434360765)
    ·
      refine ⟨2807665188621234537885287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7487107169656625434360765 2807665188621234537885287)
      ·
        refine ⟨4211497782931851806827931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807665188621234537885287 4211497782931851806827931)
        ·
          refine ⟨6317246674397777710241897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211497782931851806827931 6317246674397777710241897)
          ·
            refine ⟨4737935005798333282681423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6317246674397777710241897 4737935005798333282681423)
            ·
              refine ⟨7106902508697499924022135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4737935005798333282681423 7106902508697499924022135)
              ·
                refine ⟨10660353763046249886033203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7106902508697499924022135 10660353763046249886033203)
                ·
                  refine ⟨15990530644569374829049805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10660353763046249886033203 15990530644569374829049805)
                  ·
                    refine ⟨5996448991713515560893677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15990530644569374829049805 5996448991713515560893677)
                    ·
                      refine ⟨2248668371892568335335129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5996448991713515560893677 2248668371892568335335129)
                      ·
                        rfl

theorem cell23_4379266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4379266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379266 prefixEnd_4379266 := by exact prefixLift 4379266
  have htrace : WordTrace (prefixWord ++ tailWord_4379266) baseStart_4379266 baseEnd_4379266 := by
    simpa [prefixWord, tailWord_4379266, baseEnd_4379266] using wordTrace_append hprefix tailTrace_4379266
  have hstable : (prefixWord ++ tailWord_4379266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379266).length < 2 ^ (prefixWord ++ tailWord_4379266).sum := by decide
  have hdescent : baseEnd_4379266 < baseStart_4379266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379268 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_4379268 : Nat := 118140960795 + 4379268 * 2 ^ 59
def prefixEnd_4379268 : Nat := 4983230072969 + 3 ^ 40 * 4379268 * 2
def baseEnd_4379268 : Nat := 2248669398853877327510119

theorem tailTrace_4379268 : CollatzResearch.WordTrace tailWord_4379268 prefixEnd_4379268 2248669398853877327510119 := by
  unfold tailWord_4379268
  simp only [CollatzResearch.WordTrace]
  refine ⟨79862512949333715137301229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106483350599111620183068305 79862512949333715137301229)
  ·
    refine ⟨29948442356000143176487961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79862512949333715137301229 29948442356000143176487961)
    ·
      refine ⟨22461331767000107382365971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29948442356000143176487961 22461331767000107382365971)
      ·
        refine ⟨33691997650500161073548957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22461331767000107382365971 33691997650500161073548957)
        ·
          refine ⟨12634499118937560402580859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33691997650500161073548957 12634499118937560402580859)
          ·
            refine ⟨18951748678406340603871289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12634499118937560402580859 18951748678406340603871289)
            ·
              refine ⟨14213811508804755452903467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18951748678406340603871289 14213811508804755452903467)
              ·
                refine ⟨21320717263207133179355201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14213811508804755452903467 21320717263207133179355201)
                ·
                  refine ⟨15990537947405349884516401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21320717263207133179355201 15990537947405349884516401)
                  ·
                    refine ⟨11992903460554012413387301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15990537947405349884516401 11992903460554012413387301)
                    ·
                      refine ⟨2248669398853877327510119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11992903460554012413387301 2248669398853877327510119)
                      ·
                        rfl

theorem cell23_4379268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_4379268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379268 prefixEnd_4379268 := by exact prefixLift 4379268
  have htrace : WordTrace (prefixWord ++ tailWord_4379268) baseStart_4379268 baseEnd_4379268 := by
    simpa [prefixWord, tailWord_4379268, baseEnd_4379268] using wordTrace_append hprefix tailTrace_4379268
  have hstable : (prefixWord ++ tailWord_4379268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379268).length < 2 ^ (prefixWord ++ tailWord_4379268).sum := by decide
  have hdescent : baseEnd_4379268 < baseStart_4379268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379301 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_4379301 : Nat := 118140960795 + 4379301 * 2 ^ 59
def prefixEnd_4379301 : Nat := 4983230072969 + 3 ^ 40 * 4379301 * 2
def baseEnd_4379301 : Nat := 2248686343715475698397467

theorem tailTrace_4379301 : CollatzResearch.WordTrace tailWord_4379301 prefixEnd_4379301 2248686343715475698397467 := by
  unfold tailWord_4379301
  simp only [CollatzResearch.WordTrace]
  refine ⟨159726229507547876910553757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106484153005031917940369171 159726229507547876910553757)
  ·
    refine ⟨59897336065330453841457659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159726229507547876910553757 59897336065330453841457659)
    ·
      refine ⟨89846004097995680762186489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59897336065330453841457659 89846004097995680762186489)
      ·
        refine ⟨67384503073496760571639867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89846004097995680762186489 67384503073496760571639867)
        ·
          refine ⟨101076754610245140857459801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67384503073496760571639867 101076754610245140857459801)
          ·
            refine ⟨75807565957683855643094851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101076754610245140857459801 75807565957683855643094851)
            ·
              refine ⟨113711348936525783464642277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75807565957683855643094851 113711348936525783464642277)
              ·
                refine ⟨21320877925598584399620427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113711348936525783464642277 21320877925598584399620427)
                ·
                  refine ⟨31981316888397876599430641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21320877925598584399620427 31981316888397876599430641)
                  ·
                    refine ⟨23985987666298407449572981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31981316888397876599430641 23985987666298407449572981)
                    ·
                      refine ⟨2248686343715475698397467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23985987666298407449572981 2248686343715475698397467)
                      ·
                        rfl

theorem cell23_4379301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_4379301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379301 prefixEnd_4379301 := by exact prefixLift 4379301
  have htrace : WordTrace (prefixWord ++ tailWord_4379301) baseStart_4379301 baseEnd_4379301 := by
    simpa [prefixWord, tailWord_4379301, baseEnd_4379301] using wordTrace_append hprefix tailTrace_4379301
  have hstable : (prefixWord ++ tailWord_4379301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379301).length < 2 ^ (prefixWord ++ tailWord_4379301).sum := by decide
  have hdescent : baseEnd_4379301 < baseStart_4379301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379365 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4379365 : Nat := 118140960795 + 4379365 * 2 ^ 59
def prefixEnd_4379365 : Nat := 4983230072969 + 3 ^ 40 * 4379365 * 2
def baseEnd_4379365 : Nat := 2248719206477363447997173

theorem tailTrace_4379365 : CollatzResearch.WordTrace tailWord_4379365 prefixEnd_4379365 2248719206477363447997173 := by
  unfold tailWord_4379365
  simp only [CollatzResearch.WordTrace]
  refine ⟨159728563779316015840883549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106485709186210677227255699 159728563779316015840883549)
  ·
    refine ⟨59898211417243505940331331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159728563779316015840883549 59898211417243505940331331)
    ·
      refine ⟨89847317125865258910496997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59898211417243505940331331 89847317125865258910496997)
      ·
        refine ⟨16846371961099736045718187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89847317125865258910496997 16846371961099736045718187)
        ·
          refine ⟨25269557941649604068577281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16846371961099736045718187 25269557941649604068577281)
          ·
            refine ⟨18952168456237203051432961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25269557941649604068577281 18952168456237203051432961)
            ·
              refine ⟨14214126342177902288574721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18952168456237203051432961 14214126342177902288574721)
              ·
                refine ⟨10660594756633426716431041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14214126342177902288574721 10660594756633426716431041)
                ·
                  refine ⟨7995446067475070037323281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10660594756633426716431041 7995446067475070037323281)
                  ·
                    refine ⟨5996584550606302527992461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7995446067475070037323281 5996584550606302527992461)
                    ·
                      refine ⟨2248719206477363447997173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5996584550606302527992461 2248719206477363447997173)
                      ·
                        rfl

theorem cell23_4379365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4379365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379365 prefixEnd_4379365 := by exact prefixLift 4379365
  have htrace : WordTrace (prefixWord ++ tailWord_4379365) baseStart_4379365 baseEnd_4379365 := by
    simpa [prefixWord, tailWord_4379365, baseEnd_4379365] using wordTrace_append hprefix tailTrace_4379365
  have hstable : (prefixWord ++ tailWord_4379365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379365).length < 2 ^ (prefixWord ++ tailWord_4379365).sum := by decide
  have hdescent : baseEnd_4379365 < baseStart_4379365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379371 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_4379371 : Nat := 118140960795 + 4379371 * 2 ^ 59
def prefixEnd_4379371 : Nat := 4983230072969 + 3 ^ 40 * 4379371 * 2
def baseEnd_4379371 : Nat := 2248722287361290424522145

theorem tailTrace_4379371 : CollatzResearch.WordTrace tailWord_4379371 prefixEnd_4379371 2248722287361290424522145 := by
  unfold tailWord_4379371
  simp only [CollatzResearch.WordTrace]
  refine ⟨159728782617294278865601967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106485855078196185910401311 159728782617294278865601967)
  ·
    refine ⟨239593173925941418298402951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159728782617294278865601967 239593173925941418298402951)
    ·
      refine ⟨359389760888912127447604427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239593173925941418298402951 359389760888912127447604427)
      ·
        refine ⟨539084641333368191171406641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359389760888912127447604427 539084641333368191171406641)
        ·
          refine ⟨404313481000026143378554981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539084641333368191171406641 404313481000026143378554981)
          ·
            refine ⟨75808777687504901883479059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 404313481000026143378554981 75808777687504901883479059)
            ·
              refine ⟨113713166531257352825218589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75808777687504901883479059 113713166531257352825218589)
              ·
                refine ⟨42642437449221507309456971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113713166531257352825218589 42642437449221507309456971)
                ·
                  refine ⟨63963656173832260964185457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42642437449221507309456971 63963656173832260964185457)
                  ·
                    refine ⟨47972742130374195723139093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63963656173832260964185457 47972742130374195723139093)
                    ·
                      refine ⟨2248722287361290424522145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47972742130374195723139093 2248722287361290424522145)
                      ·
                        rfl

theorem cell23_4379371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_4379371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379371 prefixEnd_4379371 := by exact prefixLift 4379371
  have htrace : WordTrace (prefixWord ++ tailWord_4379371) baseStart_4379371 baseEnd_4379371 := by
    simpa [prefixWord, tailWord_4379371, baseEnd_4379371] using wordTrace_append hprefix tailTrace_4379371
  have hstable : (prefixWord ++ tailWord_4379371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379371).length < 2 ^ (prefixWord ++ tailWord_4379371).sum := by decide
  have hdescent : baseEnd_4379371 < baseStart_4379371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379391 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_4379391 : Nat := 118140960795 + 4379391 * 2 ^ 59
def prefixEnd_4379391 : Nat := 4983230072969 + 3 ^ 40 * 4379391 * 2
def baseEnd_4379391 : Nat := 2248732556974380346272053

theorem tailTrace_4379391 : CollatzResearch.WordTrace tailWord_4379391 prefixEnd_4379391 2248732556974380346272053 := by
  unfold tailWord_4379391
  simp only [CollatzResearch.WordTrace]
  refine ⟨159729512077221822281330027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106486341384814548187553351 159729512077221822281330027)
  ·
    refine ⟨239594268115832733421995041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159729512077221822281330027 239594268115832733421995041)
    ·
      refine ⟨179695701086874550066496281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239594268115832733421995041 179695701086874550066496281)
      ·
        refine ⟨134771775815155912549872211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179695701086874550066496281 134771775815155912549872211)
        ·
          refine ⟨202157663722733868824808317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134771775815155912549872211 202157663722733868824808317)
          ·
            refine ⟨75809123896025200809303119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202157663722733868824808317 75809123896025200809303119)
            ·
              refine ⟨113713685844037801213954679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75809123896025200809303119 113713685844037801213954679)
              ·
                refine ⟨170570528766056701820932019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113713685844037801213954679 170570528766056701820932019)
                ·
                  refine ⟨255855793149085052731398029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170570528766056701820932019 255855793149085052731398029)
                  ·
                    refine ⟨95945922430906894774274261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255855793149085052731398029 95945922430906894774274261)
                    ·
                      refine ⟨2248732556974380346272053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95945922430906894774274261 2248732556974380346272053)
                      ·
                        rfl

theorem cell23_4379391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_4379391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379391 prefixEnd_4379391 := by exact prefixLift 4379391
  have htrace : WordTrace (prefixWord ++ tailWord_4379391) baseStart_4379391 baseEnd_4379391 := by
    simpa [prefixWord, tailWord_4379391, baseEnd_4379391] using wordTrace_append hprefix tailTrace_4379391
  have hstable : (prefixWord ++ tailWord_4379391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379391).length < 2 ^ (prefixWord ++ tailWord_4379391).sum := by decide
  have hdescent : baseEnd_4379391 < baseStart_4379391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379445 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4379445 : Nat := 118140960795 + 4379445 * 2 ^ 59
def prefixEnd_4379445 : Nat := 4983230072969 + 3 ^ 40 * 4379445 * 2
def baseEnd_4379445 : Nat := 749586761643241044998935

theorem tailTrace_4379445 : CollatzResearch.WordTrace tailWord_4379445 prefixEnd_4379445 749586761643241044998935 := by
  unfold tailWord_4379445
  simp only [CollatzResearch.WordTrace]
  refine ⟨159731481619026189503795789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106487654412684126335863859 159731481619026189503795789)
  ·
    refine ⟨59899305607134821063923421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159731481619026189503795789 59899305607134821063923421)
    ·
      refine ⟨22462239602675557898971283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59899305607134821063923421 22462239602675557898971283)
      ·
        refine ⟨33693359404013336848456925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22462239602675557898971283 33693359404013336848456925)
        ·
          refine ⟨12635009776505001318171347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33693359404013336848456925 12635009776505001318171347)
          ·
            refine ⟨18952514664757501977257021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12635009776505001318171347 18952514664757501977257021)
            ·
              refine ⟨7107192999284063241471383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18952514664757501977257021 7107192999284063241471383)
              ·
                refine ⟨10660789498926094862207075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7107192999284063241471383 10660789498926094862207075)
                ·
                  refine ⟨15991184248389142293310613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10660789498926094862207075 15991184248389142293310613)
                  ·
                    refine ⟨749586761643241044998935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15991184248389142293310613 749586761643241044998935)
                    ·
                      rfl

theorem cell23_4379445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4379445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379445 prefixEnd_4379445 := by exact prefixLift 4379445
  have htrace : WordTrace (prefixWord ++ tailWord_4379445) baseStart_4379445 baseEnd_4379445 := by
    simpa [prefixWord, tailWord_4379445, baseEnd_4379445] using wordTrace_append hprefix tailTrace_4379445
  have hstable : (prefixWord ++ tailWord_4379445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379445).length < 2 ^ (prefixWord ++ tailWord_4379445).sum := by decide
  have hdescent : baseEnd_4379445 < baseStart_4379445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379448 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_4379448 : Nat := 118140960795 + 4379448 * 2 ^ 59
def prefixEnd_4379448 : Nat := 4983230072969 + 3 ^ 40 * 4379448 * 2
def baseEnd_4379448 : Nat := 2248761825371686623259291

theorem tailTrace_4379448 : CollatzResearch.WordTrace tailWord_4379448 prefixEnd_4379448 2248761825371686623259291 := by
  unfold tailWord_4379448
  simp only [CollatzResearch.WordTrace]
  refine ⟨79865795519007660508077499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106487727358676880677436665 79865795519007660508077499)
  ·
    refine ⟨119798693278511490762116249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79865795519007660508077499 119798693278511490762116249)
    ·
      refine ⟨89849019958883618071587187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119798693278511490762116249 89849019958883618071587187)
      ·
        refine ⟨134773529938325427107380781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89849019958883618071587187 134773529938325427107380781)
        ·
          refine ⟨50540073726872035165267793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134773529938325427107380781 50540073726872035165267793)
          ·
            refine ⟨37905055295154026373950845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50540073726872035165267793 37905055295154026373950845)
            ·
              refine ⟨14214395735682759890231567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37905055295154026373950845 14214395735682759890231567)
              ·
                refine ⟨21321593603524139835347351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14214395735682759890231567 21321593603524139835347351)
                ·
                  refine ⟨31982390405286209753021027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21321593603524139835347351 31982390405286209753021027)
                  ·
                    refine ⟨47973585607929314629531541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31982390405286209753021027 47973585607929314629531541)
                    ·
                      refine ⟨2248761825371686623259291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47973585607929314629531541 2248761825371686623259291)
                      ·
                        rfl

theorem cell23_4379448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_4379448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379448 prefixEnd_4379448 := by exact prefixLift 4379448
  have htrace : WordTrace (prefixWord ++ tailWord_4379448) baseStart_4379448 baseEnd_4379448 := by
    simpa [prefixWord, tailWord_4379448, baseEnd_4379448] using wordTrace_append hprefix tailTrace_4379448
  have hstable : (prefixWord ++ tailWord_4379448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379448).length < 2 ^ (prefixWord ++ tailWord_4379448).sum := by decide
  have hdescent : baseEnd_4379448 < baseStart_4379448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379488 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_4379488 : Nat := 118140960795 + 4379488 * 2 ^ 59
def prefixEnd_4379488 : Nat := 4983230072969 + 3 ^ 40 * 4379488 * 2
def baseEnd_4379488 : Nat := 749594121532622155586369

theorem tailTrace_4379488 : CollatzResearch.WordTrace tailWord_4379488 prefixEnd_4379488 749594121532622155586369 := by
  unfold tailWord_4379488
  simp only [CollatzResearch.WordTrace]
  refine ⟨79866524978935203923805559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106488699971913605231740745 79866524978935203923805559)
  ·
    refine ⟨119799787468402805885708339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79866524978935203923805559 119799787468402805885708339)
    ·
      refine ⟨179699681202604208828562509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119799787468402805885708339 179699681202604208828562509)
      ·
        refine ⟨67387380450976578310710941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179699681202604208828562509 67387380450976578310710941)
        ·
          refine ⟨25270267669116216866516603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67387380450976578310710941 25270267669116216866516603)
          ·
            refine ⟨37905401503674325299774905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25270267669116216866516603 37905401503674325299774905)
            ·
              refine ⟨28429051127755743974831179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37905401503674325299774905 28429051127755743974831179)
              ·
                refine ⟨42643576691633615962246769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28429051127755743974831179 42643576691633615962246769)
                ·
                  refine ⟨31982682518725211971685077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42643576691633615962246769 31982682518725211971685077)
                  ·
                    refine ⟨749594121532622155586369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31982682518725211971685077 749594121532622155586369)
                    ·
                      rfl

theorem cell23_4379488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_4379488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379488 prefixEnd_4379488 := by exact prefixLift 4379488
  have htrace : WordTrace (prefixWord ++ tailWord_4379488) baseStart_4379488 baseEnd_4379488 := by
    simpa [prefixWord, tailWord_4379488, baseEnd_4379488] using wordTrace_append hprefix tailTrace_4379488
  have hstable : (prefixWord ++ tailWord_4379488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379488).length < 2 ^ (prefixWord ++ tailWord_4379488).sum := by decide
  have hdescent : baseEnd_4379488 < baseStart_4379488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379512 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 1, 3, 2]
def baseStart_4379512 : Nat := 118140960795 + 4379512 * 2 ^ 59
def prefixEnd_4379512 : Nat := 4983230072969 + 3 ^ 40 * 4379512 * 2
def baseEnd_4379512 : Nat := 2248794688133574372858997

theorem tailTrace_4379512 : CollatzResearch.WordTrace tailWord_4379512 prefixEnd_4379512 2248794688133574372858997 := by
  unfold tailWord_4379512
  simp only [CollatzResearch.WordTrace]
  refine ⟨79866962654891729973242395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106489283539855639964323193 79866962654891729973242395)
  ·
    refine ⟨119800443982337594959863593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79866962654891729973242395 119800443982337594959863593)
    ·
      refine ⟨89850332986753196219897695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119800443982337594959863593 89850332986753196219897695)
      ·
        refine ⟨134775499480129794329846543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89850332986753196219897695 134775499480129794329846543)
        ·
          refine ⟨202163249220194691494769815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134775499480129794329846543 202163249220194691494769815)
          ·
            refine ⟨303244873830292037242154723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202163249220194691494769815 303244873830292037242154723)
            ·
              refine ⟨454867310745438055863232085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303244873830292037242154723 454867310745438055863232085)
              ·
                refine ⟨5330476297798102217147251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 454867310745438055863232085 5330476297798102217147251)
                ·
                  refine ⟨7995714446697153325720877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5330476297798102217147251 7995714446697153325720877)
                  ·
                    refine ⟨2998392917511432497145329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7995714446697153325720877 2998392917511432497145329)
                    ·
                      refine ⟨2248794688133574372858997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2998392917511432497145329 2248794688133574372858997)
                      ·
                        rfl

theorem cell23_4379512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_4379512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379512 prefixEnd_4379512 := by exact prefixLift 4379512
  have htrace : WordTrace (prefixWord ++ tailWord_4379512) baseStart_4379512 baseEnd_4379512 := by
    simpa [prefixWord, tailWord_4379512, baseEnd_4379512] using wordTrace_append hprefix tailTrace_4379512
  have hstable : (prefixWord ++ tailWord_4379512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379512).length < 2 ^ (prefixWord ++ tailWord_4379512).sum := by decide
  have hdescent : baseEnd_4379512 < baseStart_4379512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379655 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 8]
def baseStart_4379655 : Nat := 118140960795 + 4379655 * 2 ^ 59
def prefixEnd_4379655 : Nat := 4983230072969 + 3 ^ 40 * 4379655 * 2
def baseEnd_4379655 : Nat := 249874235096351923707871

theorem tailTrace_4379655 : CollatzResearch.WordTrace tailWord_4379655 prefixEnd_4379655 249874235096351923707871 := by
  unfold tailWord_4379655
  simp only [CollatzResearch.WordTrace]
  refine ⟨159739140948265395368940419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106492760632176930245960279 159739140948265395368940419)
  ·
    refine ⟨239608711422398093053410629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159739140948265395368940419 239608711422398093053410629)
    ·
      refine ⟨44926633391699642447514493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239608711422398093053410629 44926633391699642447514493)
      ·
        refine ⟨16847487521887365917817935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44926633391699642447514493 16847487521887365917817935)
        ·
          refine ⟨25271231282831048876726903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16847487521887365917817935 25271231282831048876726903)
          ·
            refine ⟨37906846924246573315090355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25271231282831048876726903 37906846924246573315090355)
            ·
              refine ⟨56860270386369859972635533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37906846924246573315090355 56860270386369859972635533)
              ·
                refine ⟨21322601394888697489738325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56860270386369859972635533 21322601394888697489738325)
                ·
                  refine ⟨249874235096351923707871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21322601394888697489738325 249874235096351923707871)
                  ·
                    rfl

theorem cell23_4379655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 8].length) (baseStart_4379655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379655 prefixEnd_4379655 := by exact prefixLift 4379655
  have htrace : WordTrace (prefixWord ++ tailWord_4379655) baseStart_4379655 baseEnd_4379655 := by
    simpa [prefixWord, tailWord_4379655, baseEnd_4379655] using wordTrace_append hprefix tailTrace_4379655
  have hstable : (prefixWord ++ tailWord_4379655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379655).length < 2 ^ (prefixWord ++ tailWord_4379655).sum := by decide
  have hdescent : baseEnd_4379655 < baseStart_4379655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379659 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 3, 4]
def baseStart_4379659 : Nat := 118140960795 + 4379659 * 2 ^ 59
def prefixEnd_4379659 : Nat := 4983230072969 + 3 ^ 40 * 4379659 * 2
def baseEnd_4379659 : Nat := 749623389929928432573607

theorem tailTrace_4379659 : CollatzResearch.WordTrace tailWord_4379659 prefixEnd_4379659 749623389929928432573607 := by
  unfold tailWord_4379659
  simp only [CollatzResearch.WordTrace]
  refine ⟨159739286840250904052086031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106492857893500602701390687 159739286840250904052086031)
  ·
    refine ⟨239608930260376356078129047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159739286840250904052086031 239608930260376356078129047)
    ·
      refine ⟨359413395390564534117193571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239608930260376356078129047 359413395390564534117193571)
      ·
        refine ⟨539120093085846801175790357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359413395390564534117193571 539120093085846801175790357)
        ·
          refine ⟨25271254363399068805115173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 539120093085846801175790357 25271254363399068805115173)
          ·
            refine ⟨4738360193137325400959095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25271254363399068805115173 4738360193137325400959095)
            ·
              refine ⟨7107540289705988101438643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738360193137325400959095 7107540289705988101438643)
              ·
                refine ⟨10661310434558982152157965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7107540289705988101438643 10661310434558982152157965)
                ·
                  refine ⟨3997991412959618307059237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10661310434558982152157965 3997991412959618307059237)
                  ·
                    refine ⟨749623389929928432573607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3997991412959618307059237 749623389929928432573607)
                    ·
                      rfl

theorem cell23_4379659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 4].length) (baseStart_4379659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379659 prefixEnd_4379659 := by exact prefixLift 4379659
  have htrace : WordTrace (prefixWord ++ tailWord_4379659) baseStart_4379659 baseEnd_4379659 := by
    simpa [prefixWord, tailWord_4379659, baseEnd_4379659] using wordTrace_append hprefix tailTrace_4379659
  have hstable : (prefixWord ++ tailWord_4379659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379659).length < 2 ^ (prefixWord ++ tailWord_4379659).sum := by decide
  have hdescent : baseEnd_4379659 < baseStart_4379659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379672 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 6]
def baseStart_4379672 : Nat := 118140960795 + 4379672 * 2 ^ 59
def prefixEnd_4379672 : Nat := 4983230072969 + 3 ^ 40 * 4379672 * 2
def baseEnd_4379672 : Nat := 249875205004254860762029

theorem tailTrace_4379672 : CollatzResearch.WordTrace tailWord_4379672 prefixEnd_4379672 249875205004254860762029 := by
  unfold tailWord_4379672
  simp only [CollatzResearch.WordTrace]
  refine ⟨79869880494601903636154635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106493173992802538181539513 79869880494601903636154635)
  ·
    refine ⟨119804820741902855454231953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79869880494601903636154635 119804820741902855454231953)
    ·
      refine ⟨89853615556427141590673965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119804820741902855454231953 89853615556427141590673965)
      ·
        refine ⟨33695105833660178096502737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89853615556427141590673965 33695105833660178096502737)
        ·
          refine ⟨25271329375245133572377053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33695105833660178096502737 25271329375245133572377053)
          ·
            refine ⟨9476748515716925089641395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25271329375245133572377053 9476748515716925089641395)
            ·
              refine ⟨14215122773575387634462093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9476748515716925089641395 14215122773575387634462093)
              ·
                refine ⟨5330671040090770362923285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14215122773575387634462093 5330671040090770362923285)
                ·
                  refine ⟨249875205004254860762029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5330671040090770362923285 249875205004254860762029)
                  ·
                    rfl

theorem cell23_4379672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 6].length) (baseStart_4379672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379672 prefixEnd_4379672 := by exact prefixLift 4379672
  have htrace : WordTrace (prefixWord ++ tailWord_4379672) baseStart_4379672 baseEnd_4379672 := by
    simpa [prefixWord, tailWord_4379672, baseEnd_4379672] using wordTrace_append hprefix tailTrace_4379672
  have hstable : (prefixWord ++ tailWord_4379672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379672).length < 2 ^ (prefixWord ++ tailWord_4379672).sum := by decide
  have hdescent : baseEnd_4379672 < baseStart_4379672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379710 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_4379710 : Nat := 118140960795 + 4379710 * 2 ^ 59
def prefixEnd_4379710 : Nat := 4983230072969 + 3 ^ 40 * 4379710 * 2
def baseEnd_4379710 : Nat := 749632119101054866061029

theorem tailTrace_4379710 : CollatzResearch.WordTrace tailWord_4379710 prefixEnd_4379710 749632119101054866061029 := by
  unfold tailWord_4379710
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967643370383267470274073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106494097975377426508128389 19967643370383267470274073)
  ·
    refine ⟨14975732527787450602705555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19967643370383267470274073 14975732527787450602705555)
    ·
      refine ⟨22463598791681175904058333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14975732527787450602705555 22463598791681175904058333)
      ·
        refine ⟨8423849546880440964021875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22463598791681175904058333 8423849546880440964021875)
        ·
          refine ⟨12635774320320661446032813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8423849546880440964021875 12635774320320661446032813)
          ·
            refine ⟨4738415370120248042262305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12635774320320661446032813 4738415370120248042262305)
            ·
              refine ⟨3553811527590186031696729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738415370120248042262305 3553811527590186031696729)
              ·
                refine ⟨2665358645692639523772547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3553811527590186031696729 2665358645692639523772547)
                ·
                  refine ⟨3998037968538959285658821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665358645692639523772547 3998037968538959285658821)
                  ·
                    refine ⟨749632119101054866061029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998037968538959285658821 749632119101054866061029)
                    ·
                      rfl

theorem cell23_4379710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_4379710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379710 prefixEnd_4379710 := by exact prefixLift 4379710
  have htrace : WordTrace (prefixWord ++ tailWord_4379710) baseStart_4379710 baseEnd_4379710 := by
    simpa [prefixWord, tailWord_4379710, baseEnd_4379710] using wordTrace_append hprefix tailTrace_4379710
  have hstable : (prefixWord ++ tailWord_4379710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379710).length < 2 ^ (prefixWord ++ tailWord_4379710).sum := by decide
  have hdescent : baseEnd_4379710 < baseStart_4379710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379715 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 3, 6]
def baseStart_4379715 : Nat := 118140960795 + 4379715 * 2 ^ 59
def prefixEnd_4379715 : Nat := 4983230072969 + 3 ^ 40 * 4379715 * 2
def baseEnd_4379715 : Nat := 749632974902145692873521

theorem tailTrace_4379715 : CollatzResearch.WordTrace tailWord_4379715 prefixEnd_4379715 749632974902145692873521 := by
  unfold tailWord_4379715
  simp only [CollatzResearch.WordTrace]
  refine ⟨159741329328048025616124599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106494219552032017077416399 159741329328048025616124599)
  ·
    refine ⟨239611993992072038424186899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159741329328048025616124599 239611993992072038424186899)
    ·
      refine ⟨359417990988108057636280349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239611993992072038424186899 359417990988108057636280349)
      ·
        refine ⟨134781746620540521613605131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359417990988108057636280349 134781746620540521613605131)
        ·
          refine ⟨202172619930810782420407697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134781746620540521613605131 202172619930810782420407697)
          ·
            refine ⟨151629464948108086815305773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202172619930810782420407697 151629464948108086815305773)
            ·
              refine ⟨56861049355540532555739665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151629464948108086815305773 56861049355540532555739665)
              ·
                refine ⟨42645787016655399416804749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56861049355540532555739665 42645787016655399416804749)
                ·
                  refine ⟨15992170131245774781301781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42645787016655399416804749 15992170131245774781301781)
                  ·
                    refine ⟨749632974902145692873521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15992170131245774781301781 749632974902145692873521)
                    ·
                      rfl

theorem cell23_4379715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 6].length) (baseStart_4379715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379715 prefixEnd_4379715 := by exact prefixLift 4379715
  have htrace : WordTrace (prefixWord ++ tailWord_4379715) baseStart_4379715 baseEnd_4379715 := by
    simpa [prefixWord, tailWord_4379715, baseEnd_4379715] using wordTrace_append hprefix tailTrace_4379715
  have hstable : (prefixWord ++ tailWord_4379715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379715).length < 2 ^ (prefixWord ++ tailWord_4379715).sum := by decide
  have hdescent : baseEnd_4379715 < baseStart_4379715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379722 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_4379722 : Nat := 118140960795 + 4379722 * 2 ^ 59
def prefixEnd_4379722 : Nat := 4983230072969 + 3 ^ 40 * 4379722 * 2
def baseEnd_4379722 : Nat := 2248902519071018551233031

theorem tailTrace_4379722 : CollatzResearch.WordTrace tailWord_4379722 prefixEnd_4379722 2248902519071018551233031 := by
  unfold tailWord_4379722
  simp only [CollatzResearch.WordTrace]
  refine ⟨39935396159755666452907355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106494389759348443874419613 39935396159755666452907355)
  ·
    refine ⟨59903094239633499679361033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39935396159755666452907355 59903094239633499679361033)
    ·
      refine ⟨44927320679725124759520775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59903094239633499679361033 44927320679725124759520775)
      ·
        refine ⟨67390981019587687139281163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44927320679725124759520775 67390981019587687139281163)
        ·
          refine ⟨101086471529381530708921745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67390981019587687139281163 101086471529381530708921745)
          ·
            refine ⟨75814853647036148031691309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101086471529381530708921745 75814853647036148031691309)
            ·
              refine ⟨28430570117638555511884241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75814853647036148031691309 28430570117638555511884241)
              ·
                refine ⟨21322927588228916633913181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28430570117638555511884241 21322927588228916633913181)
                ·
                  refine ⟨7996097845585843737717443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21322927588228916633913181 7996097845585843737717443)
                  ·
                    refine ⟨11994146768378765606576165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7996097845585843737717443 11994146768378765606576165)
                    ·
                      refine ⟨2248902519071018551233031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11994146768378765606576165 2248902519071018551233031)
                      ·
                        rfl

theorem cell23_4379722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_4379722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379722 prefixEnd_4379722 := by exact prefixLift 4379722
  have htrace : WordTrace (prefixWord ++ tailWord_4379722) baseStart_4379722 baseEnd_4379722 := by
    simpa [prefixWord, tailWord_4379722, baseEnd_4379722] using wordTrace_append hprefix tailTrace_4379722
  have hstable : (prefixWord ++ tailWord_4379722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379722).length < 2 ^ (prefixWord ++ tailWord_4379722).sum := by decide
  have hdescent : baseEnd_4379722 < baseStart_4379722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379732 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_4379732 : Nat := 118140960795 + 4379732 * 2 ^ 59
def prefixEnd_4379732 : Nat := 4983230072969 + 3 ^ 40 * 4379732 * 2
def baseEnd_4379732 : Nat := 749635884625854504035995

theorem tailTrace_4379732 : CollatzResearch.WordTrace tailWord_4379732 prefixEnd_4379732 749635884625854504035995 := by
  unfold tailWord_4379732
  simp only [CollatzResearch.WordTrace]
  refine ⟨79870974684493218759746725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106494632912657625012995633 79870974684493218759746725)
  ·
    refine ⟨14975807753342478517452511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79870974684493218759746725 14975807753342478517452511)
    ·
      refine ⟨22463711630013717776178767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14975807753342478517452511 22463711630013717776178767)
      ·
        refine ⟨33695567445020576664268151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22463711630013717776178767 33695567445020576664268151)
        ·
          refine ⟨50543351167530864996402227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33695567445020576664268151 50543351167530864996402227)
          ·
            refine ⟨75815026751296297494603341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50543351167530864996402227 75815026751296297494603341)
            ·
              refine ⟨28430635031736111560476253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75815026751296297494603341 28430635031736111560476253)
              ·
                refine ⟨10661488136901041835178595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28430635031736111560476253 10661488136901041835178595)
                ·
                  refine ⟨15992232205351562752767893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10661488136901041835178595 15992232205351562752767893)
                  ·
                    refine ⟨749635884625854504035995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15992232205351562752767893 749635884625854504035995)
                    ·
                      rfl

theorem cell23_4379732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_4379732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379732 prefixEnd_4379732 := by exact prefixLift 4379732
  have htrace : WordTrace (prefixWord ++ tailWord_4379732) baseStart_4379732 baseEnd_4379732 := by
    simpa [prefixWord, tailWord_4379732, baseEnd_4379732] using wordTrace_append hprefix tailTrace_4379732
  have hstable : (prefixWord ++ tailWord_4379732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379732).length < 2 ^ (prefixWord ++ tailWord_4379732).sum := by decide
  have hdescent : baseEnd_4379732 < baseStart_4379732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379745 : List Nat := [1, 2, 3, 1, 1, 2, 2, 11]
def baseStart_4379745 : Nat := 118140960795 + 4379745 * 2 ^ 59
def prefixEnd_4379745 : Nat := 4983230072969 + 3 ^ 40 * 4379745 * 2
def baseEnd_4379745 : Nat := 83293123300965628194275

theorem tailTrace_4379745 : CollatzResearch.WordTrace tailWord_4379745 prefixEnd_4379745 83293123300965628194275 := by
  unfold tailWord_4379745
  simp only [CollatzResearch.WordTrace]
  refine ⟨159742423517939340739716689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106494949011959560493144459 159742423517939340739716689)
  ·
    refine ⟨119806817638454505554787517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159742423517939340739716689 119806817638454505554787517)
    ·
      refine ⟨44927556614420439583045319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119806817638454505554787517 44927556614420439583045319)
      ·
        refine ⟨67391334921630659374567979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44927556614420439583045319 67391334921630659374567979)
        ·
          refine ⟨101087002382445989061851969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67391334921630659374567979 101087002382445989061851969)
          ·
            refine ⟨75815251786834491796388977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101087002382445989061851969 75815251786834491796388977)
            ·
              refine ⟨56861438840125868847291733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75815251786834491796388977 56861438840125868847291733)
              ·
                refine ⟨83293123300965628194275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56861438840125868847291733 83293123300965628194275)
                ·
                  rfl

theorem cell23_4379745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 11].length) (baseStart_4379745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379745 prefixEnd_4379745 := by exact prefixLift 4379745
  have htrace : WordTrace (prefixWord ++ tailWord_4379745) baseStart_4379745 baseEnd_4379745 := by
    simpa [prefixWord, tailWord_4379745, baseEnd_4379745] using wordTrace_append hprefix tailTrace_4379745
  have hstable : (prefixWord ++ tailWord_4379745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379745).length < 2 ^ (prefixWord ++ tailWord_4379745).sum := by decide
  have hdescent : baseEnd_4379745 < baseStart_4379745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379759 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 3]
def baseStart_4379759 : Nat := 118140960795 + 4379759 * 2 ^ 59
def prefixEnd_4379759 : Nat := 4983230072969 + 3 ^ 40 * 4379759 * 2
def baseEnd_4379759 : Nat := 2248921517855234906470361

theorem tailTrace_4379759 : CollatzResearch.WordTrace tailWord_4379759 prefixEnd_4379759 2248921517855234906470361 := by
  unfold tailWord_4379759
  simp only [CollatzResearch.WordTrace]
  refine ⟨159742934139888621130726331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106495289426592414087150887 159742934139888621130726331)
  ·
    refine ⟨239614401209832931696089497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159742934139888621130726331 239614401209832931696089497)
    ·
      refine ⟨179710800907374698772067123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239614401209832931696089497 179710800907374698772067123)
      ·
        refine ⟨269566201361062048158100685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179710800907374698772067123 269566201361062048158100685)
        ·
          refine ⟨101087325510398268059287757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269566201361062048158100685 101087325510398268059287757)
          ·
            refine ⟨37907747066399350522232909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101087325510398268059287757 37907747066399350522232909)
            ·
              refine ⟨14215405149899756445837341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37907747066399350522232909 14215405149899756445837341)
              ·
                refine ⟨5330776931212408667189003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14215405149899756445837341 5330776931212408667189003)
                ·
                  refine ⟨7996165396818613000783505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5330776931212408667189003 7996165396818613000783505)
                  ·
                    refine ⟨5997124047613959750587629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7996165396818613000783505 5997124047613959750587629)
                    ·
                      refine ⟨2248921517855234906470361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997124047613959750587629 2248921517855234906470361)
                      ·
                        rfl

theorem cell23_4379759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_4379759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379759 prefixEnd_4379759 := by exact prefixLift 4379759
  have htrace : WordTrace (prefixWord ++ tailWord_4379759) baseStart_4379759 baseEnd_4379759 := by
    simpa [prefixWord, tailWord_4379759, baseEnd_4379759] using wordTrace_append hprefix tailTrace_4379759
  have hstable : (prefixWord ++ tailWord_4379759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379759).length < 2 ^ (prefixWord ++ tailWord_4379759).sum := by decide
  have hdescent : baseEnd_4379759 < baseStart_4379759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379773 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_4379773 : Nat := 118140960795 + 4379773 * 2 ^ 59
def prefixEnd_4379773 : Nat := 4983230072969 + 3 ^ 40 * 4379773 * 2
def baseEnd_4379773 : Nat := 2248928706584397851695297

theorem tailTrace_4379773 : CollatzResearch.WordTrace tailWord_4379773 prefixEnd_4379773 2248928706584397851695297 := by
  unfold tailWord_4379773
  simp only [CollatzResearch.WordTrace]
  refine ⟨159743444761837901521735973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106495629841225267681157315 159743444761837901521735973)
  ·
    refine ⟨29951895892844606535325495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159743444761837901521735973 29951895892844606535325495)
    ·
      refine ⟨44927843839266909802988243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29951895892844606535325495 44927843839266909802988243)
      ·
        refine ⟨67391765758900364704482365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44927843839266909802988243 67391765758900364704482365)
        ·
          refine ⟨25271912159587636764180887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67391765758900364704482365 25271912159587636764180887)
          ·
            refine ⟨37907868239381455146271331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25271912159587636764180887 37907868239381455146271331)
            ·
              refine ⟨56861802359072182719406997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37907868239381455146271331 56861802359072182719406997)
              ·
                refine ⟨2665396985581508564972203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56861802359072182719406997 2665396985581508564972203)
                ·
                  refine ⟨3998095478372262847458305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665396985581508564972203 3998095478372262847458305)
                  ·
                    refine ⟨2998571608779197135593729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3998095478372262847458305 2998571608779197135593729)
                    ·
                      refine ⟨2248928706584397851695297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2998571608779197135593729 2248928706584397851695297)
                      ·
                        rfl

theorem cell23_4379773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_4379773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379773 prefixEnd_4379773 := by exact prefixLift 4379773
  have htrace : WordTrace (prefixWord ++ tailWord_4379773) baseStart_4379773 baseEnd_4379773 := by
    simpa [prefixWord, tailWord_4379773, baseEnd_4379773] using wordTrace_append hprefix tailTrace_4379773
  have hstable : (prefixWord ++ tailWord_4379773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379773).length < 2 ^ (prefixWord ++ tailWord_4379773).sum := by decide
  have hdescent : baseEnd_4379773 < baseStart_4379773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379807 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4379807 : Nat := 118140960795 + 4379807 * 2 ^ 59
def prefixEnd_4379807 : Nat := 4983230072969 + 3 ^ 40 * 4379807 * 2
def baseEnd_4379807 : Nat := 2248946164926650718670141

theorem tailTrace_4379807 : CollatzResearch.WordTrace tailWord_4379807 prefixEnd_4379807 2248946164926650718670141 := by
  unfold tailWord_4379807
  simp only [CollatzResearch.WordTrace]
  refine ⟨159744684843714725328473675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106496456562476483552315783 159744684843714725328473675)
  ·
    refine ⟨239617027265572087992710513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159744684843714725328473675 239617027265572087992710513)
    ·
      refine ⟨179712770449179065994532885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239617027265572087992710513 179712770449179065994532885)
      ·
        refine ⟨8424036114805268718493729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 179712770449179065994532885 8424036114805268718493729)
        ·
          refine ⟨6318027086103951538870297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8424036114805268718493729 6318027086103951538870297)
          ·
            refine ⟨4738520314577963654152723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6318027086103951538870297 4738520314577963654152723)
            ·
              refine ⟨7107780471866945481229085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738520314577963654152723 7107780471866945481229085)
              ·
                refine ⟨2665417676950104555460907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7107780471866945481229085 2665417676950104555460907)
                ·
                  refine ⟨3998126515425156833191361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665417676950104555460907 3998126515425156833191361)
                  ·
                    refine ⟨2998594886568867624893521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3998126515425156833191361 2998594886568867624893521)
                    ·
                      refine ⟨2248946164926650718670141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2998594886568867624893521 2248946164926650718670141)
                      ·
                        rfl

theorem cell23_4379807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4379807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379807 prefixEnd_4379807 := by exact prefixLift 4379807
  have htrace : WordTrace (prefixWord ++ tailWord_4379807) baseStart_4379807 baseEnd_4379807 := by
    simpa [prefixWord, tailWord_4379807, baseEnd_4379807] using wordTrace_append hprefix tailTrace_4379807
  have hstable : (prefixWord ++ tailWord_4379807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379807).length < 2 ^ (prefixWord ++ tailWord_4379807).sum := by decide
  have hdescent : baseEnd_4379807 < baseStart_4379807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379840 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 2, 1, 3]
def baseStart_4379840 : Nat := 118140960795 + 4379840 * 2 ^ 59
def prefixEnd_4379840 : Nat := 4983230072969 + 3 ^ 40 * 4379840 * 2
def baseEnd_4379840 : Nat := 2248963109788249089557489

theorem tailTrace_4379840 : CollatzResearch.WordTrace tailWord_4379840 prefixEnd_4379840 2248963109788249089557489 := by
  unfold tailWord_4379840
  simp only [CollatzResearch.WordTrace]
  refine ⟨79872944226297585982212487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106497258968396781309616649 79872944226297585982212487)
  ·
    refine ⟨119809416339446378973318731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79872944226297585982212487 119809416339446378973318731)
    ·
      refine ⟨179714124509169568459978097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119809416339446378973318731 179714124509169568459978097)
      ·
        refine ⟨134785593381877176344983573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179714124509169568459978097 134785593381877176344983573)
        ·
          refine ⟨6318074689775492641171105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134785593381877176344983573 6318074689775492641171105)
          ·
            refine ⟨4738556017331619480878329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6318074689775492641171105 4738556017331619480878329)
            ·
              refine ⟨3553917012998714610658747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738556017331619480878329 3553917012998714610658747)
              ·
                refine ⟨5330875519498071915988121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3553917012998714610658747 5330875519498071915988121)
                ·
                  refine ⟨3998156639623553936991091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5330875519498071915988121 3998156639623553936991091)
                  ·
                    refine ⟨5997234959435330905486637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998156639623553936991091 5997234959435330905486637)
                    ·
                      refine ⟨2248963109788249089557489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997234959435330905486637 2248963109788249089557489)
                      ·
                        rfl

theorem cell23_4379840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_4379840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379840 prefixEnd_4379840 := by exact prefixLift 4379840
  have htrace : WordTrace (prefixWord ++ tailWord_4379840) baseStart_4379840 baseEnd_4379840 := by
    simpa [prefixWord, tailWord_4379840, baseEnd_4379840] using wordTrace_append hprefix tailTrace_4379840
  have hstable : (prefixWord ++ tailWord_4379840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379840).length < 2 ^ (prefixWord ++ tailWord_4379840).sum := by decide
  have hdescent : baseEnd_4379840 < baseStart_4379840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379916 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_4379916 : Nat := 118140960795 + 4379916 * 2 ^ 59
def prefixEnd_4379916 : Nat := 4983230072969 + 3 ^ 40 * 4379916 * 2
def baseEnd_4379916 : Nat := 749667378105996930735713

theorem tailTrace_4379916 : CollatzResearch.WordTrace tailWord_4379916 prefixEnd_4379916 749667378105996930735713 := by
  unfold tailWord_4379916
  simp only [CollatzResearch.WordTrace]
  refine ⟨79874330200159918472095801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106499106933546557962794401 79874330200159918472095801)
  ·
    refine ⟨59905747650119938854071851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79874330200159918472095801 59905747650119938854071851)
    ·
      refine ⟨89858621475179908281107777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59905747650119938854071851 89858621475179908281107777)
      ·
        refine ⟨67393966106384931210830833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89858621475179908281107777 67393966106384931210830833)
        ·
          refine ⟨50545474579788698408123125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67393966106384931210830833 50545474579788698408123125)
          ·
            refine ⟨4738638241855190475761543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50545474579788698408123125 4738638241855190475761543)
            ·
              refine ⟨7107957362782785713642315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738638241855190475761543 7107957362782785713642315)
              ·
                refine ⟨10661936044174178570463473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7107957362782785713642315 10661936044174178570463473)
                ·
                  refine ⟨7996452033130633927847605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10661936044174178570463473 7996452033130633927847605)
                  ·
                    refine ⟨749667378105996930735713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7996452033130633927847605 749667378105996930735713)
                    ·
                      rfl

theorem cell23_4379916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_4379916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379916 prefixEnd_4379916 := by exact prefixLift 4379916
  have htrace : WordTrace (prefixWord ++ tailWord_4379916) baseStart_4379916 baseEnd_4379916 := by
    simpa [prefixWord, tailWord_4379916, baseEnd_4379916] using wordTrace_append hprefix tailTrace_4379916
  have hstable : (prefixWord ++ tailWord_4379916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379916).length < 2 ^ (prefixWord ++ tailWord_4379916).sum := by decide
  have hdescent : baseEnd_4379916 < baseStart_4379916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379956 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4379956 : Nat := 118140960795 + 4379956 * 2 ^ 59
def prefixEnd_4379956 : Nat := 4983230072969 + 3 ^ 40 * 4379956 * 2
def baseEnd_4379956 : Nat := 2249022673544170635706955

theorem tailTrace_4379956 : CollatzResearch.WordTrace tailWord_4379956 prefixEnd_4379956 2249022673544170635706955 := by
  unfold tailWord_4379956
  simp only [CollatzResearch.WordTrace]
  refine ⟨79875059660087461887823861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106500079546783282517098481 79875059660087461887823861)
  ·
    refine ⟨7488286843133199551983487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79875059660087461887823861 7488286843133199551983487)
    ·
      refine ⟨11232430264699799327975231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7488286843133199551983487 11232430264699799327975231)
      ·
        refine ⟨16848645397049698991962847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11232430264699799327975231 16848645397049698991962847)
        ·
          refine ⟨25272968095574548487944271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16848645397049698991962847 25272968095574548487944271)
          ·
            refine ⟨37909452143361822731916407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25272968095574548487944271 37909452143361822731916407)
            ·
              refine ⟨56864178215042734097874611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37909452143361822731916407 56864178215042734097874611)
              ·
                refine ⟨85296267322564101146811917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56864178215042734097874611 85296267322564101146811917)
                ·
                  refine ⟨31986100245961537930054469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85296267322564101146811917 31986100245961537930054469)
                  ·
                    refine ⟨5997393796117788361885213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31986100245961537930054469 5997393796117788361885213)
                    ·
                      refine ⟨2249022673544170635706955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997393796117788361885213 2249022673544170635706955)
                      ·
                        rfl

theorem cell23_4379956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4379956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379956 prefixEnd_4379956 := by exact prefixLift 4379956
  have htrace : WordTrace (prefixWord ++ tailWord_4379956) baseStart_4379956 baseEnd_4379956 := by
    simpa [prefixWord, tailWord_4379956, baseEnd_4379956] using wordTrace_append hprefix tailTrace_4379956
  have hstable : (prefixWord ++ tailWord_4379956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379956).length < 2 ^ (prefixWord ++ tailWord_4379956).sum := by decide
  have hdescent : baseEnd_4379956 < baseStart_4379956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4379980 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_4379980 : Nat := 118140960795 + 4379980 * 2 ^ 59
def prefixEnd_4379980 : Nat := 4983230072969 + 3 ^ 40 * 4379980 * 2
def baseEnd_4379980 : Nat := 749678332359959513935615

theorem tailTrace_4379980 : CollatzResearch.WordTrace tailWord_4379980 prefixEnd_4379980 749678332359959513935615 := by
  unfold tailWord_4379980
  simp only [CollatzResearch.WordTrace]
  refine ⟨79875497336043987937260697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106500663114725317249680929 79875497336043987937260697)
  ·
    refine ⟨59906623002032990952945523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79875497336043987937260697 59906623002032990952945523)
    ·
      refine ⟨89859934503049486429418285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59906623002032990952945523 89859934503049486429418285)
      ·
        refine ⟨33697475438643557411031857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89859934503049486429418285 33697475438643557411031857)
        ·
          refine ⟨25273106578982668058273893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33697475438643557411031857 25273106578982668058273893)
          ·
            refine ⟨4738707483559250260926355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25273106578982668058273893 4738707483559250260926355)
            ·
              refine ⟨7108061225338875391389533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738707483559250260926355 7108061225338875391389533)
              ·
                refine ⟨2665522959502078271771075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7108061225338875391389533 2665522959502078271771075)
                ·
                  refine ⟨3998284439253117407656613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665522959502078271771075 3998284439253117407656613)
                  ·
                    refine ⟨749678332359959513935615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998284439253117407656613 749678332359959513935615)
                    ·
                      rfl

theorem cell23_4379980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_4379980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4379980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4379980 prefixEnd_4379980 := by exact prefixLift 4379980
  have htrace : WordTrace (prefixWord ++ tailWord_4379980) baseStart_4379980 baseEnd_4379980 := by
    simpa [prefixWord, tailWord_4379980, baseEnd_4379980] using wordTrace_append hprefix tailTrace_4379980
  have hstable : (prefixWord ++ tailWord_4379980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4379980).length < 2 ^ (prefixWord ++ tailWord_4379980).sum := by decide
  have hdescent : baseEnd_4379980 < baseStart_4379980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4379980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380003 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 3]
def baseStart_4380003 : Nat := 118140960795 + 4380003 * 2 ^ 59
def prefixEnd_4380003 : Nat := 4983230072969 + 3 ^ 40 * 4380003 * 2
def baseEnd_4380003 : Nat := 2249046807134931951819239

theorem tailTrace_4380003 : CollatzResearch.WordTrace tailWord_4380003 prefixEnd_4380003 2249046807134931951819239 := by
  unfold tailWord_4380003
  simp only [CollatzResearch.WordTrace]
  refine ⟨159751833551004650802608663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106501222367336433868405775 159751833551004650802608663)
  ·
    refine ⟨239627750326506976203912995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159751833551004650802608663 239627750326506976203912995)
    ·
      refine ⟨359441625489760464305869493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239627750326506976203912995 359441625489760464305869493)
      ·
        refine ⟨33697652389665043528675265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 359441625489760464305869493 33697652389665043528675265)
        ·
          refine ⟨25273239292248782646506449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33697652389665043528675265 25273239292248782646506449)
          ·
            refine ⟨18954929469186586984879837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25273239292248782646506449 18954929469186586984879837)
            ·
              refine ⟨7108098550944970119329939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18954929469186586984879837 7108098550944970119329939)
              ·
                refine ⟨10662147826417455178994909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108098550944970119329939 10662147826417455178994909)
                ·
                  refine ⟨3998305434906545692123091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10662147826417455178994909 3998305434906545692123091)
                  ·
                    refine ⟨5997458152359818538184637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998305434906545692123091 5997458152359818538184637)
                    ·
                      refine ⟨2249046807134931951819239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997458152359818538184637 2249046807134931951819239)
                      ·
                        rfl

theorem cell23_4380003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_4380003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380003 prefixEnd_4380003 := by exact prefixLift 4380003
  have htrace : WordTrace (prefixWord ++ tailWord_4380003) baseStart_4380003 baseEnd_4380003 := by
    simpa [prefixWord, tailWord_4380003, baseEnd_4380003] using wordTrace_append hprefix tailTrace_4380003
  have hstable : (prefixWord ++ tailWord_4380003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380003).length < 2 ^ (prefixWord ++ tailWord_4380003).sum := by decide
  have hdescent : baseEnd_4380003 < baseStart_4380003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380010 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_4380010 : Nat := 118140960795 + 4380010 * 2 ^ 59
def prefixEnd_4380010 : Nat := 4983230072969 + 3 ^ 40 * 4380010 * 2
def baseEnd_4380010 : Nat := 249894489055501491603523

theorem tailTrace_4380010 : CollatzResearch.WordTrace tailWord_4380010 prefixEnd_4380010 249894489055501491603523 := by
  unfold tailWord_4380010
  simp only [CollatzResearch.WordTrace]
  refine ⟨39938022215494822749528371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106501392574652860665408989 39938022215494822749528371)
  ·
    refine ⟨59907033323242234124292557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39938022215494822749528371 59907033323242234124292557)
    ·
      refine ⟨22465137496215837796609709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59907033323242234124292557 22465137496215837796609709)
      ·
        refine ⟨8424426561080939173728641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22465137496215837796609709 8424426561080939173728641)
        ·
          refine ⟨6318319920810704380296481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8424426561080939173728641 6318319920810704380296481)
          ·
            refine ⟨4738739940608028285222361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6318319920810704380296481 4738739940608028285222361)
            ·
              refine ⟨3554054955456021213916771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738739940608028285222361 3554054955456021213916771)
              ·
                refine ⟨5331082433184031820875157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554054955456021213916771 5331082433184031820875157)
                ·
                  refine ⟨249894489055501491603523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5331082433184031820875157 249894489055501491603523)
                  ·
                    rfl

theorem cell23_4380010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_4380010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380010 prefixEnd_4380010 := by exact prefixLift 4380010
  have htrace : WordTrace (prefixWord ++ tailWord_4380010) baseStart_4380010 baseEnd_4380010 := by
    simpa [prefixWord, tailWord_4380010, baseEnd_4380010] using wordTrace_append hprefix tailTrace_4380010
  have hstable : (prefixWord ++ tailWord_4380010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380010).length < 2 ^ (prefixWord ++ tailWord_4380010).sum := by decide
  have hdescent : baseEnd_4380010 < baseStart_4380010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380036 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_4380036 : Nat := 118140960795 + 4380036 * 2 ^ 59
def prefixEnd_4380036 : Nat := 4983230072969 + 3 ^ 40 * 4380036 * 2
def baseEnd_4380036 : Nat := 749687917332176774235529

theorem tailTrace_4380036 : CollatzResearch.WordTrace tailWord_4380036 prefixEnd_4380036 749687917332176774235529 := by
  unfold tailWord_4380036
  simp only [CollatzResearch.WordTrace]
  refine ⟨79876518579942548719279981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106502024773256731625706641 79876518579942548719279981)
  ·
    refine ⟨29953694467478455769729993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79876518579942548719279981 29953694467478455769729993)
    ·
      refine ⟨22465270850608841827297495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29953694467478455769729993 22465270850608841827297495)
      ·
        refine ⟨33697906275913262740946243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22465270850608841827297495 33697906275913262740946243)
        ·
          refine ⟨50546859413869894111419365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33697906275913262740946243 50546859413869894111419365)
          ·
            refine ⟨9477536140100605145891131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50546859413869894111419365 9477536140100605145891131)
            ·
              refine ⟨14216304210150907718836697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9477536140100605145891131 14216304210150907718836697)
              ·
                refine ⟨10662228157613180789127523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14216304210150907718836697 10662228157613180789127523)
                ·
                  refine ⟨15993342236419771183691285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10662228157613180789127523 15993342236419771183691285)
                  ·
                    refine ⟨749687917332176774235529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15993342236419771183691285 749687917332176774235529)
                    ·
                      rfl

theorem cell23_4380036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_4380036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380036 prefixEnd_4380036 := by exact prefixLift 4380036
  have htrace : WordTrace (prefixWord ++ tailWord_4380036) baseStart_4380036 baseEnd_4380036 := by
    simpa [prefixWord, tailWord_4380036, baseEnd_4380036] using wordTrace_append hprefix tailTrace_4380036
  have hstable : (prefixWord ++ tailWord_4380036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380036).length < 2 ^ (prefixWord ++ tailWord_4380036).sum := by decide
  have hdescent : baseEnd_4380036 < baseStart_4380036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380043 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 1, 1, 4]
def baseStart_4380043 : Nat := 118140960795 + 4380043 * 2 ^ 59
def prefixEnd_4380043 : Nat := 4983230072969 + 3 ^ 40 * 4380043 * 2
def baseEnd_4380043 : Nat := 2249067346361111795319055

theorem tailTrace_4380043 : CollatzResearch.WordTrace tailWord_4380043 prefixEnd_4380043 2249067346361111795319055 := by
  unfold tailWord_4380043
  simp only [CollatzResearch.WordTrace]
  refine ⟨159753292470859737634064783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106502194980573158422709855 159753292470859737634064783)
  ·
    refine ⟨239629938706289606451097175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159753292470859737634064783 239629938706289606451097175)
    ·
      refine ⟨359444908059434409676645763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239629938706289606451097175 359444908059434409676645763)
      ·
        refine ⟨539167362089151614514968645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359444908059434409676645763 539167362089151614514968645)
        ·
          refine ⟨101093880391715927721556621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 539167362089151614514968645 101093880391715927721556621)
          ·
            refine ⟨37910205146893472895583733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101093880391715927721556621 37910205146893472895583733)
            ·
              refine ⟨3554081732521263083960975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37910205146893472895583733 3554081732521263083960975)
              ·
                refine ⟨5331122598781894625941463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554081732521263083960975 5331122598781894625941463)
                ·
                  refine ⟨7996683898172841938912195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331122598781894625941463 7996683898172841938912195)
                  ·
                    refine ⟨11995025847259262908368293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7996683898172841938912195 11995025847259262908368293)
                    ·
                      refine ⟨2249067346361111795319055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11995025847259262908368293 2249067346361111795319055)
                      ·
                        rfl

theorem cell23_4380043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 1, 4].length) (baseStart_4380043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380043 prefixEnd_4380043 := by exact prefixLift 4380043
  have htrace : WordTrace (prefixWord ++ tailWord_4380043) baseStart_4380043 baseEnd_4380043 := by
    simpa [prefixWord, tailWord_4380043, baseEnd_4380043] using wordTrace_append hprefix tailTrace_4380043
  have hstable : (prefixWord ++ tailWord_4380043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380043).length < 2 ^ (prefixWord ++ tailWord_4380043).sum := by decide
  have hdescent : baseEnd_4380043 < baseStart_4380043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380066 : List Nat := [3, 3, 1, 2, 1, 2, 3, 8]
def baseStart_4380066 : Nat := 118140960795 + 4380066 * 2 ^ 59
def prefixEnd_4380066 : Nat := 4983230072969 + 3 ^ 40 * 4380066 * 2
def baseEnd_4380066 : Nat := 83299228015413526123387

theorem tailTrace_4380066 : CollatzResearch.WordTrace tailWord_4380066 prefixEnd_4380066 83299228015413526123387 := by
  unfold tailWord_4380066
  simp only [CollatzResearch.WordTrace]
  refine ⟨39938532837444103140538013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106502754233184275041434701 39938532837444103140538013)
  ·
    refine ⟨14976949814041538677701755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39938532837444103140538013 14976949814041538677701755)
    ·
      refine ⟨22465424721062308016552633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14976949814041538677701755 22465424721062308016552633)
      ·
        refine ⟨16849068540796731012414475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22465424721062308016552633 16849068540796731012414475)
        ·
          refine ⟨25273602811195096518621713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16849068540796731012414475 25273602811195096518621713)
          ·
            refine ⟨18955202108396322388966285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25273602811195096518621713 18955202108396322388966285)
            ·
              refine ⟨7108200790648620895862357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18955202108396322388966285 7108200790648620895862357)
              ·
                refine ⟨83299228015413526123387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7108200790648620895862357 83299228015413526123387)
                ·
                  rfl

theorem cell23_4380066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_4380066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380066 prefixEnd_4380066 := by exact prefixLift 4380066
  have htrace : WordTrace (prefixWord ++ tailWord_4380066) baseStart_4380066 baseEnd_4380066 := by
    simpa [prefixWord, tailWord_4380066, baseEnd_4380066] using wordTrace_append hprefix tailTrace_4380066
  have hstable : (prefixWord ++ tailWord_4380066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380066).length < 2 ^ (prefixWord ++ tailWord_4380066).sum := by decide
  have hdescent : baseEnd_4380066 < baseStart_4380066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380076 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_4380076 : Nat := 118140960795 + 4380076 * 2 ^ 59
def prefixEnd_4380076 : Nat := 4983230072969 + 3 ^ 40 * 4380076 * 2
def baseEnd_4380076 : Nat := 2249084291222710166206403

theorem tailTrace_4380076 : CollatzResearch.WordTrace tailWord_4380076 prefixEnd_4380076 2249084291222710166206403 := by
  unfold tailWord_4380076
  simp only [CollatzResearch.WordTrace]
  refine ⟨79877248039870092135008041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106502997386493456180010721 79877248039870092135008041)
  ·
    refine ⟨59907936029902569101256031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79877248039870092135008041 59907936029902569101256031)
    ·
      refine ⟨89861904044853853651884047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59907936029902569101256031 89861904044853853651884047)
      ·
        refine ⟨134792856067280780477826071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89861904044853853651884047 134792856067280780477826071)
        ·
          refine ⟨202189284100921170716739107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134792856067280780477826071 202189284100921170716739107)
          ·
            refine ⟨303283926151381756075108661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202189284100921170716739107 303283926151381756075108661)
            ·
              refine ⟨28432868076692039632041437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 303283926151381756075108661 28432868076692039632041437)
              ·
                refine ⟨10662325528759514862015539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28432868076692039632041437 10662325528759514862015539)
                ·
                  refine ⟨15993488293139272293023309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10662325528759514862015539 15993488293139272293023309)
                  ·
                    refine ⟨5997558109927227109883741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15993488293139272293023309 5997558109927227109883741)
                    ·
                      refine ⟨2249084291222710166206403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997558109927227109883741 2249084291222710166206403)
                      ·
                        rfl

theorem cell23_4380076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_4380076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380076 prefixEnd_4380076 := by exact prefixLift 4380076
  have htrace : WordTrace (prefixWord ++ tailWord_4380076) baseStart_4380076 baseEnd_4380076 := by
    simpa [prefixWord, tailWord_4380076, baseEnd_4380076] using wordTrace_append hprefix tailTrace_4380076
  have hstable : (prefixWord ++ tailWord_4380076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380076).length < 2 ^ (prefixWord ++ tailWord_4380076).sum := by decide
  have hdescent : baseEnd_4380076 < baseStart_4380076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380077 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4380077 : Nat := 118140960795 + 4380077 * 2 ^ 59
def prefixEnd_4380077 : Nat := 4983230072969 + 3 ^ 40 * 4380077 * 2
def baseEnd_4380077 : Nat := 2249084804703364662293899

theorem tailTrace_4380077 : CollatzResearch.WordTrace tailWord_4380077 prefixEnd_4380077 2249084804703364662293899 := by
  unfold tailWord_4380077
  simp only [CollatzResearch.WordTrace]
  refine ⟨159754532552736561440802485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106503021701824374293868323 159754532552736561440802485)
  ·
    refine ⟨14976987426819052635075233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159754532552736561440802485 14976987426819052635075233)
    ·
      refine ⟨11232740570114289476306425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14976987426819052635075233 11232740570114289476306425)
      ·
        refine ⟨8424555427585717107229819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11232740570114289476306425 8424555427585717107229819)
        ·
          refine ⟨12636833141378575660844729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8424555427585717107229819 12636833141378575660844729)
          ·
            refine ⟨9477624856033931745633547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12636833141378575660844729 9477624856033931745633547)
            ·
              refine ⟨14216437284050897618450321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9477624856033931745633547 14216437284050897618450321)
              ·
                refine ⟨10662327963038173213837741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14216437284050897618450321 10662327963038173213837741)
                ·
                  refine ⟨3998372986139314955189153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10662327963038173213837741 3998372986139314955189153)
                  ·
                    refine ⟨2998779739604486216391865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3998372986139314955189153 2998779739604486216391865)
                    ·
                      refine ⟨2249084804703364662293899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2998779739604486216391865 2249084804703364662293899)
                      ·
                        rfl

theorem cell23_4380077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4380077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380077 prefixEnd_4380077 := by exact prefixLift 4380077
  have htrace : WordTrace (prefixWord ++ tailWord_4380077) baseStart_4380077 baseEnd_4380077 := by
    simpa [prefixWord, tailWord_4380077, baseEnd_4380077] using wordTrace_append hprefix tailTrace_4380077
  have hstable : (prefixWord ++ tailWord_4380077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380077).length < 2 ^ (prefixWord ++ tailWord_4380077).sum := by decide
  have hdescent : baseEnd_4380077 < baseStart_4380077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380093 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_4380093 : Nat := 118140960795 + 4380093 * 2 ^ 59
def prefixEnd_4380093 : Nat := 4983230072969 + 3 ^ 40 * 4380093 * 2
def baseEnd_4380093 : Nat := 2249093020393836599693825

theorem tailTrace_4380093 : CollatzResearch.WordTrace tailWord_4380093 prefixEnd_4380093 2249093020393836599693825 := by
  unfold tailWord_4380093
  simp only [CollatzResearch.WordTrace]
  refine ⟨159755116120678596173384933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106503410747119064115589955 159755116120678596173384933)
  ·
    refine ⟨29954084272627236782509675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159755116120678596173384933 29954084272627236782509675)
    ·
      refine ⟨44931126408940855173764513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29954084272627236782509675 44931126408940855173764513)
      ·
        refine ⟨33698344806705641380323385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44931126408940855173764513 33698344806705641380323385)
        ·
          refine ⟨25273758605029231035242539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33698344806705641380323385 25273758605029231035242539)
          ·
            refine ⟨37910637907543846552863809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25273758605029231035242539 37910637907543846552863809)
            ·
              refine ⟨28432978430657884914647857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37910637907543846552863809 28432978430657884914647857)
              ·
                refine ⟨21324733822993413685985893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28432978430657884914647857 21324733822993413685985893)
                ·
                  refine ⟨3998387591811265066122355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21324733822993413685985893 3998387591811265066122355)
                  ·
                    refine ⟨5997581387716897599183533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998387591811265066122355 5997581387716897599183533)
                    ·
                      refine ⟨2249093020393836599693825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997581387716897599183533 2249093020393836599693825)
                      ·
                        rfl

theorem cell23_4380093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_4380093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380093 prefixEnd_4380093 := by exact prefixLift 4380093
  have htrace : WordTrace (prefixWord ++ tailWord_4380093) baseStart_4380093 baseEnd_4380093 := by
    simpa [prefixWord, tailWord_4380093, baseEnd_4380093] using wordTrace_append hprefix tailTrace_4380093
  have hstable : (prefixWord ++ tailWord_4380093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380093).length < 2 ^ (prefixWord ++ tailWord_4380093).sum := by decide
  have hdescent : baseEnd_4380093 < baseStart_4380093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380110 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_4380110 : Nat := 118140960795 + 4380110 * 2 ^ 59
def prefixEnd_4380110 : Nat := 4983230072969 + 3 ^ 40 * 4380110 * 2
def baseEnd_4380110 : Nat := 2249101749564963033181247

theorem tailTrace_4380110 : CollatzResearch.WordTrace tailWord_4380110 prefixEnd_4380110 2249101749564963033181247 := by
  unfold tailWord_4380110
  simp only [CollatzResearch.WordTrace]
  refine ⟨19969467020202126009594223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106503824107744672051169189 19969467020202126009594223)
  ·
    refine ⟨29954200530303189014391335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19969467020202126009594223 29954200530303189014391335)
    ·
      refine ⟨44931300795454783521587003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29954200530303189014391335 44931300795454783521587003)
      ·
        refine ⟨67396951193182175282380505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44931300795454783521587003 67396951193182175282380505)
        ·
          refine ⟨50547713394886631461785379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67396951193182175282380505 50547713394886631461785379)
          ·
            refine ⟨75821570092329947192678069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50547713394886631461785379 75821570092329947192678069)
            ·
              refine ⟨7108272196155932549313569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75821570092329947192678069 7108272196155932549313569)
              ·
                refine ⟨5331204147116949411985177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7108272196155932549313569 5331204147116949411985177)
                ·
                  refine ⟨3998403110337712058988883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5331204147116949411985177 3998403110337712058988883)
                  ·
                    refine ⟨5997604665506568088483325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998403110337712058988883 5997604665506568088483325)
                    ·
                      refine ⟨2249101749564963033181247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997604665506568088483325 2249101749564963033181247)
                      ·
                        rfl

theorem cell23_4380110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_4380110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380110 prefixEnd_4380110 := by exact prefixLift 4380110
  have htrace : WordTrace (prefixWord ++ tailWord_4380110) baseStart_4380110 baseEnd_4380110 := by
    simpa [prefixWord, tailWord_4380110, baseEnd_4380110] using wordTrace_append hprefix tailTrace_4380110
  have hstable : (prefixWord ++ tailWord_4380110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380110).length < 2 ^ (prefixWord ++ tailWord_4380110).sum := by decide
  have hdescent : baseEnd_4380110 < baseStart_4380110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380136 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4380136 : Nat := 118140960795 + 4380136 * 2 ^ 59
def prefixEnd_4380136 : Nat := 4983230072969 + 3 ^ 40 * 4380136 * 2
def baseEnd_4380136 : Nat := 2249115100061979931456127

theorem tailTrace_4380136 : CollatzResearch.WordTrace tailWord_4380136 prefixEnd_4380136 2249115100061979931456127 := by
  unfold tailWord_4380136
  simp only [CollatzResearch.WordTrace]
  refine ⟨79878342229761407258600131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106504456306348543011466841 79878342229761407258600131)
  ·
    refine ⟨119817513344642110887900197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79878342229761407258600131 119817513344642110887900197)
    ·
      refine ⟨22465783752120395791481287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119817513344642110887900197 22465783752120395791481287)
      ·
        refine ⟨33698675628180593687221931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22465783752120395791481287 33698675628180593687221931)
        ·
          refine ⟨50548013442270890530832897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33698675628180593687221931 50548013442270890530832897)
          ·
            refine ⟨37911010081703167898124673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50548013442270890530832897 37911010081703167898124673)
            ·
              refine ⟨28433257561277375923593505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37911010081703167898124673 28433257561277375923593505)
              ·
                refine ⟨21324943170958031942695129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28433257561277375923593505 21324943170958031942695129)
                ·
                  refine ⟨15993707378218523957021347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21324943170958031942695129 15993707378218523957021347)
                  ·
                    refine ⟨23990561067327785935532021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15993707378218523957021347 23990561067327785935532021)
                    ·
                      refine ⟨2249115100061979931456127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23990561067327785935532021 2249115100061979931456127)
                      ·
                        rfl

theorem cell23_4380136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4380136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380136 prefixEnd_4380136 := by exact prefixLift 4380136
  have htrace : WordTrace (prefixWord ++ tailWord_4380136) baseStart_4380136 baseEnd_4380136 := by
    simpa [prefixWord, tailWord_4380136, baseEnd_4380136] using wordTrace_append hprefix tailTrace_4380136
  have hstable : (prefixWord ++ tailWord_4380136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380136).length < 2 ^ (prefixWord ++ tailWord_4380136).sum := by decide
  have hdescent : baseEnd_4380136 < baseStart_4380136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380139 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 9]
def baseStart_4380139 : Nat := 118140960795 + 4380139 * 2 ^ 59
def prefixEnd_4380139 : Nat := 4983230072969 + 3 ^ 40 * 4380139 * 2
def baseEnd_4380139 : Nat := 249901848944882602190957

theorem tailTrace_4380139 : CollatzResearch.WordTrace tailWord_4380139 prefixEnd_4380139 249901848944882602190957 := by
  unfold tailWord_4380139
  simp only [CollatzResearch.WordTrace]
  refine ⟨159756793878511946029559471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106504529252341297353039647 159756793878511946029559471)
  ·
    refine ⟨239635190817767919044339207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159756793878511946029559471 239635190817767919044339207)
    ·
      refine ⟨359452786226651878566508811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239635190817767919044339207 359452786226651878566508811)
      ·
        refine ⟨539179179339977817849763217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359452786226651878566508811 539179179339977817849763217)
        ·
          refine ⟨404384384504983363387322413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539179179339977817849763217 404384384504983363387322413)
          ·
            refine ⟨151644144189368761270245905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 404384384504983363387322413 151644144189368761270245905)
            ·
              refine ⟨113733108142026570952684429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151644144189368761270245905 113733108142026570952684429)
              ·
                refine ⟨42649915553259964107256661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113733108142026570952684429 42649915553259964107256661)
                ·
                  refine ⟨249901848944882602190957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42649915553259964107256661 249901848944882602190957)
                  ·
                    rfl

theorem cell23_4380139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 9].length) (baseStart_4380139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380139 prefixEnd_4380139 := by exact prefixLift 4380139
  have htrace : WordTrace (prefixWord ++ tailWord_4380139) baseStart_4380139 baseEnd_4380139 := by
    simpa [prefixWord, tailWord_4380139, baseEnd_4380139] using wordTrace_append hprefix tailTrace_4380139
  have hstable : (prefixWord ++ tailWord_4380139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380139).length < 2 ^ (prefixWord ++ tailWord_4380139).sum := by decide
  have hdescent : baseEnd_4380139 < baseStart_4380139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380186 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_4380186 : Nat := 118140960795 + 4380186 * 2 ^ 59
def prefixEnd_4380186 : Nat := 4983230072969 + 3 ^ 40 * 4380186 * 2
def baseEnd_4380186 : Nat := 749713591364901578610299

theorem tailTrace_4380186 : CollatzResearch.WordTrace tailWord_4380186 prefixEnd_4380186 749713591364901578610299 := by
  unfold tailWord_4380186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39939627027335418264130103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106505672072894448704346941 39939627027335418264130103)
  ·
    refine ⟨59909440541003127396195155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39939627027335418264130103 59909440541003127396195155)
    ·
      refine ⟨89864160811504691094292733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59909440541003127396195155 89864160811504691094292733)
      ·
        refine ⟨33699060304314259160359775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89864160811504691094292733 33699060304314259160359775)
        ·
          refine ⟨50548590456471388740539663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33699060304314259160359775 50548590456471388740539663)
          ·
            refine ⟨75822885684707083110809495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50548590456471388740539663 75822885684707083110809495)
            ·
              refine ⟨113734328527060624666214243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75822885684707083110809495 113734328527060624666214243)
              ·
                refine ⟨170601492790590936999321365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113734328527060624666214243 170601492790590936999321365)
                ·
                  refine ⟨7996944974558950171843189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170601492790590936999321365 7996944974558950171843189)
                  ·
                    refine ⟨749713591364901578610299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7996944974558950171843189 749713591364901578610299)
                    ·
                      rfl

theorem cell23_4380186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_4380186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380186 prefixEnd_4380186 := by exact prefixLift 4380186
  have htrace : WordTrace (prefixWord ++ tailWord_4380186) baseStart_4380186 baseEnd_4380186 := by
    simpa [prefixWord, tailWord_4380186, baseEnd_4380186] using wordTrace_append hprefix tailTrace_4380186
  have hstable : (prefixWord ++ tailWord_4380186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380186).length < 2 ^ (prefixWord ++ tailWord_4380186).sum := by decide
  have hdescent : baseEnd_4380186 < baseStart_4380186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380223 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_4380223 : Nat := 118140960795 + 4380223 * 2 ^ 59
def prefixEnd_4380223 : Nat := 4983230072969 + 3 ^ 40 * 4380223 * 2
def baseEnd_4380223 : Nat := 2249159772878921091068227

theorem tailTrace_4380223 : CollatzResearch.WordTrace tailWord_4380223 prefixEnd_4380223 2249159772878921091068227 := by
  unfold tailWord_4380223
  simp only [CollatzResearch.WordTrace]
  refine ⟨159759857610207628375617323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106506571740138418917078215 159759857610207628375617323)
  ·
    refine ⟨239639786415311442563425985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159759857610207628375617323 239639786415311442563425985)
    ·
      refine ⟨179729839811483581922569489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239639786415311442563425985 179729839811483581922569489)
      ·
        refine ⟨134797379858612686441927117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179729839811483581922569489 134797379858612686441927117)
        ·
          refine ⟨50549017446979757415722669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134797379858612686441927117 50549017446979757415722669)
          ·
            refine ⟨18955881542617409030896001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50549017446979757415722669 18955881542617409030896001)
            ·
              refine ⟨14216911156963056773172001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18955881542617409030896001 14216911156963056773172001)
              ·
                refine ⟨10662683367722292579879001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14216911156963056773172001 10662683367722292579879001)
                ·
                  refine ⟨7997012525791719434909251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10662683367722292579879001 7997012525791719434909251)
                  ·
                    refine ⟨11995518788687579152363877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7997012525791719434909251 11995518788687579152363877)
                    ·
                      refine ⟨2249159772878921091068227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11995518788687579152363877 2249159772878921091068227)
                      ·
                        rfl

theorem cell23_4380223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_4380223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380223 prefixEnd_4380223 := by exact prefixLift 4380223
  have htrace : WordTrace (prefixWord ++ tailWord_4380223) baseStart_4380223 baseEnd_4380223 := by
    simpa [prefixWord, tailWord_4380223, baseEnd_4380223] using wordTrace_append hprefix tailTrace_4380223
  have hstable : (prefixWord ++ tailWord_4380223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380223).length < 2 ^ (prefixWord ++ tailWord_4380223).sum := by decide
  have hdescent : baseEnd_4380223 < baseStart_4380223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380260 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_4380260 : Nat := 118140960795 + 4380260 * 2 ^ 59
def prefixEnd_4380260 : Nat := 4983230072969 + 3 ^ 40 * 4380260 * 2
def baseEnd_4380260 : Nat := 2249178771663137446305557

theorem tailTrace_4380260 : CollatzResearch.WordTrace tailWord_4380260 prefixEnd_4380260 2249178771663137446305557 := by
  unfold tailWord_4380260
  simp only [CollatzResearch.WordTrace]
  refine ⟨79880603555536791847357117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106507471407382389129809489 79880603555536791847357117)
  ·
    refine ⟨29955226333326296942758919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79880603555536791847357117 29955226333326296942758919)
    ·
      refine ⟨44932839499989445414138379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29955226333326296942758919 44932839499989445414138379)
      ·
        refine ⟨67399259249984168121207569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44932839499989445414138379 67399259249984168121207569)
        ·
          refine ⟨50549444437488126090905677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67399259249984168121207569 50549444437488126090905677)
          ·
            refine ⟨18956041664058047284089629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50549444437488126090905677 18956041664058047284089629)
            ·
              refine ⟨7108515624021767731533611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18956041664058047284089629 7108515624021767731533611)
              ·
                refine ⟨10662773436032651597300417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108515624021767731533611 10662773436032651597300417)
                ·
                  refine ⟨7997080077024488697975313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10662773436032651597300417 7997080077024488697975313)
                  ·
                    refine ⟨5997810057768366523481485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7997080077024488697975313 5997810057768366523481485)
                    ·
                      refine ⟨2249178771663137446305557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997810057768366523481485 2249178771663137446305557)
                      ·
                        rfl

theorem cell23_4380260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_4380260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380260 prefixEnd_4380260 := by exact prefixLift 4380260
  have htrace : WordTrace (prefixWord ++ tailWord_4380260) baseStart_4380260 baseEnd_4380260 := by
    simpa [prefixWord, tailWord_4380260, baseEnd_4380260] using wordTrace_append hprefix tailTrace_4380260
  have hstable : (prefixWord ++ tailWord_4380260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380260).length < 2 ^ (prefixWord ++ tailWord_4380260).sum := by decide
  have hdescent : baseEnd_4380260 < baseStart_4380260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380323 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 6, 4]
def baseStart_4380323 : Nat := 118140960795 + 4380323 * 2 ^ 59
def prefixEnd_4380323 : Nat := 4983230072969 + 3 ^ 40 * 4380323 * 2
def baseEnd_4380323 : Nat := 749737040314790233272589

theorem tailTrace_4380323 : CollatzResearch.WordTrace tailWord_4380323 prefixEnd_4380323 749737040314790233272589 := by
  unfold tailWord_4380323
  simp only [CollatzResearch.WordTrace]
  refine ⟨159763504909845345454257623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106509003273230230302838415 159763504909845345454257623)
  ·
    refine ⟨239645257364768018181386435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159763504909845345454257623 239645257364768018181386435)
    ·
      refine ⟨359467886047152027272079653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239645257364768018181386435 359467886047152027272079653)
      ·
        refine ⟨67400228633841005113514935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 359467886047152027272079653 67400228633841005113514935)
        ·
          refine ⟨101100342950761507670272403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67400228633841005113514935 101100342950761507670272403)
          ·
            refine ⟨151650514426142261505408605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101100342950761507670272403 151650514426142261505408605)
            ·
              refine ⟨56868942909803348064528227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151650514426142261505408605 56868942909803348064528227)
              ·
                refine ⟨85303414364705022096792341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56868942909803348064528227 85303414364705022096792341)
                ·
                  refine ⟨3998597548345547910787141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85303414364705022096792341 3998597548345547910787141)
                  ·
                    refine ⟨749737040314790233272589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998597548345547910787141 749737040314790233272589)
                    ·
                      rfl

theorem cell23_4380323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 4].length) (baseStart_4380323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380323 prefixEnd_4380323 := by exact prefixLift 4380323
  have htrace : WordTrace (prefixWord ++ tailWord_4380323) baseStart_4380323 baseEnd_4380323 := by
    simpa [prefixWord, tailWord_4380323, baseEnd_4380323] using wordTrace_append hprefix tailTrace_4380323
  have hstable : (prefixWord ++ tailWord_4380323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380323).length < 2 ^ (prefixWord ++ tailWord_4380323).sum := by decide
  have hdescent : baseEnd_4380323 < baseStart_4380323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380324 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_4380324 : Nat := 118140960795 + 4380324 * 2 ^ 59
def prefixEnd_4380324 : Nat := 4983230072969 + 3 ^ 40 * 4380324 * 2
def baseEnd_4380324 : Nat := 2249211634425025195905263

theorem tailTrace_4380324 : CollatzResearch.WordTrace tailWord_4380324 prefixEnd_4380324 2249211634425025195905263 := by
  unfold tailWord_4380324
  simp only [CollatzResearch.WordTrace]
  refine ⟨79881770691420861312522013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106509027588561148416696017 79881770691420861312522013)
  ·
    refine ⟨29955664009282822992195755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79881770691420861312522013 29955664009282822992195755)
    ·
      refine ⟨44933496013924234488293633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29955664009282822992195755 44933496013924234488293633)
      ·
        refine ⟨33700122010443175866220225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44933496013924234488293633 33700122010443175866220225)
        ·
          refine ⟨25275091507832381899665169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33700122010443175866220225 25275091507832381899665169)
          ·
            refine ⟨18956318630874286424748877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25275091507832381899665169 18956318630874286424748877)
            ·
              refine ⟨7108619486577857409280829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18956318630874286424748877 7108619486577857409280829)
              ·
                refine ⟨2665732307466696528480311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7108619486577857409280829 2665732307466696528480311)
                ·
                  refine ⟨3998598461200044792720467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665732307466696528480311 3998598461200044792720467)
                  ·
                    refine ⟨5997897691800067189080701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998598461200044792720467 5997897691800067189080701)
                    ·
                      refine ⟨2249211634425025195905263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997897691800067189080701 2249211634425025195905263)
                      ·
                        rfl

theorem cell23_4380324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_4380324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380324 prefixEnd_4380324 := by exact prefixLift 4380324
  have htrace : WordTrace (prefixWord ++ tailWord_4380324) baseStart_4380324 baseEnd_4380324 := by
    simpa [prefixWord, tailWord_4380324, baseEnd_4380324] using wordTrace_append hprefix tailTrace_4380324
  have hstable : (prefixWord ++ tailWord_4380324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380324).length < 2 ^ (prefixWord ++ tailWord_4380324).sum := by decide
  have hdescent : baseEnd_4380324 < baseStart_4380324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380336 : List Nat := [2, 1, 1, 1, 2, 1, 15]
def baseStart_4380336 : Nat := 118140960795 + 4380336 * 2 ^ 59
def prefixEnd_4380336 : Nat := 4983230072969 + 3 ^ 40 * 4380336 * 2
def baseEnd_4380336 : Nat := 27768120940652828999447

theorem tailTrace_4380336 : CollatzResearch.WordTrace tailWord_4380336 prefixEnd_4380336 27768120940652828999447 := by
  unfold tailWord_4380336
  simp only [CollatzResearch.WordTrace]
  refine ⟨79881989529399124337240431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106509319372532165782987241 79881989529399124337240431)
  ·
    refine ⟨119822984294098686505860647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79881989529399124337240431 119822984294098686505860647)
    ·
      refine ⟨179734476441148029758790971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119822984294098686505860647 179734476441148029758790971)
      ·
        refine ⟨269601714661722044638186457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179734476441148029758790971 269601714661722044638186457)
        ·
          refine ⟨202201285996291533478639843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269601714661722044638186457 202201285996291533478639843)
          ·
            refine ⟨303301928994437300217959765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202201285996291533478639843 303301928994437300217959765)
            ·
              refine ⟨27768120940652828999447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 303301928994437300217959765 27768120940652828999447)
              ·
                rfl

theorem cell23_4380336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 15].length) (baseStart_4380336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380336 prefixEnd_4380336 := by exact prefixLift 4380336
  have htrace : WordTrace (prefixWord ++ tailWord_4380336) baseStart_4380336 baseEnd_4380336 := by
    simpa [prefixWord, tailWord_4380336, baseEnd_4380336] using wordTrace_append hprefix tailTrace_4380336
  have hstable : (prefixWord ++ tailWord_4380336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380336).length < 2 ^ (prefixWord ++ tailWord_4380336).sum := by decide
  have hdescent : baseEnd_4380336 < baseStart_4380336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380341 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4380341 : Nat := 118140960795 + 4380341 * 2 ^ 59
def prefixEnd_4380341 : Nat := 4983230072969 + 3 ^ 40 * 4380341 * 2
def baseEnd_4380341 : Nat := 2249220363596151629392685

theorem tailTrace_4380341 : CollatzResearch.WordTrace tailWord_4380341 prefixEnd_4380341 2249220363596151629392685 := by
  unfold tailWord_4380341
  simp only [CollatzResearch.WordTrace]
  refine ⟨159764161423780134528412877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106509440949186756352275251 159764161423780134528412877)
  ·
    refine ⟨59911560533917550448154829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159764161423780134528412877 59911560533917550448154829)
    ·
      refine ⟨22466835200219081418058061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59911560533917550448154829 22466835200219081418058061)
      ·
        refine ⟨8425063200082155531771773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22466835200219081418058061 8425063200082155531771773)
        ·
          refine ⟨3159398700030808324414415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8425063200082155531771773 3159398700030808324414415)
          ·
            refine ⟨4739098050046212486621623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159398700030808324414415 4739098050046212486621623)
            ·
              refine ⟨7108647075069318729932435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739098050046212486621623 7108647075069318729932435)
              ·
                refine ⟨10662970612603978094898653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108647075069318729932435 10662970612603978094898653)
                ·
                  refine ⟨3998613979726491785586995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10662970612603978094898653 3998613979726491785586995)
                  ·
                    refine ⟨5997920969589737678380493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998613979726491785586995 5997920969589737678380493)
                    ·
                      refine ⟨2249220363596151629392685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997920969589737678380493 2249220363596151629392685)
                      ·
                        rfl

theorem cell23_4380341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4380341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380341 prefixEnd_4380341 := by exact prefixLift 4380341
  have htrace : WordTrace (prefixWord ++ tailWord_4380341) baseStart_4380341 baseEnd_4380341 := by
    simpa [prefixWord, tailWord_4380341, baseEnd_4380341] using wordTrace_append hprefix tailTrace_4380341
  have hstable : (prefixWord ++ tailWord_4380341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380341).length < 2 ^ (prefixWord ++ tailWord_4380341).sum := by decide
  have hdescent : baseEnd_4380341 < baseStart_4380341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380343 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_4380343 : Nat := 118140960795 + 4380343 * 2 ^ 59
def prefixEnd_4380343 : Nat := 4983230072969 + 3 ^ 40 * 4380343 * 2
def baseEnd_4380343 : Nat := 2249221390557460621567675

theorem tailTrace_4380343 : CollatzResearch.WordTrace tailWord_4380343 prefixEnd_4380343 2249221390557460621567675 := by
  unfold tailWord_4380343
  simp only [CollatzResearch.WordTrace]
  refine ⟨159764234369772888869985683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106509489579848592579990455 159764234369772888869985683)
  ·
    refine ⟨239646351554659333304978525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159764234369772888869985683 239646351554659333304978525)
    ·
      refine ⟨89867381832997249989366947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239646351554659333304978525 89867381832997249989366947)
      ·
        refine ⟨134801072749495874984050421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89867381832997249989366947 134801072749495874984050421)
        ·
          refine ⟨12637600570265238279754727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134801072749495874984050421 12637600570265238279754727)
          ·
            refine ⟨18956400855397857419632091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12637600570265238279754727 18956400855397857419632091)
            ·
              refine ⟨28434601283096786129448137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18956400855397857419632091 28434601283096786129448137)
              ·
                refine ⟨21325950962322589597086103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28434601283096786129448137 21325950962322589597086103)
                ·
                  refine ⟨31988926443483884395629155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21325950962322589597086103 31988926443483884395629155)
                  ·
                    refine ⟨47983389665225826593443733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31988926443483884395629155 47983389665225826593443733)
                    ·
                      refine ⟨2249221390557460621567675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47983389665225826593443733 2249221390557460621567675)
                      ·
                        rfl

theorem cell23_4380343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_4380343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380343 prefixEnd_4380343 := by exact prefixLift 4380343
  have htrace : WordTrace (prefixWord ++ tailWord_4380343) baseStart_4380343 baseEnd_4380343 := by
    simpa [prefixWord, tailWord_4380343, baseEnd_4380343] using wordTrace_append hprefix tailTrace_4380343
  have hstable : (prefixWord ++ tailWord_4380343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380343).length < 2 ^ (prefixWord ++ tailWord_4380343).sum := by decide
  have hdescent : baseEnd_4380343 < baseStart_4380343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380350 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4380350 : Nat := 118140960795 + 4380350 * 2 ^ 59
def prefixEnd_4380350 : Nat := 4983230072969 + 3 ^ 40 * 4380350 * 2
def baseEnd_4380350 : Nat := 2249224984922042094180143

theorem tailTrace_4380350 : CollatzResearch.WordTrace tailWord_4380350 prefixEnd_4380350 2249224984922042094180143 := by
  unfold tailWord_4380350
  simp only [CollatzResearch.WordTrace]
  refine ⟨19970561210093441133186313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106509659787165019376993669 19970561210093441133186313)
  ·
    refine ⟨14977920907570080849889735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19970561210093441133186313 14977920907570080849889735)
    ·
      refine ⟨22466881361355121274834603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14977920907570080849889735 22466881361355121274834603)
      ·
        refine ⟨33700322042032681912251905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22466881361355121274834603 33700322042032681912251905)
        ·
          refine ⟨25275241531524511434188929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33700322042032681912251905 25275241531524511434188929)
          ·
            refine ⟨18956431148643383575641697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25275241531524511434188929 18956431148643383575641697)
            ·
              refine ⟨14217323361482537681731273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18956431148643383575641697 14217323361482537681731273)
              ·
                refine ⟨10662992521111903261298455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14217323361482537681731273 10662992521111903261298455)
                ·
                  refine ⟨15994488781667854891947683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10662992521111903261298455 15994488781667854891947683)
                  ·
                    refine ⟨23991733172501782337921525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15994488781667854891947683 23991733172501782337921525)
                    ·
                      refine ⟨2249224984922042094180143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23991733172501782337921525 2249224984922042094180143)
                      ·
                        rfl

theorem cell23_4380350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4380350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380350 prefixEnd_4380350 := by exact prefixLift 4380350
  have htrace : WordTrace (prefixWord ++ tailWord_4380350) baseStart_4380350 baseEnd_4380350 := by
    simpa [prefixWord, tailWord_4380350, baseEnd_4380350] using wordTrace_append hprefix tailTrace_4380350
  have hstable : (prefixWord ++ tailWord_4380350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380350).length < 2 ^ (prefixWord ++ tailWord_4380350).sum := by decide
  have hdescent : baseEnd_4380350 < baseStart_4380350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380363 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 3]
def baseStart_4380363 : Nat := 118140960795 + 4380363 * 2 ^ 59
def prefixEnd_4380363 : Nat := 4983230072969 + 3 ^ 40 * 4380363 * 2
def baseEnd_4380363 : Nat := 2249231660170550543317583

theorem tailTrace_4380363 : CollatzResearch.WordTrace tailWord_4380363 prefixEnd_4380363 2249231660170550543317583 := by
  unfold tailWord_4380363
  simp only [CollatzResearch.WordTrace]
  refine ⟨159764963829700432285713743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106509975886466954857142495 159764963829700432285713743)
  ·
    refine ⟨239647445744550648428570615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159764963829700432285713743 239647445744550648428570615)
    ·
      refine ⟨359471168616825972642855923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239647445744550648428570615 359471168616825972642855923)
      ·
        refine ⟨539206752925238958964283885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359471168616825972642855923 539206752925238958964283885)
        ·
          refine ⟨202202532346964609611606457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539206752925238958964283885 202202532346964609611606457)
          ·
            refine ⟨151651899260223457208704843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202202532346964609611606457 151651899260223457208704843)
            ·
              refine ⟨227477848890335185813057265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151651899260223457208704843 227477848890335185813057265)
              ·
                refine ⟨170608386667751389359792949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227477848890335185813057265 170608386667751389359792949)
                ·
                  refine ⟨15994536250101692752480589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170608386667751389359792949 15994536250101692752480589)
                  ·
                    refine ⟨5997951093788134782180221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15994536250101692752480589 5997951093788134782180221)
                    ·
                      refine ⟨2249231660170550543317583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5997951093788134782180221 2249231660170550543317583)
                      ·
                        rfl

theorem cell23_4380363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 3].length) (baseStart_4380363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380363 prefixEnd_4380363 := by exact prefixLift 4380363
  have htrace : WordTrace (prefixWord ++ tailWord_4380363) baseStart_4380363 baseEnd_4380363 := by
    simpa [prefixWord, tailWord_4380363, baseEnd_4380363] using wordTrace_append hprefix tailTrace_4380363
  have hstable : (prefixWord ++ tailWord_4380363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380363).length < 2 ^ (prefixWord ++ tailWord_4380363).sum := by decide
  have hdescent : baseEnd_4380363 < baseStart_4380363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380364 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4380364 : Nat := 118140960795 + 4380364 * 2 ^ 59
def prefixEnd_4380364 : Nat := 4983230072969 + 3 ^ 40 * 4380364 * 2
def baseEnd_4380364 : Nat := 2249232173651205039405079

theorem tailTrace_4380364 : CollatzResearch.WordTrace tailWord_4380364 prefixEnd_4380364 2249232173651205039405079 := by
  unfold tailWord_4380364
  simp only [CollatzResearch.WordTrace]
  refine ⟨79882500151348404728250073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106510000201797872971000097 79882500151348404728250073)
  ·
    refine ⟨59911875113511303546187555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79882500151348404728250073 59911875113511303546187555)
    ·
      refine ⟨89867812670266955319281333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59911875113511303546187555 89867812670266955319281333)
      ·
        refine ⟨8425107437837527061182625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89867812670266955319281333 8425107437837527061182625)
        ·
          refine ⟨6318830578378145295886969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8425107437837527061182625 6318830578378145295886969)
          ·
            refine ⟨4739122933783608971915227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6318830578378145295886969 4739122933783608971915227)
            ·
              refine ⟨7108684400675413457872841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739122933783608971915227 7108684400675413457872841)
              ·
                refine ⟨5331513300506560093404631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7108684400675413457872841 5331513300506560093404631)
                ·
                  refine ⟨7997269950759840140106947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331513300506560093404631 7997269950759840140106947)
                  ·
                    refine ⟨11995904926139760210160421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7997269950759840140106947 11995904926139760210160421)
                    ·
                      refine ⟨2249232173651205039405079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11995904926139760210160421 2249232173651205039405079)
                      ·
                        rfl

theorem cell23_4380364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4380364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380364 prefixEnd_4380364 := by exact prefixLift 4380364
  have htrace : WordTrace (prefixWord ++ tailWord_4380364) baseStart_4380364 baseEnd_4380364 := by
    simpa [prefixWord, tailWord_4380364, baseEnd_4380364] using wordTrace_append hprefix tailTrace_4380364
  have hstable : (prefixWord ++ tailWord_4380364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380364).length < 2 ^ (prefixWord ++ tailWord_4380364).sum := by decide
  have hdescent : baseEnd_4380364 < baseStart_4380364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380374 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4380374 : Nat := 118140960795 + 4380374 * 2 ^ 59
def prefixEnd_4380374 : Nat := 4983230072969 + 3 ^ 40 * 4380374 * 2
def baseEnd_4380374 : Nat := 749745769485916666760011

theorem tailTrace_4380374 : CollatzResearch.WordTrace tailWord_4380374 prefixEnd_4380374 749745769485916666760011 := by
  unfold tailWord_4380374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985335314541286322772761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106510243355107054109576117 9985335314541286322772761)
  ·
    refine ⟨7489001485905964742079571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9985335314541286322772761 7489001485905964742079571)
    ·
      refine ⟨11233502228858947113119357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7489001485905964742079571 11233502228858947113119357)
      ·
        refine ⟨4212563335822105167419759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11233502228858947113119357 4212563335822105167419759)
        ·
          refine ⟨6318845003733157751129639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212563335822105167419759 6318845003733157751129639)
          ·
            refine ⟨9478267505599736626694459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6318845003733157751129639 9478267505599736626694459)
            ·
              refine ⟨14217401258399604940041689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9478267505599736626694459 14217401258399604940041689)
              ·
                refine ⟨10663050943799703705031267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14217401258399604940041689 10663050943799703705031267)
                ·
                  refine ⟨15994576415699555557546901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10663050943799703705031267 15994576415699555557546901)
                  ·
                    refine ⟨749745769485916666760011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15994576415699555557546901 749745769485916666760011)
                    ·
                      rfl

theorem cell23_4380374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4380374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380374 prefixEnd_4380374 := by exact prefixLift 4380374
  have htrace : WordTrace (prefixWord ++ tailWord_4380374) baseStart_4380374 baseEnd_4380374 := by
    simpa [prefixWord, tailWord_4380374, baseEnd_4380374] using wordTrace_append hprefix tailTrace_4380374
  have hstable : (prefixWord ++ tailWord_4380374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380374).length < 2 ^ (prefixWord ++ tailWord_4380374).sum := by decide
  have hdescent : baseEnd_4380374 < baseStart_4380374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380381 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4380381 : Nat := 118140960795 + 4380381 * 2 ^ 59
def prefixEnd_4380381 : Nat := 4983230072969 + 3 ^ 40 * 4380381 * 2
def baseEnd_4380381 : Nat := 2249240902822331472892501

theorem tailTrace_4380381 : CollatzResearch.WordTrace tailWord_4380381 prefixEnd_4380381 2249240902822331472892501 := by
  unfold tailWord_4380381
  simp only [CollatzResearch.WordTrace]
  refine ⟨159765620343635221359868997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106510413562423480906579331 159765620343635221359868997)
  ·
    refine ⟨29956053814431604004975437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159765620343635221359868997 29956053814431604004975437)
    ·
      refine ⟨11233520180411851501865789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29956053814431604004975437 11233520180411851501865789)
      ·
        refine ⟨4212570067654444313199671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11233520180411851501865789 4212570067654444313199671)
        ·
          refine ⟨6318855101481666469799507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212570067654444313199671 6318855101481666469799507)
          ·
            refine ⟨9478282652222499704699261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6318855101481666469799507 9478282652222499704699261)
            ·
              refine ⟨3554355994583437389262223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9478282652222499704699261 3554355994583437389262223)
              ·
                refine ⟨5331533991875156083893335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554355994583437389262223 5331533991875156083893335)
                ·
                  refine ⟨7997300987812734125840003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331533991875156083893335 7997300987812734125840003)
                  ·
                    refine ⟨11995951481719101188760005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7997300987812734125840003 11995951481719101188760005)
                    ·
                      refine ⟨2249240902822331472892501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11995951481719101188760005 2249240902822331472892501)
                      ·
                        rfl

theorem cell23_4380381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4380381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380381 prefixEnd_4380381 := by exact prefixLift 4380381
  have htrace : WordTrace (prefixWord ++ tailWord_4380381) baseStart_4380381 baseEnd_4380381 := by
    simpa [prefixWord, tailWord_4380381, baseEnd_4380381] using wordTrace_append hprefix tailTrace_4380381
  have hstable : (prefixWord ++ tailWord_4380381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380381).length < 2 ^ (prefixWord ++ tailWord_4380381).sum := by decide
  have hdescent : baseEnd_4380381 < baseStart_4380381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380403 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4]
def baseStart_4380403 : Nat := 118140960795 + 4380403 * 2 ^ 59
def prefixEnd_4380403 : Nat := 4983230072969 + 3 ^ 40 * 4380403 * 2
def baseEnd_4380403 : Nat := 2249252199396730386817399

theorem tailTrace_4380403 : CollatzResearch.WordTrace tailWord_4380403 prefixEnd_4380403 2249252199396730386817399 := by
  unfold tailWord_4380403
  simp only [CollatzResearch.WordTrace]
  refine ⟨159766422749555519117169863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106510948499703679411446575 159766422749555519117169863)
  ·
    refine ⟨239649634124333278675754795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159766422749555519117169863 239649634124333278675754795)
    ·
      refine ⟨359474451186499918013632193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239649634124333278675754795 359474451186499918013632193)
      ·
        refine ⟨269605838389874938510224145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359474451186499918013632193 269605838389874938510224145)
        ·
          refine ⟨202204378792406203882668109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269605838389874938510224145 202204378792406203882668109)
          ·
            refine ⟨75826642047152326456000541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202204378792406203882668109 75826642047152326456000541)
            ·
              refine ⟨28434990767682122421000203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75826642047152326456000541 28434990767682122421000203)
              ·
                refine ⟨42652486151523183631500305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28434990767682122421000203 42652486151523183631500305)
                ·
                  refine ⟨31989364613642387723625229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42652486151523183631500305 31989364613642387723625229)
                  ·
                    refine ⟨11996011730115895396359461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31989364613642387723625229 11996011730115895396359461)
                    ·
                      refine ⟨2249252199396730386817399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11996011730115895396359461 2249252199396730386817399)
                      ·
                        rfl

theorem cell23_4380403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_4380403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380403 prefixEnd_4380403 := by exact prefixLift 4380403
  have htrace : WordTrace (prefixWord ++ tailWord_4380403) baseStart_4380403 baseEnd_4380403 := by
    simpa [prefixWord, tailWord_4380403, baseEnd_4380403] using wordTrace_append hprefix tailTrace_4380403
  have hstable : (prefixWord ++ tailWord_4380403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380403).length < 2 ^ (prefixWord ++ tailWord_4380403).sum := by decide
  have hdescent : baseEnd_4380403 < baseStart_4380403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380404 : List Nat := [2, 6, 1, 1, 1, 3, 1, 8]
def baseStart_4380404 : Nat := 118140960795 + 4380404 * 2 ^ 59
def prefixEnd_4380404 : Nat := 4983230072969 + 3 ^ 40 * 4380404 * 2
def baseEnd_4380404 : Nat := 83305656032495736403885

theorem tailTrace_4380404 : CollatzResearch.WordTrace tailWord_4380404 prefixEnd_4380404 83305656032495736403885 := by
  unfold tailWord_4380404
  simp only [CollatzResearch.WordTrace]
  refine ⟨79883229611275948143978133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106510972815034597525304177 79883229611275948143978133)
  ·
    refine ⟨3744526388028560069248975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79883229611275948143978133 3744526388028560069248975)
    ·
      refine ⟨5616789582042840103873463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744526388028560069248975 5616789582042840103873463)
      ·
        refine ⟨8425184373064260155810195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5616789582042840103873463 8425184373064260155810195)
        ·
          refine ⟨12637776559596390233715293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8425184373064260155810195 12637776559596390233715293)
          ·
            refine ⟨4739166209848646337643235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12637776559596390233715293 4739166209848646337643235)
            ·
              refine ⟨7108749314772969506464853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739166209848646337643235 7108749314772969506464853)
              ·
                refine ⟨83305656032495736403885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7108749314772969506464853 83305656032495736403885)
                ·
                  rfl

theorem cell23_4380404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 8].length) (baseStart_4380404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380404 prefixEnd_4380404 := by exact prefixLift 4380404
  have htrace : WordTrace (prefixWord ++ tailWord_4380404) baseStart_4380404 baseEnd_4380404 := by
    simpa [prefixWord, tailWord_4380404, baseEnd_4380404] using wordTrace_append hprefix tailTrace_4380404
  have hstable : (prefixWord ++ tailWord_4380404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380404).length < 2 ^ (prefixWord ++ tailWord_4380404).sum := by decide
  have hdescent : baseEnd_4380404 < baseStart_4380404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380414 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4380414 : Nat := 118140960795 + 4380414 * 2 ^ 59
def prefixEnd_4380414 : Nat := 4983230072969 + 3 ^ 40 * 4380414 * 2
def baseEnd_4380414 : Nat := 2249257847683929843779849

theorem tailTrace_4380414 : CollatzResearch.WordTrace tailWord_4380414 prefixEnd_4380414 2249257847683929843779849 := by
  unfold tailWord_4380414
  simp only [CollatzResearch.WordTrace]
  refine ⟨19970852994064458499477537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106511215968343778663880197 19970852994064458499477537)
  ·
    refine ⟨14978139745548343874608153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19970852994064458499477537 14978139745548343874608153)
    ·
      refine ⟨11233604809161257905956115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14978139745548343874608153 11233604809161257905956115)
      ·
        refine ⟨16850407213741886858934173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11233604809161257905956115 16850407213741886858934173)
        ·
          refine ⟨6318902705153207572100315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16850407213741886858934173 6318902705153207572100315)
          ·
            refine ⟨9478354057729811358150473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6318902705153207572100315 9478354057729811358150473)
            ·
              refine ⟨7108765543297358518612855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9478354057729811358150473 7108765543297358518612855)
              ·
                refine ⟨10663148314946037777919283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108765543297358518612855 10663148314946037777919283)
                ·
                  refine ⟨15994722472419056666878925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10663148314946037777919283 15994722472419056666878925)
                  ·
                    refine ⟨5998020927157146250079597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15994722472419056666878925 5998020927157146250079597)
                    ·
                      refine ⟨2249257847683929843779849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998020927157146250079597 2249257847683929843779849)
                      ·
                        rfl

theorem cell23_4380414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4380414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380414 prefixEnd_4380414 := by exact prefixLift 4380414
  have htrace : WordTrace (prefixWord ++ tailWord_4380414) baseStart_4380414 baseEnd_4380414 := by
    simpa [prefixWord, tailWord_4380414, baseEnd_4380414] using wordTrace_append hprefix tailTrace_4380414
  have hstable : (prefixWord ++ tailWord_4380414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380414).length < 2 ^ (prefixWord ++ tailWord_4380414).sum := by decide
  have hdescent : baseEnd_4380414 < baseStart_4380414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380433 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_4380433 : Nat := 118140960795 + 4380433 * 2 ^ 59
def prefixEnd_4380433 : Nat := 4983230072969 + 3 ^ 40 * 4380433 * 2
def baseEnd_4380433 : Nat := 2249267603816365269442261

theorem tailTrace_4380433 : CollatzResearch.WordTrace tailWord_4380433 prefixEnd_4380433 2249267603816365269442261 := by
  unfold tailWord_4380433
  simp only [CollatzResearch.WordTrace]
  refine ⟨159767516939446834240761953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106511677959631222827174635 159767516939446834240761953)
  ·
    refine ⟨119825637704585125680571465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159767516939446834240761953 119825637704585125680571465)
    ·
      refine ⟨89869228278438844260428599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119825637704585125680571465 89869228278438844260428599)
      ·
        refine ⟨134803842417658266390642899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89869228278438844260428599 134803842417658266390642899)
        ·
          refine ⟨202205763626487399585964349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134803842417658266390642899 202205763626487399585964349)
          ·
            refine ⟨75827161359932774844736631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202205763626487399585964349 75827161359932774844736631)
            ·
              refine ⟨113740742039899162267104947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75827161359932774844736631 113740742039899162267104947)
              ·
                refine ⟨170611113059848743400657421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113740742039899162267104947 170611113059848743400657421)
                ·
                  refine ⟨63979167397443278775246533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170611113059848743400657421 63979167397443278775246533)
                  ·
                    refine ⟨11996093887020614770358725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63979167397443278775246533 11996093887020614770358725)
                    ·
                      refine ⟨2249267603816365269442261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11996093887020614770358725 2249267603816365269442261)
                      ·
                        rfl

theorem cell23_4380433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_4380433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380433 prefixEnd_4380433 := by exact prefixLift 4380433
  have htrace : WordTrace (prefixWord ++ tailWord_4380433) baseStart_4380433 baseEnd_4380433 := by
    simpa [prefixWord, tailWord_4380433, baseEnd_4380433] using wordTrace_append hprefix tailTrace_4380433
  have hstable : (prefixWord ++ tailWord_4380433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380433).length < 2 ^ (prefixWord ++ tailWord_4380433).sum := by decide
  have hdescent : baseEnd_4380433 < baseStart_4380433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380437 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_4380437 : Nat := 118140960795 + 4380437 * 2 ^ 59
def prefixEnd_4380437 : Nat := 4983230072969 + 3 ^ 40 * 4380437 * 2
def baseEnd_4380437 : Nat := 2249269657738983253792243

theorem tailTrace_4380437 : CollatzResearch.WordTrace tailWord_4380437 prefixEnd_4380437 2249269657738983253792243 := by
  unfold tailWord_4380437
  simp only [CollatzResearch.WordTrace]
  refine ⟨159767662831432342923907565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106511775220954895282605043 159767662831432342923907565)
  ·
    refine ⟨59912873561787128596465337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159767662831432342923907565 59912873561787128596465337)
    ·
      refine ⟨44934655171340346447349003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59912873561787128596465337 44934655171340346447349003)
      ·
        refine ⟨67401982757010519671023505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44934655171340346447349003 67401982757010519671023505)
        ·
          refine ⟨50551487067757889753267629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67401982757010519671023505 50551487067757889753267629)
          ·
            refine ⟨18956807650409208657475361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50551487067757889753267629 18956807650409208657475361)
            ·
              refine ⟨14217605737806906493106521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18956807650409208657475361 14217605737806906493106521)
              ·
                refine ⟨10663204303355179869829891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14217605737806906493106521 10663204303355179869829891)
                ·
                  refine ⟨15994806455032769804744837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10663204303355179869829891 15994806455032769804744837)
                  ·
                    refine ⟨2999026210318644338389657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15994806455032769804744837 2999026210318644338389657)
                    ·
                      refine ⟨2249269657738983253792243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999026210318644338389657 2249269657738983253792243)
                      ·
                        rfl

theorem cell23_4380437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_4380437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380437 prefixEnd_4380437 := by exact prefixLift 4380437
  have htrace : WordTrace (prefixWord ++ tailWord_4380437) baseStart_4380437 baseEnd_4380437 := by
    simpa [prefixWord, tailWord_4380437, baseEnd_4380437] using wordTrace_append hprefix tailTrace_4380437
  have hstable : (prefixWord ++ tailWord_4380437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380437).length < 2 ^ (prefixWord ++ tailWord_4380437).sum := by decide
  have hdescent : baseEnd_4380437 < baseStart_4380437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380450 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4380450 : Nat := 118140960795 + 4380450 * 2 ^ 59
def prefixEnd_4380450 : Nat := 4983230072969 + 3 ^ 40 * 4380450 * 2
def baseEnd_4380450 : Nat := 2249276332987491702929683

theorem tailTrace_4380450 : CollatzResearch.WordTrace tailWord_4380450 prefixEnd_4380450 2249276332987491702929683 := by
  unfold tailWord_4380450
  simp only [CollatzResearch.WordTrace]
  refine ⟨39942034245096311536032701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106512091320256830762753869 39942034245096311536032701)
  ·
    refine ⟨14978262841911116826012263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39942034245096311536032701 14978262841911116826012263)
    ·
      refine ⟨22467394262866675239018395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14978262841911116826012263 22467394262866675239018395)
      ·
        refine ⟨33701091394300012858527593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22467394262866675239018395 33701091394300012858527593)
        ·
          refine ⟨25275818545725009643895695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33701091394300012858527593 25275818545725009643895695)
          ·
            refine ⟨37913727818587514465843543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25275818545725009643895695 37913727818587514465843543)
            ·
              refine ⟨56870591727881271698765315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37913727818587514465843543 56870591727881271698765315)
              ·
                refine ⟨85305887591821907548147973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56870591727881271698765315 85305887591821907548147973)
                ·
                  refine ⟨15994853923466607665277745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85305887591821907548147973 15994853923466607665277745)
                  ·
                    refine ⟨11996140442599955748958309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15994853923466607665277745 11996140442599955748958309)
                    ·
                      refine ⟨2249276332987491702929683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11996140442599955748958309 2249276332987491702929683)
                      ·
                        rfl

theorem cell23_4380450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4380450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380450 prefixEnd_4380450 := by exact prefixLift 4380450
  have htrace : WordTrace (prefixWord ++ tailWord_4380450) baseStart_4380450 baseEnd_4380450 := by
    simpa [prefixWord, tailWord_4380450, baseEnd_4380450] using wordTrace_append hprefix tailTrace_4380450
  have hstable : (prefixWord ++ tailWord_4380450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380450).length < 2 ^ (prefixWord ++ tailWord_4380450).sum := by decide
  have hdescent : baseEnd_4380450 < baseStart_4380450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380460 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 7]
def baseStart_4380460 : Nat := 118140960795 + 4380460 * 2 ^ 59
def prefixEnd_4380460 : Nat := 4983230072969 + 3 ^ 40 * 4380460 * 2
def baseEnd_4380460 : Nat := 249920163088226295978293

theorem tailTrace_4380460 : CollatzResearch.WordTrace tailWord_4380460 prefixEnd_4380460 249920163088226295978293 := by
  unfold tailWord_4380460
  simp only [CollatzResearch.WordTrace]
  refine ⟨79884250855174508925997417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106512334473566011901329889 79884250855174508925997417)
  ·
    refine ⟨59913188141380881694498063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79884250855174508925997417 59913188141380881694498063)
    ·
      refine ⟨89869782212071322541747095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59913188141380881694498063 89869782212071322541747095)
      ·
        refine ⟨134804673318106983812620643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89869782212071322541747095 134804673318106983812620643)
        ·
          refine ⟨202207009977160475718930965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134804673318106983812620643 202207009977160475718930965)
          ·
            refine ⟨9478453592679397299324889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 202207009977160475718930965 9478453592679397299324889)
            ·
              refine ⟨7108840194509547974493667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9478453592679397299324889 7108840194509547974493667)
              ·
                refine ⟨10663260291764321961740501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7108840194509547974493667 10663260291764321961740501)
                ·
                  refine ⟨249920163088226295978293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10663260291764321961740501 249920163088226295978293)
                  ·
                    rfl

theorem cell23_4380460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_4380460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380460 prefixEnd_4380460 := by exact prefixLift 4380460
  have htrace : WordTrace (prefixWord ++ tailWord_4380460) baseStart_4380460 baseEnd_4380460 := by
    simpa [prefixWord, tailWord_4380460, baseEnd_4380460] using wordTrace_append hprefix tailTrace_4380460
  have hstable : (prefixWord ++ tailWord_4380460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380460).length < 2 ^ (prefixWord ++ tailWord_4380460).sum := by decide
  have hdescent : baseEnd_4380460 < baseStart_4380460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380490 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_4380490 : Nat := 118140960795 + 4380490 * 2 ^ 59
def prefixEnd_4380490 : Nat := 4983230072969 + 3 ^ 40 * 4380490 * 2
def baseEnd_4380490 : Nat := 749765624071223848809833

theorem tailTrace_4380490 : CollatzResearch.WordTrace tailWord_4380490 prefixEnd_4380490 749765624071223848809833 := by
  unfold tailWord_4380490
  simp only [CollatzResearch.WordTrace]
  refine ⟨39942398975060083243896731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106513063933493555317057949 39942398975060083243896731)
  ·
    refine ⟨59913598462590124865845097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39942398975060083243896731 59913598462590124865845097)
    ·
      refine ⟨44935198846942593649383823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59913598462590124865845097 44935198846942593649383823)
      ·
        refine ⟨67402798270413890474075735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44935198846942593649383823 67402798270413890474075735)
        ·
          refine ⟨101104197405620835711113603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67402798270413890474075735 101104197405620835711113603)
          ·
            refine ⟨151656296108431253566670405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101104197405620835711113603 151656296108431253566670405)
            ·
              refine ⟨28435555520330860043750701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151656296108431253566670405 28435555520330860043750701)
              ·
                refine ⟨10663333320124072516406513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28435555520330860043750701 10663333320124072516406513)
                ·
                  refine ⟨7997499990093054387304885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10663333320124072516406513 7997499990093054387304885)
                  ·
                    refine ⟨749765624071223848809833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7997499990093054387304885 749765624071223848809833)
                    ·
                      rfl

theorem cell23_4380490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_4380490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380490 prefixEnd_4380490 := by exact prefixLift 4380490
  have htrace : WordTrace (prefixWord ++ tailWord_4380490) baseStart_4380490 baseEnd_4380490 := by
    simpa [prefixWord, tailWord_4380490, baseEnd_4380490] using wordTrace_append hprefix tailTrace_4380490
  have hstable : (prefixWord ++ tailWord_4380490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380490).length < 2 ^ (prefixWord ++ tailWord_4380490).sum := by decide
  have hdescent : baseEnd_4380490 < baseStart_4380490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380522 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4380522 : Nat := 118140960795 + 4380522 * 2 ^ 59
def prefixEnd_4380522 : Nat := 4983230072969 + 3 ^ 40 * 4380522 * 2
def baseEnd_4380522 : Nat := 2249313303594615421229353

theorem tailTrace_4380522 : CollatzResearch.WordTrace tailWord_4380522 prefixEnd_4380522 2249313303594615421229353 := by
  unfold tailWord_4380522
  simp only [CollatzResearch.WordTrace]
  refine ⟨39942690759031100610187955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106513842024082934960501213 39942690759031100610187955)
  ·
    refine ⟨59914036138546650915281933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39942690759031100610187955 59914036138546650915281933)
    ·
      refine ⟨22467763551954994093230725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59914036138546650915281933 22467763551954994093230725)
      ·
        refine ⟨4212705665991561392480761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22467763551954994093230725 4212705665991561392480761)
        ·
          refine ⟨3159529249493671044360571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4212705665991561392480761 3159529249493671044360571)
          ·
            refine ⟨4739293874240506566540857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159529249493671044360571 4739293874240506566540857)
            ·
              refine ⟨3554470405680379924905643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4739293874240506566540857 3554470405680379924905643)
              ·
                refine ⟨5331705608520569887358465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554470405680379924905643 5331705608520569887358465)
                ·
                  refine ⟨3998779206390427415518849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5331705608520569887358465 3998779206390427415518849)
                  ·
                    refine ⟨2999084404792820561639137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3998779206390427415518849 2999084404792820561639137)
                    ·
                      refine ⟨2249313303594615421229353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999084404792820561639137 2249313303594615421229353)
                      ·
                        rfl

theorem cell23_4380522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4380522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380522 prefixEnd_4380522 := by exact prefixLift 4380522
  have htrace : WordTrace (prefixWord ++ tailWord_4380522) baseStart_4380522 baseEnd_4380522 := by
    simpa [prefixWord, tailWord_4380522, baseEnd_4380522] using wordTrace_append hprefix tailTrace_4380522
  have hstable : (prefixWord ++ tailWord_4380522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380522).length < 2 ^ (prefixWord ++ tailWord_4380522).sum := by decide
  have hdescent : baseEnd_4380522 < baseStart_4380522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380547 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 3]
def baseStart_4380547 : Nat := 118140960795 + 4380547 * 2 ^ 59
def prefixEnd_4380547 : Nat := 4983230072969 + 3 ^ 40 * 4380547 * 2
def baseEnd_4380547 : Nat := 2249326140610977823416737

theorem tailTrace_4380547 : CollatzResearch.WordTrace tailWord_4380547 prefixEnd_4380547 2249326140610977823416737 := by
  unfold tailWord_4380547
  simp only [CollatzResearch.WordTrace]
  refine ⟨159771674861033831710411895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106514449907355887806941263 159771674861033831710411895)
  ·
    refine ⟨239657512291550747565617843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159771674861033831710411895 239657512291550747565617843)
    ·
      refine ⟨359486268437326121348426765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239657512291550747565617843 359486268437326121348426765)
      ·
        refine ⟨134807350663997295505660037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359486268437326121348426765 134807350663997295505660037)
        ·
          refine ⟨25276378249499492907311257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134807350663997295505660037 25276378249499492907311257)
          ·
            refine ⟨18957283687124619680483443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25276378249499492907311257 18957283687124619680483443)
            ·
              refine ⟨28435925530686929520725165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18957283687124619680483443 28435925530686929520725165)
              ·
                refine ⟨10663472074007598570271937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28435925530686929520725165 10663472074007598570271937)
                ·
                  refine ⟨7997604055505698927703953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10663472074007598570271937 7997604055505698927703953)
                  ·
                    refine ⟨5998203041629274195777965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7997604055505698927703953 5998203041629274195777965)
                    ·
                      refine ⟨2249326140610977823416737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998203041629274195777965 2249326140610977823416737)
                      ·
                        rfl

theorem cell23_4380547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_4380547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380547 prefixEnd_4380547 := by exact prefixLift 4380547
  have htrace : WordTrace (prefixWord ++ tailWord_4380547) baseStart_4380547 baseEnd_4380547 := by
    simpa [prefixWord, tailWord_4380547, baseEnd_4380547] using wordTrace_append hprefix tailTrace_4380547
  have hstable : (prefixWord ++ tailWord_4380547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380547).length < 2 ^ (prefixWord ++ tailWord_4380547).sum := by decide
  have hdescent : baseEnd_4380547 < baseStart_4380547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380564 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4380564 : Nat := 118140960795 + 4380564 * 2 ^ 59
def prefixEnd_4380564 : Nat := 4983230072969 + 3 ^ 40 * 4380564 * 2
def baseEnd_4380564 : Nat := 2249334869782104256904159

theorem tailTrace_4380564 : CollatzResearch.WordTrace tailWord_4380564 prefixEnd_4380564 2249334869782104256904159 := by
  unfold tailWord_4380564
  simp only [CollatzResearch.WordTrace]
  refine ⟨79886147450986121806890373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106514863267981495742520497 79886147450986121806890373)
  ·
    refine ⟨14978652647059897838791945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79886147450986121806890373 14978652647059897838791945)
    ·
      refine ⟨11233989485294923379093959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14978652647059897838791945 11233989485294923379093959)
      ·
        refine ⟨16850984227942385068640939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11233989485294923379093959 16850984227942385068640939)
        ·
          refine ⟨25276476341913577602961409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16850984227942385068640939 25276476341913577602961409)
          ·
            refine ⟨18957357256435183202221057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25276476341913577602961409 18957357256435183202221057)
            ·
              refine ⟨14218017942326387401665793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18957357256435183202221057 14218017942326387401665793)
              ·
                refine ⟨10663513456744790551249345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14218017942326387401665793 10663513456744790551249345)
                ·
                  refine ⟨7997635092558592913437009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10663513456744790551249345 7997635092558592913437009)
                  ·
                    refine ⟨5998226319418944685077757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7997635092558592913437009 5998226319418944685077757)
                    ·
                      refine ⟨2249334869782104256904159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998226319418944685077757 2249334869782104256904159)
                      ·
                        rfl

theorem cell23_4380564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4380564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380564 prefixEnd_4380564 := by exact prefixLift 4380564
  have htrace : WordTrace (prefixWord ++ tailWord_4380564) baseStart_4380564 baseEnd_4380564 := by
    simpa [prefixWord, tailWord_4380564, baseEnd_4380564] using wordTrace_append hprefix tailTrace_4380564
  have hstable : (prefixWord ++ tailWord_4380564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380564).length < 2 ^ (prefixWord ++ tailWord_4380564).sum := by decide
  have hdescent : baseEnd_4380564 < baseStart_4380564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380567 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 6]
def baseStart_4380567 : Nat := 118140960795 + 4380567 * 2 ^ 59
def prefixEnd_4380567 : Nat := 4983230072969 + 3 ^ 40 * 4380567 * 2
def baseEnd_4380567 : Nat := 249926267802674193907405

theorem tailTrace_4380567 : CollatzResearch.WordTrace tailWord_4380567 prefixEnd_4380567 249926267802674193907405 := by
  unfold tailWord_4380567
  simp only [CollatzResearch.WordTrace]
  refine ⟨159772404320961375126139955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106514936213974250084093303 159772404320961375126139955)
  ·
    refine ⟨239658606481442062689209933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159772404320961375126139955 239658606481442062689209933)
    ·
      refine ⟨89871977430540773508453725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239658606481442062689209933 89871977430540773508453725)
      ·
        refine ⟨33701991536452790065670147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89871977430540773508453725 33701991536452790065670147)
        ·
          refine ⟨50552987304679185098505221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33701991536452790065670147 50552987304679185098505221)
          ·
            refine ⟨9478685119627347205969729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50552987304679185098505221 9478685119627347205969729)
            ·
              refine ⟨7109013839720510404477297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9478685119627347205969729 7109013839720510404477297)
              ·
                refine ⟨5331760379790382803357973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7109013839720510404477297 5331760379790382803357973)
                ·
                  refine ⟨249926267802674193907405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5331760379790382803357973 249926267802674193907405)
                  ·
                    rfl

theorem cell23_4380567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 6].length) (baseStart_4380567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380567 prefixEnd_4380567 := by exact prefixLift 4380567
  have htrace : WordTrace (prefixWord ++ tailWord_4380567) baseStart_4380567 baseEnd_4380567 := by
    simpa [prefixWord, tailWord_4380567, baseEnd_4380567] using wordTrace_append hprefix tailTrace_4380567
  have hstable : (prefixWord ++ tailWord_4380567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380567).length < 2 ^ (prefixWord ++ tailWord_4380567).sum := by decide
  have hdescent : baseEnd_4380567 < baseStart_4380567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380597 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4380597 : Nat := 118140960795 + 4380597 * 2 ^ 59
def prefixEnd_4380597 : Nat := 4983230072969 + 3 ^ 40 * 4380597 * 2
def baseEnd_4380597 : Nat := 749783938214567542597169

theorem tailTrace_4380597 : CollatzResearch.WordTrace tailWord_4380597 prefixEnd_4380597 749783938214567542597169 := by
  unfold tailWord_4380597
  simp only [CollatzResearch.WordTrace]
  refine ⟨159773498510852690249732045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106515665673901793499821363 159773498510852690249732045)
  ·
    refine ⟨59915061941569758843649517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159773498510852690249732045 59915061941569758843649517)
    ·
      refine ⟨22468148228088659566368569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59915061941569758843649517 22468148228088659566368569)
      ·
        refine ⟨16851111171066494674776427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22468148228088659566368569 16851111171066494674776427)
        ·
          refine ⟨25276666756599742012164641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16851111171066494674776427 25276666756599742012164641)
          ·
            refine ⟨18957500067449806509123481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25276666756599742012164641 18957500067449806509123481)
            ·
              refine ⟨14218125050587354881842611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18957500067449806509123481 14218125050587354881842611)
              ·
                refine ⟨21327187575881032322763917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14218125050587354881842611 21327187575881032322763917)
                ·
                  refine ⟨7997695340955387121036469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21327187575881032322763917 7997695340955387121036469)
                  ·
                    refine ⟨749783938214567542597169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7997695340955387121036469 749783938214567542597169)
                    ·
                      rfl

theorem cell23_4380597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4380597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380597 prefixEnd_4380597 := by exact prefixLift 4380597
  have htrace : WordTrace (prefixWord ++ tailWord_4380597) baseStart_4380597 baseEnd_4380597 := by
    simpa [prefixWord, tailWord_4380597, baseEnd_4380597] using wordTrace_append hprefix tailTrace_4380597
  have hstable : (prefixWord ++ tailWord_4380597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380597).length < 2 ^ (prefixWord ++ tailWord_4380597).sum := by decide
  have hdescent : baseEnd_4380597 < baseStart_4380597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380617 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 4]
def baseStart_4380617 : Nat := 118140960795 + 4380617 * 2 ^ 59
def prefixEnd_4380617 : Nat := 4983230072969 + 3 ^ 40 * 4380617 * 2
def baseEnd_4380617 : Nat := 2249362084256792549541415

theorem tailTrace_4380617 : CollatzResearch.WordTrace tailWord_4380617 prefixEnd_4380617 2249362084256792549541415 := by
  unfold tailWord_4380617
  simp only [CollatzResearch.WordTrace]
  refine ⟨159774227970780233665460105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106516151980520155776973403 159774227970780233665460105)
  ·
    refine ⟨119830670978085175249095079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159774227970780233665460105 119830670978085175249095079)
    ·
      refine ⟨179746006467127762873642619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119830670978085175249095079 179746006467127762873642619)
      ·
        refine ⟨269619009700691644310463929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179746006467127762873642619 269619009700691644310463929)
        ·
          refine ⟨202214257275518733232847947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269619009700691644310463929 202214257275518733232847947)
          ·
            refine ⟨303321385913278099849271921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202214257275518733232847947 303321385913278099849271921)
            ·
              refine ⟨227491039434958574886953941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303321385913278099849271921 227491039434958574886953941)
              ·
                refine ⟨5331821236756841598912983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 227491039434958574886953941 5331821236756841598912983)
                ·
                  refine ⟨7997731855135262398369475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5331821236756841598912983 7997731855135262398369475)
                  ·
                    refine ⟨11996597782702893597554213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7997731855135262398369475 11996597782702893597554213)
                    ·
                      refine ⟨2249362084256792549541415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11996597782702893597554213 2249362084256792549541415)
                      ·
                        rfl

theorem cell23_4380617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_4380617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380617 prefixEnd_4380617 := by exact prefixLift 4380617
  have htrace : WordTrace (prefixWord ++ tailWord_4380617) baseStart_4380617 baseEnd_4380617 := by
    simpa [prefixWord, tailWord_4380617, baseEnd_4380617] using wordTrace_append hprefix tailTrace_4380617
  have hstable : (prefixWord ++ tailWord_4380617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380617).length < 2 ^ (prefixWord ++ tailWord_4380617).sum := by decide
  have hdescent : baseEnd_4380617 < baseStart_4380617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380657 : List Nat := [1, 2, 2, 2, 5, 1, 1, 9]
def baseStart_4380657 : Nat := 118140960795 + 4380657 * 2 ^ 59
def prefixEnd_4380657 : Nat := 4983230072969 + 3 ^ 40 * 4380657 * 2
def baseEnd_4380657 : Nat := 83310467536406384927453

theorem tailTrace_4380657 : CollatzResearch.WordTrace tailWord_4380657 prefixEnd_4380657 83310467536406384927453 := by
  unfold tailWord_4380657
  simp only [CollatzResearch.WordTrace]
  refine ⟨159775686890635320496916225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106517124593756880331277483 159775686890635320496916225)
  ·
    refine ⟨119831765167976490372687169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159775686890635320496916225 119831765167976490372687169)
    ·
      refine ⟨89873823875982367779515377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119831765167976490372687169 89873823875982367779515377)
      ·
        refine ⟨67405367906986775834636533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89873823875982367779515377 67405367906986775834636533)
        ·
          refine ⟨6319253241280010234497175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67405367906986775834636533 6319253241280010234497175)
          ·
            refine ⟨9478879861920015351745763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319253241280010234497175 9478879861920015351745763)
            ·
              refine ⟨14218319792880023027618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9478879861920015351745763 14218319792880023027618645)
              ·
                refine ⟨83310467536406384927453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14218319792880023027618645 83310467536406384927453)
                ·
                  rfl

theorem cell23_4380657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 9].length) (baseStart_4380657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380657 prefixEnd_4380657 := by exact prefixLift 4380657
  have htrace : WordTrace (prefixWord ++ tailWord_4380657) baseStart_4380657 baseEnd_4380657 := by
    simpa [prefixWord, tailWord_4380657, baseEnd_4380657] using wordTrace_append hprefix tailTrace_4380657
  have hstable : (prefixWord ++ tailWord_4380657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380657).length < 2 ^ (prefixWord ++ tailWord_4380657).sum := by decide
  have hdescent : baseEnd_4380657 < baseStart_4380657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380662 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4380662 : Nat := 118140960795 + 4380662 * 2 ^ 59
def prefixEnd_4380662 : Nat := 4983230072969 + 3 ^ 40 * 4380662 * 2
def baseEnd_4380662 : Nat := 2249385190886244873478709

theorem tailTrace_4380662 : CollatzResearch.WordTrace tailWord_4380662 prefixEnd_4380662 2249385190886244873478709 := by
  unfold tailWord_4380662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985991828476075396928015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106517246170411470900565493 9985991828476075396928015)
  ·
    refine ⟨14978987742714113095392023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9985991828476075396928015 14978987742714113095392023)
    ·
      refine ⟨22468481614071169643088035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14978987742714113095392023 22468481614071169643088035)
      ·
        refine ⟨33702722421106754464632053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22468481614071169643088035 33702722421106754464632053)
        ·
          refine ⟨3159630226978758231059255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33702722421106754464632053 3159630226978758231059255)
          ·
            refine ⟨4739445340468137346588883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159630226978758231059255 4739445340468137346588883)
            ·
              refine ⟨7109168010702206019883325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739445340468137346588883 7109168010702206019883325)
              ·
                refine ⟨2665938004013327257456247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7109168010702206019883325 2665938004013327257456247)
                ·
                  refine ⟨3998907006019990886184371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665938004013327257456247 3998907006019990886184371)
                  ·
                    refine ⟨5998360509029986329276557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998907006019990886184371 5998360509029986329276557)
                    ·
                      refine ⟨2249385190886244873478709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998360509029986329276557 2249385190886244873478709)
                      ·
                        rfl

theorem cell23_4380662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4380662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380662 prefixEnd_4380662 := by exact prefixLift 4380662
  have htrace : WordTrace (prefixWord ++ tailWord_4380662) baseStart_4380662 baseEnd_4380662 := by
    simpa [prefixWord, tailWord_4380662, baseEnd_4380662] using wordTrace_append hprefix tailTrace_4380662
  have hstable : (prefixWord ++ tailWord_4380662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380662).length < 2 ^ (prefixWord ++ tailWord_4380662).sum := by decide
  have hdescent : baseEnd_4380662 < baseStart_4380662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380667 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 3]
def baseStart_4380667 : Nat := 118140960795 + 4380667 * 2 ^ 59
def prefixEnd_4380667 : Nat := 4983230072969 + 3 ^ 40 * 4380667 * 2
def baseEnd_4380667 : Nat := 2249387758289517353916185

theorem tailTrace_4380667 : CollatzResearch.WordTrace tailWord_4380667 prefixEnd_4380667 2249387758289517353916185 := by
  unfold tailWord_4380667
  simp only [CollatzResearch.WordTrace]
  refine ⟨159776051620599092204780255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106517367747066061469853503 159776051620599092204780255)
  ·
    refine ⟨239664077430898638307170383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159776051620599092204780255 239664077430898638307170383)
    ·
      refine ⟨359496116146347957460755575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239664077430898638307170383 359496116146347957460755575)
      ·
        refine ⟨539244174219521936191133363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359496116146347957460755575 539244174219521936191133363)
        ·
          refine ⟨808866261329282904286700045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539244174219521936191133363 808866261329282904286700045)
          ·
            refine ⟨303324847998481089107512517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 808866261329282904286700045 303324847998481089107512517)
            ·
              refine ⟨56873408999715204207658597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 303324847998481089107512517 56873408999715204207658597)
              ·
                refine ⟨10663764187446600788935987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56873408999715204207658597 10663764187446600788935987)
                ·
                  refine ⟨15995646281169901183403981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10663764187446600788935987 15995646281169901183403981)
                  ·
                    refine ⟨5998367355438712943776493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15995646281169901183403981 5998367355438712943776493)
                    ·
                      refine ⟨2249387758289517353916185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998367355438712943776493 2249387758289517353916185)
                      ·
                        rfl

theorem cell23_4380667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 3].length) (baseStart_4380667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380667 prefixEnd_4380667 := by exact prefixLift 4380667
  have htrace : WordTrace (prefixWord ++ tailWord_4380667) baseStart_4380667 baseEnd_4380667 := by
    simpa [prefixWord, tailWord_4380667, baseEnd_4380667] using wordTrace_append hprefix tailTrace_4380667
  have hstable : (prefixWord ++ tailWord_4380667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380667).length < 2 ^ (prefixWord ++ tailWord_4380667).sum := by decide
  have hdescent : baseEnd_4380667 < baseStart_4380667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380684 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_4380684 : Nat := 118140960795 + 4380684 * 2 ^ 59
def prefixEnd_4380684 : Nat := 4983230072969 + 3 ^ 40 * 4380684 * 2
def baseEnd_4380684 : Nat := 2249396487460643787403607

theorem tailTrace_4380684 : CollatzResearch.WordTrace tailWord_4380684 prefixEnd_4380684 2249396487460643787403607 := by
  unfold tailWord_4380684
  simp only [CollatzResearch.WordTrace]
  refine ⟨79888335830768752054074553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106517781107691669405432737 79888335830768752054074553)
  ·
    refine ⟨59916251873076564040555915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79888335830768752054074553 59916251873076564040555915)
    ·
      refine ⟨89874377809614846060833873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59916251873076564040555915 89874377809614846060833873)
      ·
        refine ⟨67405783357211134545625405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89874377809614846060833873 67405783357211134545625405)
        ·
          refine ⟨25277168758954175454609527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67405783357211134545625405 25277168758954175454609527)
          ·
            refine ⟨37915753138431263181914291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25277168758954175454609527 37915753138431263181914291)
            ·
              refine ⟨56873629707646894772871437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37915753138431263181914291 56873629707646894772871437)
              ·
                refine ⟨21327611140367585539826789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56873629707646894772871437 21327611140367585539826789)
                ·
                  refine ⟨3998927088818922288717523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21327611140367585539826789 3998927088818922288717523)
                  ·
                    refine ⟨5998390633228383433076285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3998927088818922288717523 5998390633228383433076285)
                    ·
                      refine ⟨2249396487460643787403607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998390633228383433076285 2249396487460643787403607)
                      ·
                        rfl

theorem cell23_4380684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_4380684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380684 prefixEnd_4380684 := by exact prefixLift 4380684
  have htrace : WordTrace (prefixWord ++ tailWord_4380684) baseStart_4380684 baseEnd_4380684 := by
    simpa [prefixWord, tailWord_4380684, baseEnd_4380684] using wordTrace_append hprefix tailTrace_4380684
  have hstable : (prefixWord ++ tailWord_4380684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380684).length < 2 ^ (prefixWord ++ tailWord_4380684).sum := by decide
  have hdescent : baseEnd_4380684 < baseStart_4380684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380695 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 2, 4]
def baseStart_4380695 : Nat := 118140960795 + 4380695 * 2 ^ 59
def prefixEnd_4380695 : Nat := 4983230072969 + 3 ^ 40 * 4380695 * 2
def baseEnd_4380695 : Nat := 749800711915947748122019

theorem tailTrace_4380695 : CollatzResearch.WordTrace tailWord_4380695 prefixEnd_4380695 749800711915947748122019 := by
  unfold tailWord_4380695
  simp only [CollatzResearch.WordTrace]
  refine ⟨159777072864497652986799539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106518048576331768657866359 159777072864497652986799539)
  ·
    refine ⟨239665609296746479480199309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159777072864497652986799539 239665609296746479480199309)
    ·
      refine ⟨89874603486279929805074741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239665609296746479480199309 89874603486279929805074741)
      ·
        refine ⟨8425744076838743419225757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89874603486279929805074741 8425744076838743419225757)
        ·
          refine ⟨3159654028814528782209659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8425744076838743419225757 3159654028814528782209659)
          ·
            refine ⟨4739481043221793173314489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159654028814528782209659 4739481043221793173314489)
            ·
              refine ⟨3554610782416344879985867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4739481043221793173314489 3554610782416344879985867)
              ·
                refine ⟨5331916173624517319978801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554610782416344879985867 5331916173624517319978801)
                ·
                  refine ⟨3998937130218387989984101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5331916173624517319978801 3998937130218387989984101)
                  ·
                    refine ⟨749800711915947748122019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998937130218387989984101 749800711915947748122019)
                    ·
                      rfl

theorem cell23_4380695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_4380695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380695 prefixEnd_4380695 := by exact prefixLift 4380695
  have htrace : WordTrace (prefixWord ++ tailWord_4380695) baseStart_4380695 baseEnd_4380695 := by
    simpa [prefixWord, tailWord_4380695, baseEnd_4380695] using wordTrace_append hprefix tailTrace_4380695
  have hstable : (prefixWord ++ tailWord_4380695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380695).length < 2 ^ (prefixWord ++ tailWord_4380695).sum := by decide
  have hdescent : baseEnd_4380695 < baseStart_4380695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380727 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_4380727 : Nat := 118140960795 + 4380727 * 2 ^ 59
def prefixEnd_4380727 : Nat := 4983230072969 + 3 ^ 40 * 4380727 * 2
def baseEnd_4380727 : Nat := 2249418567128787119165909

theorem tailTrace_4380727 : CollatzResearch.WordTrace tailWord_4380727 prefixEnd_4380727 2249418567128787119165909 := by
  unfold tailWord_4380727
  simp only [CollatzResearch.WordTrace]
  refine ⟨159778240000381722451964435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106518826666921148301309623 159778240000381722451964435)
  ·
    refine ⟨239667360000572583677946653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159778240000381722451964435 239667360000572583677946653)
    ·
      refine ⟨89875260000214718879229995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239667360000572583677946653 89875260000214718879229995)
      ·
        refine ⟨134812890000322078318844993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89875260000214718879229995 134812890000322078318844993)
        ·
          refine ⟨101109667500241558739133745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134812890000322078318844993 101109667500241558739133745)
          ·
            refine ⟨75832250625181169054350309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101109667500241558739133745 75832250625181169054350309)
            ·
              refine ⟨14218546992221469197690683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75832250625181169054350309 14218546992221469197690683)
              ·
                refine ⟨21327820488332203796536025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14218546992221469197690683 21327820488332203796536025)
                ·
                  refine ⟨15995865366249152847402019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21327820488332203796536025 15995865366249152847402019)
                  ·
                    refine ⟨23993798049373729271103029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15995865366249152847402019 23993798049373729271103029)
                    ·
                      refine ⟨2249418567128787119165909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23993798049373729271103029 2249418567128787119165909)
                      ·
                        rfl

theorem cell23_4380727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_4380727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380727 prefixEnd_4380727 := by exact prefixLift 4380727
  have htrace : WordTrace (prefixWord ++ tailWord_4380727) baseStart_4380727 baseEnd_4380727 := by
    simpa [prefixWord, tailWord_4380727, baseEnd_4380727] using wordTrace_append hprefix tailTrace_4380727
  have hstable : (prefixWord ++ tailWord_4380727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380727).length < 2 ^ (prefixWord ++ tailWord_4380727).sum := by decide
  have hdescent : baseEnd_4380727 < baseStart_4380727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380764 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 7]
def baseStart_4380764 : Nat := 118140960795 + 4380764 * 2 ^ 59
def prefixEnd_4380764 : Nat := 4983230072969 + 3 ^ 40 * 4380764 * 2
def baseEnd_4380764 : Nat := 249937507323667052711471

theorem tailTrace_4380764 : CollatzResearch.WordTrace tailWord_4380764 prefixEnd_4380764 249937507323667052711471 := by
  unfold tailWord_4380764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79889794750623838885530673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106519726334165118514040897 79889794750623838885530673)
  ·
    refine ⟨59917346062967879164148005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79889794750623838885530673 59917346062967879164148005)
    ·
      refine ⟨11234502386806477343277751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59917346062967879164148005 11234502386806477343277751)
      ·
        refine ⟨16851753580209716014916627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11234502386806477343277751 16851753580209716014916627)
        ·
          refine ⟨25277630370314574022374941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16851753580209716014916627 25277630370314574022374941)
          ·
            refine ⟨9479111388867965258390603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25277630370314574022374941 9479111388867965258390603)
            ·
              refine ⟨14218667083301947887585905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9479111388867965258390603 14218667083301947887585905)
              ·
                refine ⟨10664000312476460915689429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14218667083301947887585905 10664000312476460915689429)
                ·
                  refine ⟨249937507323667052711471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10664000312476460915689429 249937507323667052711471)
                  ·
                    rfl

theorem cell23_4380764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_4380764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380764 prefixEnd_4380764 := by exact prefixLift 4380764
  have htrace : WordTrace (prefixWord ++ tailWord_4380764) baseStart_4380764 baseEnd_4380764 := by
    simpa [prefixWord, tailWord_4380764, baseEnd_4380764] using wordTrace_append hprefix tailTrace_4380764
  have hstable : (prefixWord ++ tailWord_4380764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380764).length < 2 ^ (prefixWord ++ tailWord_4380764).sum := by decide
  have hdescent : baseEnd_4380764 < baseStart_4380764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380777 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_4380777 : Nat := 118140960795 + 4380777 * 2 ^ 59
def prefixEnd_4380777 : Nat := 4983230072969 + 3 ^ 40 * 4380777 * 2
def baseEnd_4380777 : Nat := 749814747053837307846893

theorem tailTrace_4380777 : CollatzResearch.WordTrace tailWord_4380777 prefixEnd_4380777 749814747053837307846893 := by
  unfold tailWord_4380777
  simp only [CollatzResearch.WordTrace]
  refine ⟨159780063650200580991284585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106520042433467053994189723 159780063650200580991284585)
  ·
    refine ⟨119835047737650435743463439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159780063650200580991284585 119835047737650435743463439)
    ·
      refine ⟨179752571606475653615195159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119835047737650435743463439 179752571606475653615195159)
      ·
        refine ⟨269628857409713480422792739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179752571606475653615195159 269628857409713480422792739)
        ·
          refine ⟨404443286114570220634189109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269628857409713480422792739 404443286114570220634189109)
          ·
            refine ⟨37916558073240958184455229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 404443286114570220634189109 37916558073240958184455229)
            ·
              refine ⟨14218709277465359319170711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37916558073240958184455229 14218709277465359319170711)
              ·
                refine ⟨21328063916198038978756067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14218709277465359319170711 21328063916198038978756067)
                ·
                  refine ⟨31992095874297058468134101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21328063916198038978756067 31992095874297058468134101)
                  ·
                    refine ⟨749814747053837307846893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31992095874297058468134101 749814747053837307846893)
                    ·
                      rfl

theorem cell23_4380777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_4380777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380777 prefixEnd_4380777 := by exact prefixLift 4380777
  have htrace : WordTrace (prefixWord ++ tailWord_4380777) baseStart_4380777 baseEnd_4380777 := by
    simpa [prefixWord, tailWord_4380777, baseEnd_4380777] using wordTrace_append hprefix tailTrace_4380777
  have hstable : (prefixWord ++ tailWord_4380777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380777).length < 2 ^ (prefixWord ++ tailWord_4380777).sum := by decide
  have hdescent : baseEnd_4380777 < baseStart_4380777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380781 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 5]
def baseStart_4380781 : Nat := 118140960795 + 4380781 * 2 ^ 59
def prefixEnd_4380781 : Nat := 4983230072969 + 3 ^ 40 * 4380781 * 2
def baseEnd_4380781 : Nat := 249938477231569989765629

theorem tailTrace_4380781 : CollatzResearch.WordTrace tailWord_4380781 prefixEnd_4380781 249938477231569989765629 := by
  unfold tailWord_4380781
  simp only [CollatzResearch.WordTrace]
  refine ⟨159780209542186089674430197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106520139694790726449620131 159780209542186089674430197)
  ·
    refine ⟨14979394644579945906977831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159780209542186089674430197 14979394644579945906977831)
    ·
      refine ⟨22469091966869918860466747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14979394644579945906977831 22469091966869918860466747)
      ·
        refine ⟨33703637950304878290700121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22469091966869918860466747 33703637950304878290700121)
        ·
          refine ⟨25277728462728658718025091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33703637950304878290700121 25277728462728658718025091)
          ·
            refine ⟨37916592694092988077037637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25277728462728658718025091 37916592694092988077037637)
            ·
              refine ⟨7109361130142435264444557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37916592694092988077037637 7109361130142435264444557)
              ·
                refine ⟨2666010423803413224166709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7109361130142435264444557 2666010423803413224166709)
                ·
                  refine ⟨249938477231569989765629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2666010423803413224166709 249938477231569989765629)
                  ·
                    rfl

theorem cell23_4380781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_4380781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380781 prefixEnd_4380781 := by exact prefixLift 4380781
  have htrace : WordTrace (prefixWord ++ tailWord_4380781) baseStart_4380781 baseEnd_4380781 := by
    simpa [prefixWord, tailWord_4380781, baseEnd_4380781] using wordTrace_append hprefix tailTrace_4380781
  have hstable : (prefixWord ++ tailWord_4380781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380781).length < 2 ^ (prefixWord ++ tailWord_4380781).sum := by decide
  have hdescent : baseEnd_4380781 < baseStart_4380781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380827 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4]
def baseStart_4380827 : Nat := 118140960795 + 4380827 * 2 ^ 59
def prefixEnd_4380827 : Nat := 4983230072969 + 3 ^ 40 * 4380827 * 2
def baseEnd_4380827 : Nat := 2249469915194236727915449

theorem tailTrace_4380827 : CollatzResearch.WordTrace tailWord_4380827 prefixEnd_4380827 2249469915194236727915449 := by
  unfold tailWord_4380827
  simp only [CollatzResearch.WordTrace]
  refine ⟨159781887300019439530604735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106521258200012959687069823 159781887300019439530604735)
  ·
    refine ⟨239672830950029159295907103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159781887300019439530604735 239672830950029159295907103)
    ·
      refine ⟨359509246425043738943860655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239672830950029159295907103 359509246425043738943860655)
      ·
        refine ⟨539263869637565608415790983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359509246425043738943860655 539263869637565608415790983)
        ·
          refine ⟨808895804456348412623686475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539263869637565608415790983 808895804456348412623686475)
          ·
            refine ⟨1213343706684522618935529713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808895804456348412623686475 1213343706684522618935529713)
            ·
              refine ⟨910007780013391964201647285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213343706684522618935529713 910007780013391964201647285)
              ·
                refine ⟨85313229376255496643904433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 910007780013391964201647285 85313229376255496643904433)
                ·
                  refine ⟨63984922032191622482928325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85313229376255496643904433 63984922032191622482928325)
                  ·
                    refine ⟨11997172881035929215549061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63984922032191622482928325 11997172881035929215549061)
                    ·
                      refine ⟨2249469915194236727915449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11997172881035929215549061 2249469915194236727915449)
                      ·
                        rfl

theorem cell23_4380827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_4380827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380827 prefixEnd_4380827 := by exact prefixLift 4380827
  have htrace : WordTrace (prefixWord ++ tailWord_4380827) baseStart_4380827 baseEnd_4380827 := by
    simpa [prefixWord, tailWord_4380827, baseEnd_4380827] using wordTrace_append hprefix tailTrace_4380827
  have hstable : (prefixWord ++ tailWord_4380827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380827).length < 2 ^ (prefixWord ++ tailWord_4380827).sum := by decide
  have hdescent : baseEnd_4380827 < baseStart_4380827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380837 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 10]
def baseStart_4380837 : Nat := 118140960795 + 4380837 * 2 ^ 59
def prefixEnd_4380837 : Nat := 4983230072969 + 3 ^ 40 * 4380837 * 2
def baseEnd_4380837 : Nat := 249941672222309076532267

theorem tailTrace_4380837 : CollatzResearch.WordTrace tailWord_4380837 prefixEnd_4380837 249941672222309076532267 := by
  unfold tailWord_4380837
  simp only [CollatzResearch.WordTrace]
  refine ⟨159782252029983211238468765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106521501353322140825645843 159782252029983211238468765)
  ·
    refine ⟨59918344511243704214425787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159782252029983211238468765 59918344511243704214425787)
    ·
      refine ⟨89877516766865556321638681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59918344511243704214425787 89877516766865556321638681)
      ·
        refine ⟨67408137575149167241229011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89877516766865556321638681 67408137575149167241229011)
        ·
          refine ⟨101112206362723750861843517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67408137575149167241229011 101112206362723750861843517)
          ·
            refine ⟨37917077386021406573191319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101112206362723750861843517 37917077386021406573191319)
            ·
              refine ⟨56875616079032109859786979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37917077386021406573191319 56875616079032109859786979)
              ·
                refine ⟨85313424118548164789680469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56875616079032109859786979 85313424118548164789680469)
                ·
                  refine ⟨249941672222309076532267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85313424118548164789680469 249941672222309076532267)
                  ·
                    rfl

theorem cell23_4380837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_4380837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380837 prefixEnd_4380837 := by exact prefixLift 4380837
  have htrace : WordTrace (prefixWord ++ tailWord_4380837) baseStart_4380837 baseEnd_4380837 := by
    simpa [prefixWord, tailWord_4380837, baseEnd_4380837] using wordTrace_append hprefix tailTrace_4380837
  have hstable : (prefixWord ++ tailWord_4380837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380837).length < 2 ^ (prefixWord ++ tailWord_4380837).sum := by decide
  have hdescent : baseEnd_4380837 < baseStart_4380837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380881 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_4380881 : Nat := 118140960795 + 4380881 * 2 ^ 59
def prefixEnd_4380881 : Nat := 4983230072969 + 3 ^ 40 * 4380881 * 2
def baseEnd_4380881 : Nat := 2249497643149579516640201

theorem tailTrace_4380881 : CollatzResearch.WordTrace tailWord_4380881 prefixEnd_4380881 2249497643149579516640201 := by
  unfold tailWord_4380881
  simp only [CollatzResearch.WordTrace]
  refine ⟨159783856841823806753070497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106522571227882537835380331 159783856841823806753070497)
  ·
    refine ⟨119837892631367855064802873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159783856841823806753070497 119837892631367855064802873)
    ·
      refine ⟨89878419473525891298602155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119837892631367855064802873 89878419473525891298602155)
      ·
        refine ⟨134817629210288836947903233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89878419473525891298602155 134817629210288836947903233)
        ·
          refine ⟨101113221907716627710927425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134817629210288836947903233 101113221907716627710927425)
          ·
            refine ⟨75834916430787470783195569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101113221907716627710927425 75834916430787470783195569)
            ·
              refine ⟨56876187323090603087396677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75834916430787470783195569 56876187323090603087396677)
              ·
                refine ⟨10664285123079488078886877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56876187323090603087396677 10664285123079488078886877)
                ·
                  refine ⟨3999106921154808029582579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10664285123079488078886877 3999106921154808029582579)
                  ·
                    refine ⟨5998660381732212044373869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3999106921154808029582579 5998660381732212044373869)
                    ·
                      refine ⟨2249497643149579516640201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998660381732212044373869 2249497643149579516640201)
                      ·
                        rfl

theorem cell23_4380881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_4380881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380881 prefixEnd_4380881 := by exact prefixLift 4380881
  have htrace : WordTrace (prefixWord ++ tailWord_4380881) baseStart_4380881 baseEnd_4380881 := by
    simpa [prefixWord, tailWord_4380881, baseEnd_4380881] using wordTrace_append hprefix tailTrace_4380881
  have hstable : (prefixWord ++ tailWord_4380881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380881).length < 2 ^ (prefixWord ++ tailWord_4380881).sum := by decide
  have hdescent : baseEnd_4380881 < baseStart_4380881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380891 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 2, 3, 2]
def baseStart_4380891 : Nat := 118140960795 + 4380891 * 2 ^ 59
def prefixEnd_4380891 : Nat := 4983230072969 + 3 ^ 40 * 4380891 * 2
def baseEnd_4380891 : Nat := 2249502777956124477515155

theorem tailTrace_4380891 : CollatzResearch.WordTrace tailWord_4380891 prefixEnd_4380891 2249502777956124477515155 := by
  unfold tailWord_4380891
  simp only [CollatzResearch.WordTrace]
  refine ⟨159784221571787578460934527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106522814381191718973956351 159784221571787578460934527)
  ·
    refine ⟨239676332357681367691401791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159784221571787578460934527 239676332357681367691401791)
    ·
      refine ⟨359514498536522051537102687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239676332357681367691401791 359514498536522051537102687)
      ·
        refine ⟨539271747804783077305654031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359514498536522051537102687 539271747804783077305654031)
        ·
          refine ⟨808907621707174615958481047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539271747804783077305654031 808907621707174615958481047)
          ·
            refine ⟨1213361432560761923937721571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808907621707174615958481047 1213361432560761923937721571)
            ·
              refine ⟨1820042148841142885906582357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213361432560761923937721571 1820042148841142885906582357)
              ·
                refine ⟨10664309465866071597108881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1820042148841142885906582357 10664309465866071597108881)
                ·
                  refine ⟨7998232099399553697831661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10664309465866071597108881 7998232099399553697831661)
                  ·
                    refine ⟨2999337037274832636686873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7998232099399553697831661 2999337037274832636686873)
                    ·
                      refine ⟨2249502777956124477515155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999337037274832636686873 2249502777956124477515155)
                      ·
                        rfl

theorem cell23_4380891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3, 2].length) (baseStart_4380891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380891 prefixEnd_4380891 := by exact prefixLift 4380891
  have htrace : WordTrace (prefixWord ++ tailWord_4380891) baseStart_4380891 baseEnd_4380891 := by
    simpa [prefixWord, tailWord_4380891, baseEnd_4380891] using wordTrace_append hprefix tailTrace_4380891
  have hstable : (prefixWord ++ tailWord_4380891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380891).length < 2 ^ (prefixWord ++ tailWord_4380891).sum := by decide
  have hdescent : baseEnd_4380891 < baseStart_4380891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380909 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_4380909 : Nat := 118140960795 + 4380909 * 2 ^ 59
def prefixEnd_4380909 : Nat := 4983230072969 + 3 ^ 40 * 4380909 * 2
def baseEnd_4380909 : Nat := 749837340202635135696691

theorem tailTrace_4380909 : CollatzResearch.WordTrace tailWord_4380909 prefixEnd_4380909 749837340202635135696691 := by
  unfold tailWord_4380909
  simp only [CollatzResearch.WordTrace]
  refine ⟨159784878085722367535089781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106523252057148245023393187 159784878085722367535089781)
  ·
    refine ⟨14979832320536471956414667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159784878085722367535089781 14979832320536471956414667)
    ·
      refine ⟨22469748480804707934622001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14979832320536471956414667 22469748480804707934622001)
      ·
        refine ⟨16852311360603530950966501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22469748480804707934622001 16852311360603530950966501)
        ·
          refine ⟨3159808380113162053306219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16852311360603530950966501 3159808380113162053306219)
          ·
            refine ⟨4739712570169743079959329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159808380113162053306219 4739712570169743079959329)
            ·
              refine ⟨3554784427627307309969497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4739712570169743079959329 3554784427627307309969497)
              ·
                refine ⟨2666088320720480482477123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3554784427627307309969497 2666088320720480482477123)
                ·
                  refine ⟨3999132481080720723715685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666088320720480482477123 3999132481080720723715685)
                  ·
                    refine ⟨749837340202635135696691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3999132481080720723715685 749837340202635135696691)
                    ·
                      rfl

theorem cell23_4380909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_4380909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380909 prefixEnd_4380909 := by exact prefixLift 4380909
  have htrace : WordTrace (prefixWord ++ tailWord_4380909) baseStart_4380909 baseEnd_4380909 := by
    simpa [prefixWord, tailWord_4380909, baseEnd_4380909] using wordTrace_append hprefix tailTrace_4380909
  have hstable : (prefixWord ++ tailWord_4380909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380909).length < 2 ^ (prefixWord ++ tailWord_4380909).sum := by decide
  have hdescent : baseEnd_4380909 < baseStart_4380909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380931 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 2, 4]
def baseStart_4380931 : Nat := 118140960795 + 4380931 * 2 ^ 59
def prefixEnd_4380931 : Nat := 4983230072969 + 3 ^ 40 * 4380931 * 2
def baseEnd_4380931 : Nat := 749841105727434773671657

theorem tailTrace_4380931 : CollatzResearch.WordTrace tailWord_4380931 prefixEnd_4380931 749841105727434773671657 := by
  unfold tailWord_4380931
  simp only [CollatzResearch.WordTrace]
  refine ⟨159785680491642665292390647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106523786994428443528260431 159785680491642665292390647)
  ·
    refine ⟨239678520737463997938585971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159785680491642665292390647 239678520737463997938585971)
    ·
      refine ⟨359517781106195996907878957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239678520737463997938585971 359517781106195996907878957)
      ·
        refine ⟨134819167914823498840454609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359517781106195996907878957 134819167914823498840454609)
        ·
          refine ⟨101114375936117624130340957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134819167914823498840454609 101114375936117624130340957)
          ·
            refine ⟨37917890976044109048877859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101114375936117624130340957 37917890976044109048877859)
            ·
              refine ⟨56876836464066163573316789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37917890976044109048877859 56876836464066163573316789)
              ·
                refine ⟨5332203418506202834998449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56876836464066163573316789 5332203418506202834998449)
                ·
                  refine ⟨3999152563879652126248837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5332203418506202834998449 3999152563879652126248837)
                  ·
                    refine ⟨749841105727434773671657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3999152563879652126248837 749841105727434773671657)
                    ·
                      rfl

theorem cell23_4380931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 4].length) (baseStart_4380931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380931 prefixEnd_4380931 := by exact prefixLift 4380931
  have htrace : WordTrace (prefixWord ++ tailWord_4380931) baseStart_4380931 baseEnd_4380931 := by
    simpa [prefixWord, tailWord_4380931, baseEnd_4380931] using wordTrace_append hprefix tailTrace_4380931
  have hstable : (prefixWord ++ tailWord_4380931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380931).length < 2 ^ (prefixWord ++ tailWord_4380931).sum := by decide
  have hdescent : baseEnd_4380931 < baseStart_4380931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380938 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_4380938 : Nat := 118140960795 + 4380938 * 2 ^ 59
def prefixEnd_4380938 : Nat := 4983230072969 + 3 ^ 40 * 4380938 * 2
def baseEnd_4380938 : Nat := 2249526911546885793627439

theorem tailTrace_4380938 : CollatzResearch.WordTrace tailWord_4380938 prefixEnd_4380938 2249526911546885793627439 := by
  unfold tailWord_4380938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39946483950654326371973867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106523957201744870325263645 39946483950654326371973867)
  ·
    refine ⟨59919725925981489557960801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39946483950654326371973867 59919725925981489557960801)
    ·
      refine ⟨44939794444486117168470601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59919725925981489557960801 44939794444486117168470601)
      ·
        refine ⟨33704845833364587876352951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44939794444486117168470601 33704845833364587876352951)
        ·
          refine ⟨50557268750046881814529427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33704845833364587876352951 50557268750046881814529427)
          ·
            refine ⟨75835903125070322721794141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50557268750046881814529427 75835903125070322721794141)
            ·
              refine ⟨28438463671901371020672803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75835903125070322721794141 28438463671901371020672803)
              ·
                refine ⟨42657695507852056531009205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28438463671901371020672803 42657695507852056531009205)
                ·
                  refine ⟨3999158953861130299782113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42657695507852056531009205 3999158953861130299782113)
                  ·
                    refine ⟨2999369215395847724836585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999158953861130299782113 2999369215395847724836585)
                    ·
                      refine ⟨2249526911546885793627439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999369215395847724836585 2249526911546885793627439)
                      ·
                        rfl

theorem cell23_4380938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_4380938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380938 prefixEnd_4380938 := by exact prefixLift 4380938
  have htrace : WordTrace (prefixWord ++ tailWord_4380938) baseStart_4380938 baseEnd_4380938 := by
    simpa [prefixWord, tailWord_4380938, baseEnd_4380938] using wordTrace_append hprefix tailTrace_4380938
  have hstable : (prefixWord ++ tailWord_4380938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380938).length < 2 ^ (prefixWord ++ tailWord_4380938).sum := by decide
  have hdescent : baseEnd_4380938 < baseStart_4380938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380951 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4380951 : Nat := 118140960795 + 4380951 * 2 ^ 59
def prefixEnd_4380951 : Nat := 4983230072969 + 3 ^ 40 * 4380951 * 2
def baseEnd_4380951 : Nat := 2249533586795394242764879

theorem tailTrace_4380951 : CollatzResearch.WordTrace tailWord_4380951 prefixEnd_4380951 2249533586795394242764879 := by
  unfold tailWord_4380951
  simp only [CollatzResearch.WordTrace]
  refine ⟨159786409951570208708118707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106524273301046805805412471 159786409951570208708118707)
  ·
    refine ⟨239679614927355313062178061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159786409951570208708118707 239679614927355313062178061)
    ·
      refine ⟨89879855597758242398316773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239679614927355313062178061 89879855597758242398316773)
      ·
        refine ⟨16852472924579670449684395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89879855597758242398316773 16852472924579670449684395)
        ·
          refine ⟨25278709386869505674526593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16852472924579670449684395 25278709386869505674526593)
          ·
            refine ⟨18959032040152129255894945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25278709386869505674526593 18959032040152129255894945)
            ·
              refine ⟨14219274030114096941921209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18959032040152129255894945 14219274030114096941921209)
              ·
                refine ⟨10664455522585572706440907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14219274030114096941921209 10664455522585572706440907)
                ·
                  refine ⟨15996683283878359059661361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10664455522585572706440907 15996683283878359059661361)
                  ·
                    refine ⟨11997512462908769294746021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15996683283878359059661361 11997512462908769294746021)
                    ·
                      refine ⟨2249533586795394242764879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11997512462908769294746021 2249533586795394242764879)
                      ·
                        rfl

theorem cell23_4380951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4380951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380951 prefixEnd_4380951 := by exact prefixLift 4380951
  have htrace : WordTrace (prefixWord ++ tailWord_4380951) baseStart_4380951 baseEnd_4380951 := by
    simpa [prefixWord, tailWord_4380951, baseEnd_4380951] using wordTrace_append hprefix tailTrace_4380951
  have hstable : (prefixWord ++ tailWord_4380951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380951).length < 2 ^ (prefixWord ++ tailWord_4380951).sum := by decide
  have hdescent : baseEnd_4380951 < baseStart_4380951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380955 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 1, 2, 2]
def baseStart_4380955 : Nat := 118140960795 + 4380955 * 2 ^ 59
def prefixEnd_4380955 : Nat := 4983230072969 + 3 ^ 40 * 4380955 * 2
def baseEnd_4380955 : Nat := 2249535640718012227114861

theorem tailTrace_4380955 : CollatzResearch.WordTrace tailWord_4380955 prefixEnd_4380955 2249535640718012227114861 := by
  unfold tailWord_4380955
  simp only [CollatzResearch.WordTrace]
  refine ⟨159786555843555717391264319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106524370562370478260842879 159786555843555717391264319)
  ·
    refine ⟨239679833765333576086896479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159786555843555717391264319 239679833765333576086896479)
    ·
      refine ⟨359519750648000364130344719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239679833765333576086896479 359519750648000364130344719)
      ·
        refine ⟨539279625972000546195517079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359519750648000364130344719 539279625972000546195517079)
        ·
          refine ⟨808919438958000819293275619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539279625972000546195517079 808919438958000819293275619)
          ·
            refine ⟨1213379158437001228939913429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808919438958000819293275619 1213379158437001228939913429)
            ·
              refine ⟨28438574025867216303279221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1213379158437001228939913429 28438574025867216303279221)
              ·
                refine ⟨2666116314925051528432427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28438574025867216303279221 2666116314925051528432427)
                ·
                  refine ⟨3999174472387577292648641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666116314925051528432427 3999174472387577292648641)
                  ·
                    refine ⟨2999380854290682969486481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999174472387577292648641 2999380854290682969486481)
                    ·
                      refine ⟨2249535640718012227114861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999380854290682969486481 2249535640718012227114861)
                      ·
                        rfl

theorem cell23_4380955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 2, 2].length) (baseStart_4380955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380955 prefixEnd_4380955 := by exact prefixLift 4380955
  have htrace : WordTrace (prefixWord ++ tailWord_4380955) baseStart_4380955 baseEnd_4380955 := by
    simpa [prefixWord, tailWord_4380955, baseEnd_4380955] using wordTrace_append hprefix tailTrace_4380955
  have hstable : (prefixWord ++ tailWord_4380955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380955).length < 2 ^ (prefixWord ++ tailWord_4380955).sum := by decide
  have hdescent : baseEnd_4380955 < baseStart_4380955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4380965 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_4380965 : Nat := 118140960795 + 4380965 * 2 ^ 59
def prefixEnd_4380965 : Nat := 4983230072969 + 3 ^ 40 * 4380965 * 2
def baseEnd_4380965 : Nat := 749846925174852395996605

theorem tailTrace_4380965 : CollatzResearch.WordTrace tailWord_4380965 prefixEnd_4380965 749846925174852395996605 := by
  unfold tailWord_4380965
  simp only [CollatzResearch.WordTrace]
  refine ⟨159786920573519489099128349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106524613715679659399418899 159786920573519489099128349)
  ·
    refine ⟨59920095215069808412173131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159786920573519489099128349 59920095215069808412173131)
    ·
      refine ⟨89880142822604712618259697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59920095215069808412173131 89880142822604712618259697)
      ·
        refine ⟨67410107116953534463694773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89880142822604712618259697 67410107116953534463694773)
        ·
          refine ⟨6319697542214393855971385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67410107116953534463694773 6319697542214393855971385)
          ·
            refine ⟨4739773156660795391978539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6319697542214393855971385 4739773156660795391978539)
            ·
              refine ⟨7109659734991193087967809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739773156660795391978539 7109659734991193087967809)
              ·
                refine ⟨5332244801243394815975857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7109659734991193087967809 5332244801243394815975857)
                ·
                  refine ⟨3999183600932546111981893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5332244801243394815975857 3999183600932546111981893)
                  ·
                    refine ⟨749846925174852395996605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3999183600932546111981893 749846925174852395996605)
                    ·
                      rfl

theorem cell23_4380965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_4380965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4380965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4380965 prefixEnd_4380965 := by exact prefixLift 4380965
  have htrace : WordTrace (prefixWord ++ tailWord_4380965) baseStart_4380965 baseEnd_4380965 := by
    simpa [prefixWord, tailWord_4380965, baseEnd_4380965] using wordTrace_append hprefix tailTrace_4380965
  have hstable : (prefixWord ++ tailWord_4380965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4380965).length < 2 ^ (prefixWord ++ tailWord_4380965).sum := by decide
  have hdescent : baseEnd_4380965 < baseStart_4380965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4380965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381061 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_4381061 : Nat := 118140960795 + 4381061 * 2 ^ 59
def prefixEnd_4381061 : Nat := 4983230072969 + 3 ^ 40 * 4381061 * 2
def baseEnd_4381061 : Nat := 2249590069667388812389373

theorem tailTrace_4381061 : CollatzResearch.WordTrace tailWord_4381061 prefixEnd_4381061 2249590069667388812389373 := by
  unfold tailWord_4381061
  simp only [CollatzResearch.WordTrace]
  refine ⟨159790421981171697494623037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106526947987447798329748691 159790421981171697494623037)
  ·
    refine ⟨59921408242939386560483639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159790421981171697494623037 59921408242939386560483639)
    ·
      refine ⟨89882112364409079840725459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59921408242939386560483639 89882112364409079840725459)
      ·
        refine ⟨134823168546613619761088189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89882112364409079840725459 134823168546613619761088189)
        ·
          refine ⟨50558688204980107410408071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134823168546613619761088189 50558688204980107410408071)
          ·
            refine ⟨75838032307470161115612107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50558688204980107410408071 75838032307470161115612107)
            ·
              refine ⟨113757048461205241673418161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75838032307470161115612107 113757048461205241673418161)
              ·
                refine ⟨85317786345903931255063621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113757048461205241673418161 85317786345903931255063621)
                ·
                  refine ⟨15997084939856987110324429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85317786345903931255063621 15997084939856987110324429)
                  ·
                    refine ⟨5998906852446370166371661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15997084939856987110324429 5998906852446370166371661)
                    ·
                      refine ⟨2249590069667388812389373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5998906852446370166371661 2249590069667388812389373)
                      ·
                        rfl

theorem cell23_4381061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_4381061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381061 prefixEnd_4381061 := by exact prefixLift 4381061
  have htrace : WordTrace (prefixWord ++ tailWord_4381061) baseStart_4381061 baseEnd_4381061 := by
    simpa [prefixWord, tailWord_4381061, baseEnd_4381061] using wordTrace_append hprefix tailTrace_4381061
  have hstable : (prefixWord ++ tailWord_4381061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381061).length < 2 ^ (prefixWord ++ tailWord_4381061).sum := by decide
  have hdescent : baseEnd_4381061 < baseStart_4381061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381081 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_4381081 : Nat := 118140960795 + 4381081 * 2 ^ 59
def prefixEnd_4381081 : Nat := 4983230072969 + 3 ^ 40 * 4381081 * 2
def baseEnd_4381081 : Nat := 749866779760159578046427

theorem tailTrace_4381081 : CollatzResearch.WordTrace tailWord_4381081 prefixEnd_4381081 749866779760159578046427 := by
  unfold tailWord_4381081
  simp only [CollatzResearch.WordTrace]
  refine ⟨159791151441099240910351097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106527434294066160606900731 159791151441099240910351097)
  ·
    refine ⟨119843363580824430682763323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159791151441099240910351097 119843363580824430682763323)
    ·
      refine ⟨179765045371236646024144985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119843363580824430682763323 179765045371236646024144985)
      ·
        refine ⟨134823784028427484518108739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179765045371236646024144985 134823784028427484518108739)
        ·
          refine ⟨202235676042641226777163109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134823784028427484518108739 202235676042641226777163109)
          ·
            refine ⟨37919189257995230020718083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202235676042641226777163109 37919189257995230020718083)
            ·
              refine ⟨56878783886992845031077125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37919189257995230020718083 56878783886992845031077125)
              ·
                refine ⟨10664771978811158443326961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56878783886992845031077125 10664771978811158443326961)
                ·
                  refine ⟨7998578984108368832495221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10664771978811158443326961 7998578984108368832495221)
                  ·
                    refine ⟨749866779760159578046427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7998578984108368832495221 749866779760159578046427)
                    ·
                      rfl

theorem cell23_4381081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_4381081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381081 prefixEnd_4381081 := by exact prefixLift 4381081
  have htrace : WordTrace (prefixWord ++ tailWord_4381081) baseStart_4381081 baseEnd_4381081 := by
    simpa [prefixWord, tailWord_4381081, baseEnd_4381081] using wordTrace_append hprefix tailTrace_4381081
  have hstable : (prefixWord ++ tailWord_4381081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381081).length < 2 ^ (prefixWord ++ tailWord_4381081).sum := by decide
  have hdescent : baseEnd_4381081 < baseStart_4381081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381085 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 5]
def baseStart_4381085 : Nat := 118140960795 + 4381085 * 2 ^ 59
def prefixEnd_4381085 : Nat := 4983230072969 + 3 ^ 40 * 4381085 * 2
def baseEnd_4381085 : Nat := 249955821467010746498807

theorem tailTrace_4381085 : CollatzResearch.WordTrace tailWord_4381085 prefixEnd_4381085 249955821467010746498807 := by
  unfold tailWord_4381085
  simp only [CollatzResearch.WordTrace]
  refine ⟨159791297333084749593496709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106527531555389833062331139 159791297333084749593496709)
  ·
    refine ⟨29960868249953390548780633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159791297333084749593496709 29960868249953390548780633)
    ·
      refine ⟨22470651187465042911585475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29960868249953390548780633 22470651187465042911585475)
      ·
        refine ⟨33705976781197564367378213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22470651187465042911585475 33705976781197564367378213)
        ·
          refine ⟨6319870646474543318883415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33705976781197564367378213 6319870646474543318883415)
          ·
            refine ⟨9479805969711814978325123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319870646474543318883415 9479805969711814978325123)
            ·
              refine ⟨14219708954567722467487685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9479805969711814978325123 14219708954567722467487685)
              ·
                refine ⟨2666195428981447962653941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14219708954567722467487685 2666195428981447962653941)
                ·
                  refine ⟨249955821467010746498807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2666195428981447962653941 249955821467010746498807)
                  ·
                    rfl

theorem cell23_4381085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_4381085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381085 prefixEnd_4381085 := by exact prefixLift 4381085
  have htrace : WordTrace (prefixWord ++ tailWord_4381085) baseStart_4381085 baseEnd_4381085 := by
    simpa [prefixWord, tailWord_4381085, baseEnd_4381085] using wordTrace_append hprefix tailTrace_4381085
  have hstable : (prefixWord ++ tailWord_4381085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381085).length < 2 ^ (prefixWord ++ tailWord_4381085).sum := by decide
  have hdescent : baseEnd_4381085 < baseStart_4381085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381088 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 2, 5, 2]
def baseStart_4381088 : Nat := 118140960795 + 4381088 * 2 ^ 59
def prefixEnd_4381088 : Nat := 4983230072969 + 3 ^ 40 * 4381088 * 2
def baseEnd_4381088 : Nat := 2249603933645060206751749

theorem tailTrace_4381088 : CollatzResearch.WordTrace tailWord_4381088 prefixEnd_4381088 2249603933645060206751749 := by
  unfold tailWord_4381088
  simp only [CollatzResearch.WordTrace]
  refine ⟨79895703376036940552927959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106527604501382587403903945 79895703376036940552927959)
  ·
    refine ⟨119843555064055410829391939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79895703376036940552927959 119843555064055410829391939)
    ·
      refine ⟨179765332596083116244087909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119843555064055410829391939 179765332596083116244087909)
      ·
        refine ⟨33705999861765584295766483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179765332596083116244087909 33705999861765584295766483)
        ·
          refine ⟨50558999792648376443649725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33705999861765584295766483 50558999792648376443649725)
          ·
            refine ⟨18959624922243141166368647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50558999792648376443649725 18959624922243141166368647)
            ·
              refine ⟨28439437383364711749552971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18959624922243141166368647 28439437383364711749552971)
              ·
                refine ⟨42659156075047067624329457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28439437383364711749552971 42659156075047067624329457)
                ·
                  refine ⟨31994367056285300718247093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42659156075047067624329457 31994367056285300718247093)
                  ·
                    refine ⟨2999471911526746942335665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31994367056285300718247093 2999471911526746942335665)
                    ·
                      refine ⟨2249603933645060206751749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999471911526746942335665 2249603933645060206751749)
                      ·
                        rfl

theorem cell23_4381088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_4381088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381088 prefixEnd_4381088 := by exact prefixLift 4381088
  have htrace : WordTrace (prefixWord ++ tailWord_4381088) baseStart_4381088 baseEnd_4381088 := by
    simpa [prefixWord, tailWord_4381088, baseEnd_4381088] using wordTrace_append hprefix tailTrace_4381088
  have hstable : (prefixWord ++ tailWord_4381088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381088).length < 2 ^ (prefixWord ++ tailWord_4381088).sum := by decide
  have hdescent : baseEnd_4381088 < baseStart_4381088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381091 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5]
def baseStart_4381091 : Nat := 118140960795 + 4381091 * 2 ^ 59
def prefixEnd_4381091 : Nat := 4983230072969 + 3 ^ 40 * 4381091 * 2
def baseEnd_4381091 : Nat := 2249605474087023695014235

theorem tailTrace_4381091 : CollatzResearch.WordTrace tailWord_4381091 prefixEnd_4381091 2249605474087023695014235 := by
  unfold tailWord_4381091
  simp only [CollatzResearch.WordTrace]
  refine ⟨159791516171063012618215127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106527677447375341745476751 159791516171063012618215127)
  ·
    refine ⟨239687274256594518927322691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159791516171063012618215127 239687274256594518927322691)
    ·
      refine ⟨359530911384891778390984037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239687274256594518927322691 359530911384891778390984037)
      ·
        refine ⟨67412045884667208448309507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 359530911384891778390984037 67412045884667208448309507)
        ·
          refine ⟨101118068827000812672464261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67412045884667208448309507 101118068827000812672464261)
          ·
            refine ⟨18959637905062652376087049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101118068827000812672464261 18959637905062652376087049)
            ·
              refine ⟨14219728428796989282065287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18959637905062652376087049 14219728428796989282065287)
              ·
                refine ⟨21329592643195483923097931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14219728428796989282065287 21329592643195483923097931)
                ·
                  refine ⟨31994388964793225884646897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21329592643195483923097931 31994388964793225884646897)
                  ·
                    refine ⟨23995791723594919413485173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31994388964793225884646897 23995791723594919413485173)
                    ·
                      refine ⟨2249605474087023695014235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23995791723594919413485173 2249605474087023695014235)
                      ·
                        rfl

theorem cell23_4381091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_4381091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381091 prefixEnd_4381091 := by exact prefixLift 4381091
  have htrace : WordTrace (prefixWord ++ tailWord_4381091) baseStart_4381091 baseEnd_4381091 := by
    simpa [prefixWord, tailWord_4381091, baseEnd_4381091] using wordTrace_append hprefix tailTrace_4381091
  have hstable : (prefixWord ++ tailWord_4381091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381091).length < 2 ^ (prefixWord ++ tailWord_4381091).sum := by decide
  have hdescent : baseEnd_4381091 < baseStart_4381091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381145 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 1, 4]
def baseStart_4381145 : Nat := 118140960795 + 4381145 * 2 ^ 59
def prefixEnd_4381145 : Nat := 4983230072969 + 3 ^ 40 * 4381145 * 2
def baseEnd_4381145 : Nat := 749877734014122161246329

theorem tailTrace_4381145 : CollatzResearch.WordTrace tailWord_4381145 prefixEnd_4381145 749877734014122161246329 := by
  unfold tailWord_4381145
  simp only [CollatzResearch.WordTrace]
  refine ⟨159793485712867379840680889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106528990475244919893787259 159793485712867379840680889)
  ·
    refine ⟨119845114284650534880510667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159793485712867379840680889 119845114284650534880510667)
    ·
      refine ⟨179767671426975802320766001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119845114284650534880510667 179767671426975802320766001)
      ·
        refine ⟨134825753570231851740574501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179767671426975802320766001 134825753570231851740574501)
        ·
          refine ⟨25279828794418472201357719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134825753570231851740574501 25279828794418472201357719)
          ·
            refine ⟨37919743191627708302036579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25279828794418472201357719 37919743191627708302036579)
            ·
              refine ⟨56879614787441562453054869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37919743191627708302036579 56879614787441562453054869)
              ·
                refine ⟨2666231943161323239986947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56879614787441562453054869 2666231943161323239986947)
                ·
                  refine ⟨3999347914741984859980421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666231943161323239986947 3999347914741984859980421)
                  ·
                    refine ⟨749877734014122161246329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3999347914741984859980421 749877734014122161246329)
                    ·
                      rfl

theorem cell23_4381145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 4].length) (baseStart_4381145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381145 prefixEnd_4381145 := by exact prefixLift 4381145
  have htrace : WordTrace (prefixWord ++ tailWord_4381145) baseStart_4381145 baseEnd_4381145 := by
    simpa [prefixWord, tailWord_4381145, baseEnd_4381145] using wordTrace_append hprefix tailTrace_4381145
  have hstable : (prefixWord ++ tailWord_4381145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381145).length < 2 ^ (prefixWord ++ tailWord_4381145).sum := by decide
  have hdescent : baseEnd_4381145 < baseStart_4381145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381195 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 4, 3, 2]
def baseStart_4381195 : Nat := 118140960795 + 4381195 * 2 ^ 59
def prefixEnd_4381195 : Nat := 4983230072969 + 3 ^ 40 * 4381195 * 2
def baseEnd_4381195 : Nat := 2249658876075091288113757

theorem tailTrace_4381195 : CollatzResearch.WordTrace tailWord_4381195 prefixEnd_4381195 2249658876075091288113757 := by
  unfold tailWord_4381195
  simp only [CollatzResearch.WordTrace]
  refine ⟨159795309362686238380001039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106530206241790825586667359 159795309362686238380001039)
  ·
    refine ⟨239692964044029357570001559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159795309362686238380001039 239692964044029357570001559)
    ·
      refine ⟨359539446066044036355002339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239692964044029357570001559 359539446066044036355002339)
      ·
        refine ⟨539309169099066054532503509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359539446066044036355002339 539309169099066054532503509)
        ·
          refine ⟨12640058650759360653105551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 539309169099066054532503509 12640058650759360653105551)
          ·
            refine ⟨18960087976139040979658327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12640058650759360653105551 18960087976139040979658327)
            ·
              refine ⟨28440131964208561469487491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18960087976139040979658327 28440131964208561469487491)
              ·
                refine ⟨42660197946312842204231237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28440131964208561469487491 42660197946312842204231237)
                ·
                  refine ⟨7998787114933657913293357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42660197946312842204231237 7998787114933657913293357)
                  ·
                    refine ⟨2999545168100121717485009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7998787114933657913293357 2999545168100121717485009)
                    ·
                      refine ⟨2249658876075091288113757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999545168100121717485009 2249658876075091288113757)
                      ·
                        rfl

theorem cell23_4381195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3, 2].length) (baseStart_4381195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381195 prefixEnd_4381195 := by exact prefixLift 4381195
  have htrace : WordTrace (prefixWord ++ tailWord_4381195) baseStart_4381195 baseEnd_4381195 := by
    simpa [prefixWord, tailWord_4381195, baseEnd_4381195] using wordTrace_append hprefix tailTrace_4381195
  have hstable : (prefixWord ++ tailWord_4381195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381195).length < 2 ^ (prefixWord ++ tailWord_4381195).sum := by decide
  have hdescent : baseEnd_4381195 < baseStart_4381195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381201 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_4381201 : Nat := 118140960795 + 4381201 * 2 ^ 59
def prefixEnd_4381201 : Nat := 4983230072969 + 3 ^ 40 * 4381201 * 2
def baseEnd_4381201 : Nat := 749887318986339421546243

theorem tailTrace_4381201 : CollatzResearch.WordTrace tailWord_4381201 prefixEnd_4381201 749887318986339421546243 := by
  unfold tailWord_4381201
  simp only [CollatzResearch.WordTrace]
  refine ⟨159795528200664501404719457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106530352133776334269812971 159795528200664501404719457)
  ·
    refine ⟨119846646150498376053539593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159795528200664501404719457 119846646150498376053539593)
    ·
      refine ⟨89884984612873782040154695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119846646150498376053539593 89884984612873782040154695)
      ·
        refine ⟨134827476919310673060232043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89884984612873782040154695 134827476919310673060232043)
        ·
          refine ⟨202241215378966009590348065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134827476919310673060232043 202241215378966009590348065)
          ·
            refine ⟨151680911534224507192761049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202241215378966009590348065 151680911534224507192761049)
            ·
              refine ⟨113760683650668380394570787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151680911534224507192761049 113760683650668380394570787)
              ·
                refine ⟨170641025476002570591856181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113760683650668380394570787 170641025476002570591856181)
                ·
                  refine ⟨15997596138375240992986517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170641025476002570591856181 15997596138375240992986517)
                  ·
                    refine ⟨749887318986339421546243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15997596138375240992986517 749887318986339421546243)
                    ·
                      rfl

theorem cell23_4381201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_4381201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381201 prefixEnd_4381201 := by exact prefixLift 4381201
  have htrace : WordTrace (prefixWord ++ tailWord_4381201) baseStart_4381201 baseEnd_4381201 := by
    simpa [prefixWord, tailWord_4381201, baseEnd_4381201] using wordTrace_append hprefix tailTrace_4381201
  have hstable : (prefixWord ++ tailWord_4381201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381201).length < 2 ^ (prefixWord ++ tailWord_4381201).sum := by decide
  have hdescent : baseEnd_4381201 < baseStart_4381201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381218 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_4381218 : Nat := 118140960795 + 4381218 * 2 ^ 59
def prefixEnd_4381218 : Nat := 4983230072969 + 3 ^ 40 * 4381218 * 2
def baseEnd_4381218 : Nat := 749890228710048232708717

theorem tailTrace_4381218 : CollatzResearch.WordTrace tailWord_4381218 prefixEnd_4381218 749890228710048232708717 := by
  unfold tailWord_4381218
  simp only [CollatzResearch.WordTrace]
  refine ⟨39949037060400728327022077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106530765494401942205392205 39949037060400728327022077)
  ·
    refine ⟨14980888897650273122633279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39949037060400728327022077 14980888897650273122633279)
    ·
      refine ⟨22471333346475409683949919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14980888897650273122633279 22471333346475409683949919)
      ·
        refine ⟨33707000019713114525924879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22471333346475409683949919 33707000019713114525924879)
        ·
          refine ⟨50560500029569671788887319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33707000019713114525924879 50560500029569671788887319)
          ·
            refine ⟨75840750044354507683330979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50560500029569671788887319 75840750044354507683330979)
            ·
              refine ⟨113761125066531761524996469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75840750044354507683330979 113761125066531761524996469)
              ·
                refine ⟨10665105474987352642968419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113761125066531761524996469 10665105474987352642968419)
                ·
                  refine ⟨15997658212481028964452629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10665105474987352642968419 15997658212481028964452629)
                  ·
                    refine ⟨749890228710048232708717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15997658212481028964452629 749890228710048232708717)
                    ·
                      rfl

theorem cell23_4381218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_4381218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381218 prefixEnd_4381218 := by exact prefixLift 4381218
  have htrace : WordTrace (prefixWord ++ tailWord_4381218) baseStart_4381218 baseEnd_4381218 := by
    simpa [prefixWord, tailWord_4381218, baseEnd_4381218] using wordTrace_append hprefix tailTrace_4381218
  have hstable : (prefixWord ++ tailWord_4381218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381218).length < 2 ^ (prefixWord ++ tailWord_4381218).sum := by decide
  have hdescent : baseEnd_4381218 < baseStart_4381218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381242 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4]
def baseStart_4381242 : Nat := 118140960795 + 4381242 * 2 ^ 59
def prefixEnd_4381242 : Nat := 4983230072969 + 3 ^ 40 * 4381242 * 2
def baseEnd_4381242 : Nat := 2249683009665852604226041

theorem tailTrace_4381242 : CollatzResearch.WordTrace tailWord_4381242 prefixEnd_4381242 2249683009665852604226041 := by
  unfold tailWord_4381242
  simp only [CollatzResearch.WordTrace]
  refine ⟨39949255898378991351740495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106531349062343976937974653 39949255898378991351740495)
  ·
    refine ⟨59923883847568487027610743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39949255898378991351740495 59923883847568487027610743)
    ·
      refine ⟨89885825771352730541416115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59923883847568487027610743 89885825771352730541416115)
      ·
        refine ⟨134828738657029095812124173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89885825771352730541416115 134828738657029095812124173)
        ·
          refine ⟨50560776996385910929546565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134828738657029095812124173 50560776996385910929546565)
          ·
            refine ⟨9480145686822358299289981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50560776996385910929546565 9480145686822358299289981)
            ·
              refine ⟨3555054632558384362233743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9480145686822358299289981 3555054632558384362233743)
              ·
                refine ⟨5332581948837576543350615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555054632558384362233743 5332581948837576543350615)
                ·
                  refine ⟨7998872923256364815025923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5332581948837576543350615 7998872923256364815025923)
                  ·
                    refine ⟨11998309384884547222538885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7998872923256364815025923 11998309384884547222538885)
                    ·
                      refine ⟨2249683009665852604226041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11998309384884547222538885 2249683009665852604226041)
                      ·
                        rfl

theorem cell23_4381242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_4381242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381242 prefixEnd_4381242 := by exact prefixLift 4381242
  have htrace : WordTrace (prefixWord ++ tailWord_4381242) baseStart_4381242 baseEnd_4381242 := by
    simpa [prefixWord, tailWord_4381242, baseEnd_4381242] using wordTrace_append hprefix tailTrace_4381242
  have hstable : (prefixWord ++ tailWord_4381242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381242).length < 2 ^ (prefixWord ++ tailWord_4381242).sum := by decide
  have hdescent : baseEnd_4381242 < baseStart_4381242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381245 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_4381245 : Nat := 118140960795 + 4381245 * 2 ^ 59
def prefixEnd_4381245 : Nat := 4983230072969 + 3 ^ 40 * 4381245 * 2
def baseEnd_4381245 : Nat := 2249684550107816092488527

theorem tailTrace_4381245 : CollatzResearch.WordTrace tailWord_4381245 prefixEnd_4381245 2249684550107816092488527 := by
  unfold tailWord_4381245
  simp only [CollatzResearch.WordTrace]
  refine ⟨159797133012505096919321189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106531422008336731279547459 159797133012505096919321189)
  ·
    refine ⟨29961962439844705672372723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159797133012505096919321189 29961962439844705672372723)
    ·
      refine ⟨44942943659767058508559085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29961962439844705672372723 44942943659767058508559085)
      ·
        refine ⟨16853603872412646940709657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44942943659767058508559085 16853603872412646940709657)
        ·
          refine ⟨12640202904309485205532243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16853603872412646940709657 12640202904309485205532243)
          ·
            refine ⟨18960304356464227808298365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12640202904309485205532243 18960304356464227808298365)
            ·
              refine ⟨7110114133674085428111887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18960304356464227808298365 7110114133674085428111887)
              ·
                refine ⟨10665171200511128142167831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7110114133674085428111887 10665171200511128142167831)
                ·
                  refine ⟨15997756800766692213251747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10665171200511128142167831 15997756800766692213251747)
                  ·
                    refine ⟨23996635201150038319877621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15997756800766692213251747 23996635201150038319877621)
                    ·
                      refine ⟨2249684550107816092488527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23996635201150038319877621 2249684550107816092488527)
                      ·
                        rfl

theorem cell23_4381245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_4381245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381245 prefixEnd_4381245 := by exact prefixLift 4381245
  have htrace : WordTrace (prefixWord ++ tailWord_4381245) baseStart_4381245 baseEnd_4381245 := by
    simpa [prefixWord, tailWord_4381245, baseEnd_4381245] using wordTrace_append hprefix tailTrace_4381245
  have hstable : (prefixWord ++ tailWord_4381245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381245).length < 2 ^ (prefixWord ++ tailWord_4381245).sum := by decide
  have hdescent : baseEnd_4381245 < baseStart_4381245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
