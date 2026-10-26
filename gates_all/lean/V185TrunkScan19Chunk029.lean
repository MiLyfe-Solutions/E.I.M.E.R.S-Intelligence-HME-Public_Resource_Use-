import V185TrunkScan19Chunk028

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_290767 : List Nat := [1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_290767 : Nat := 118140960795 + 290767 * 2 ^ 59
def prefixEnd_290767 : Nat := 4983230072969 + 3 ^ 40 * 290767 * 2
def baseEnd_290767 : Nat := 88475987831685396429803

theorem tailTrace_290767 : CollatzResearch.WordTrace tailWord_290767 prefixEnd_290767 88475987831685396429803 := by
  unfold tailWord_290767
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605143737608292895150555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7070095825072195263433703 10605143737608292895150555)
  ·
    refine ⟨15907715606412439342725833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10605143737608292895150555 15907715606412439342725833)
    ·
      refine ⟨11930786704809329507044375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15907715606412439342725833 11930786704809329507044375)
      ·
        refine ⟨17896180057213994260566563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11930786704809329507044375 17896180057213994260566563)
        ·
          refine ⟨26844270085820991390849845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17896180057213994260566563 26844270085820991390849845)
          ·
            refine ⟨2516650320545717942892173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26844270085820991390849845 2516650320545717942892173)
            ·
              refine ⟨943743870204644228584565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2516650320545717942892173 943743870204644228584565)
              ·
                refine ⟨88475987831685396429803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 943743870204644228584565 88475987831685396429803)
                ·
                  rfl

theorem cell19_290767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_290767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290767 prefixEnd_290767 := by exact prefixLift 290767
  have htrace : WordTrace (prefixWord ++ tailWord_290767) baseStart_290767 baseEnd_290767 := by
    simpa [prefixWord, tailWord_290767, baseEnd_290767] using wordTrace_append hprefix tailTrace_290767
  have hstable : (prefixWord ++ tailWord_290767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290767).length < 2 ^ (prefixWord ++ tailWord_290767).sum := by decide
  have hdescent : baseEnd_290767 < baseStart_290767 := by decide
  rcases family_descends (prefixWord ++ tailWord_290767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290824 : List Nat := [2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_290824 : Nat := 118140960795 + 290824 * 2 ^ 59
def prefixEnd_290824 : Nat := 4983230072969 + 3 ^ 40 * 290824 * 2
def baseEnd_290824 : Nat := 88493332067126153162981

theorem tailTrace_290824 : CollatzResearch.WordTrace tailWord_290824 prefixEnd_290824 88493332067126153162981 := by
  unfold tailWord_290824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303611349200895814987763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7071481798934527753317017 5303611349200895814987763)
  ·
    refine ⟨7955417023801343722481645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5303611349200895814987763 7955417023801343722481645)
    ·
      refine ⟨2983281383925503895930617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7955417023801343722481645 2983281383925503895930617)
      ·
        refine ⟨2237461037944127921947963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2983281383925503895930617 2237461037944127921947963)
        ·
          refine ⟨3356191556916191882921945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237461037944127921947963 3356191556916191882921945)
          ·
            refine ⟨2517143667687143912191459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356191556916191882921945 2517143667687143912191459)
            ·
              refine ⟨3775715501530715868287189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517143667687143912191459 3775715501530715868287189)
              ·
                refine ⟨88493332067126153162981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3775715501530715868287189 88493332067126153162981)
                ·
                  rfl

theorem cell19_290824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_290824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290824 prefixEnd_290824 := by exact prefixLift 290824
  have htrace : WordTrace (prefixWord ++ tailWord_290824) baseStart_290824 baseEnd_290824 := by
    simpa [prefixWord, tailWord_290824, baseEnd_290824] using wordTrace_append hprefix tailTrace_290824
  have hstable : (prefixWord ++ tailWord_290824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290824).length < 2 ^ (prefixWord ++ tailWord_290824).sum := by decide
  have hdescent : baseEnd_290824 < baseStart_290824 := by decide
  rcases family_descends (prefixWord ++ tailWord_290824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290856 : List Nat := [2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_290856 : Nat := 118140960795 + 290856 * 2 ^ 59
def prefixEnd_290856 : Nat := 4983230072969 + 3 ^ 40 * 290856 * 2
def baseEnd_290856 : Nat := 88503069181759560451783

theorem tailTrace_290856 : CollatzResearch.WordTrace tailWord_290856 prefixEnd_290856 88503069181759560451783 := by
  unfold tailWord_290856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304194917142930547570211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7072259889523907396760281 5304194917142930547570211)
  ·
    refine ⟨7956292375714395821355317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5304194917142930547570211 7956292375714395821355317)
    ·
      refine ⟨745902410223224608252061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7956292375714395821355317 745902410223224608252061)
      ·
        refine ⟨279713403833709228094523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 745902410223224608252061 279713403833709228094523)
        ·
          refine ⟨419570105750563842141785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279713403833709228094523 419570105750563842141785)
          ·
            refine ⟨314677579312922881606339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419570105750563842141785 314677579312922881606339)
            ·
              refine ⟨472016368969384322409509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314677579312922881606339 472016368969384322409509)
              ·
                refine ⟨88503069181759560451783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472016368969384322409509 88503069181759560451783)
                ·
                  rfl

theorem cell19_290856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_290856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290856 prefixEnd_290856 := by exact prefixLift 290856
  have htrace : WordTrace (prefixWord ++ tailWord_290856) baseStart_290856 baseEnd_290856 := by
    simpa [prefixWord, tailWord_290856, baseEnd_290856] using wordTrace_append hprefix tailTrace_290856
  have hstable : (prefixWord ++ tailWord_290856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290856).length < 2 ^ (prefixWord ++ tailWord_290856).sum := by decide
  have hdescent : baseEnd_290856 < baseStart_290856 := by decide
  rcases family_descends (prefixWord ++ tailWord_290856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290858 : List Nat := [3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_290858 : Nat := 118140960795 + 290858 * 2 ^ 59
def prefixEnd_290858 : Nat := 4983230072969 + 3 ^ 40 * 290858 * 2
def baseEnd_290858 : Nat := 88503677751424148407333

theorem tailTrace_290858 : CollatzResearch.WordTrace tailWord_290858 prefixEnd_290858 88503677751424148407333 := by
  unfold tailWord_290858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652115695069653859178307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7072308520185743624475485 2652115695069653859178307)
  ·
    refine ⟨3978173542604480788767461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2652115695069653859178307 3978173542604480788767461)
    ·
      refine ⟨745907539238340147893899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3978173542604480788767461 745907539238340147893899)
      ·
        refine ⟨1118861308857510221840849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745907539238340147893899 1118861308857510221840849)
        ·
          refine ⟨839145981643132666380637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1118861308857510221840849 839145981643132666380637)
          ·
            refine ⟨314679743116174749892739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 839145981643132666380637 314679743116174749892739)
            ·
              refine ⟨472019614674262124839109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314679743116174749892739 472019614674262124839109)
              ·
                refine ⟨88503677751424148407333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472019614674262124839109 88503677751424148407333)
                ·
                  rfl

theorem cell19_290858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_290858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290858 prefixEnd_290858 := by exact prefixLift 290858
  have htrace : WordTrace (prefixWord ++ tailWord_290858) baseStart_290858 baseEnd_290858 := by
    simpa [prefixWord, tailWord_290858, baseEnd_290858] using wordTrace_append hprefix tailTrace_290858
  have hstable : (prefixWord ++ tailWord_290858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290858).length < 2 ^ (prefixWord ++ tailWord_290858).sum := by decide
  have hdescent : baseEnd_290858 < baseStart_290858 := by decide
  rcases family_descends (prefixWord ++ tailWord_290858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290898 : List Nat := [3, 2, 2, 1, 4, 1, 6]
def baseStart_290898 : Nat := 118140960795 + 290898 * 2 ^ 59
def prefixEnd_290898 : Nat := 4983230072969 + 3 ^ 40 * 290898 * 2
def baseEnd_290898 : Nat := 29505283048238635839445

theorem tailTrace_290898 : CollatzResearch.WordTrace tailWord_290898 prefixEnd_290898 29505283048238635839445 := by
  unfold tailWord_290898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652480425033425567042337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7073281133422468178779565 2652480425033425567042337)
  ·
    refine ⟨1989360318775069175281753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2652480425033425567042337 1989360318775069175281753)
    ·
      refine ⟨1492020239081301881461315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1989360318775069175281753 1492020239081301881461315)
      ·
        refine ⟨2238030358621952822191973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492020239081301881461315 2238030358621952822191973)
        ·
          refine ⟨419630692241616154160995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2238030358621952822191973 419630692241616154160995)
          ·
            refine ⟨629446038362424231241493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419630692241616154160995 629446038362424231241493)
            ·
              refine ⟨29505283048238635839445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 629446038362424231241493 29505283048238635839445)
              ·
                rfl

theorem cell19_290898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_290898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290898 prefixEnd_290898 := by exact prefixLift 290898
  have htrace : WordTrace (prefixWord ++ tailWord_290898) baseStart_290898 baseEnd_290898 := by
    simpa [prefixWord, tailWord_290898, baseEnd_290898] using wordTrace_append hprefix tailTrace_290898
  have hstable : (prefixWord ++ tailWord_290898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290898).length < 2 ^ (prefixWord ++ tailWord_290898).sum := by decide
  have hdescent : baseEnd_290898 < baseStart_290898 := by decide
  rcases family_descends (prefixWord ++ tailWord_290898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290919 : List Nat := [1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_290919 : Nat := 118140960795 + 290919 * 2 ^ 59
def prefixEnd_290919 : Nat := 4983230072969 + 3 ^ 40 * 290919 * 2
def baseEnd_290919 : Nat := 88522239126194081051611

theorem tailTrace_290919 : CollatzResearch.WordTrace tailWord_290919 prefixEnd_290919 88522239126194081051611 := by
  unfold tailWord_290919
  simp only [CollatzResearch.WordTrace]
  refine ⟨10610687633057622854683811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7073791755371748569789207 10610687633057622854683811)
  ·
    refine ⟨15916031449586434282025717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10610687633057622854683811 15916031449586434282025717)
    ·
      refine ⟨1492127948398728213939911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15916031449586434282025717 1492127948398728213939911)
      ·
        refine ⟨2238191922598092320909867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492127948398728213939911 2238191922598092320909867)
        ·
          refine ⟨3357287883897138481364801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238191922598092320909867 3357287883897138481364801)
          ·
            refine ⟨2517965912922853861023601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3357287883897138481364801 2517965912922853861023601)
            ·
              refine ⟨1888474434692140395767701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517965912922853861023601 1888474434692140395767701)
              ·
                refine ⟨88522239126194081051611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1888474434692140395767701 88522239126194081051611)
                ·
                  rfl

theorem cell19_290919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_290919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290919 prefixEnd_290919 := by exact prefixLift 290919
  have htrace : WordTrace (prefixWord ++ tailWord_290919) baseStart_290919 baseEnd_290919 := by
    simpa [prefixWord, tailWord_290919, baseEnd_290919] using wordTrace_append hprefix tailTrace_290919
  have hstable : (prefixWord ++ tailWord_290919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290919).length < 2 ^ (prefixWord ++ tailWord_290919).sum := by decide
  have hdescent : baseEnd_290919 < baseStart_290919 := by decide
  rcases family_descends (prefixWord ++ tailWord_290919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290934 : List Nat := [5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_290934 : Nat := 118140960795 + 290934 * 2 ^ 59
def prefixEnd_290934 : Nat := 4983230072969 + 3 ^ 40 * 290934 * 2
def baseEnd_290934 : Nat := 88526803398678490718237

theorem tailTrace_290934 : CollatzResearch.WordTrace tailWord_290934 prefixEnd_290934 88526803398678490718237 := by
  unfold tailWord_290934
  simp only [CollatzResearch.WordTrace]
  refine ⟨663202170500205026029991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7074156485335520277653237 663202170500205026029991)
  ·
    refine ⟨994803255750307539044987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 663202170500205026029991 994803255750307539044987)
    ·
      refine ⟨1492204883625461308567481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994803255750307539044987 1492204883625461308567481)
      ·
        refine ⟨1119153662719095981425611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1492204883625461308567481 1119153662719095981425611)
        ·
          refine ⟨1678730494078643972138417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119153662719095981425611 1678730494078643972138417)
          ·
            refine ⟨1259047870558982979103813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678730494078643972138417 1259047870558982979103813)
            ·
              refine ⟨236071475729809308581965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1259047870558982979103813 236071475729809308581965)
              ·
                refine ⟨88526803398678490718237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236071475729809308581965 88526803398678490718237)
                ·
                  rfl

theorem cell19_290934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_290934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290934 prefixEnd_290934 := by exact prefixLift 290934
  have htrace : WordTrace (prefixWord ++ tailWord_290934) baseStart_290934 baseEnd_290934 := by
    simpa [prefixWord, tailWord_290934, baseEnd_290934] using wordTrace_append hprefix tailTrace_290934
  have hstable : (prefixWord ++ tailWord_290934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290934).length < 2 ^ (prefixWord ++ tailWord_290934).sum := by decide
  have hdescent : baseEnd_290934 < baseStart_290934 := by decide
  rcases family_descends (prefixWord ++ tailWord_290934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290966 : List Nat := [5, 3, 2, 1, 1, 1, 2, 4]
def baseStart_290966 : Nat := 118140960795 + 290966 * 2 ^ 59
def prefixEnd_290966 : Nat := 4983230072969 + 3 ^ 40 * 290966 * 2
def baseEnd_290966 : Nat := 88536540513311898007039

theorem tailTrace_290966 : CollatzResearch.WordTrace tailWord_290966 prefixEnd_290966 88536540513311898007039 := by
  unfold tailWord_290966
  simp only [CollatzResearch.WordTrace]
  refine ⟨663275116492959367602797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7074934575924899921096501 663275116492959367602797)
  ·
    refine ⟨248728168684859762851049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 663275116492959367602797 248728168684859762851049)
    ·
      refine ⟨186546126513644822138287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248728168684859762851049 186546126513644822138287)
      ·
        refine ⟨279819189770467233207431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186546126513644822138287 279819189770467233207431)
        ·
          refine ⟨419728784655700849811147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279819189770467233207431 419728784655700849811147)
          ·
            refine ⟨629593176983551274716721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419728784655700849811147 629593176983551274716721)
            ·
              refine ⟨472194882737663456037541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629593176983551274716721 472194882737663456037541)
              ·
                refine ⟨88536540513311898007039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472194882737663456037541 88536540513311898007039)
                ·
                  rfl

theorem cell19_290966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_290966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290966 prefixEnd_290966 := by exact prefixLift 290966
  have htrace : WordTrace (prefixWord ++ tailWord_290966) baseStart_290966 baseEnd_290966 := by
    simpa [prefixWord, tailWord_290966, baseEnd_290966] using wordTrace_append hprefix tailTrace_290966
  have hstable : (prefixWord ++ tailWord_290966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290966).length < 2 ^ (prefixWord ++ tailWord_290966).sum := by decide
  have hdescent : baseEnd_290966 < baseStart_290966 := by decide
  rcases family_descends (prefixWord ++ tailWord_290966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_290976 : List Nat := [2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_290976 : Nat := 118140960795 + 290976 * 2 ^ 59
def prefixEnd_290976 : Nat := 4983230072969 + 3 ^ 40 * 290976 * 2
def baseEnd_290976 : Nat := 88539583361634837784789

theorem tailTrace_290976 : CollatzResearch.WordTrace tailWord_290976 prefixEnd_290976 88539583361634837784789 := by
  unfold tailWord_290976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306383296925560794754391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7075177729234081059672521 5306383296925560794754391)
  ·
    refine ⟨7959574945388341192131587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5306383296925560794754391 7959574945388341192131587)
    ·
      refine ⟨11939362418082511788197381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7959574945388341192131587 11939362418082511788197381)
      ·
        refine ⟨2238630453390470960287009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11939362418082511788197381 2238630453390470960287009)
        ·
          refine ⟨1678972840042853220215257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238630453390470960287009 1678972840042853220215257)
          ·
            refine ⟨1259229630032139915161443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678972840042853220215257 1259229630032139915161443)
            ·
              refine ⟨1888844445048209872742165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259229630032139915161443 1888844445048209872742165)
              ·
                refine ⟨88539583361634837784789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1888844445048209872742165 88539583361634837784789)
                ·
                  rfl

theorem cell19_290976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_290976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_290976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_290976 prefixEnd_290976 := by exact prefixLift 290976
  have htrace : WordTrace (prefixWord ++ tailWord_290976) baseStart_290976 baseEnd_290976 := by
    simpa [prefixWord, tailWord_290976, baseEnd_290976] using wordTrace_append hprefix tailTrace_290976
  have hstable : (prefixWord ++ tailWord_290976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_290976).length < 2 ^ (prefixWord ++ tailWord_290976).sum := by decide
  have hdescent : baseEnd_290976 < baseStart_290976 := by decide
  rcases family_descends (prefixWord ++ tailWord_290976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291010 : List Nat := [3, 5, 1, 1, 1, 8]
def baseStart_291010 : Nat := 118140960795 + 291010 * 2 ^ 59
def prefixEnd_291010 : Nat := 4983230072969 + 3 ^ 40 * 291010 * 2
def baseEnd_291010 : Nat := 9838881005103648114349

theorem tailTrace_291010 : CollatzResearch.WordTrace tailWord_291010 prefixEnd_291010 9838881005103648114349 := by
  unfold tailWord_291010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653501668931986349061621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7076004450485296930830989 2653501668931986349061621)
  ·
    refine ⟨248765781462373720224527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2653501668931986349061621 248765781462373720224527)
    ·
      refine ⟨373148672193560580336791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248765781462373720224527 373148672193560580336791)
      ·
        refine ⟨559723008290340870505187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373148672193560580336791 559723008290340870505187)
        ·
          refine ⟨839584512435511305757781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559723008290340870505187 839584512435511305757781)
          ·
            refine ⟨9838881005103648114349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 839584512435511305757781 9838881005103648114349)
            ·
              rfl

theorem cell19_291010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_291010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291010 prefixEnd_291010 := by exact prefixLift 291010
  have htrace : WordTrace (prefixWord ++ tailWord_291010) baseStart_291010 baseEnd_291010 := by
    simpa [prefixWord, tailWord_291010, baseEnd_291010] using wordTrace_append hprefix tailTrace_291010
  have hstable : (prefixWord ++ tailWord_291010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291010).length < 2 ^ (prefixWord ++ tailWord_291010).sum := by decide
  have hdescent : baseEnd_291010 < baseStart_291010 := by decide
  rcases family_descends (prefixWord ++ tailWord_291010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291029 : List Nat := [1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_291029 : Nat := 118140960795 + 291029 * 2 ^ 59
def prefixEnd_291029 : Nat := 4983230072969 + 3 ^ 40 * 291029 * 2
def baseEnd_291029 : Nat := 88555710457746418606867

theorem tailTrace_291029 : CollatzResearch.WordTrace tailWord_291029 prefixEnd_291029 88555710457746418606867 := by
  unfold tailWord_291029
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614699662659111641188141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7076466441772741094125427 10614699662659111641188141)
  ·
    refine ⟨3980512373497166865445553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10614699662659111641188141 3980512373497166865445553)
    ·
      refine ⟨2985384280122875149084165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3980512373497166865445553 2985384280122875149084165)
      ·
        refine ⟨559759552523039090453281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2985384280122875149084165 559759552523039090453281)
        ·
          refine ⟨419819664392279317839961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559759552523039090453281 419819664392279317839961)
          ·
            refine ⟨314864748294209488379971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419819664392279317839961 314864748294209488379971)
            ·
              refine ⟨472297122441314232569957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314864748294209488379971 472297122441314232569957)
              ·
                refine ⟨88555710457746418606867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472297122441314232569957 88555710457746418606867)
                ·
                  rfl

theorem cell19_291029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_291029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291029 prefixEnd_291029 := by exact prefixLift 291029
  have htrace : WordTrace (prefixWord ++ tailWord_291029) baseStart_291029 baseEnd_291029 := by
    simpa [prefixWord, tailWord_291029, baseEnd_291029] using wordTrace_append hprefix tailTrace_291029
  have hstable : (prefixWord ++ tailWord_291029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291029).length < 2 ^ (prefixWord ++ tailWord_291029).sum := by decide
  have hdescent : baseEnd_291029 < baseStart_291029 := by decide
  rcases family_descends (prefixWord ++ tailWord_291029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291033 : List Nat := [1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_291033 : Nat := 118140960795 + 291033 * 2 ^ 59
def prefixEnd_291033 : Nat := 4983230072969 + 3 ^ 40 * 291033 * 2
def baseEnd_291033 : Nat := 88556927597075594517967

theorem tailTrace_291033 : CollatzResearch.WordTrace tailWord_291033 prefixEnd_291033 88556927597075594517967 := by
  unfold tailWord_291033
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614845554644620324333753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7076563703096413549555835 10614845554644620324333753)
  ·
    refine ⟨7961134165983465243250315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10614845554644620324333753 7961134165983465243250315)
    ·
      refine ⟨11941701248975197864875473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7961134165983465243250315 11941701248975197864875473)
      ·
        refine ⟨8956275936731398398656605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11941701248975197864875473 8956275936731398398656605)
        ·
          refine ⟨3358603476274274399496227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8956275936731398398656605 3358603476274274399496227)
          ·
            refine ⟨5037905214411411599244341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358603476274274399496227 5037905214411411599244341)
            ·
              refine ⟨472303613851069837429157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5037905214411411599244341 472303613851069837429157)
              ·
                refine ⟨88556927597075594517967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472303613851069837429157 88556927597075594517967)
                ·
                  rfl

theorem cell19_291033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_291033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291033 prefixEnd_291033 := by exact prefixLift 291033
  have htrace : WordTrace (prefixWord ++ tailWord_291033) baseStart_291033 baseEnd_291033 := by
    simpa [prefixWord, tailWord_291033, baseEnd_291033] using wordTrace_append hprefix tailTrace_291033
  have hstable : (prefixWord ++ tailWord_291033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291033).length < 2 ^ (prefixWord ++ tailWord_291033).sum := by decide
  have hdescent : baseEnd_291033 < baseStart_291033 := by decide
  rcases family_descends (prefixWord ++ tailWord_291033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291050 : List Nat := [3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_291050 : Nat := 118140960795 + 291050 * 2 ^ 59
def prefixEnd_291050 : Nat := 4983230072969 + 3 ^ 40 * 291050 * 2
def baseEnd_291050 : Nat := 88562100439224592140143

theorem tailTrace_291050 : CollatzResearch.WordTrace tailWord_291050 prefixEnd_291050 88562100439224592140143 := by
  unfold tailWord_291050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653866398895758056925651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7076977063722021485135069 2653866398895758056925651)
  ·
    refine ⟨3980799598343637085388477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2653866398895758056925651 3980799598343637085388477)
    ·
      refine ⟨1492799849378863907020679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3980799598343637085388477 1492799849378863907020679)
      ·
        refine ⟨2239199774068295860531019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492799849378863907020679 2239199774068295860531019)
        ·
          refine ⟨3358799661102443790796529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239199774068295860531019 3358799661102443790796529)
          ·
            refine ⟨2519099745826832843097397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3358799661102443790796529 2519099745826832843097397)
            ·
              refine ⟨236165601171265579040381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2519099745826832843097397 236165601171265579040381)
              ·
                refine ⟨88562100439224592140143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236165601171265579040381 88562100439224592140143)
                ·
                  rfl

theorem cell19_291050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_291050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291050 prefixEnd_291050 := by exact prefixLift 291050
  have htrace : WordTrace (prefixWord ++ tailWord_291050) baseStart_291050 baseEnd_291050 := by
    simpa [prefixWord, tailWord_291050, baseEnd_291050] using wordTrace_append hprefix tailTrace_291050
  have hstable : (prefixWord ++ tailWord_291050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291050).length < 2 ^ (prefixWord ++ tailWord_291050).sum := by decide
  have hdescent : baseEnd_291050 < baseStart_291050 := by decide
  rcases family_descends (prefixWord ++ tailWord_291050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291240 : List Nat := [2, 1, 6, 1, 1, 2, 6]
def baseStart_291240 : Nat := 118140960795 + 291240 * 2 ^ 59
def prefixEnd_291240 : Nat := 4983230072969 + 3 ^ 40 * 291240 * 2
def baseEnd_291240 : Nat := 29539971519120149305801

theorem tailTrace_291240 : CollatzResearch.WordTrace tailWord_291240 prefixEnd_291240 29539971519120149305801 := by
  unfold tailWord_291240
  simp only [CollatzResearch.WordTrace]
  refine ⟨5311197732447347338559587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7081596976596463118079449 5311197732447347338559587)
  ·
    refine ⟨7966796598671021007839381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5311197732447347338559587 7966796598671021007839381)
    ·
      refine ⟨373443590562704109742471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7966796598671021007839381 373443590562704109742471)
      ·
        refine ⟨560165385844056164613707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373443590562704109742471 560165385844056164613707)
        ·
          refine ⟨840248078766084246920561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560165385844056164613707 840248078766084246920561)
          ·
            refine ⟨630186059074563185190421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840248078766084246920561 630186059074563185190421)
            ·
              refine ⟨29539971519120149305801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 630186059074563185190421 29539971519120149305801)
              ·
                rfl

theorem cell19_291240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_291240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291240 prefixEnd_291240 := by exact prefixLift 291240
  have htrace : WordTrace (prefixWord ++ tailWord_291240) baseStart_291240 baseEnd_291240 := by
    simpa [prefixWord, tailWord_291240, baseEnd_291240] using wordTrace_append hprefix tailTrace_291240
  have hstable : (prefixWord ++ tailWord_291240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291240).length < 2 ^ (prefixWord ++ tailWord_291240).sum := by decide
  have hdescent : baseEnd_291240 < baseStart_291240 := by decide
  rcases family_descends (prefixWord ++ tailWord_291240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291276 : List Nat := [2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_291276 : Nat := 118140960795 + 291276 * 2 ^ 59
def prefixEnd_291276 : Nat := 4983230072969 + 3 ^ 40 * 291276 * 2
def baseEnd_291276 : Nat := 88630868811323031117305

theorem tailTrace_291276 : CollatzResearch.WordTrace tailWord_291276 prefixEnd_291276 88630868811323031117305 := by
  unfold tailWord_291276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5311854246382136412714841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7082472328509515216953121 5311854246382136412714841)
  ·
    refine ⟨3983890684786602309536131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5311854246382136412714841 3983890684786602309536131)
    ·
      refine ⟨5975836027179903464304197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3983890684786602309536131 5975836027179903464304197)
      ·
        refine ⟨1120469255096231899557037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5975836027179903464304197 1120469255096231899557037)
        ·
          refine ⟨420175970661086962333889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1120469255096231899557037 420175970661086962333889)
          ·
            refine ⟨315131977995815221750417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420175970661086962333889 315131977995815221750417)
            ·
              refine ⟨236348983496861416312813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315131977995815221750417 236348983496861416312813)
              ·
                refine ⟨88630868811323031117305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236348983496861416312813 88630868811323031117305)
                ·
                  rfl

theorem cell19_291276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_291276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291276 prefixEnd_291276 := by exact prefixLift 291276
  have htrace : WordTrace (prefixWord ++ tailWord_291276) baseStart_291276 baseEnd_291276 := by
    simpa [prefixWord, tailWord_291276, baseEnd_291276] using wordTrace_append hprefix tailTrace_291276
  have hstable : (prefixWord ++ tailWord_291276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291276).length < 2 ^ (prefixWord ++ tailWord_291276).sum := by decide
  have hdescent : baseEnd_291276 < baseStart_291276 := by decide
  rcases family_descends (prefixWord ++ tailWord_291276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291415 : List Nat := [1, 1, 3, 2, 2, 2, 8]
def baseStart_291415 : Nat := 118140960795 + 291415 * 2 ^ 59
def prefixEnd_291415 : Nat := 4983230072969 + 3 ^ 40 * 291415 * 2
def baseEnd_291415 : Nat := 29557721467670631342679

theorem tailTrace_291415 : CollatzResearch.WordTrace tailWord_291415 prefixEnd_291415 29557721467670631342679 := by
  unfold tailWord_291415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10628778239260699564739699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7085852159507133043159799 10628778239260699564739699)
  ·
    refine ⟨15943167358891049347109549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10628778239260699564739699 15943167358891049347109549)
    ·
      refine ⟨5978687759584143505166081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15943167358891049347109549 5978687759584143505166081)
      ·
        refine ⟨4484015819688107628874561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5978687759584143505166081 4484015819688107628874561)
        ·
          refine ⟨3363011864766080721655921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4484015819688107628874561 3363011864766080721655921)
          ·
            refine ⟨2522258898574560541241941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3363011864766080721655921 2522258898574560541241941)
            ·
              refine ⟨29557721467670631342679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2522258898574560541241941 29557721467670631342679)
              ·
                rfl

theorem cell19_291415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_291415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291415 prefixEnd_291415 := by exact prefixLift 291415
  have htrace : WordTrace (prefixWord ++ tailWord_291415) baseStart_291415 baseEnd_291415 := by
    simpa [prefixWord, tailWord_291415, baseEnd_291415] using wordTrace_append hprefix tailTrace_291415
  have hstable : (prefixWord ++ tailWord_291415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291415).length < 2 ^ (prefixWord ++ tailWord_291415).sum := by decide
  have hdescent : baseEnd_291415 < baseStart_291415 := by decide
  rcases family_descends (prefixWord ++ tailWord_291415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291445 : List Nat := [1, 3, 4, 2, 3, 1, 2, 3]
def baseStart_291445 : Nat := 118140960795 + 291445 * 2 ^ 59
def prefixEnd_291445 : Nat := 4983230072969 + 3 ^ 40 * 291445 * 2
def baseEnd_291445 : Nat := 88682292947980713361289

theorem tailTrace_291445 : CollatzResearch.WordTrace tailWord_291445 prefixEnd_291445 88682292947980713361289 := by
  unfold tailWord_291445
  simp only [CollatzResearch.WordTrace]
  refine ⟨10629872429152014688331789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7086581619434676458887859 10629872429152014688331789)
  ·
    refine ⟨3986202160932005508124421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10629872429152014688331789 3986202160932005508124421)
    ·
      refine ⟨747412905174751032773329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3986202160932005508124421 747412905174751032773329)
      ·
        refine ⟨560559678881063274579997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 747412905174751032773329 560559678881063274579997)
        ·
          refine ⟨210209879580398727967499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 560559678881063274579997 210209879580398727967499)
          ·
            refine ⟨315314819370598091951249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210209879580398727967499 315314819370598091951249)
            ·
              refine ⟨236486114527948568963437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315314819370598091951249 236486114527948568963437)
              ·
                refine ⟨88682292947980713361289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236486114527948568963437 88682292947980713361289)
                ·
                  rfl

theorem cell19_291445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_291445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291445 prefixEnd_291445 := by exact prefixLift 291445
  have htrace : WordTrace (prefixWord ++ tailWord_291445) baseStart_291445 baseEnd_291445 := by
    simpa [prefixWord, tailWord_291445, baseEnd_291445] using wordTrace_append hprefix tailTrace_291445
  have hstable : (prefixWord ++ tailWord_291445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291445).length < 2 ^ (prefixWord ++ tailWord_291445).sum := by decide
  have hdescent : baseEnd_291445 < baseStart_291445 := by decide
  rcases family_descends (prefixWord ++ tailWord_291445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291449 : List Nat := [1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_291449 : Nat := 118140960795 + 291449 * 2 ^ 59
def prefixEnd_291449 : Nat := 4983230072969 + 3 ^ 40 * 291449 * 2
def baseEnd_291449 : Nat := 88683510087309889272389

theorem tailTrace_291449 : CollatzResearch.WordTrace tailWord_291449 prefixEnd_291449 88683510087309889272389 := by
  unfold tailWord_291449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10630018321137523371477401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7086678880758348914318267 10630018321137523371477401)
  ·
    refine ⟨7972513740853142528608051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10630018321137523371477401 7972513740853142528608051)
    ·
      refine ⟨11958770611279713792912077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7972513740853142528608051 11958770611279713792912077)
      ·
        refine ⟨4484538979229892672342029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11958770611279713792912077 4484538979229892672342029)
        ·
          refine ⟨1681702117211209752128261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4484538979229892672342029 1681702117211209752128261)
          ·
            refine ⟨315319146977101828524049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1681702117211209752128261 315319146977101828524049)
            ·
              refine ⟨236489360232826371393037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315319146977101828524049 236489360232826371393037)
              ·
                refine ⟨88683510087309889272389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236489360232826371393037 88683510087309889272389)
                ·
                  rfl

theorem cell19_291449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_291449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291449 prefixEnd_291449 := by exact prefixLift 291449
  have htrace : WordTrace (prefixWord ++ tailWord_291449) baseStart_291449 baseEnd_291449 := by
    simpa [prefixWord, tailWord_291449, baseEnd_291449] using wordTrace_append hprefix tailTrace_291449
  have hstable : (prefixWord ++ tailWord_291449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291449).length < 2 ^ (prefixWord ++ tailWord_291449).sum := by decide
  have hdescent : baseEnd_291449 < baseStart_291449 := by decide
  rcases family_descends (prefixWord ++ tailWord_291449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291605 : List Nat := [1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_291605 : Nat := 118140960795 + 291605 * 2 ^ 59
def prefixEnd_291605 : Nat := 4983230072969 + 3 ^ 40 * 291605 * 2
def baseEnd_291605 : Nat := 88730978521147749805297

theorem tailTrace_291605 : CollatzResearch.WordTrace tailWord_291605 prefixEnd_291605 88730978521147749805297 := by
  unfold tailWord_291605
  simp only [CollatzResearch.WordTrace]
  refine ⟨10635708108572362014156269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7090472072381574676104179 10635708108572362014156269)
  ·
    refine ⟨3988390540714635755308601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10635708108572362014156269 3988390540714635755308601)
    ·
      refine ⟨2991292905535976816481451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3988390540714635755308601 2991292905535976816481451)
      ·
        refine ⟨4486939358303965224722177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991292905535976816481451 4486939358303965224722177)
        ·
          refine ⟨3365204518727973918541633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4486939358303965224722177 3365204518727973918541633)
          ·
            refine ⟨2523903389045980438906225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3365204518727973918541633 2523903389045980438906225)
            ·
              refine ⟨1892927541784485329179669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523903389045980438906225 1892927541784485329179669)
              ·
                refine ⟨88730978521147749805297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1892927541784485329179669 88730978521147749805297)
                ·
                  rfl

theorem cell19_291605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_291605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291605 prefixEnd_291605 := by exact prefixLift 291605
  have htrace : WordTrace (prefixWord ++ tailWord_291605) baseStart_291605 baseEnd_291605 := by
    simpa [prefixWord, tailWord_291605, baseEnd_291605] using wordTrace_append hprefix tailTrace_291605
  have hstable : (prefixWord ++ tailWord_291605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291605).length < 2 ^ (prefixWord ++ tailWord_291605).sum := by decide
  have hdescent : baseEnd_291605 < baseStart_291605 := by decide
  rcases family_descends (prefixWord ++ tailWord_291605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291660 : List Nat := [2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_291660 : Nat := 118140960795 + 291660 * 2 ^ 59
def prefixEnd_291660 : Nat := 4983230072969 + 3 ^ 40 * 291660 * 2
def baseEnd_291660 : Nat := 88747714186923918582925

theorem tailTrace_291660 : CollatzResearch.WordTrace tailWord_291660 prefixEnd_291660 88747714186923918582925 := by
  unfold tailWord_291660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318857061686553203704217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7091809415582070938272289 5318857061686553203704217)
  ·
    refine ⟨3989142796264914902778163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5318857061686553203704217 3989142796264914902778163)
    ·
      refine ⟨5983714194397372354167245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3989142796264914902778163 5983714194397372354167245)
      ·
        refine ⟨2243892822899014632812717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5983714194397372354167245 2243892822899014632812717)
        ·
          refine ⟨841459808587130487304769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2243892822899014632812717 841459808587130487304769)
          ·
            refine ⟨631094856440347865478577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841459808587130487304769 631094856440347865478577)
            ·
              refine ⟨473321142330260899108933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631094856440347865478577 473321142330260899108933)
              ·
                refine ⟨88747714186923918582925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473321142330260899108933 88747714186923918582925)
                ·
                  rfl

theorem cell19_291660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_291660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291660 prefixEnd_291660 := by exact prefixLift 291660
  have htrace : WordTrace (prefixWord ++ tailWord_291660) baseStart_291660 baseEnd_291660 := by
    simpa [prefixWord, tailWord_291660, baseEnd_291660] using wordTrace_append hprefix tailTrace_291660
  have hstable : (prefixWord ++ tailWord_291660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291660).length < 2 ^ (prefixWord ++ tailWord_291660).sum := by decide
  have hdescent : baseEnd_291660 < baseStart_291660 := by decide
  rcases family_descends (prefixWord ++ tailWord_291660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291717 : List Nat := [1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_291717 : Nat := 118140960795 + 291717 * 2 ^ 59
def prefixEnd_291717 : Nat := 4983230072969 + 3 ^ 40 * 291717 * 2
def baseEnd_291717 : Nat := 88765058422364675316103

theorem tailTrace_291717 : CollatzResearch.WordTrace tailWord_291717 prefixEnd_291717 88765058422364675316103 := by
  unfold tailWord_291717
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639793084166605142233405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7093195389444403428155603 10639793084166605142233405)
  ·
    refine ⟨3989922406562476928337527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10639793084166605142233405 3989922406562476928337527)
    ·
      refine ⟨5984883609843715392506291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3989922406562476928337527 5984883609843715392506291)
      ·
        refine ⟨8977325414765573088759437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5984883609843715392506291 8977325414765573088759437)
        ·
          refine ⟨3366497030537089908284789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8977325414765573088759437 3366497030537089908284789)
          ·
            refine ⟨315609096612852178901699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3366497030537089908284789 315609096612852178901699)
            ·
              refine ⟨473413644919278268352549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315609096612852178901699 473413644919278268352549)
              ·
                refine ⟨88765058422364675316103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473413644919278268352549 88765058422364675316103)
                ·
                  rfl

theorem cell19_291717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_291717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291717 prefixEnd_291717 := by exact prefixLift 291717
  have htrace : WordTrace (prefixWord ++ tailWord_291717) baseStart_291717 baseEnd_291717 := by
    simpa [prefixWord, tailWord_291717, baseEnd_291717] using wordTrace_append hprefix tailTrace_291717
  have hstable : (prefixWord ++ tailWord_291717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291717).length < 2 ^ (prefixWord ++ tailWord_291717).sum := by decide
  have hdescent : baseEnd_291717 < baseStart_291717 := by decide
  rcases family_descends (prefixWord ++ tailWord_291717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291810 : List Nat := [3, 3, 3, 1, 1, 3, 5]
def baseStart_291810 : Nat := 118140960795 + 291810 * 2 ^ 59
def prefixEnd_291810 : Nat := 4983230072969 + 3 ^ 40 * 291810 * 2
def baseEnd_291810 : Nat := 29597785637256005083061

theorem tailTrace_291810 : CollatzResearch.WordTrace tailWord_291810 prefixEnd_291810 29597785637256005083061 := by
  unfold tailWord_291810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660796268207420506342221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7095456715219788016912589 2660796268207420506342221)
  ·
    refine ⟨997798600577782689878333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2660796268207420506342221 997798600577782689878333)
    ·
      refine ⟨374174475216668508704375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 997798600577782689878333 374174475216668508704375)
      ·
        refine ⟨561261712825002763056563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374174475216668508704375 561261712825002763056563)
        ·
          refine ⟨841892569237504144584845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561261712825002763056563 841892569237504144584845)
          ·
            refine ⟨315709713464064054219317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 841892569237504144584845 315709713464064054219317)
            ·
              refine ⟨29597785637256005083061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 315709713464064054219317 29597785637256005083061)
              ·
                rfl

theorem cell19_291810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_291810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291810 prefixEnd_291810 := by exact prefixLift 291810
  have htrace : WordTrace (prefixWord ++ tailWord_291810) baseStart_291810 baseEnd_291810 := by
    simpa [prefixWord, tailWord_291810, baseEnd_291810] using wordTrace_append hprefix tailTrace_291810
  have hstable : (prefixWord ++ tailWord_291810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291810).length < 2 ^ (prefixWord ++ tailWord_291810).sum := by decide
  have hdescent : baseEnd_291810 < baseStart_291810 := by decide
  rcases family_descends (prefixWord ++ tailWord_291810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291833 : List Nat := [1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_291833 : Nat := 118140960795 + 291833 * 2 ^ 59
def prefixEnd_291833 : Nat := 4983230072969 + 3 ^ 40 * 291833 * 2
def baseEnd_291833 : Nat := 88800355462910776738009

theorem tailTrace_291833 : CollatzResearch.WordTrace tailWord_291833 prefixEnd_291833 88800355462910776738009 := by
  unfold tailWord_291833
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644023951746356953456153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7096015967830904635637435 10644023951746356953456153)
  ·
    refine ⟨7983017963809767715092115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10644023951746356953456153 7983017963809767715092115)
    ·
      refine ⟨11974526945714651572638173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983017963809767715092115 11974526945714651572638173)
      ·
        refine ⟨4490447604642994339739315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11974526945714651572638173 4490447604642994339739315)
        ·
          refine ⟨6735671406964491509608973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490447604642994339739315 6735671406964491509608973)
          ·
            refine ⟨2525876777611684316103365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6735671406964491509608973 2525876777611684316103365)
            ·
              refine ⟨473601895802190809269381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2525876777611684316103365 473601895802190809269381)
              ·
                refine ⟨88800355462910776738009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473601895802190809269381 88800355462910776738009)
                ·
                  rfl

theorem cell19_291833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_291833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291833 prefixEnd_291833 := by exact prefixLift 291833
  have htrace : WordTrace (prefixWord ++ tailWord_291833) baseStart_291833 baseEnd_291833 := by
    simpa [prefixWord, tailWord_291833, baseEnd_291833] using wordTrace_append hprefix tailTrace_291833
  have hstable : (prefixWord ++ tailWord_291833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291833).length < 2 ^ (prefixWord ++ tailWord_291833).sum := by decide
  have hdescent : baseEnd_291833 < baseStart_291833 := by decide
  rcases family_descends (prefixWord ++ tailWord_291833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291852 : List Nat := [2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_291852 : Nat := 118140960795 + 291852 * 2 ^ 59
def prefixEnd_291852 : Nat := 4983230072969 + 3 ^ 40 * 291852 * 2
def baseEnd_291852 : Nat := 88806136874724362315735

theorem tailTrace_291852 : CollatzResearch.WordTrace tailWord_291852 prefixEnd_291852 88806136874724362315735 := by
  unfold tailWord_291852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322358469338761599198905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7096477959118348798931873 5322358469338761599198905)
  ·
    refine ⟨3991768852004071199399179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5322358469338761599198905 3991768852004071199399179)
    ·
      refine ⟨5987653278006106799098769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3991768852004071199399179 5987653278006106799098769)
      ·
        refine ⟨4490739958504580099324077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5987653278006106799098769 4490739958504580099324077)
        ·
          refine ⟨1684027484439217537246529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4490739958504580099324077 1684027484439217537246529)
          ·
            refine ⟨1263020613329413152934897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684027484439217537246529 1263020613329413152934897)
            ·
              refine ⟨947265459997059864701173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263020613329413152934897 947265459997059864701173)
              ·
                refine ⟨88806136874724362315735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 947265459997059864701173 88806136874724362315735)
                ·
                  rfl

theorem cell19_291852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_291852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291852 prefixEnd_291852 := by exact prefixLift 291852
  have htrace : WordTrace (prefixWord ++ tailWord_291852) baseStart_291852 baseEnd_291852 := by
    simpa [prefixWord, tailWord_291852, baseEnd_291852] using wordTrace_append hprefix tailTrace_291852
  have hstable : (prefixWord ++ tailWord_291852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291852).length < 2 ^ (prefixWord ++ tailWord_291852).sum := by decide
  have hdescent : baseEnd_291852 < baseStart_291852 := by decide
  rcases family_descends (prefixWord ++ tailWord_291852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291869 : List Nat := [1, 4, 2, 2, 4, 6]
def baseStart_291869 : Nat := 118140960795 + 291869 * 2 ^ 59
def prefixEnd_291869 : Nat := 4983230072969 + 3 ^ 40 * 291869 * 2
def baseEnd_291869 : Nat := 9867923301874817770879

theorem tailTrace_291869 : CollatzResearch.WordTrace tailWord_291869 prefixEnd_291869 9867923301874817770879 := by
  unfold tailWord_291869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645336979615935101766661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7096891319743956734511107 10645336979615935101766661)
  ·
    refine ⟨1996000683677987831581249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10645336979615935101766661 1996000683677987831581249)
    ·
      refine ⟨1497000512758490873685937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1996000683677987831581249 1497000512758490873685937)
      ·
        refine ⟨1122750384568868155264453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497000512758490873685937 1122750384568868155264453)
        ·
          refine ⟨210515697106662779112085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1122750384568868155264453 210515697106662779112085)
          ·
            refine ⟨9867923301874817770879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 210515697106662779112085 9867923301874817770879)
            ·
              rfl

theorem cell19_291869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_291869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291869 prefixEnd_291869 := by exact prefixLift 291869
  have htrace : WordTrace (prefixWord ++ tailWord_291869) baseStart_291869 baseEnd_291869 := by
    simpa [prefixWord, tailWord_291869, baseEnd_291869] using wordTrace_append hprefix tailTrace_291869
  have hstable : (prefixWord ++ tailWord_291869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291869).length < 2 ^ (prefixWord ++ tailWord_291869).sum := by decide
  have hdescent : baseEnd_291869 < baseStart_291869 := by decide
  rcases family_descends (prefixWord ++ tailWord_291869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291905 : List Nat := [1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_291905 : Nat := 118140960795 + 291905 * 2 ^ 59
def prefixEnd_291905 : Nat := 4983230072969 + 3 ^ 40 * 291905 * 2
def baseEnd_291905 : Nat := 88822263970835943137813

theorem tailTrace_291905 : CollatzResearch.WordTrace tailWord_291905 prefixEnd_291905 88822263970835943137813 := by
  unfold tailWord_291905
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646650007485513250077169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7097766671657008833384779 10646650007485513250077169)
  ·
    refine ⟨7984987505614134937557877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10646650007485513250077169 7984987505614134937557877)
    ·
      refine ⟨748592578651325150396051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7984987505614134937557877 748592578651325150396051)
      ·
        refine ⟨1122888867976987725594077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748592578651325150396051 1122888867976987725594077)
        ·
          refine ⟨421083325491370397097779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1122888867976987725594077 421083325491370397097779)
          ·
            refine ⟨631624988237055595646669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421083325491370397097779 631624988237055595646669)
            ·
              refine ⟨236859370588895848367501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 631624988237055595646669 236859370588895848367501)
              ·
                refine ⟨88822263970835943137813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236859370588895848367501 88822263970835943137813)
                ·
                  rfl

theorem cell19_291905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_291905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291905 prefixEnd_291905 := by exact prefixLift 291905
  have htrace : WordTrace (prefixWord ++ tailWord_291905) baseStart_291905 baseEnd_291905 := by
    simpa [prefixWord, tailWord_291905, baseEnd_291905] using wordTrace_append hprefix tailTrace_291905
  have hstable : (prefixWord ++ tailWord_291905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291905).length < 2 ^ (prefixWord ++ tailWord_291905).sum := by decide
  have hdescent : baseEnd_291905 < baseStart_291905 := by decide
  rcases family_descends (prefixWord ++ tailWord_291905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_291987 : List Nat := [1, 1, 1, 2, 1, 2, 11]
def baseStart_291987 : Nat := 118140960795 + 291987 * 2 ^ 59
def prefixEnd_291987 : Nat := 4983230072969 + 3 ^ 40 * 291987 * 2
def baseEnd_291987 : Nat := 29615738442361349771789

theorem tailTrace_291987 : CollatzResearch.WordTrace tailWord_291987 prefixEnd_291987 29615738442361349771789 := by
  unfold tailWord_291987
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649640793188441254562215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7099760528792294169708143 10649640793188441254562215)
  ·
    refine ⟨15974461189782661881843323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10649640793188441254562215 15974461189782661881843323)
    ·
      refine ⟨23961691784673992822764985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15974461189782661881843323 23961691784673992822764985)
      ·
        refine ⟨17971268838505494617073739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23961691784673992822764985 17971268838505494617073739)
        ·
          refine ⟨26956903257758241925610609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17971268838505494617073739 26956903257758241925610609)
          ·
            refine ⟨20217677443318681444207957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26956903257758241925610609 20217677443318681444207957)
            ·
              refine ⟨29615738442361349771789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20217677443318681444207957 29615738442361349771789)
              ·
                rfl

theorem cell19_291987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_291987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_291987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_291987 prefixEnd_291987 := by exact prefixLift 291987
  have htrace : WordTrace (prefixWord ++ tailWord_291987) baseStart_291987 baseEnd_291987 := by
    simpa [prefixWord, tailWord_291987, baseEnd_291987] using wordTrace_append hprefix tailTrace_291987
  have hstable : (prefixWord ++ tailWord_291987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_291987).length < 2 ^ (prefixWord ++ tailWord_291987).sum := by decide
  have hdescent : baseEnd_291987 < baseStart_291987 := by decide
  rcases family_descends (prefixWord ++ tailWord_291987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292004 : List Nat := [2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_292004 : Nat := 118140960795 + 292004 * 2 ^ 59
def prefixEnd_292004 : Nat := 4983230072969 + 3 ^ 40 * 292004 * 2
def baseEnd_292004 : Nat := 88852388169233046937543

theorem tailTrace_292004 : CollatzResearch.WordTrace tailWord_292004 prefixEnd_292004 88852388169233046937543 := by
  unfold tailWord_292004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325130417063426578965533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7100173889417902105287377 5325130417063426578965533)
  ·
    refine ⟨1996923906398784967112075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5325130417063426578965533 1996923906398784967112075)
    ·
      refine ⟨2995385859598177450668113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996923906398784967112075 2995385859598177450668113)
      ·
        refine ⟨2246539394698633088001085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2995385859598177450668113 2246539394698633088001085)
        ·
          refine ⟨842452273011987408000407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2246539394698633088001085 842452273011987408000407)
          ·
            refine ⟨1263678409517981112000611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842452273011987408000407 1263678409517981112000611)
            ·
              refine ⟨1895517614276971668000917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263678409517981112000611 1895517614276971668000917)
              ·
                refine ⟨88852388169233046937543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1895517614276971668000917 88852388169233046937543)
                ·
                  rfl

theorem cell19_292004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_292004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292004 prefixEnd_292004 := by exact prefixLift 292004
  have htrace : WordTrace (prefixWord ++ tailWord_292004) baseStart_292004 baseEnd_292004 := by
    simpa [prefixWord, tailWord_292004, baseEnd_292004] using wordTrace_append hprefix tailTrace_292004
  have hstable : (prefixWord ++ tailWord_292004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292004).length < 2 ^ (prefixWord ++ tailWord_292004).sum := by decide
  have hdescent : baseEnd_292004 < baseStart_292004 := by decide
  rcases family_descends (prefixWord ++ tailWord_292004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292038 : List Nat := [6, 1, 2, 2, 8]
def baseStart_292038 : Nat := 118140960795 + 292038 * 2 ^ 59
def prefixEnd_292038 : Nat := 4983230072969 + 3 ^ 40 * 292038 * 2
def baseEnd_292038 : Nat := 3291212364945594154885

theorem tailTrace_292038 : CollatzResearch.WordTrace tailWord_292038 prefixEnd_292038 3291212364945594154885 := by
  unfold tailWord_292038
  simp only [CollatzResearch.WordTrace]
  refine ⟨332859403625114905145899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7101000610669117976445845 332859403625114905145899)
  ·
    refine ⟨499289105437672357718849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 332859403625114905145899 499289105437672357718849)
    ·
      refine ⟨374466829078254268289137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 499289105437672357718849 374466829078254268289137)
      ·
        refine ⟨280850121808690701216853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 374466829078254268289137 280850121808690701216853)
        ·
          refine ⟨3291212364945594154885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 280850121808690701216853 3291212364945594154885)
          ·
            rfl

theorem cell19_292038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 8].length) (baseStart_292038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292038 prefixEnd_292038 := by exact prefixLift 292038
  have htrace : WordTrace (prefixWord ++ tailWord_292038) baseStart_292038 baseEnd_292038 := by
    simpa [prefixWord, tailWord_292038, baseEnd_292038] using wordTrace_append hprefix tailTrace_292038
  have hstable : (prefixWord ++ tailWord_292038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292038).length < 2 ^ (prefixWord ++ tailWord_292038).sum := by decide
  have hdescent : baseEnd_292038 < baseStart_292038 := by decide
  rcases family_descends (prefixWord ++ tailWord_292038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292044 : List Nat := [2, 2, 1, 14]
def baseStart_292044 : Nat := 118140960795 + 292044 * 2 ^ 59
def prefixEnd_292044 : Nat := 4983230072969 + 3 ^ 40 * 292044 * 2
def baseEnd_292044 : Nat := 1097093327932405012945

theorem tailTrace_292044 : CollatzResearch.WordTrace tailWord_292044 prefixEnd_292044 1097093327932405012945 := by
  unfold tailWord_292044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325859876990969994693593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7101146502654626659591457 5325859876990969994693593)
  ·
    refine ⟨3994394907743227496020195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5325859876990969994693593 3994394907743227496020195)
    ·
      refine ⟨5991592361614841244030293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994394907743227496020195 5991592361614841244030293)
      ·
        refine ⟨1097093327932405012945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5991592361614841244030293 1097093327932405012945)
        ·
          rfl

theorem cell19_292044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 14].length) (baseStart_292044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292044 prefixEnd_292044 := by exact prefixLift 292044
  have htrace : WordTrace (prefixWord ++ tailWord_292044) baseStart_292044 baseEnd_292044 := by
    simpa [prefixWord, tailWord_292044, baseEnd_292044] using wordTrace_append hprefix tailTrace_292044
  have hstable : (prefixWord ++ tailWord_292044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292044).length < 2 ^ (prefixWord ++ tailWord_292044).sum := by decide
  have hdescent : baseEnd_292044 < baseStart_292044 := by decide
  rcases family_descends (prefixWord ++ tailWord_292044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292101 : List Nat := [1, 3, 1, 1, 2, 1, 10]
def baseStart_292101 : Nat := 118140960795 + 292101 * 2 ^ 59
def prefixEnd_292101 : Nat := 4983230072969 + 3 ^ 40 * 292101 * 2
def baseEnd_292101 : Nat := 29627301265988520927241

theorem tailTrace_292101 : CollatzResearch.WordTrace tailWord_292101 prefixEnd_292101 29627301265988520927241 := by
  unfold tailWord_292101
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653798714775438724212157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7102532476516959149474771 10653798714775438724212157)
  ·
    refine ⟨3995174518040789521579559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10653798714775438724212157 3995174518040789521579559)
    ·
      refine ⟨5992761777061184282369339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995174518040789521579559 5992761777061184282369339)
      ·
        refine ⟨8989142665591776423554009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5992761777061184282369339 8989142665591776423554009)
        ·
          refine ⟨6741856999193832317665507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8989142665591776423554009 6741856999193832317665507)
          ·
            refine ⟨10112785498790748476498261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6741856999193832317665507 10112785498790748476498261)
            ·
              refine ⟨29627301265988520927241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10112785498790748476498261 29627301265988520927241)
              ·
                rfl

theorem cell19_292101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_292101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292101 prefixEnd_292101 := by exact prefixLift 292101
  have htrace : WordTrace (prefixWord ++ tailWord_292101) baseStart_292101 baseEnd_292101 := by
    simpa [prefixWord, tailWord_292101, baseEnd_292101] using wordTrace_append hprefix tailTrace_292101
  have hstable : (prefixWord ++ tailWord_292101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292101).length < 2 ^ (prefixWord ++ tailWord_292101).sum := by decide
  have hdescent : baseEnd_292101 < baseStart_292101 := by decide
  rcases family_descends (prefixWord ++ tailWord_292101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292150 : List Nat := [5, 1, 2, 3, 2, 1, 5]
def baseStart_292150 : Nat := 118140960795 + 292150 * 2 ^ 59
def prefixEnd_292150 : Nat := 4983230072969 + 3 ^ 40 * 292150 * 2
def baseEnd_292150 : Nat := 29632271251582655897567

theorem tailTrace_292150 : CollatzResearch.WordTrace tailWord_292150 prefixEnd_292150 29632271251582655897567 := by
  unfold tailWord_292150
  simp only [CollatzResearch.WordTrace]
  refine ⟨665974118224870005796619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7103723927731946728497269 665974118224870005796619)
  ·
    refine ⟨998961177337305008694929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665974118224870005796619 998961177337305008694929)
    ·
      refine ⟨749220883002978756521197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 998961177337305008694929 749220883002978756521197)
      ·
        refine ⟨280957831126117033695449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 749220883002978756521197 280957831126117033695449)
        ·
          refine ⟨210718373344587775271587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280957831126117033695449 210718373344587775271587)
          ·
            refine ⟨316077560016881662907381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210718373344587775271587 316077560016881662907381)
            ·
              refine ⟨29632271251582655897567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 316077560016881662907381 29632271251582655897567)
              ·
                rfl

theorem cell19_292150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_292150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292150 prefixEnd_292150 := by exact prefixLift 292150
  have htrace : WordTrace (prefixWord ++ tailWord_292150) baseStart_292150 baseEnd_292150 := by
    simpa [prefixWord, tailWord_292150, baseEnd_292150] using wordTrace_append hprefix tailTrace_292150
  have hstable : (prefixWord ++ tailWord_292150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292150).length < 2 ^ (prefixWord ++ tailWord_292150).sum := by decide
  have hdescent : baseEnd_292150 < baseStart_292150 := by decide
  rcases family_descends (prefixWord ++ tailWord_292150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292156 : List Nat := [2, 2, 2, 2, 1, 5, 5]
def baseStart_292156 : Nat := 118140960795 + 292156 * 2 ^ 59
def prefixEnd_292156 : Nat := 4983230072969 + 3 ^ 40 * 292156 * 2
def baseEnd_292156 : Nat := 29632879821247243853117

theorem tailTrace_292156 : CollatzResearch.WordTrace tailWord_292156 prefixEnd_292156 29632879821247243853117 := by
  unfold tailWord_292156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327902364788091558732161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7103869819717455411642881 5327902364788091558732161)
  ·
    refine ⟨3995926773591068669049121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5327902364788091558732161 3995926773591068669049121)
    ·
      refine ⟨2996945080193301501786841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3995926773591068669049121 2996945080193301501786841)
      ·
        refine ⟨2247708810144976126340131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2996945080193301501786841 2247708810144976126340131)
        ·
          refine ⟨3371563215217464189510197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247708810144976126340131 3371563215217464189510197)
          ·
            refine ⟨316084051426637267766581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3371563215217464189510197 316084051426637267766581)
            ·
              refine ⟨29632879821247243853117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 316084051426637267766581 29632879821247243853117)
              ·
                rfl

theorem cell19_292156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_292156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292156 prefixEnd_292156 := by exact prefixLift 292156
  have htrace : WordTrace (prefixWord ++ tailWord_292156) baseStart_292156 baseEnd_292156 := by
    simpa [prefixWord, tailWord_292156, baseEnd_292156] using wordTrace_append hprefix tailTrace_292156
  have hstable : (prefixWord ++ tailWord_292156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292156).length < 2 ^ (prefixWord ++ tailWord_292156).sum := by decide
  have hdescent : baseEnd_292156 < baseStart_292156 := by decide
  rcases family_descends (prefixWord ++ tailWord_292156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292194 : List Nat := [3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_292194 : Nat := 118140960795 + 292194 * 2 ^ 59
def prefixEnd_292194 : Nat := 4983230072969 + 3 ^ 40 * 292194 * 2
def baseEnd_292194 : Nat := 88910202287368902714803

theorem tailTrace_292194 : CollatzResearch.WordTrace tailWord_292194 prefixEnd_292194 88910202287368902714803 := by
  unfold tailWord_292194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664297675859628901836909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7104793802292343738231757 2664297675859628901836909)
  ·
    refine ⟨999111628447360838188841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2664297675859628901836909 999111628447360838188841)
    ·
      refine ⟨749333721335520628641631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999111628447360838188841 749333721335520628641631)
      ·
        refine ⟨1124000582003280942962447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749333721335520628641631 1124000582003280942962447)
        ·
          refine ⟨1686000873004921414443671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124000582003280942962447 1686000873004921414443671)
          ·
            refine ⟨2529001309507382121665507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686000873004921414443671 2529001309507382121665507)
            ·
              refine ⟨3793501964261073182498261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529001309507382121665507 3793501964261073182498261)
              ·
                refine ⟨88910202287368902714803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3793501964261073182498261 88910202287368902714803)
                ·
                  rfl

theorem cell19_292194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_292194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292194 prefixEnd_292194 := by exact prefixLift 292194
  have htrace : WordTrace (prefixWord ++ tailWord_292194) baseStart_292194 baseEnd_292194 := by
    simpa [prefixWord, tailWord_292194, baseEnd_292194] using wordTrace_append hprefix tailTrace_292194
  have hstable : (prefixWord ++ tailWord_292194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292194).length < 2 ^ (prefixWord ++ tailWord_292194).sum := by decide
  have hdescent : baseEnd_292194 < baseStart_292194 := by decide
  rcases family_descends (prefixWord ++ tailWord_292194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292213 : List Nat := [1, 3, 4, 1, 3, 7]
def baseStart_292213 : Nat := 118140960795 + 292213 * 2 ^ 59
def prefixEnd_292213 : Nat := 4983230072969 + 3 ^ 40 * 292213 * 2
def baseEnd_292213 : Nat := 9879553744353609810281

theorem tailTrace_292213 : CollatzResearch.WordTrace tailWord_292213 prefixEnd_292213 9879553744353609810281 := by
  unfold tailWord_292213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657883690369681852289293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7105255793579787901526195 10657883690369681852289293)
  ·
    refine ⟨3996706383888630694608485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10657883690369681852289293 3996706383888630694608485)
    ·
      refine ⟨749382446979118255239091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3996706383888630694608485 749382446979118255239091)
      ·
        refine ⟨1124073670468677382858637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749382446979118255239091 1124073670468677382858637)
        ·
          refine ⟨421527626425754018571989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1124073670468677382858637 421527626425754018571989)
          ·
            refine ⟨9879553744353609810281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 421527626425754018571989 9879553744353609810281)
            ·
              rfl

theorem cell19_292213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_292213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292213 prefixEnd_292213 := by exact prefixLift 292213
  have htrace : WordTrace (prefixWord ++ tailWord_292213) baseStart_292213 baseEnd_292213 := by
    simpa [prefixWord, tailWord_292213, baseEnd_292213] using wordTrace_append hprefix tailTrace_292213
  have hstable : (prefixWord ++ tailWord_292213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292213).length < 2 ^ (prefixWord ++ tailWord_292213).sum := by decide
  have hdescent : baseEnd_292213 < baseStart_292213 := by decide
  rcases family_descends (prefixWord ++ tailWord_292213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292232 : List Nat := [2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_292232 : Nat := 118140960795 + 292232 * 2 ^ 59
def prefixEnd_292232 : Nat := 4983230072969 + 3 ^ 40 * 292232 * 2
def baseEnd_292232 : Nat := 88921765110996073870255

theorem tailTrace_292232 : CollatzResearch.WordTrace tailWord_292232 prefixEnd_292232 88921765110996073870255 := by
  unfold tailWord_292232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329288338650424048615475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7105717784867232064820633 5329288338650424048615475)
  ·
    refine ⟨7993932507975636072923213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5329288338650424048615475 7993932507975636072923213)
    ·
      refine ⟨2997724690490863527346205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7993932507975636072923213 2997724690490863527346205)
      ·
        refine ⟨1124146758934073822754827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2997724690490863527346205 1124146758934073822754827)
        ·
          refine ⟨1686220138401110734132241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124146758934073822754827 1686220138401110734132241)
          ·
            refine ⟨1264665103800833050599181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686220138401110734132241 1264665103800833050599181)
            ·
              refine ⟨474249413925312393974693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264665103800833050599181 474249413925312393974693)
              ·
                refine ⟨88921765110996073870255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474249413925312393974693 88921765110996073870255)
                ·
                  rfl

theorem cell19_292232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_292232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292232 prefixEnd_292232 := by exact prefixLift 292232
  have htrace : WordTrace (prefixWord ++ tailWord_292232) baseStart_292232 baseEnd_292232 := by
    simpa [prefixWord, tailWord_292232, baseEnd_292232] using wordTrace_append hprefix tailTrace_292232
  have hstable : (prefixWord ++ tailWord_292232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292232).length < 2 ^ (prefixWord ++ tailWord_292232).sum := by decide
  have hdescent : baseEnd_292232 < baseStart_292232 := by decide
  rcases family_descends (prefixWord ++ tailWord_292232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292327 : List Nat := [1, 1, 5, 2, 1, 4, 5]
def baseStart_292327 : Nat := 118140960795 + 292327 * 2 ^ 59
def prefixEnd_292327 : Nat := 4983230072969 + 3 ^ 40 * 292327 * 2
def baseEnd_292327 : Nat := 29650224056688000586295

theorem tailTrace_292327 : CollatzResearch.WordTrace tailWord_292327 prefixEnd_292327 29650224056688000586295 := by
  unfold tailWord_292327
  simp only [CollatzResearch.WordTrace]
  refine ⟨10662041611956679321939235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7108027741304452881292823 10662041611956679321939235)
  ·
    refine ⟨15993062417935018982908853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10662041611956679321939235 15993062417935018982908853)
    ·
      refine ⟨1499349601681408029647705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15993062417935018982908853 1499349601681408029647705)
      ·
        refine ⟨1124512201261056022235779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1499349601681408029647705 1124512201261056022235779)
        ·
          refine ⟨1686768301891584033353669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124512201261056022235779 1686768301891584033353669)
          ·
            refine ⟨316269056604672006253813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1686768301891584033353669 316269056604672006253813)
            ·
              refine ⟨29650224056688000586295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 316269056604672006253813 29650224056688000586295)
              ·
                rfl

theorem cell19_292327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_292327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292327 prefixEnd_292327 := by exact prefixLift 292327
  have htrace : WordTrace (prefixWord ++ tailWord_292327) baseStart_292327 baseEnd_292327 := by
    simpa [prefixWord, tailWord_292327, baseEnd_292327] using wordTrace_append hprefix tailTrace_292327
  have hstable : (prefixWord ++ tailWord_292327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292327).length < 2 ^ (prefixWord ++ tailWord_292327).sum := by decide
  have hdescent : baseEnd_292327 < baseStart_292327 := by decide
  rcases family_descends (prefixWord ++ tailWord_292327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292348 : List Nat := [2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_292348 : Nat := 118140960795 + 292348 * 2 ^ 59
def prefixEnd_292348 : Nat := 4983230072969 + 3 ^ 40 * 292348 * 2
def baseEnd_292348 : Nat := 88957062151542175292161

theorem tailTrace_292348 : CollatzResearch.WordTrace tailWord_292348 prefixEnd_292348 88957062151542175292161 := by
  unfold tailWord_292348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331403772440299954226849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7108538363253733272302465 5331403772440299954226849)
  ·
    refine ⟨3998552829330224965670137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5331403772440299954226849 3998552829330224965670137)
    ·
      refine ⟨2998914621997668724252603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3998552829330224965670137 2998914621997668724252603)
      ·
        refine ⟨4498371932996503086378905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2998914621997668724252603 4498371932996503086378905)
        ·
          refine ⟨3373778949747377314784179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4498371932996503086378905 3373778949747377314784179)
          ·
            refine ⟨5060668424621065972176269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373778949747377314784179 5060668424621065972176269)
            ·
              refine ⟨1897750659232899739566101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5060668424621065972176269 1897750659232899739566101)
              ·
                refine ⟨88957062151542175292161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1897750659232899739566101 88957062151542175292161)
                ·
                  rfl

theorem cell19_292348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_292348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292348 prefixEnd_292348 := by exact prefixLift 292348
  have htrace : WordTrace (prefixWord ++ tailWord_292348) baseStart_292348 baseEnd_292348 := by
    simpa [prefixWord, tailWord_292348, baseEnd_292348] using wordTrace_append hprefix tailTrace_292348
  have hstable : (prefixWord ++ tailWord_292348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292348).length < 2 ^ (prefixWord ++ tailWord_292348).sum := by decide
  have hdescent : baseEnd_292348 < baseStart_292348 := by decide
  rcases family_descends (prefixWord ++ tailWord_292348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292403 : List Nat := [1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_292403 : Nat := 118140960795 + 292403 * 2 ^ 59
def prefixEnd_292403 : Nat := 4983230072969 + 3 ^ 40 * 292403 * 2
def baseEnd_292403 : Nat := 88973797817318344069789

theorem tailTrace_292403 : CollatzResearch.WordTrace tailWord_292403 prefixEnd_292403 88973797817318344069789 := by
  unfold tailWord_292403
  simp only [CollatzResearch.WordTrace]
  refine ⟨10664813559681344301705863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7109875706454229534470575 10664813559681344301705863)
  ·
    refine ⟨15997220339522016452558795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10664813559681344301705863 15997220339522016452558795)
    ·
      refine ⟨23995830509283024678838193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15997220339522016452558795 23995830509283024678838193)
      ·
        refine ⟨17996872881962268509128645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23995830509283024678838193 17996872881962268509128645)
        ·
          refine ⟨3374413665367925345461621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17996872881962268509128645 3374413665367925345461621)
          ·
            refine ⟨316351281128243001137027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3374413665367925345461621 316351281128243001137027)
            ·
              refine ⟨474526921692364501705541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316351281128243001137027 474526921692364501705541)
              ·
                refine ⟨88973797817318344069789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474526921692364501705541 88973797817318344069789)
                ·
                  rfl

theorem cell19_292403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_292403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292403 prefixEnd_292403 := by exact prefixLift 292403
  have htrace : WordTrace (prefixWord ++ tailWord_292403) baseStart_292403 baseEnd_292403 := by
    simpa [prefixWord, tailWord_292403, baseEnd_292403] using wordTrace_append hprefix tailTrace_292403
  have hstable : (prefixWord ++ tailWord_292403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292403).length < 2 ^ (prefixWord ++ tailWord_292403).sum := by decide
  have hdescent : baseEnd_292403 < baseStart_292403 := by decide
  rcases family_descends (prefixWord ++ tailWord_292403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292477 : List Nat := [1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_292477 : Nat := 118140960795 + 292477 * 2 ^ 59
def prefixEnd_292477 : Nat := 4983230072969 + 3 ^ 40 * 292477 * 2
def baseEnd_292477 : Nat := 88996314894908098425143

theorem tailTrace_292477 : CollatzResearch.WordTrace tailWord_292477 prefixEnd_292477 88996314894908098425143 := by
  unfold tailWord_292477
  simp only [CollatzResearch.WordTrace]
  refine ⟨10667512561413254939899685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7111675040942169959933123 10667512561413254939899685)
  ·
    refine ⟨2000158605264985301231191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10667512561413254939899685 2000158605264985301231191)
    ·
      refine ⟨3000237907897477951846787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000158605264985301231191 3000237907897477951846787)
      ·
        refine ⟨4500356861846216927770181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000237907897477951846787 4500356861846216927770181)
        ·
          refine ⟨843816911596165673956909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4500356861846216927770181 843816911596165673956909)
          ·
            refine ⟨316431341848562127733841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 843816911596165673956909 316431341848562127733841)
            ·
              refine ⟨237323506386421595800381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316431341848562127733841 237323506386421595800381)
              ·
                refine ⟨88996314894908098425143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237323506386421595800381 88996314894908098425143)
                ·
                  rfl

theorem cell19_292477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_292477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292477 prefixEnd_292477 := by exact prefixLift 292477
  have htrace : WordTrace (prefixWord ++ tailWord_292477) baseStart_292477 baseEnd_292477 := by
    simpa [prefixWord, tailWord_292477, baseEnd_292477] using wordTrace_append hprefix tailTrace_292477
  have hstable : (prefixWord ++ tailWord_292477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292477).length < 2 ^ (prefixWord ++ tailWord_292477).sum := by decide
  have hdescent : baseEnd_292477 < baseStart_292477 := by decide
  rcases family_descends (prefixWord ++ tailWord_292477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292534 : List Nat := [5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_292534 : Nat := 118140960795 + 292534 * 2 ^ 59
def prefixEnd_292534 : Nat := 4983230072969 + 3 ^ 40 * 292534 * 2
def baseEnd_292534 : Nat := 89013659130348855158321

theorem tailTrace_292534 : CollatzResearch.WordTrace tailWord_292534 prefixEnd_292534 89013659130348855158321 := by
  unfold tailWord_292534
  simp only [CollatzResearch.WordTrace]
  refine ⟨666849470137922104670291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7113061014804502449816437 666849470137922104670291)
  ·
    refine ⟨1000274205206883157005437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666849470137922104670291 1000274205206883157005437)
    ·
      refine ⟨375102826952581183877039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1000274205206883157005437 375102826952581183877039)
      ·
        refine ⟨562654240428871775815559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375102826952581183877039 562654240428871775815559)
        ·
          refine ⟨843981360643307663723339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562654240428871775815559 843981360643307663723339)
          ·
            refine ⟨1265972040964961495585009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843981360643307663723339 1265972040964961495585009)
            ·
              refine ⟨949479030723721121688757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265972040964961495585009 949479030723721121688757)
              ·
                refine ⟨89013659130348855158321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 949479030723721121688757 89013659130348855158321)
                ·
                  rfl

theorem cell19_292534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_292534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292534 prefixEnd_292534 := by exact prefixLift 292534
  have htrace : WordTrace (prefixWord ++ tailWord_292534) baseStart_292534 baseEnd_292534 := by
    simpa [prefixWord, tailWord_292534, baseEnd_292534] using wordTrace_append hprefix tailTrace_292534
  have hstable : (prefixWord ++ tailWord_292534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292534).length < 2 ^ (prefixWord ++ tailWord_292534).sum := by decide
  have hdescent : baseEnd_292534 < baseStart_292534 := by decide
  rcases family_descends (prefixWord ++ tailWord_292534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292538 : List Nat := [3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_292538 : Nat := 118140960795 + 292538 * 2 ^ 59
def prefixEnd_292538 : Nat := 4983230072969 + 3 ^ 40 * 292538 * 2
def baseEnd_292538 : Nat := 89014876269678031069421

theorem tailTrace_292538 : CollatzResearch.WordTrace tailWord_292538 prefixEnd_292538 89014876269678031069421 := by
  unfold tailWord_292538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667434353548065589467567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7113158276128174905246845 2667434353548065589467567)
  ·
    refine ⟨4001151530322098384201351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2667434353548065589467567 4001151530322098384201351)
    ·
      refine ⟨6001727295483147576302027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4001151530322098384201351 6001727295483147576302027)
      ·
        refine ⟨9002590943224721364453041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6001727295483147576302027 9002590943224721364453041)
        ·
          refine ⟨6751943207418541023339781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9002590943224721364453041 6751943207418541023339781)
          ·
            refine ⟨1265989351390976441876209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6751943207418541023339781 1265989351390976441876209)
            ·
              refine ⟨949492013543232331407157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265989351390976441876209 949492013543232331407157)
              ·
                refine ⟨89014876269678031069421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 949492013543232331407157 89014876269678031069421)
                ·
                  rfl

theorem cell19_292538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_292538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292538 prefixEnd_292538 := by exact prefixLift 292538
  have htrace : WordTrace (prefixWord ++ tailWord_292538) baseStart_292538 baseEnd_292538 := by
    simpa [prefixWord, tailWord_292538, baseEnd_292538] using wordTrace_append hprefix tailTrace_292538
  have hstable : (prefixWord ++ tailWord_292538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292538).length < 2 ^ (prefixWord ++ tailWord_292538).sum := by decide
  have hdescent : baseEnd_292538 < baseStart_292538 := by decide
  rcases family_descends (prefixWord ++ tailWord_292538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292576 : List Nat := [2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_292576 : Nat := 118140960795 + 292576 * 2 ^ 59
def prefixEnd_292576 : Nat := 4983230072969 + 3 ^ 40 * 292576 * 2
def baseEnd_292576 : Nat := 89026439093305202224873

theorem tailTrace_292576 : CollatzResearch.WordTrace tailWord_292576 prefixEnd_292576 89026439093305202224873 := by
  unfold tailWord_292576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335561694027297423876791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7114082258703063231835721 5335561694027297423876791)
  ·
    refine ⟨8003342541040946135815187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5335561694027297423876791 8003342541040946135815187)
    ·
      refine ⟨12005013811561419203722781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8003342541040946135815187 12005013811561419203722781)
      ·
        refine ⟨4501880179335532201396043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12005013811561419203722781 4501880179335532201396043)
        ·
          refine ⟨6752820269003298302094065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501880179335532201396043 6752820269003298302094065)
          ·
            refine ⟨5064615201752473726570549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6752820269003298302094065 5064615201752473726570549)
            ·
              refine ⟨474807675164294411865989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5064615201752473726570549 474807675164294411865989)
              ·
                refine ⟨89026439093305202224873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474807675164294411865989 89026439093305202224873)
                ·
                  rfl

theorem cell19_292576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_292576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292576 prefixEnd_292576 := by exact prefixLift 292576
  have htrace : WordTrace (prefixWord ++ tailWord_292576) baseStart_292576 baseEnd_292576 := by
    simpa [prefixWord, tailWord_292576, baseEnd_292576] using wordTrace_append hprefix tailTrace_292576
  have hstable : (prefixWord ++ tailWord_292576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292576).length < 2 ^ (prefixWord ++ tailWord_292576).sum := by decide
  have hdescent : baseEnd_292576 < baseStart_292576 := by decide
  rcases family_descends (prefixWord ++ tailWord_292576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292593 : List Nat := [1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_292593 : Nat := 118140960795 + 292593 * 2 ^ 59
def prefixEnd_292593 : Nat := 4983230072969 + 3 ^ 40 * 292593 * 2
def baseEnd_292593 : Nat := 89031611935454199847049

theorem tailTrace_292593 : CollatzResearch.WordTrace tailWord_292593 prefixEnd_292593 89031611935454199847049 := by
  unfold tailWord_292593
  simp only [CollatzResearch.WordTrace]
  refine ⟨10671743428993006751122433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7114495619328671167414955 10671743428993006751122433)
  ·
    refine ⟨8003807571744755063341825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10671743428993006751122433 8003807571744755063341825)
    ·
      refine ⟨6002855678808566297506369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8003807571744755063341825 6002855678808566297506369)
      ·
        refine ⟨4502141759106424723129777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6002855678808566297506369 4502141759106424723129777)
        ·
          refine ⟨3376606319329818542347333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502141759106424723129777 3376606319329818542347333)
          ·
            refine ⟨633113684874340976690125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3376606319329818542347333 633113684874340976690125)
            ·
              refine ⟨237417631827877866258797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 633113684874340976690125 237417631827877866258797)
              ·
                refine ⟨89031611935454199847049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237417631827877866258797 89031611935454199847049)
                ·
                  rfl

theorem cell19_292593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_292593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292593 prefixEnd_292593 := by exact prefixLift 292593
  have htrace : WordTrace (prefixWord ++ tailWord_292593) baseStart_292593 baseEnd_292593 := by
    simpa [prefixWord, tailWord_292593, baseEnd_292593] using wordTrace_append hprefix tailTrace_292593
  have hstable : (prefixWord ++ tailWord_292593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292593).length < 2 ^ (prefixWord ++ tailWord_292593).sum := by decide
  have hdescent : baseEnd_292593 < baseStart_292593 := by decide
  rcases family_descends (prefixWord ++ tailWord_292593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292648 : List Nat := [2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_292648 : Nat := 118140960795 + 292648 * 2 ^ 59
def prefixEnd_292648 : Nat := 4983230072969 + 3 ^ 40 * 292648 * 2
def baseEnd_292648 : Nat := 89048347601230368624677

theorem tailTrace_292648 : CollatzResearch.WordTrace tailWord_292648 prefixEnd_292648 89048347601230368624677 := by
  unfold tailWord_292648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336874721896875572187299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7115832962529167429583065 5336874721896875572187299)
  ·
    refine ⟨8005312082845313358280949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5336874721896875572187299 8005312082845313358280949)
    ·
      refine ⟨750498007766748127338839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8005312082845313358280949 750498007766748127338839)
      ·
        refine ⟨1125747011650122191008259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750498007766748127338839 1125747011650122191008259)
        ·
          refine ⟨1688620517475183286512389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125747011650122191008259 1688620517475183286512389)
          ·
            refine ⟨316616347026596866221073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1688620517475183286512389 316616347026596866221073)
            ·
              refine ⟨237462260269947649665805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316616347026596866221073 237462260269947649665805)
              ·
                refine ⟨89048347601230368624677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237462260269947649665805 89048347601230368624677)
                ·
                  rfl

theorem cell19_292648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_292648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292648 prefixEnd_292648 := by exact prefixLift 292648
  have htrace : WordTrace (prefixWord ++ tailWord_292648) baseStart_292648 baseEnd_292648 := by
    simpa [prefixWord, tailWord_292648, baseEnd_292648] using wordTrace_append hprefix tailTrace_292648
  have hstable : (prefixWord ++ tailWord_292648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292648).length < 2 ^ (prefixWord ++ tailWord_292648).sum := by decide
  have hdescent : baseEnd_292648 < baseStart_292648 := by decide
  rcases family_descends (prefixWord ++ tailWord_292648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292652 : List Nat := [2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_292652 : Nat := 118140960795 + 292652 * 2 ^ 59
def prefixEnd_292652 : Nat := 4983230072969 + 3 ^ 40 * 292652 * 2
def baseEnd_292652 : Nat := 89049564740559544535777

theorem tailTrace_292652 : CollatzResearch.WordTrace tailWord_292652 prefixEnd_292652 89049564740559544535777 := by
  unfold tailWord_292652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336947667889629913760105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7115930223852839885013473 5336947667889629913760105)
  ·
    refine ⟨4002710750917222435320079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5336947667889629913760105 4002710750917222435320079)
    ·
      refine ⟨6004066126375833652980119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002710750917222435320079 6004066126375833652980119)
      ·
        refine ⟨9006099189563750479470179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004066126375833652980119 9006099189563750479470179)
        ·
          refine ⟨13509148784345625719205269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006099189563750479470179 13509148784345625719205269)
          ·
            refine ⟨633241349266201205587747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13509148784345625719205269 633241349266201205587747)
            ·
              refine ⟨949862023899301808381621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633241349266201205587747 949862023899301808381621)
              ·
                refine ⟨89049564740559544535777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 949862023899301808381621 89049564740559544535777)
                ·
                  rfl

theorem cell19_292652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_292652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292652 prefixEnd_292652 := by exact prefixLift 292652
  have htrace : WordTrace (prefixWord ++ tailWord_292652) baseStart_292652 baseEnd_292652 := by
    simpa [prefixWord, tailWord_292652, baseEnd_292652] using wordTrace_append hprefix tailTrace_292652
  have hstable : (prefixWord ++ tailWord_292652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292652).length < 2 ^ (prefixWord ++ tailWord_292652).sum := by decide
  have hdescent : baseEnd_292652 < baseStart_292652 := by decide
  rcases family_descends (prefixWord ++ tailWord_292652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292669 : List Nat := [1, 4, 1, 4, 1, 3, 5]
def baseStart_292669 : Nat := 118140960795 + 292669 * 2 ^ 59
def prefixEnd_292669 : Nat := 4983230072969 + 3 ^ 40 * 292669 * 2
def baseEnd_292669 : Nat := 29684912527569514052651

theorem tailTrace_292669 : CollatzResearch.WordTrace tailWord_292669 prefixEnd_292669 29684912527569514052651 := by
  unfold tailWord_292669
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674515376717671730889061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7116343584478447820592707 10674515376717671730889061)
  ·
    refine ⟨2001471633134563449541699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10674515376717671730889061 2001471633134563449541699)
    ·
      refine ⟨3002207449701845174312549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001471633134563449541699 3002207449701845174312549)
      ·
        refine ⟨562913896819095970183603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3002207449701845174312549 562913896819095970183603)
        ·
          refine ⟨844370845228643955275405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562913896819095970183603 844370845228643955275405)
          ·
            refine ⟨316639066960741483228277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 844370845228643955275405 316639066960741483228277)
            ·
              refine ⟨29684912527569514052651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 316639066960741483228277 29684912527569514052651)
              ·
                rfl

theorem cell19_292669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_292669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292669 prefixEnd_292669 := by exact prefixLift 292669
  have htrace : WordTrace (prefixWord ++ tailWord_292669) baseStart_292669 baseEnd_292669 := by
    simpa [prefixWord, tailWord_292669, baseEnd_292669] using wordTrace_append hprefix tailTrace_292669
  have hstable : (prefixWord ++ tailWord_292669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292669).length < 2 ^ (prefixWord ++ tailWord_292669).sum := by decide
  have hdescent : baseEnd_292669 < baseStart_292669 := by decide
  rcases family_descends (prefixWord ++ tailWord_292669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292690 : List Nat := [3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_292690 : Nat := 118140960795 + 292690 * 2 ^ 59
def prefixEnd_292690 : Nat := 4983230072969 + 3 ^ 40 * 292690 * 2
def baseEnd_292690 : Nat := 89061127564186715691229

theorem tailTrace_292690 : CollatzResearch.WordTrace tailWord_292690 prefixEnd_292690 89061127564186715691229 := by
  unfold tailWord_292690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668820327410398079350881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7116854206427728211602349 2668820327410398079350881)
  ·
    refine ⟨2001615245557798559513161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2668820327410398079350881 2001615245557798559513161)
    ·
      refine ⟨1501211434168348919634871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2001615245557798559513161 1501211434168348919634871)
      ·
        refine ⟨2251817151252523379452307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501211434168348919634871 2251817151252523379452307)
        ·
          refine ⟨3377725726878785069178461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251817151252523379452307 3377725726878785069178461)
          ·
            refine ⟨1266647147579544400941923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3377725726878785069178461 1266647147579544400941923)
            ·
              refine ⟨1899970721369316601412885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266647147579544400941923 1899970721369316601412885)
              ·
                refine ⟨89061127564186715691229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1899970721369316601412885 89061127564186715691229)
                ·
                  rfl

theorem cell19_292690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_292690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292690 prefixEnd_292690 := by exact prefixLift 292690
  have htrace : WordTrace (prefixWord ++ tailWord_292690) baseStart_292690 baseEnd_292690 := by
    simpa [prefixWord, tailWord_292690, baseEnd_292690] using wordTrace_append hprefix tailTrace_292690
  have hstable : (prefixWord ++ tailWord_292690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292690).length < 2 ^ (prefixWord ++ tailWord_292690).sum := by decide
  have hdescent : baseEnd_292690 < baseStart_292690 := by decide
  rcases family_descends (prefixWord ++ tailWord_292690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292726 : List Nat := [5, 1, 1, 3, 2, 7]
def baseStart_292726 : Nat := 118140960795 + 292726 * 2 ^ 59
def prefixEnd_292726 : Nat := 4983230072969 + 3 ^ 40 * 292726 * 2
def baseEnd_292726 : Nat := 9896897979794366543459

theorem tailTrace_292726 : CollatzResearch.WordTrace tailWord_292726 prefixEnd_292726 9896897979794366543459 := by
  unfold tailWord_292726
  simp only [CollatzResearch.WordTrace]
  refine ⟨667287146094448154107127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7117729558340780310476021 667287146094448154107127)
  ·
    refine ⟨1000930719141672231160691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 667287146094448154107127 1000930719141672231160691)
    ·
      refine ⟨1501396078712508346741037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000930719141672231160691 1501396078712508346741037)
      ·
        refine ⟨563023529517190630027889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1501396078712508346741037 563023529517190630027889)
        ·
          refine ⟨422267647137892972520917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563023529517190630027889 422267647137892972520917)
          ·
            refine ⟨9896897979794366543459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 422267647137892972520917 9896897979794366543459)
            ·
              rfl

theorem cell19_292726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_292726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292726 prefixEnd_292726 := by exact prefixLift 292726
  have htrace : WordTrace (prefixWord ++ tailWord_292726) baseStart_292726 baseEnd_292726 := by
    simpa [prefixWord, tailWord_292726, baseEnd_292726] using wordTrace_append hprefix tailTrace_292726
  have hstable : (prefixWord ++ tailWord_292726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292726).length < 2 ^ (prefixWord ++ tailWord_292726).sum := by decide
  have hdescent : baseEnd_292726 < baseStart_292726 := by decide
  rcases family_descends (prefixWord ++ tailWord_292726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292743 : List Nat := [1, 1, 4, 2, 5, 1, 1, 4]
def baseStart_292743 : Nat := 118140960795 + 292743 * 2 ^ 59
def prefixEnd_292743 : Nat := 4983230072969 + 3 ^ 40 * 292743 * 2
def baseEnd_292743 : Nat := 89077254660298296513307

theorem tailTrace_292743 : CollatzResearch.WordTrace tailWord_292743 prefixEnd_292743 89077254660298296513307 := by
  unfold tailWord_292743
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677214378449582369082883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7118142918966388246055255 10677214378449582369082883)
  ·
    refine ⟨16015821567674373553624325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10677214378449582369082883 16015821567674373553624325)
    ·
      refine ⟨3002966543938945041304561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16015821567674373553624325 3002966543938945041304561)
      ·
        refine ⟨2252224907954208780978421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3002966543938945041304561 2252224907954208780978421)
        ·
          refine ⟨211146085120707073216727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2252224907954208780978421 211146085120707073216727)
          ·
            refine ⟨316719127681060609825091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211146085120707073216727 316719127681060609825091)
            ·
              refine ⟨475078691521590914737637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316719127681060609825091 475078691521590914737637)
              ·
                refine ⟨89077254660298296513307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 475078691521590914737637 89077254660298296513307)
                ·
                  rfl

theorem cell19_292743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_292743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292743 prefixEnd_292743 := by exact prefixLift 292743
  have htrace : WordTrace (prefixWord ++ tailWord_292743) baseStart_292743 baseEnd_292743 := by
    simpa [prefixWord, tailWord_292743, baseEnd_292743] using wordTrace_append hprefix tailTrace_292743
  have hstable : (prefixWord ++ tailWord_292743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292743).length < 2 ^ (prefixWord ++ tailWord_292743).sum := by decide
  have hdescent : baseEnd_292743 < baseStart_292743 := by decide
  rcases family_descends (prefixWord ++ tailWord_292743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292758 : List Nat := [5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_292758 : Nat := 118140960795 + 292758 * 2 ^ 59
def prefixEnd_292758 : Nat := 4983230072969 + 3 ^ 40 * 292758 * 2
def baseEnd_292758 : Nat := 89081818932782706179933

theorem tailTrace_292758 : CollatzResearch.WordTrace tailWord_292758 prefixEnd_292758 89081818932782706179933 := by
  unfold tailWord_292758
  simp only [CollatzResearch.WordTrace]
  refine ⟨667360092087202495679933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7118507648930159953919285 667360092087202495679933)
  ·
    refine ⟨250260034532700935879975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 667360092087202495679933 250260034532700935879975)
    ·
      refine ⟨375390051799051403819963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250260034532700935879975 375390051799051403819963)
      ·
        refine ⟨563085077698577105729945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375390051799051403819963 563085077698577105729945)
        ·
          refine ⟨422313808273932829297459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563085077698577105729945 422313808273932829297459)
          ·
            refine ⟨633470712410899243946189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422313808273932829297459 633470712410899243946189)
            ·
              refine ⟨237551517154087216479821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 633470712410899243946189 237551517154087216479821)
              ·
                refine ⟨89081818932782706179933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237551517154087216479821 89081818932782706179933)
                ·
                  rfl

theorem cell19_292758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_292758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292758 prefixEnd_292758 := by exact prefixLift 292758
  have htrace : WordTrace (prefixWord ++ tailWord_292758) baseStart_292758 baseEnd_292758 := by
    simpa [prefixWord, tailWord_292758, baseEnd_292758] using wordTrace_append hprefix tailTrace_292758
  have hstable : (prefixWord ++ tailWord_292758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292758).length < 2 ^ (prefixWord ++ tailWord_292758).sum := by decide
  have hdescent : baseEnd_292758 < baseStart_292758 := by decide
  rcases family_descends (prefixWord ++ tailWord_292758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292785 : List Nat := [1, 2, 2, 4, 2, 2, 6]
def baseStart_292785 : Nat := 118140960795 + 292785 * 2 ^ 59
def prefixEnd_292785 : Nat := 4983230072969 + 3 ^ 40 * 292785 * 2
def baseEnd_292785 : Nat := 29696678207751547859953

theorem tailTrace_292785 : CollatzResearch.WordTrace tailWord_292785 prefixEnd_292785 29696678207751547859953 := by
  unfold tailWord_292785
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678746244297423542111809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7119164162864949028074539 10678746244297423542111809)
  ·
    refine ⟨8009059683223067656583857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10678746244297423542111809 8009059683223067656583857)
    ·
      refine ⟨6006794762417300742437893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8009059683223067656583857 6006794762417300742437893)
      ·
        refine ⟨1126274017953243889207105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6006794762417300742437893 1126274017953243889207105)
        ·
          refine ⟨844705513464932916905329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126274017953243889207105 844705513464932916905329)
          ·
            refine ⟨633529135098699687678997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844705513464932916905329 633529135098699687678997)
            ·
              refine ⟨29696678207751547859953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 633529135098699687678997 29696678207751547859953)
              ·
                rfl

theorem cell19_292785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_292785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292785 prefixEnd_292785 := by exact prefixLift 292785
  have htrace : WordTrace (prefixWord ++ tailWord_292785) baseStart_292785 baseEnd_292785 := by
    simpa [prefixWord, tailWord_292785, baseEnd_292785] using wordTrace_append hprefix tailTrace_292785
  have hstable : (prefixWord ++ tailWord_292785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292785).length < 2 ^ (prefixWord ++ tailWord_292785).sum := by decide
  have hdescent : baseEnd_292785 < baseStart_292785 := by decide
  rcases family_descends (prefixWord ++ tailWord_292785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292787 : List Nat := [1, 1, 1, 2, 3, 1, 10]
def baseStart_292787 : Nat := 118140960795 + 292787 * 2 ^ 59
def prefixEnd_292787 : Nat := 4983230072969 + 3 ^ 40 * 292787 * 2
def baseEnd_292787 : Nat := 29696881064306410511803

theorem tailTrace_292787 : CollatzResearch.WordTrace tailWord_292787 prefixEnd_292787 29696881064306410511803 := by
  unfold tailWord_292787
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678819190290177883684615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7119212793526785255789743 10678819190290177883684615)
  ·
    refine ⟨16018228785435266825526923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10678819190290177883684615 16018228785435266825526923)
    ·
      refine ⟨24027343178152900238290385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16018228785435266825526923 24027343178152900238290385)
      ·
        refine ⟨18020507383614675178717789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24027343178152900238290385 18020507383614675178717789)
        ·
          refine ⟨6757690268855503192019171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18020507383614675178717789 6757690268855503192019171)
          ·
            refine ⟨10136535403283254788028757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6757690268855503192019171 10136535403283254788028757)
            ·
              refine ⟨29696881064306410511803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10136535403283254788028757 29696881064306410511803)
              ·
                rfl

theorem cell19_292787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_292787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292787 prefixEnd_292787 := by exact prefixLift 292787
  have htrace : WordTrace (prefixWord ++ tailWord_292787) baseStart_292787 baseEnd_292787 := by
    simpa [prefixWord, tailWord_292787, baseEnd_292787] using wordTrace_append hprefix tailTrace_292787
  have hstable : (prefixWord ++ tailWord_292787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292787).length < 2 ^ (prefixWord ++ tailWord_292787).sum := by decide
  have hdescent : baseEnd_292787 < baseStart_292787 := by decide
  rcases family_descends (prefixWord ++ tailWord_292787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292821 : List Nat := [1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_292821 : Nat := 118140960795 + 292821 * 2 ^ 59
def prefixEnd_292821 : Nat := 4983230072969 + 3 ^ 40 * 292821 * 2
def baseEnd_292821 : Nat := 89100988877217226779761

theorem tailTrace_292821 : CollatzResearch.WordTrace tailWord_292821 prefixEnd_292821 89100988877217226779761 := by
  unfold tailWord_292821
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680059272167001690422317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7120039514778001126948211 10680059272167001690422317)
  ·
    refine ⟨4005022227062625633908369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10680059272167001690422317 4005022227062625633908369)
    ·
      refine ⟨3003766670296969225431277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4005022227062625633908369 3003766670296969225431277)
      ·
        refine ⟨1126412501361363459536729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3003766670296969225431277 1126412501361363459536729)
        ·
          refine ⟨844809376021022594652547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126412501361363459536729 844809376021022594652547)
          ·
            refine ⟨1267214064031533891978821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844809376021022594652547 1267214064031533891978821)
            ·
              refine ⟨237602637005912604746029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1267214064031533891978821 237602637005912604746029)
              ·
                refine ⟨89100988877217226779761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237602637005912604746029 89100988877217226779761)
                ·
                  rfl

theorem cell19_292821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_292821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292821 prefixEnd_292821 := by exact prefixLift 292821
  have htrace : WordTrace (prefixWord ++ tailWord_292821) baseStart_292821 baseEnd_292821 := by
    simpa [prefixWord, tailWord_292821, baseEnd_292821] using wordTrace_append hprefix tailTrace_292821
  have hstable : (prefixWord ++ tailWord_292821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292821).length < 2 ^ (prefixWord ++ tailWord_292821).sum := by decide
  have hdescent : baseEnd_292821 < baseStart_292821 := by decide
  rcases family_descends (prefixWord ++ tailWord_292821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292901 : List Nat := [1, 3, 1, 2, 2, 10]
def baseStart_292901 : Nat := 118140960795 + 292901 * 2 ^ 59
def prefixEnd_292901 : Nat := 4983230072969 + 3 ^ 40 * 292901 * 2
def baseEnd_292901 : Nat := 9902814629311193889085

theorem tailTrace_292901 : CollatzResearch.WordTrace tailWord_292901 prefixEnd_292901 9902814629311193889085 := by
  unfold tailWord_292901
  simp only [CollatzResearch.WordTrace]
  refine ⟨10682977111877175353334557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7121984741251450235556371 10682977111877175353334557)
  ·
    refine ⟨4006116416953940757500459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10682977111877175353334557 4006116416953940757500459)
    ·
      refine ⟨6009174625430911136250689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4006116416953940757500459 6009174625430911136250689)
      ·
        refine ⟨4506880969073183352188017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6009174625430911136250689 4506880969073183352188017)
        ·
          refine ⟨3380160726804887514141013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4506880969073183352188017 3380160726804887514141013)
          ·
            refine ⟨9902814629311193889085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3380160726804887514141013 9902814629311193889085)
            ·
              rfl

theorem cell19_292901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_292901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292901 prefixEnd_292901 := by exact prefixLift 292901
  have htrace : WordTrace (prefixWord ++ tailWord_292901) baseStart_292901 baseEnd_292901 := by
    simpa [prefixWord, tailWord_292901, baseEnd_292901] using wordTrace_append hprefix tailTrace_292901
  have hstable : (prefixWord ++ tailWord_292901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292901).length < 2 ^ (prefixWord ++ tailWord_292901).sum := by decide
  have hdescent : baseEnd_292901 < baseStart_292901 := by decide
  rcases family_descends (prefixWord ++ tailWord_292901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292937 : List Nat := [1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_292937 : Nat := 118140960795 + 292937 * 2 ^ 59
def prefixEnd_292937 : Nat := 4983230072969 + 3 ^ 40 * 292937 * 2
def baseEnd_292937 : Nat := 89136285917763328201667

theorem tailTrace_292937 : CollatzResearch.WordTrace tailWord_292937 prefixEnd_292937 89136285917763328201667 := by
  unfold tailWord_292937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10684290139746753501645065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7122860093164502334430043 10684290139746753501645065)
  ·
    refine ⟨8013217604810065126233799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10684290139746753501645065 8013217604810065126233799)
    ·
      refine ⟨12019826407215097689350699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013217604810065126233799 12019826407215097689350699)
      ·
        refine ⟨18029739610822646534026049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12019826407215097689350699 18029739610822646534026049)
        ·
          refine ⟨13522304708116984900519537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18029739610822646534026049 13522304708116984900519537)
          ·
            refine ⟨10141728531087738675389653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13522304708116984900519537 10141728531087738675389653)
            ·
              refine ⟨237696762447368875204445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10141728531087738675389653 237696762447368875204445)
              ·
                refine ⟨89136285917763328201667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237696762447368875204445 89136285917763328201667)
                ·
                  rfl

theorem cell19_292937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_292937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292937 prefixEnd_292937 := by exact prefixLift 292937
  have htrace : WordTrace (prefixWord ++ tailWord_292937) baseStart_292937 baseEnd_292937 := by
    simpa [prefixWord, tailWord_292937, baseEnd_292937] using wordTrace_append hprefix tailTrace_292937
  have hstable : (prefixWord ++ tailWord_292937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292937).length < 2 ^ (prefixWord ++ tailWord_292937).sum := by decide
  have hdescent : baseEnd_292937 < baseStart_292937 := by decide
  rcases family_descends (prefixWord ++ tailWord_292937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292956 : List Nat := [2, 2, 4, 1, 1, 3, 6]
def baseStart_292956 : Nat := 118140960795 + 292956 * 2 ^ 59
def prefixEnd_292956 : Nat := 4983230072969 + 3 ^ 40 * 292956 * 2
def baseEnd_292956 : Nat := 29714022443192304593131

theorem tailTrace_292956 : CollatzResearch.WordTrace tailWord_292956 prefixEnd_292956 29714022443192304593131 := by
  unfold tailWord_292956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342491563338959873293361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7123322084451946497724481 5342491563338959873293361)
  ·
    refine ⟨4006868672504219904970021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5342491563338959873293361 4006868672504219904970021)
    ·
      refine ⟨751287876094541232181879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4006868672504219904970021 751287876094541232181879)
      ·
        refine ⟨1126931814141811848272819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751287876094541232181879 1126931814141811848272819)
        ·
          refine ⟨1690397721212717772409229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126931814141811848272819 1690397721212717772409229)
          ·
            refine ⟨633899145454769164653461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1690397721212717772409229 633899145454769164653461)
            ·
              refine ⟨29714022443192304593131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 633899145454769164653461 29714022443192304593131)
              ·
                rfl

theorem cell19_292956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_292956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292956 prefixEnd_292956 := by exact prefixLift 292956
  have htrace : WordTrace (prefixWord ++ tailWord_292956) baseStart_292956 baseEnd_292956 := by
    simpa [prefixWord, tailWord_292956, baseEnd_292956] using wordTrace_append hprefix tailTrace_292956
  have hstable : (prefixWord ++ tailWord_292956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292956).length < 2 ^ (prefixWord ++ tailWord_292956).sum := by decide
  have hdescent : baseEnd_292956 < baseStart_292956 := by decide
  rcases family_descends (prefixWord ++ tailWord_292956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292977 : List Nat := [1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_292977 : Nat := 118140960795 + 292977 * 2 ^ 59
def prefixEnd_292977 : Nat := 4983230072969 + 3 ^ 40 * 292977 * 2
def baseEnd_292977 : Nat := 89148457311055087312669

theorem tailTrace_292977 : CollatzResearch.WordTrace tailWord_292977 prefixEnd_292977 89148457311055087312669 := by
  unfold tailWord_292977
  simp only [CollatzResearch.WordTrace]
  refine ⟨10685749059601840333101185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7123832706401226888734123 10685749059601840333101185)
  ·
    refine ⟨8014311794701380249825889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10685749059601840333101185 8014311794701380249825889)
    ·
      refine ⟨6010733846026035187369417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8014311794701380249825889 6010733846026035187369417)
      ·
        refine ⟨4508050384519526390527063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6010733846026035187369417 4508050384519526390527063)
        ·
          refine ⟨6762075576779289585790595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508050384519526390527063 6762075576779289585790595)
          ·
            refine ⟨10143113365168934378685893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6762075576779289585790595 10143113365168934378685893)
            ·
              refine ⟨1901833755969175196003605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10143113365168934378685893 1901833755969175196003605)
              ·
                refine ⟨89148457311055087312669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1901833755969175196003605 89148457311055087312669)
                ·
                  rfl

theorem cell19_292977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_292977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_292977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_292977 prefixEnd_292977 := by exact prefixLift 292977
  have htrace : WordTrace (prefixWord ++ tailWord_292977) baseStart_292977 baseEnd_292977 := by
    simpa [prefixWord, tailWord_292977, baseEnd_292977] using wordTrace_append hprefix tailTrace_292977
  have hstable : (prefixWord ++ tailWord_292977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292977).length < 2 ^ (prefixWord ++ tailWord_292977).sum := by decide
  have hdescent : baseEnd_292977 < baseStart_292977 := by decide
  rcases family_descends (prefixWord ++ tailWord_292977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293068 : List Nat := [2, 2, 1, 6, 2, 6]
def baseStart_293068 : Nat := 118140960795 + 293068 * 2 ^ 59
def prefixEnd_293068 : Nat := 4983230072969 + 3 ^ 40 * 293068 * 2
def baseEnd_293068 : Nat := 9908460803421537698911

theorem tailTrace_293068 : CollatzResearch.WordTrace tailWord_293068 prefixEnd_293068 9908460803421537698911 := by
  unfold tailWord_293068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344534051136081437331929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7126045401514775249775905 5344534051136081437331929)
  ·
    refine ⟨4008400538352061077998947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5344534051136081437331929 4008400538352061077998947)
    ·
      refine ⟨6012600807528091616998421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4008400538352061077998947 6012600807528091616998421)
      ·
        refine ⟨281840662852879294546801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6012600807528091616998421 281840662852879294546801)
        ·
          refine ⟨211380497139659470910101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281840662852879294546801 211380497139659470910101)
          ·
            refine ⟨9908460803421537698911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211380497139659470910101 9908460803421537698911)
            ·
              rfl

theorem cell19_293068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_293068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293068 prefixEnd_293068 := by exact prefixLift 293068
  have htrace : WordTrace (prefixWord ++ tailWord_293068) baseStart_293068 baseEnd_293068 := by
    simpa [prefixWord, tailWord_293068, baseEnd_293068] using wordTrace_append hprefix tailTrace_293068
  have hstable : (prefixWord ++ tailWord_293068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293068).length < 2 ^ (prefixWord ++ tailWord_293068).sum := by decide
  have hdescent : baseEnd_293068 < baseStart_293068 := by decide
  rcases family_descends (prefixWord ++ tailWord_293068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293106 : List Nat := [3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_293106 : Nat := 118140960795 + 293106 * 2 ^ 59
def prefixEnd_293106 : Nat := 4983230072969 + 3 ^ 40 * 293106 * 2
def baseEnd_293106 : Nat := 89187710054421010445651

theorem tailTrace_293106 : CollatzResearch.WordTrace tailWord_293106 prefixEnd_293106 89187710054421010445651 := by
  unfold tailWord_293106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672613519033623841136793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7126969384089663576364781 2672613519033623841136793)
  ·
    refine ⟨2004460139275217880852595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2672613519033623841136793 2004460139275217880852595)
    ·
      refine ⟨3006690208912826821278893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2004460139275217880852595 3006690208912826821278893)
      ·
        refine ⟨1127508828342310057979585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3006690208912826821278893 1127508828342310057979585)
        ·
          refine ⟨845631621256732543484689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127508828342310057979585 845631621256732543484689)
          ·
            refine ⟨634223715942549407613517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845631621256732543484689 634223715942549407613517)
            ·
              refine ⟨237833893478456027855069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634223715942549407613517 237833893478456027855069)
              ·
                refine ⟨89187710054421010445651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237833893478456027855069 89187710054421010445651)
                ·
                  rfl

theorem cell19_293106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_293106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293106 prefixEnd_293106 := by exact prefixLift 293106
  have htrace : WordTrace (prefixWord ++ tailWord_293106) baseStart_293106 baseEnd_293106 := by
    simpa [prefixWord, tailWord_293106, baseEnd_293106] using wordTrace_append hprefix tailTrace_293106
  have hstable : (prefixWord ++ tailWord_293106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293106).length < 2 ^ (prefixWord ++ tailWord_293106).sum := by decide
  have hdescent : baseEnd_293106 < baseStart_293106 := by decide
  rcases family_descends (prefixWord ++ tailWord_293106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293129 : List Nat := [1, 2, 1, 1, 3, 5, 6]
def baseStart_293129 : Nat := 118140960795 + 293129 * 2 ^ 59
def prefixEnd_293129 : Nat := 4983230072969 + 3 ^ 40 * 293129 * 2
def baseEnd_293129 : Nat := 29731569535187923978159

theorem tailTrace_293129 : CollatzResearch.WordTrace tailWord_293129 prefixEnd_293129 29731569535187923978159 := by
  unfold tailWord_293129
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691292955051170292634441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7127528636700780195089627 10691292955051170292634441)
  ·
    refine ⟨8018469716288377719475831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10691292955051170292634441 8018469716288377719475831)
    ·
      refine ⟨12027704574432566579213747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8018469716288377719475831 12027704574432566579213747)
      ·
        refine ⟨18041556861648849868820621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12027704574432566579213747 18041556861648849868820621)
        ·
          refine ⟨6765583823118318700807733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18041556861648849868820621 6765583823118318700807733)
          ·
            refine ⟨634273483417342378200725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6765583823118318700807733 634273483417342378200725)
            ·
              refine ⟨29731569535187923978159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 634273483417342378200725 29731569535187923978159)
              ·
                rfl

theorem cell19_293129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_293129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293129 prefixEnd_293129 := by exact prefixLift 293129
  have htrace : WordTrace (prefixWord ++ tailWord_293129) baseStart_293129 baseEnd_293129 := by
    simpa [prefixWord, tailWord_293129, baseEnd_293129] using wordTrace_append hprefix tailTrace_293129
  have hstable : (prefixWord ++ tailWord_293129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293129).length < 2 ^ (prefixWord ++ tailWord_293129).sum := by decide
  have hdescent : baseEnd_293129 < baseStart_293129 := by decide
  rcases family_descends (prefixWord ++ tailWord_293129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293148 : List Nat := [2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_293148 : Nat := 118140960795 + 293148 * 2 ^ 59
def prefixEnd_293148 : Nat := 4983230072969 + 3 ^ 40 * 293148 * 2
def baseEnd_293148 : Nat := 89200490017377357512203

theorem tailTrace_293148 : CollatzResearch.WordTrace tailWord_293148 prefixEnd_293148 89200490017377357512203 := by
  unfold tailWord_293148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345992970991168268788049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7127990627988224358384065 5345992970991168268788049)
  ·
    refine ⟨4009494728243376201591037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5345992970991168268788049 4009494728243376201591037)
    ·
      refine ⟨1503560523091266075596639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4009494728243376201591037 1503560523091266075596639)
      ·
        refine ⟨2255340784636899113394959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503560523091266075596639 2255340784636899113394959)
        ·
          refine ⟨3383011176955348670092439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255340784636899113394959 3383011176955348670092439)
          ·
            refine ⟨5074516765433023005138659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383011176955348670092439 5074516765433023005138659)
            ·
              refine ⟨7611775148149534507707989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074516765433023005138659 7611775148149534507707989)
              ·
                refine ⟨89200490017377357512203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7611775148149534507707989 89200490017377357512203)
                ·
                  rfl

theorem cell19_293148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_293148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293148 prefixEnd_293148 := by exact prefixLift 293148
  have htrace : WordTrace (prefixWord ++ tailWord_293148) baseStart_293148 baseEnd_293148 := by
    simpa [prefixWord, tailWord_293148, baseEnd_293148] using wordTrace_append hprefix tailTrace_293148
  have hstable : (prefixWord ++ tailWord_293148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293148).length < 2 ^ (prefixWord ++ tailWord_293148).sum := by decide
  have hdescent : baseEnd_293148 < baseStart_293148 := by decide
  rcases family_descends (prefixWord ++ tailWord_293148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293260 : List Nat := [2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_293260 : Nat := 118140960795 + 293260 * 2 ^ 59
def prefixEnd_293260 : Nat := 4983230072969 + 3 ^ 40 * 293260 * 2
def baseEnd_293260 : Nat := 89234569918594283023009

theorem tailTrace_293260 : CollatzResearch.WordTrace tailWord_293260 prefixEnd_293260 89234569918594283023009 := by
  unfold tailWord_293260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348035458788289832826617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7130713945051053110435489 5348035458788289832826617)
  ·
    refine ⟨4011026594091217374619963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5348035458788289832826617 4011026594091217374619963)
    ·
      refine ⟨6016539891136826061929945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4011026594091217374619963 6016539891136826061929945)
      ·
        refine ⟨4512404918352619546447459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6016539891136826061929945 4512404918352619546447459)
        ·
          refine ⟨6768607377528929319671189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512404918352619546447459 6768607377528929319671189)
          ·
            refine ⟨317278470821668561859587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6768607377528929319671189 317278470821668561859587)
            ·
              refine ⟨475917706232502842789381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317278470821668561859587 475917706232502842789381)
              ·
                refine ⟨89234569918594283023009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 475917706232502842789381 89234569918594283023009)
                ·
                  rfl

theorem cell19_293260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_293260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293260 prefixEnd_293260 := by exact prefixLift 293260
  have htrace : WordTrace (prefixWord ++ tailWord_293260) baseStart_293260 baseEnd_293260 := by
    simpa [prefixWord, tailWord_293260, baseEnd_293260] using wordTrace_append hprefix tailTrace_293260
  have hstable : (prefixWord ++ tailWord_293260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293260).length < 2 ^ (prefixWord ++ tailWord_293260).sum := by decide
  have hdescent : baseEnd_293260 < baseStart_293260 := by decide
  rcases family_descends (prefixWord ++ tailWord_293260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293277 : List Nat := [1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_293277 : Nat := 118140960795 + 293277 * 2 ^ 59
def prefixEnd_293277 : Nat := 4983230072969 + 3 ^ 40 * 293277 * 2
def baseEnd_293277 : Nat := 89239742760743280645185

theorem tailTrace_293277 : CollatzResearch.WordTrace tailWord_293277 prefixEnd_293277 89239742760743280645185 := by
  unfold tailWord_293277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10696690958514991569022085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7131127305676661046014723 10696690958514991569022085)
  ·
    refine ⟨2005629554721560919191641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10696690958514991569022085 2005629554721560919191641)
    ·
      refine ⟨1504222166041170689393731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2005629554721560919191641 1504222166041170689393731)
      ·
        refine ⟨2256333249061756034090597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504222166041170689393731 2256333249061756034090597)
        ·
          refine ⟨423062484199079256391987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2256333249061756034090597 423062484199079256391987)
          ·
            refine ⟨634593726298618884587981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423062484199079256391987 634593726298618884587981)
            ·
              refine ⟨237972647361982081720493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634593726298618884587981 237972647361982081720493)
              ·
                refine ⟨89239742760743280645185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237972647361982081720493 89239742760743280645185)
                ·
                  rfl

theorem cell19_293277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_293277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293277 prefixEnd_293277 := by exact prefixLift 293277
  have htrace : WordTrace (prefixWord ++ tailWord_293277) baseStart_293277 baseEnd_293277 := by
    simpa [prefixWord, tailWord_293277, baseEnd_293277] using wordTrace_append hprefix tailTrace_293277
  have hstable : (prefixWord ++ tailWord_293277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293277).length < 2 ^ (prefixWord ++ tailWord_293277).sum := by decide
  have hdescent : baseEnd_293277 < baseStart_293277 := by decide
  rcases family_descends (prefixWord ++ tailWord_293277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293279 : List Nat := [1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_293279 : Nat := 118140960795 + 293279 * 2 ^ 59
def prefixEnd_293279 : Nat := 4983230072969 + 3 ^ 40 * 293279 * 2
def baseEnd_293279 : Nat := 89240351330407868600735

theorem tailTrace_293279 : CollatzResearch.WordTrace tailWord_293279 prefixEnd_293279 89240351330407868600735 := by
  unfold tailWord_293279
  simp only [CollatzResearch.WordTrace]
  refine ⟨10696763904507745910594891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7131175936338497273729927 10696763904507745910594891)
  ·
    refine ⟨16045145856761618865892337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10696763904507745910594891 16045145856761618865892337)
    ·
      refine ⟨12033859392571214149419253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16045145856761618865892337 12033859392571214149419253)
      ·
        refine ⟨1128174318053551326508055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12033859392571214149419253 1128174318053551326508055)
        ·
          refine ⟨1692261477080326989762083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128174318053551326508055 1692261477080326989762083)
          ·
            refine ⟨2538392215620490484643125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692261477080326989762083 2538392215620490484643125)
            ·
              refine ⟨237974270214420982935293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2538392215620490484643125 237974270214420982935293)
              ·
                refine ⟨89240351330407868600735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237974270214420982935293 89240351330407868600735)
                ·
                  rfl

theorem cell19_293279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_293279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293279 prefixEnd_293279 := by exact prefixLift 293279
  have htrace : WordTrace (prefixWord ++ tailWord_293279) baseStart_293279 baseEnd_293279 := by
    simpa [prefixWord, tailWord_293279, baseEnd_293279] using wordTrace_append hprefix tailTrace_293279
  have hstable : (prefixWord ++ tailWord_293279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293279).length < 2 ^ (prefixWord ++ tailWord_293279).sum := by decide
  have hdescent : baseEnd_293279 < baseStart_293279 := by decide
  rcases family_descends (prefixWord ++ tailWord_293279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293330 : List Nat := [3, 2, 2, 4, 2, 1, 2, 3]
def baseStart_293330 : Nat := 118140960795 + 293330 * 2 ^ 59
def prefixEnd_293330 : Nat := 4983230072969 + 3 ^ 40 * 293330 * 2
def baseEnd_293330 : Nat := 89255869856854861467263

theorem tailTrace_293330 : CollatzResearch.WordTrace tailWord_293330 prefixEnd_293330 89255869856854861467263 := by
  unfold tailWord_293330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674656006830745405175361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7132416018215321080467629 2674656006830745405175361)
  ·
    refine ⟨2005992005123059053881521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2674656006830745405175361 2005992005123059053881521)
    ·
      refine ⟨1504494003842294290411141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2005992005123059053881521 1504494003842294290411141)
      ·
        refine ⟨282092625720430179452089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1504494003842294290411141 282092625720430179452089)
        ·
          refine ⟨211569469290322634589067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282092625720430179452089 211569469290322634589067)
          ·
            refine ⟨317354203935483951883601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211569469290322634589067 317354203935483951883601)
            ·
              refine ⟨238015652951612963912701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317354203935483951883601 238015652951612963912701)
              ·
                refine ⟨89255869856854861467263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238015652951612963912701 89255869856854861467263)
                ·
                  rfl

theorem cell19_293330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_293330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293330 prefixEnd_293330 := by exact prefixLift 293330
  have htrace : WordTrace (prefixWord ++ tailWord_293330) baseStart_293330 baseEnd_293330 := by
    simpa [prefixWord, tailWord_293330, baseEnd_293330] using wordTrace_append hprefix tailTrace_293330
  have hstable : (prefixWord ++ tailWord_293330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293330).length < 2 ^ (prefixWord ++ tailWord_293330).sum := by decide
  have hdescent : baseEnd_293330 < baseStart_293330 := by decide
  rcases family_descends (prefixWord ++ tailWord_293330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293338 : List Nat := [3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_293338 : Nat := 118140960795 + 293338 * 2 ^ 59
def prefixEnd_293338 : Nat := 4983230072969 + 3 ^ 40 * 293338 * 2
def baseEnd_293338 : Nat := 89258304135513213289463

theorem tailTrace_293338 : CollatzResearch.WordTrace tailWord_293338 prefixEnd_293338 89258304135513213289463 := by
  unfold tailWord_293338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674728952823499746748167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7132610540862665991328445 2674728952823499746748167)
  ·
    refine ⟨4012093429235249620122251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2674728952823499746748167 4012093429235249620122251)
    ·
      refine ⟨6018140143852874430183377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012093429235249620122251 6018140143852874430183377)
      ·
        refine ⟨4513605107889655822637533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6018140143852874430183377 4513605107889655822637533)
        ·
          refine ⟨1692601915458620933489075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4513605107889655822637533 1692601915458620933489075)
          ·
            refine ⟨2538902873187931400233613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692601915458620933489075 2538902873187931400233613)
            ·
              refine ⟨952088577445474275087605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2538902873187931400233613 952088577445474275087605)
              ·
                refine ⟨89258304135513213289463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 952088577445474275087605 89258304135513213289463)
                ·
                  rfl

theorem cell19_293338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_293338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293338 prefixEnd_293338 := by exact prefixLift 293338
  have htrace : WordTrace (prefixWord ++ tailWord_293338) baseStart_293338 baseEnd_293338 := by
    simpa [prefixWord, tailWord_293338, baseEnd_293338] using wordTrace_append hprefix tailTrace_293338
  have hstable : (prefixWord ++ tailWord_293338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293338).length < 2 ^ (prefixWord ++ tailWord_293338).sum := by decide
  have hdescent : baseEnd_293338 < baseStart_293338 := by decide
  rcases family_descends (prefixWord ++ tailWord_293338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293412 : List Nat := [2, 3, 1, 5, 1, 7]
def baseStart_293412 : Nat := 118140960795 + 293412 * 2 ^ 59
def prefixEnd_293412 : Nat := 4983230072969 + 3 ^ 40 * 293412 * 2
def baseEnd_293412 : Nat := 9920091245900329738313

theorem tailTrace_293412 : CollatzResearch.WordTrace tailWord_293412 prefixEnd_293412 9920091245900329738313 := by
  unfold tailWord_293412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350807406512954812593245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7134409875350606416790993 5350807406512954812593245)
  ·
    refine ⟨2006552777442358054722467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5350807406512954812593245 2006552777442358054722467)
    ·
      refine ⟨3009829166163537082083701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006552777442358054722467 3009829166163537082083701)
      ·
        refine ⟨282171484327831601445347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3009829166163537082083701 282171484327831601445347)
        ·
          refine ⟨423257226491747402168021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282171484327831601445347 423257226491747402168021)
          ·
            refine ⟨9920091245900329738313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 423257226491747402168021 9920091245900329738313)
            ·
              rfl

theorem cell19_293412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_293412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293412 prefixEnd_293412 := by exact prefixLift 293412
  have htrace : WordTrace (prefixWord ++ tailWord_293412) baseStart_293412 baseEnd_293412 := by
    simpa [prefixWord, tailWord_293412, baseEnd_293412] using wordTrace_append hprefix tailTrace_293412
  have hstable : (prefixWord ++ tailWord_293412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293412).length < 2 ^ (prefixWord ++ tailWord_293412).sum := by decide
  have hdescent : baseEnd_293412 < baseStart_293412 := by decide
  rcases family_descends (prefixWord ++ tailWord_293412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293444 : List Nat := [2, 3, 5, 1, 1, 1, 3, 3]
def baseStart_293444 : Nat := 118140960795 + 293444 * 2 ^ 59
def prefixEnd_293444 : Nat := 4983230072969 + 3 ^ 40 * 293444 * 2
def baseEnd_293444 : Nat := 89290558327736374933619

theorem tailTrace_293444 : CollatzResearch.WordTrace tailWord_293444 prefixEnd_293444 89290558327736374933619 := by
  unfold tailWord_293444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5351390974454989545175693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7135187965939986060234257 5351390974454989545175693)
  ·
    refine ⟨2006771615420621079440885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5351390974454989545175693 2006771615420621079440885)
    ·
      refine ⟨188134838945683226197583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2006771615420621079440885 188134838945683226197583)
      ·
        refine ⟨282202258418524839296375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188134838945683226197583 282202258418524839296375)
        ·
          refine ⟨423303387627787258944563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282202258418524839296375 423303387627787258944563)
          ·
            refine ⟨634955081441680888416845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423303387627787258944563 634955081441680888416845)
            ·
              refine ⟨238108155540630333156317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634955081441680888416845 238108155540630333156317)
              ·
                refine ⟨89290558327736374933619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238108155540630333156317 89290558327736374933619)
                ·
                  rfl

theorem cell19_293444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_293444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293444 prefixEnd_293444 := by exact prefixLift 293444
  have htrace : WordTrace (prefixWord ++ tailWord_293444) baseStart_293444 baseEnd_293444 := by
    simpa [prefixWord, tailWord_293444, baseEnd_293444] using wordTrace_append hprefix tailTrace_293444
  have hstable : (prefixWord ++ tailWord_293444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293444).length < 2 ^ (prefixWord ++ tailWord_293444).sum := by decide
  have hdescent : baseEnd_293444 < baseStart_293444 := by decide
  rcases family_descends (prefixWord ++ tailWord_293444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293446 : List Nat := [6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_293446 : Nat := 118140960795 + 293446 * 2 ^ 59
def prefixEnd_293446 : Nat := 4983230072969 + 3 ^ 40 * 293446 * 2
def baseEnd_293446 : Nat := 89291166897400962889169

theorem tailTrace_293446 : CollatzResearch.WordTrace tailWord_293446 prefixEnd_293446 89291166897400962889169 := by
  unfold tailWord_293446
  simp only [CollatzResearch.WordTrace]
  refine ⟨334464215465710419747631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7135236596601822287949461 334464215465710419747631)
  ·
    refine ⟨501696323198565629621447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334464215465710419747631 501696323198565629621447)
    ·
      refine ⟨752544484797848444432171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501696323198565629621447 752544484797848444432171)
      ·
        refine ⟨1128816727196772666648257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752544484797848444432171 1128816727196772666648257)
        ·
          refine ⟨846612545397579499986193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1128816727196772666648257 846612545397579499986193)
          ·
            refine ⟨634959409048184624989645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846612545397579499986193 634959409048184624989645)
            ·
              refine ⟨238109778393069234371117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634959409048184624989645 238109778393069234371117)
              ·
                refine ⟨89291166897400962889169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238109778393069234371117 89291166897400962889169)
                ·
                  rfl

theorem cell19_293446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_293446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293446 prefixEnd_293446 := by exact prefixLift 293446
  have htrace : WordTrace (prefixWord ++ tailWord_293446) baseStart_293446 baseEnd_293446 := by
    simpa [prefixWord, tailWord_293446, baseEnd_293446] using wordTrace_append hprefix tailTrace_293446
  have hstable : (prefixWord ++ tailWord_293446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293446).length < 2 ^ (prefixWord ++ tailWord_293446).sum := by decide
  have hdescent : baseEnd_293446 < baseStart_293446 := by decide
  rcases family_descends (prefixWord ++ tailWord_293446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293450 : List Nat := [3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_293450 : Nat := 118140960795 + 293450 * 2 ^ 59
def prefixEnd_293450 : Nat := 4983230072969 + 3 ^ 40 * 293450 * 2
def baseEnd_293450 : Nat := 89292384036730138800269

theorem tailTrace_293450 : CollatzResearch.WordTrace tailWord_293450 prefixEnd_293450 89292384036730138800269 := by
  unfold tailWord_293450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675750196722060528767451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7135333857925494743379869 2675750196722060528767451)
  ·
    refine ⟨4013625295083090793151177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675750196722060528767451 4013625295083090793151177)
    ·
      refine ⟨3010218971312318094863383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4013625295083090793151177 3010218971312318094863383)
      ·
        refine ⟨4515328456968477142295075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010218971312318094863383 4515328456968477142295075)
        ·
          refine ⟨6772992685452715713442613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515328456968477142295075 6772992685452715713442613)
          ·
            refine ⟨634968064261192098135245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6772992685452715713442613 634968064261192098135245)
            ·
              refine ⟨238113024097947036800717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634968064261192098135245 238113024097947036800717)
              ·
                refine ⟨89292384036730138800269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238113024097947036800717 89292384036730138800269)
                ·
                  rfl

theorem cell19_293450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_293450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293450 prefixEnd_293450 := by exact prefixLift 293450
  have htrace : WordTrace (prefixWord ++ tailWord_293450) baseStart_293450 baseEnd_293450 := by
    simpa [prefixWord, tailWord_293450, baseEnd_293450] using wordTrace_append hprefix tailTrace_293450
  have hstable : (prefixWord ++ tailWord_293450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293450).length < 2 ^ (prefixWord ++ tailWord_293450).sum := by decide
  have hdescent : baseEnd_293450 < baseStart_293450 := by decide
  rcases family_descends (prefixWord ++ tailWord_293450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293509 : List Nat := [1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_293509 : Nat := 118140960795 + 293509 * 2 ^ 59
def prefixEnd_293509 : Nat := 4983230072969 + 3 ^ 40 * 293509 * 2
def baseEnd_293509 : Nat := 89310336841835483488997

theorem tailTrace_293509 : CollatzResearch.WordTrace tailWord_293509 prefixEnd_293509 89310336841835483488997 := by
  unfold tailWord_293509
  simp only [CollatzResearch.WordTrace]
  refine ⟨10705152693674495191467581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7136768462449663460978387 10705152693674495191467581)
  ·
    refine ⟨4014432260127935696800343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10705152693674495191467581 4014432260127935696800343)
    ·
      refine ⟨6021648390191903545200515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4014432260127935696800343 6021648390191903545200515)
      ·
        refine ⟨9032472585287855317800773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6021648390191903545200515 9032472585287855317800773)
        ·
          refine ⟨1693588609741472872087645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9032472585287855317800773 1693588609741472872087645)
          ·
            refine ⟨635095728653052327032867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1693588609741472872087645 635095728653052327032867)
            ·
              refine ⟨952643592979578490549301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635095728653052327032867 952643592979578490549301)
              ·
                refine ⟨89310336841835483488997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 952643592979578490549301 89310336841835483488997)
                ·
                  rfl

theorem cell19_293509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_293509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293509 prefixEnd_293509 := by exact prefixLift 293509
  have htrace : WordTrace (prefixWord ++ tailWord_293509) baseStart_293509 baseEnd_293509 := by
    simpa [prefixWord, tailWord_293509, baseEnd_293509] using wordTrace_append hprefix tailTrace_293509
  have hstable : (prefixWord ++ tailWord_293509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293509).length < 2 ^ (prefixWord ++ tailWord_293509).sum := by decide
  have hdescent : baseEnd_293509 < baseStart_293509 := by decide
  rcases family_descends (prefixWord ++ tailWord_293509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293543 : List Nat := [1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_293543 : Nat := 118140960795 + 293543 * 2 ^ 59
def prefixEnd_293543 : Nat := 4983230072969 + 3 ^ 40 * 293543 * 2
def baseEnd_293543 : Nat := 89320682526133478733349

theorem tailTrace_293543 : CollatzResearch.WordTrace tailWord_293543 prefixEnd_293543 89320682526133478733349 := by
  unfold tailWord_293543
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706392775551318998205283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7137595183700879332136855 10706392775551318998205283)
  ·
    refine ⟨16059589163326978497307925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706392775551318998205283 16059589163326978497307925)
    ·
      refine ⟨752793242030952117061309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16059589163326978497307925 752793242030952117061309)
      ·
        refine ⟨282297465761607043897991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 752793242030952117061309 282297465761607043897991)
        ·
          refine ⟨423446198642410565846987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282297465761607043897991 423446198642410565846987)
          ·
            refine ⟨635169297963615848770481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423446198642410565846987 635169297963615848770481)
            ·
              refine ⟨476376973472711886577861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635169297963615848770481 476376973472711886577861)
              ·
                refine ⟨89320682526133478733349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476376973472711886577861 89320682526133478733349)
                ·
                  rfl

theorem cell19_293543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_293543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293543 prefixEnd_293543 := by exact prefixLift 293543
  have htrace : WordTrace (prefixWord ++ tailWord_293543) baseStart_293543 baseEnd_293543 := by
    simpa [prefixWord, tailWord_293543, baseEnd_293543] using wordTrace_append hprefix tailTrace_293543
  have hstable : (prefixWord ++ tailWord_293543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293543).length < 2 ^ (prefixWord ++ tailWord_293543).sum := by decide
  have hdescent : baseEnd_293543 < baseStart_293543 := by decide
  rcases family_descends (prefixWord ++ tailWord_293543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293566 : List Nat := [4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_293566 : Nat := 118140960795 + 293566 * 2 ^ 59
def prefixEnd_293566 : Nat := 4983230072969 + 3 ^ 40 * 293566 * 2
def baseEnd_293566 : Nat := 89327681077276240222175

theorem tailTrace_293566 : CollatzResearch.WordTrace tailWord_293566 prefixEnd_293566 89327681077276240222175 := by
  unfold tailWord_293566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338403956808499240786569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7138154436311995950861701 1338403956808499240786569)
  ·
    refine ⟨1003802967606374430589927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1338403956808499240786569 1003802967606374430589927)
    ·
      refine ⟨1505704451409561645884891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1003802967606374430589927 1505704451409561645884891)
      ·
        refine ⟨2258556677114342468827337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505704451409561645884891 2258556677114342468827337)
        ·
          refine ⟨1693917507835756851620503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2258556677114342468827337 1693917507835756851620503)
          ·
            refine ⟨2540876261753635277430755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693917507835756851620503 2540876261753635277430755)
            ·
              refine ⟨3811314392630452916146133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540876261753635277430755 3811314392630452916146133)
              ·
                refine ⟨89327681077276240222175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3811314392630452916146133 89327681077276240222175)
                ·
                  rfl

theorem cell19_293566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_293566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293566 prefixEnd_293566 := by exact prefixLift 293566
  have htrace : WordTrace (prefixWord ++ tailWord_293566) baseStart_293566 baseEnd_293566 := by
    simpa [prefixWord, tailWord_293566, baseEnd_293566] using wordTrace_append hprefix tailTrace_293566
  have hstable : (prefixWord ++ tailWord_293566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293566).length < 2 ^ (prefixWord ++ tailWord_293566).sum := by decide
  have hdescent : baseEnd_293566 < baseStart_293566 := by decide
  rcases family_descends (prefixWord ++ tailWord_293566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293581 : List Nat := [1, 6, 2, 1, 3, 6]
def baseStart_293581 : Nat := 118140960795 + 293581 * 2 ^ 59
def prefixEnd_293581 : Nat := 4983230072969 + 3 ^ 40 * 293581 * 2
def baseEnd_293581 : Nat := 9925805038862294432089

theorem tailTrace_293581 : CollatzResearch.WordTrace tailWord_293581 prefixEnd_293581 9925805038862294432089 := by
  unfold tailWord_293581
  simp only [CollatzResearch.WordTrace]
  refine ⟨10707778749413651488088597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7138519166275767658725731 10707778749413651488088597)
  ·
    refine ⟨501927128878764913504153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10707778749413651488088597 501927128878764913504153)
    ·
      refine ⟨376445346659073685128115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 501927128878764913504153 376445346659073685128115)
      ·
        refine ⟨564668019988610527692173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376445346659073685128115 564668019988610527692173)
        ·
          refine ⟨211750507495728947884565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 564668019988610527692173 211750507495728947884565)
          ·
            refine ⟨9925805038862294432089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211750507495728947884565 9925805038862294432089)
            ·
              rfl

theorem cell19_293581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_293581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293581 prefixEnd_293581 := by exact prefixLift 293581
  have htrace : WordTrace (prefixWord ++ tailWord_293581) baseStart_293581 baseEnd_293581 := by
    simpa [prefixWord, tailWord_293581, baseEnd_293581] using wordTrace_append hprefix tailTrace_293581
  have hstable : (prefixWord ++ tailWord_293581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293581).length < 2 ^ (prefixWord ++ tailWord_293581).sum := by decide
  have hdescent : baseEnd_293581 < baseStart_293581 := by decide
  rcases family_descends (prefixWord ++ tailWord_293581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293604 : List Nat := [2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_293604 : Nat := 118140960795 + 293604 * 2 ^ 59
def prefixEnd_293604 : Nat := 4983230072969 + 3 ^ 40 * 293604 * 2
def baseEnd_293604 : Nat := 89339243900903411377627

theorem tailTrace_293604 : CollatzResearch.WordTrace tailWord_293604 prefixEnd_293604 89339243900903411377627 := by
  unfold tailWord_293604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354308814165163208087933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7139078418886884277450577 5354308814165163208087933)
  ·
    refine ⟨2007865805311936203032975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5354308814165163208087933 2007865805311936203032975)
    ·
      refine ⟨3011798707967904304549463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2007865805311936203032975 3011798707967904304549463)
      ·
        refine ⟨4517698061951856456824195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3011798707967904304549463 4517698061951856456824195)
        ·
          refine ⟨6776547092927784685236293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517698061951856456824195 6776547092927784685236293)
          ·
            refine ⟨1270602579923959628481805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6776547092927784685236293 1270602579923959628481805)
            ·
              refine ⟨476475967471484860680677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1270602579923959628481805 476475967471484860680677)
              ·
                refine ⟨89339243900903411377627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476475967471484860680677 89339243900903411377627)
                ·
                  rfl

theorem cell19_293604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_293604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293604 prefixEnd_293604 := by exact prefixLift 293604
  have htrace : WordTrace (prefixWord ++ tailWord_293604) baseStart_293604 baseEnd_293604 := by
    simpa [prefixWord, tailWord_293604, baseEnd_293604] using wordTrace_append hprefix tailTrace_293604
  have hstable : (prefixWord ++ tailWord_293604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293604).length < 2 ^ (prefixWord ++ tailWord_293604).sum := by decide
  have hdescent : baseEnd_293604 < baseStart_293604 := by decide
  rcases family_descends (prefixWord ++ tailWord_293604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293625 : List Nat := [1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_293625 : Nat := 118140960795 + 293625 * 2 ^ 59
def prefixEnd_293625 : Nat := 4983230072969 + 3 ^ 40 * 293625 * 2
def baseEnd_293625 : Nat := 89345633882381584910903

theorem tailTrace_293625 : CollatzResearch.WordTrace tailWord_293625 prefixEnd_293625 89345633882381584910903 := by
  unfold tailWord_293625
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709383561254247002690329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7139589040836164668460219 10709383561254247002690329)
  ·
    refine ⟨8032037670940685252017747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10709383561254247002690329 8032037670940685252017747)
    ·
      refine ⟨12048056506411027878026621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8032037670940685252017747 12048056506411027878026621)
      ·
        refine ⟨4518021189904135454259983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12048056506411027878026621 4518021189904135454259983)
        ·
          refine ⟨6777031784856203181389975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518021189904135454259983 6777031784856203181389975)
          ·
            refine ⟨10165547677284304772084963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777031784856203181389975 10165547677284304772084963)
            ·
              refine ⟨15248321515926457158127445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10165547677284304772084963 15248321515926457158127445)
              ·
                refine ⟨89345633882381584910903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15248321515926457158127445 89345633882381584910903)
                ·
                  rfl

theorem cell19_293625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_293625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293625 prefixEnd_293625 := by exact prefixLift 293625
  have htrace : WordTrace (prefixWord ++ tailWord_293625) baseStart_293625 baseEnd_293625 := by
    simpa [prefixWord, tailWord_293625, baseEnd_293625] using wordTrace_append hprefix tailTrace_293625
  have hstable : (prefixWord ++ tailWord_293625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293625).length < 2 ^ (prefixWord ++ tailWord_293625).sum := by decide
  have hdescent : baseEnd_293625 < baseStart_293625 := by decide
  rcases family_descends (prefixWord ++ tailWord_293625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293674 : List Nat := [3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_293674 : Nat := 118140960795 + 293674 * 2 ^ 59
def prefixEnd_293674 : Nat := 4983230072969 + 3 ^ 40 * 293674 * 2
def baseEnd_293674 : Nat := 89360543839163989821881

theorem tailTrace_293674 : CollatzResearch.WordTrace tailWord_293674 prefixEnd_293674 89360543839163989821881 := by
  unfold tailWord_293674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677792684519182092806019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7140780492051152247482717 2677792684519182092806019)
  ·
    refine ⟨4016689026778773139209029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677792684519182092806019 4016689026778773139209029)
    ·
      refine ⟨753129192521019963601693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4016689026778773139209029 753129192521019963601693)
      ·
        refine ⟨282423447195382486350635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 753129192521019963601693 282423447195382486350635)
        ·
          refine ⟨423635170793073729525953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282423447195382486350635 423635170793073729525953)
          ·
            refine ⟨317726378094805297144465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423635170793073729525953 317726378094805297144465)
            ·
              refine ⟨238294783571103972858349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317726378094805297144465 238294783571103972858349)
              ·
                refine ⟨89360543839163989821881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238294783571103972858349 89360543839163989821881)
                ·
                  rfl

theorem cell19_293674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_293674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293674 prefixEnd_293674 := by exact prefixLift 293674
  have htrace : WordTrace (prefixWord ++ tailWord_293674) baseStart_293674 baseEnd_293674 := by
    simpa [prefixWord, tailWord_293674, baseEnd_293674] using wordTrace_append hprefix tailTrace_293674
  have hstable : (prefixWord ++ tailWord_293674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293674).length < 2 ^ (prefixWord ++ tailWord_293674).sum := by decide
  have hdescent : baseEnd_293674 < baseStart_293674 := by decide
  rcases family_descends (prefixWord ++ tailWord_293674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293678 : List Nat := [4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_293678 : Nat := 118140960795 + 293678 * 2 ^ 59
def prefixEnd_293678 : Nat := 4983230072969 + 3 ^ 40 * 293678 * 2
def baseEnd_293678 : Nat := 89361760978493165732981

theorem tailTrace_293678 : CollatzResearch.WordTrace tailWord_293678 prefixEnd_293678 89361760978493165732981 := by
  unfold tailWord_293678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338914578757779631796211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7140877753374824702913125 1338914578757779631796211)
  ·
    refine ⟨2008371868136669447694317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1338914578757779631796211 2008371868136669447694317)
    ·
      refine ⟨753139450551251042885369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2008371868136669447694317 753139450551251042885369)
      ·
        refine ⟨564854587913438282164027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753139450551251042885369 564854587913438282164027)
        ·
          refine ⟨847281881870157423246041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564854587913438282164027 847281881870157423246041)
          ·
            refine ⟨635461411402618067434531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847281881870157423246041 635461411402618067434531)
            ·
              refine ⟨953192117103927101151797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635461411402618067434531 953192117103927101151797)
              ·
                refine ⟨89361760978493165732981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 953192117103927101151797 89361760978493165732981)
                ·
                  rfl

theorem cell19_293678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_293678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293678 prefixEnd_293678 := by exact prefixLift 293678
  have htrace : WordTrace (prefixWord ++ tailWord_293678) baseStart_293678 baseEnd_293678 := by
    simpa [prefixWord, tailWord_293678, baseEnd_293678] using wordTrace_append hprefix tailTrace_293678
  have hstable : (prefixWord ++ tailWord_293678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293678).length < 2 ^ (prefixWord ++ tailWord_293678).sum := by decide
  have hdescent : baseEnd_293678 < baseStart_293678 := by decide
  rcases family_descends (prefixWord ++ tailWord_293678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293716 : List Nat := [2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_293716 : Nat := 118140960795 + 293716 * 2 ^ 59
def prefixEnd_293716 : Nat := 4983230072969 + 3 ^ 40 * 293716 * 2
def baseEnd_293716 : Nat := 89373323802120336888433

theorem tailTrace_293716 : CollatzResearch.WordTrace tailWord_293716 prefixEnd_293716 89373323802120336888433 := by
  unfold tailWord_293716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356351301962284772126501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7141801735949713029502001 5356351301962284772126501)
  ·
    refine ⟨1004315869117928394773719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5356351301962284772126501 1004315869117928394773719)
    ·
      refine ⟨1506473803676892592160579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004315869117928394773719 1506473803676892592160579)
      ·
        refine ⟨2259710705515338888240869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506473803676892592160579 2259710705515338888240869)
        ·
          refine ⟨423695757284126041545163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2259710705515338888240869 423695757284126041545163)
          ·
            refine ⟨635543635926189062317745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423695757284126041545163 635543635926189062317745)
            ·
              refine ⟨476657726944641796738309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635543635926189062317745 476657726944641796738309)
              ·
                refine ⟨89373323802120336888433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476657726944641796738309 89373323802120336888433)
                ·
                  rfl

theorem cell19_293716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_293716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293716 prefixEnd_293716 := by exact prefixLift 293716
  have htrace : WordTrace (prefixWord ++ tailWord_293716) baseStart_293716 baseEnd_293716 := by
    simpa [prefixWord, tailWord_293716, baseEnd_293716] using wordTrace_append hprefix tailTrace_293716
  have hstable : (prefixWord ++ tailWord_293716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293716).length < 2 ^ (prefixWord ++ tailWord_293716).sum := by decide
  have hdescent : baseEnd_293716 < baseStart_293716 := by decide
  rcases family_descends (prefixWord ++ tailWord_293716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293739 : List Nat := [1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_293739 : Nat := 118140960795 + 293739 * 2 ^ 59
def prefixEnd_293739 : Nat := 4983230072969 + 3 ^ 40 * 293739 * 2
def baseEnd_293739 : Nat := 89380322353263098377259

theorem tailTrace_293739 : CollatzResearch.WordTrace tailWord_293739 prefixEnd_293739 89380322353263098377259 := by
  unfold tailWord_293739
  simp only [CollatzResearch.WordTrace]
  refine ⟨10713541482841244472340271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7142360988560829648226847 10713541482841244472340271)
  ·
    refine ⟨16070312224261866708510407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10713541482841244472340271 16070312224261866708510407)
    ·
      refine ⟨24105468336392800062765611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16070312224261866708510407 24105468336392800062765611)
      ·
        refine ⟨36158202504589200094148417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24105468336392800062765611 36158202504589200094148417)
        ·
          refine ⟨27118651878441900070611313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36158202504589200094148417 27118651878441900070611313)
          ·
            refine ⟨20338988908831425052958485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27118651878441900070611313 20338988908831425052958485)
            ·
              refine ⟨953390105101473049357429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20338988908831425052958485 953390105101473049357429)
              ·
                refine ⟨89380322353263098377259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 953390105101473049357429 89380322353263098377259)
                ·
                  rfl

theorem cell19_293739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_293739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293739 prefixEnd_293739 := by exact prefixLift 293739
  have htrace : WordTrace (prefixWord ++ tailWord_293739) baseStart_293739 baseEnd_293739 := by
    simpa [prefixWord, tailWord_293739, baseEnd_293739] using wordTrace_append hprefix tailTrace_293739
  have hstable : (prefixWord ++ tailWord_293739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293739).length < 2 ^ (prefixWord ++ tailWord_293739).sum := by decide
  have hdescent : baseEnd_293739 < baseStart_293739 := by decide
  rcases family_descends (prefixWord ++ tailWord_293739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293834 : List Nat := [3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_293834 : Nat := 118140960795 + 293834 * 2 ^ 59
def prefixEnd_293834 : Nat := 4983230072969 + 3 ^ 40 * 293834 * 2
def baseEnd_293834 : Nat := 89409229412331026265889

theorem tailTrace_293834 : CollatzResearch.WordTrace tailWord_293834 prefixEnd_293834 89409229412331026265889 := by
  unfold tailWord_293834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679251604374268924262139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7144670944998050464699037 2679251604374268924262139)
  ·
    refine ⟨4018877406561403386393209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679251604374268924262139 4018877406561403386393209)
    ·
      refine ⟨3014158054921052539794907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4018877406561403386393209 3014158054921052539794907)
      ·
        refine ⟨4521237082381578809692361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014158054921052539794907 4521237082381578809692361)
        ·
          refine ⟨3390927811786184107269271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4521237082381578809692361 3390927811786184107269271)
          ·
            refine ⟨5086391717679276160903907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390927811786184107269271 5086391717679276160903907)
            ·
              refine ⟨7629587576518914241355861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086391717679276160903907 7629587576518914241355861)
              ·
                refine ⟨89409229412331026265889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7629587576518914241355861 89409229412331026265889)
                ·
                  rfl

theorem cell19_293834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_293834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293834 prefixEnd_293834 := by exact prefixLift 293834
  have htrace : WordTrace (prefixWord ++ tailWord_293834) baseStart_293834 baseEnd_293834 := by
    simpa [prefixWord, tailWord_293834, baseEnd_293834] using wordTrace_append hprefix tailTrace_293834
  have hstable : (prefixWord ++ tailWord_293834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293834).length < 2 ^ (prefixWord ++ tailWord_293834).sum := by decide
  have hdescent : baseEnd_293834 < baseStart_293834 := by decide
  rcases family_descends (prefixWord ++ tailWord_293834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293849 : List Nat := [1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_293849 : Nat := 118140960795 + 293849 * 2 ^ 59
def prefixEnd_293849 : Nat := 4983230072969 + 3 ^ 40 * 293849 * 2
def baseEnd_293849 : Nat := 89413793684815435932515

theorem tailTrace_293849 : CollatzResearch.WordTrace tailWord_293849 prefixEnd_293849 89413793684815435932515 := by
  unfold tailWord_293849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717553512442733258844601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7145035674961822172563067 10717553512442733258844601)
  ·
    refine ⟨8038165134332049944133451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10717553512442733258844601 8038165134332049944133451)
    ·
      refine ⟨12057247701498074916200177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8038165134332049944133451 12057247701498074916200177)
      ·
        refine ⟨9042935776123556187150133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12057247701498074916200177 9042935776123556187150133)
        ·
          refine ⟨847775229011583392545325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9042935776123556187150133 847775229011583392545325)
          ·
            refine ⟨317915710879343772204497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 847775229011583392545325 317915710879343772204497)
            ·
              refine ⟨238436783159507829153373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317915710879343772204497 238436783159507829153373)
              ·
                refine ⟨89413793684815435932515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238436783159507829153373 89413793684815435932515)
                ·
                  rfl

theorem cell19_293849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_293849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293849 prefixEnd_293849 := by exact prefixLift 293849
  have htrace : WordTrace (prefixWord ++ tailWord_293849) baseStart_293849 baseEnd_293849 := by
    simpa [prefixWord, tailWord_293849, baseEnd_293849] using wordTrace_append hprefix tailTrace_293849
  have hstable : (prefixWord ++ tailWord_293849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293849).length < 2 ^ (prefixWord ++ tailWord_293849).sum := by decide
  have hdescent : baseEnd_293849 < baseStart_293849 := by decide
  rcases family_descends (prefixWord ++ tailWord_293849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293889 : List Nat := [1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_293889 : Nat := 118140960795 + 293889 * 2 ^ 59
def prefixEnd_293889 : Nat := 4983230072969 + 3 ^ 40 * 293889 * 2
def baseEnd_293889 : Nat := 89425965078107195043517

theorem tailTrace_293889 : CollatzResearch.WordTrace tailWord_293889 prefixEnd_293889 89425965078107195043517 := by
  unfold tailWord_293889
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719012432297820090300721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7146008288198546726867147 10719012432297820090300721)
  ·
    refine ⟨8039259324223365067725541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10719012432297820090300721 8039259324223365067725541)
    ·
      refine ⟨1507361123291880950198539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8039259324223365067725541 1507361123291880950198539)
      ·
        refine ⟨2261041684937821425297809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507361123291880950198539 2261041684937821425297809)
        ·
          refine ⟨1695781263703366068973357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261041684937821425297809 1695781263703366068973357)
          ·
            refine ⟨635917973888762275865009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1695781263703366068973357 635917973888762275865009)
            ·
              refine ⟨476938480416571706898757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635917973888762275865009 476938480416571706898757)
              ·
                refine ⟨89425965078107195043517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476938480416571706898757 89425965078107195043517)
                ·
                  rfl

theorem cell19_293889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_293889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293889 prefixEnd_293889 := by exact prefixLift 293889
  have htrace : WordTrace (prefixWord ++ tailWord_293889) baseStart_293889 baseEnd_293889 := by
    simpa [prefixWord, tailWord_293889, baseEnd_293889] using wordTrace_append hprefix tailTrace_293889
  have hstable : (prefixWord ++ tailWord_293889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293889).length < 2 ^ (prefixWord ++ tailWord_293889).sum := by decide
  have hdescent : baseEnd_293889 < baseStart_293889 := by decide
  rcases family_descends (prefixWord ++ tailWord_293889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293927 : List Nat := [1, 1, 7, 1, 1, 8]
def baseStart_293927 : Nat := 118140960795 + 293927 * 2 ^ 59
def prefixEnd_293927 : Nat := 4983230072969 + 3 ^ 40 * 293927 * 2
def baseEnd_293927 : Nat := 9937503100192707355441

theorem tailTrace_293927 : CollatzResearch.WordTrace tailWord_293927 prefixEnd_293927 9937503100192707355441 := by
  unfold tailWord_293927
  simp only [CollatzResearch.WordTrace]
  refine ⟨10720398406160152580184035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7146932270773435053456023 10720398406160152580184035)
  ·
    refine ⟨16080597609240228870276053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10720398406160152580184035 16080597609240228870276053)
    ·
      refine ⟨376889006466567864147095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16080597609240228870276053 376889006466567864147095)
      ·
        refine ⟨565333509699851796220643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376889006466567864147095 565333509699851796220643)
        ·
          refine ⟨848000264549777694330965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565333509699851796220643 848000264549777694330965)
          ·
            refine ⟨9937503100192707355441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 848000264549777694330965 9937503100192707355441)
            ·
              rfl

theorem cell19_293927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_293927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_293927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_293927 prefixEnd_293927 := by exact prefixLift 293927
  have htrace : WordTrace (prefixWord ++ tailWord_293927) baseStart_293927 baseEnd_293927 := by
    simpa [prefixWord, tailWord_293927, baseEnd_293927] using wordTrace_append hprefix tailTrace_293927
  have hstable : (prefixWord ++ tailWord_293927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293927).length < 2 ^ (prefixWord ++ tailWord_293927).sum := by decide
  have hdescent : baseEnd_293927 < baseStart_293927 := by decide
  rcases family_descends (prefixWord ++ tailWord_293927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294014 : List Nat := [4, 2, 4, 1, 1, 2, 2, 3]
def baseStart_294014 : Nat := 118140960795 + 294014 * 2 ^ 59
def prefixEnd_294014 : Nat := 4983230072969 + 3 ^ 40 * 294014 * 2
def baseEnd_294014 : Nat := 89464000682143942265399

theorem tailTrace_294014 : CollatzResearch.WordTrace tailWord_294014 prefixEnd_294014 89464000682143942265399 := by
  unfold tailWord_294014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340446444605620804825137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7149047704563310959067397 1340446444605620804825137)
  ·
    refine ⟨1005334833454215603618853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1340446444605620804825137 1005334833454215603618853)
    ·
      refine ⟨188500281272665425678535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1005334833454215603618853 188500281272665425678535)
      ·
        refine ⟨282750421908998138517803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188500281272665425678535 282750421908998138517803)
        ·
          refine ⟨424125632863497207776705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282750421908998138517803 424125632863497207776705)
          ·
            refine ⟨318094224647622905832529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424125632863497207776705 318094224647622905832529)
            ·
              refine ⟨238570668485717179374397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318094224647622905832529 238570668485717179374397)
              ·
                refine ⟨89464000682143942265399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238570668485717179374397 89464000682143942265399)
                ·
                  rfl

theorem cell19_294014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_294014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294014 prefixEnd_294014 := by exact prefixLift 294014
  have htrace : WordTrace (prefixWord ++ tailWord_294014) baseStart_294014 baseEnd_294014 := by
    simpa [prefixWord, tailWord_294014, baseEnd_294014] using wordTrace_append hprefix tailTrace_294014
  have hstable : (prefixWord ++ tailWord_294014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294014).length < 2 ^ (prefixWord ++ tailWord_294014).sum := by decide
  have hdescent : baseEnd_294014 < baseStart_294014 := by decide
  rcases family_descends (prefixWord ++ tailWord_294014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294020 : List Nat := [2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_294020 : Nat := 118140960795 + 294020 * 2 ^ 59
def prefixEnd_294020 : Nat := 4983230072969 + 3 ^ 40 * 294020 * 2
def baseEnd_294020 : Nat := 89465826391137706132049

theorem tailTrace_294020 : CollatzResearch.WordTrace tailWord_294020 prefixEnd_294020 89465826391137706132049 := by
  unfold tailWord_294020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361895197411614731659757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7149193596548819642213009 5361895197411614731659757)
  ·
    refine ⟨2010710699029355524372409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5361895197411614731659757 2010710699029355524372409)
    ·
      refine ⟨1508033024272016643279307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2010710699029355524372409 1508033024272016643279307)
      ·
        refine ⟨2262049536408024964918961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508033024272016643279307 2262049536408024964918961)
        ·
          refine ⟨1696537152306018723689221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2262049536408024964918961 1696537152306018723689221)
          ·
            refine ⟨318100716057378510691729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1696537152306018723689221 318100716057378510691729)
            ·
              refine ⟨238575537043033883018797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318100716057378510691729 238575537043033883018797)
              ·
                refine ⟨89465826391137706132049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238575537043033883018797 89465826391137706132049)
                ·
                  rfl

theorem cell19_294020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_294020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294020 prefixEnd_294020 := by exact prefixLift 294020
  have htrace : WordTrace (prefixWord ++ tailWord_294020) baseStart_294020 baseEnd_294020 := by
    simpa [prefixWord, tailWord_294020, baseEnd_294020] using wordTrace_append hprefix tailTrace_294020
  have hstable : (prefixWord ++ tailWord_294020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294020).length < 2 ^ (prefixWord ++ tailWord_294020).sum := by decide
  have hdescent : baseEnd_294020 < baseStart_294020 := by decide
  rcases family_descends (prefixWord ++ tailWord_294020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294058 : List Nat := [3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_294058 : Nat := 118140960795 + 294058 * 2 ^ 59
def prefixEnd_294058 : Nat := 4983230072969 + 3 ^ 40 * 294058 * 2
def baseEnd_294058 : Nat := 89477389214764877287501

theorem tailTrace_294058 : CollatzResearch.WordTrace tailWord_294058 prefixEnd_294058 89477389214764877287501 := by
  unfold tailWord_294058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681294092171390488300707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7150117579123707968801885 2681294092171390488300707)
  ·
    refine ⟨4021941138257085732451061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2681294092171390488300707 4021941138257085732451061)
    ·
      refine ⟨377056981711601787417287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4021941138257085732451061 377056981711601787417287)
      ·
        refine ⟨565585472567402681125931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377056981711601787417287 565585472567402681125931)
        ·
          refine ⟨848378208851104021688897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565585472567402681125931 848378208851104021688897)
          ·
            refine ⟨636283656638328016266673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 848378208851104021688897 636283656638328016266673)
            ·
              refine ⟨477212742478746012200005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636283656638328016266673 477212742478746012200005)
              ·
                refine ⟨89477389214764877287501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477212742478746012200005 89477389214764877287501)
                ·
                  rfl

theorem cell19_294058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_294058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294058 prefixEnd_294058 := by exact prefixLift 294058
  have htrace : WordTrace (prefixWord ++ tailWord_294058) baseStart_294058 baseEnd_294058 := by
    simpa [prefixWord, tailWord_294058, baseEnd_294058] using wordTrace_append hprefix tailTrace_294058
  have hstable : (prefixWord ++ tailWord_294058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294058).length < 2 ^ (prefixWord ++ tailWord_294058).sum := by decide
  have hdescent : baseEnd_294058 < baseStart_294058 := by decide
  rcases family_descends (prefixWord ++ tailWord_294058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294189 : List Nat := [1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_294189 : Nat := 118140960795 + 294189 * 2 ^ 59
def prefixEnd_294189 : Nat := 4983230072969 + 3 ^ 40 * 294189 * 2
def baseEnd_294189 : Nat := 89517250527795388376033

theorem tailTrace_294189 : CollatzResearch.WordTrace tailWord_294189 prefixEnd_294189 89517250527795388376033 := by
  unfold tailWord_294189
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729954331210971326221621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7153302887473980884147747 10729954331210971326221621)
  ·
    refine ⟨1005933218551028561833277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10729954331210971326221621 1005933218551028561833277)
    ·
      refine ⟨377224956956635710687479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1005933218551028561833277 377224956956635710687479)
      ·
        refine ⟨565837435434953566031219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377224956956635710687479 565837435434953566031219)
        ·
          refine ⟨848756153152430349046829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565837435434953566031219 848756153152430349046829)
          ·
            refine ⟨318283557432161380892561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 848756153152430349046829 318283557432161380892561)
            ·
              refine ⟨238712668074121035669421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318283557432161380892561 238712668074121035669421)
              ·
                refine ⟨89517250527795388376033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238712668074121035669421 89517250527795388376033)
                ·
                  rfl

theorem cell19_294189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_294189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294189 prefixEnd_294189 := by exact prefixLift 294189
  have htrace : WordTrace (prefixWord ++ tailWord_294189) baseStart_294189 baseEnd_294189 := by
    simpa [prefixWord, tailWord_294189, baseEnd_294189] using wordTrace_append hprefix tailTrace_294189
  have hstable : (prefixWord ++ tailWord_294189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294189).length < 2 ^ (prefixWord ++ tailWord_294189).sum := by decide
  have hdescent : baseEnd_294189 < baseStart_294189 := by decide
  rcases family_descends (prefixWord ++ tailWord_294189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294193 : List Nat := [1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_294193 : Nat := 118140960795 + 294193 * 2 ^ 59
def prefixEnd_294193 : Nat := 4983230072969 + 3 ^ 40 * 294193 * 2
def baseEnd_294193 : Nat := 89518467667124564287133

theorem tailTrace_294193 : CollatzResearch.WordTrace tailWord_294193 prefixEnd_294193 89518467667124564287133 := by
  unfold tailWord_294193
  simp only [CollatzResearch.WordTrace]
  refine ⟨10730100223196480009367233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7153400148797653339578155 10730100223196480009367233)
  ·
    refine ⟨8047575167397360007025425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10730100223196480009367233 8047575167397360007025425)
    ·
      refine ⟨6035681375548020005269069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8047575167397360007025425 6035681375548020005269069)
      ·
        refine ⟨2263380515830507501975901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6035681375548020005269069 2263380515830507501975901)
        ·
          refine ⟨848767693436440313240963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2263380515830507501975901 848767693436440313240963)
          ·
            refine ⟨1273151540154660469861445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848767693436440313240963 1273151540154660469861445)
            ·
              refine ⟨238715913778998838099021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1273151540154660469861445 238715913778998838099021)
              ·
                refine ⟨89518467667124564287133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238715913778998838099021 89518467667124564287133)
                ·
                  rfl

theorem cell19_294193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_294193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294193 prefixEnd_294193 := by exact prefixLift 294193
  have htrace : WordTrace (prefixWord ++ tailWord_294193) baseStart_294193 baseEnd_294193 := by
    simpa [prefixWord, tailWord_294193, baseEnd_294193] using wordTrace_append hprefix tailTrace_294193
  have hstable : (prefixWord ++ tailWord_294193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294193).length < 2 ^ (prefixWord ++ tailWord_294193).sum := by decide
  have hdescent : baseEnd_294193 < baseStart_294193 := by decide
  rcases family_descends (prefixWord ++ tailWord_294193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294195 : List Nat := [1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_294195 : Nat := 118140960795 + 294195 * 2 ^ 59
def prefixEnd_294195 : Nat := 4983230072969 + 3 ^ 40 * 294195 * 2
def baseEnd_294195 : Nat := 89519076236789152242683

theorem tailTrace_294195 : CollatzResearch.WordTrace tailWord_294195 prefixEnd_294195 89519076236789152242683 := by
  unfold tailWord_294195
  simp only [CollatzResearch.WordTrace]
  refine ⟨10730173169189234350940039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7153448779459489567293359 10730173169189234350940039)
  ·
    refine ⟨16095259753783851526410059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10730173169189234350940039 16095259753783851526410059)
    ·
      refine ⟨24142889630675777289615089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16095259753783851526410059 24142889630675777289615089)
      ·
        refine ⟨18107167223006832967211317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24142889630675777289615089 18107167223006832967211317)
        ·
          refine ⟨1697546927156890590676061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18107167223006832967211317 1697546927156890590676061)
          ·
            refine ⟨636580097683833971503523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1697546927156890590676061 636580097683833971503523)
            ·
              refine ⟨954870146525750957255285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636580097683833971503523 954870146525750957255285)
              ·
                refine ⟨89519076236789152242683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 954870146525750957255285 89519076236789152242683)
                ·
                  rfl

theorem cell19_294195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_294195 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294195 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294195 prefixEnd_294195 := by exact prefixLift 294195
  have htrace : WordTrace (prefixWord ++ tailWord_294195) baseStart_294195 baseEnd_294195 := by
    simpa [prefixWord, tailWord_294195, baseEnd_294195] using wordTrace_append hprefix tailTrace_294195
  have hstable : (prefixWord ++ tailWord_294195).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294195).length < 2 ^ (prefixWord ++ tailWord_294195).sum := by decide
  have hdescent : baseEnd_294195 < baseStart_294195 := by decide
  rcases family_descends (prefixWord ++ tailWord_294195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294212 : List Nat := [2, 3, 4, 1, 1, 1, 7]
def baseStart_294212 : Nat := 118140960795 + 294212 * 2 ^ 59
def prefixEnd_294212 : Nat := 4983230072969 + 3 ^ 40 * 294212 * 2
def baseEnd_294212 : Nat := 29841416359646049954953

theorem tailTrace_294212 : CollatzResearch.WordTrace tailWord_294212 prefixEnd_294212 29841416359646049954953 := by
  unfold tailWord_294212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365396605063823127154445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7153862140085097502872593 5365396605063823127154445)
  ·
    refine ⟨2012023726898933672682917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5365396605063823127154445 2012023726898933672682917)
    ·
      refine ⟨377254448793550063628047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2012023726898933672682917 377254448793550063628047)
      ·
        refine ⟨565881673190325095442071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377254448793550063628047 565881673190325095442071)
        ·
          refine ⟨848822509785487643163107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565881673190325095442071 848822509785487643163107)
          ·
            refine ⟨1273233764678231464744661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848822509785487643163107 1273233764678231464744661)
            ·
              refine ⟨29841416359646049954953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1273233764678231464744661 29841416359646049954953)
              ·
                rfl

theorem cell19_294212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_294212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294212 prefixEnd_294212 := by exact prefixLift 294212
  have htrace : WordTrace (prefixWord ++ tailWord_294212) baseStart_294212 baseEnd_294212 := by
    simpa [prefixWord, tailWord_294212, baseEnd_294212] using wordTrace_append hprefix tailTrace_294212
  have hstable : (prefixWord ++ tailWord_294212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294212).length < 2 ^ (prefixWord ++ tailWord_294212).sum := by decide
  have hdescent : baseEnd_294212 < baseStart_294212 := by decide
  rcases family_descends (prefixWord ++ tailWord_294212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294252 : List Nat := [2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_294252 : Nat := 118140960795 + 294252 * 2 ^ 59
def prefixEnd_294252 : Nat := 4983230072969 + 3 ^ 40 * 294252 * 2
def baseEnd_294252 : Nat := 89536420472229908975861

theorem tailTrace_294252 : CollatzResearch.WordTrace tailWord_294252 prefixEnd_294252 89536420472229908975861 := by
  unfold tailWord_294252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366126064991366542882505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7154834753321822057176673 5366126064991366542882505)
  ·
    refine ⟨4024594548743524907161879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5366126064991366542882505 4024594548743524907161879)
    ·
      refine ⟨6036891823115287360742819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4024594548743524907161879 6036891823115287360742819)
      ·
        refine ⟨9055337734672931041114229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6036891823115287360742819 9055337734672931041114229)
        ·
          refine ⟨848937912625587285104459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9055337734672931041114229 848937912625587285104459)
          ·
            refine ⟨1273406868938380927656689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848937912625587285104459 1273406868938380927656689)
            ·
              refine ⟨955055151703785695742517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273406868938380927656689 955055151703785695742517)
              ·
                refine ⟨89536420472229908975861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 955055151703785695742517 89536420472229908975861)
                ·
                  rfl

theorem cell19_294252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_294252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294252 prefixEnd_294252 := by exact prefixLift 294252
  have htrace : WordTrace (prefixWord ++ tailWord_294252) baseStart_294252 baseEnd_294252 := by
    simpa [prefixWord, tailWord_294252, baseEnd_294252] using wordTrace_append hprefix tailTrace_294252
  have hstable : (prefixWord ++ tailWord_294252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294252).length < 2 ^ (prefixWord ++ tailWord_294252).sum := by decide
  have hdescent : baseEnd_294252 < baseStart_294252 := by decide
  rcases family_descends (prefixWord ++ tailWord_294252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294286 : List Nat := [4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_294286 : Nat := 118140960795 + 294286 * 2 ^ 59
def prefixEnd_294286 : Nat := 4983230072969 + 3 ^ 40 * 294286 * 2
def baseEnd_294286 : Nat := 89546766156527904220213

theorem tailTrace_294286 : CollatzResearch.WordTrace tailWord_294286 prefixEnd_294286 89546766156527904220213 := by
  unfold tailWord_294286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341686526482444611562839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7155661474573037928335141 1341686526482444611562839)
  ·
    refine ⟨2012529789723666917344259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1341686526482444611562839 2012529789723666917344259)
    ·
      refine ⟨3018794684585500376016389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012529789723666917344259 3018794684585500376016389)
      ·
        refine ⟨566024003359781320503073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3018794684585500376016389 566024003359781320503073)
        ·
          refine ⟨424518002519835990377305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566024003359781320503073 424518002519835990377305)
          ·
            refine ⟨318388501889876992782979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424518002519835990377305 318388501889876992782979)
            ·
              refine ⟨477582752834815489174469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318388501889876992782979 477582752834815489174469)
              ·
                refine ⟨89546766156527904220213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477582752834815489174469 89546766156527904220213)
                ·
                  rfl

theorem cell19_294286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_294286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294286 prefixEnd_294286 := by exact prefixLift 294286
  have htrace : WordTrace (prefixWord ++ tailWord_294286) baseStart_294286 baseEnd_294286 := by
    simpa [prefixWord, tailWord_294286, baseEnd_294286] using wordTrace_append hprefix tailTrace_294286
  have hstable : (prefixWord ++ tailWord_294286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294286).length < 2 ^ (prefixWord ++ tailWord_294286).sum := by decide
  have hdescent : baseEnd_294286 < baseStart_294286 := by decide
  rcases family_descends (prefixWord ++ tailWord_294286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294381 : List Nat := [1, 5, 1, 3, 3, 1, 5]
def baseStart_294381 : Nat := 118140960795 + 294381 * 2 ^ 59
def prefixEnd_294381 : Nat := 4983230072969 + 3 ^ 40 * 294381 * 2
def baseEnd_294381 : Nat := 29858557738531944036281

theorem tailTrace_294381 : CollatzResearch.WordTrace tailWord_294381 prefixEnd_294381 29858557738531944036281 := by
  unfold tailWord_294381
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736957146515388117210997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7157971431010258744807331 10736957146515388117210997)
  ·
    refine ⟨1006589732485817635988531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10736957146515388117210997 1006589732485817635988531)
    ·
      refine ⟨1509884598728726453982797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006589732485817635988531 1509884598728726453982797)
      ·
        refine ⟨566206724523272420243549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1509884598728726453982797 566206724523272420243549)
        ·
          refine ⟨212327521696227157591331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 566206724523272420243549 212327521696227157591331)
          ·
            refine ⟨318491282544340736386997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212327521696227157591331 318491282544340736386997)
            ·
              refine ⟨29858557738531944036281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 318491282544340736386997 29858557738531944036281)
              ·
                rfl

theorem cell19_294381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_294381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294381 prefixEnd_294381 := by exact prefixLift 294381
  have htrace : WordTrace (prefixWord ++ tailWord_294381) baseStart_294381 baseEnd_294381 := by
    simpa [prefixWord, tailWord_294381, baseEnd_294381] using wordTrace_append hprefix tailTrace_294381
  have hstable : (prefixWord ++ tailWord_294381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294381).length < 2 ^ (prefixWord ++ tailWord_294381).sum := by decide
  have hdescent : baseEnd_294381 < baseStart_294381 := by decide
  rcases family_descends (prefixWord ++ tailWord_294381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294385 : List Nat := [1, 2, 2, 2, 3, 4, 5]
def baseStart_294385 : Nat := 118140960795 + 294385 * 2 ^ 59
def prefixEnd_294385 : Nat := 4983230072969 + 3 ^ 40 * 294385 * 2
def baseEnd_294385 : Nat := 29858963451641669339981

theorem tailTrace_294385 : CollatzResearch.WordTrace tailWord_294385 prefixEnd_294385 29858963451641669339981 := by
  unfold tailWord_294385
  simp only [CollatzResearch.WordTrace]
  refine ⟨10737103038500896800356609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7158068692333931200237739 10737103038500896800356609)
  ·
    refine ⟨8052827278875672600267457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10737103038500896800356609 8052827278875672600267457)
    ·
      refine ⟨6039620459156754450200593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8052827278875672600267457 6039620459156754450200593)
      ·
        refine ⟨4529715344367565837650445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6039620459156754450200593 4529715344367565837650445)
        ·
          refine ⟨1698643254137837189118917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4529715344367565837650445 1698643254137837189118917)
          ·
            refine ⟨318495610150844472959797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1698643254137837189118917 318495610150844472959797)
            ·
              refine ⟨29858963451641669339981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 318495610150844472959797 29858963451641669339981)
              ·
                rfl

theorem cell19_294385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_294385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294385 prefixEnd_294385 := by exact prefixLift 294385
  have htrace : WordTrace (prefixWord ++ tailWord_294385) baseStart_294385 baseEnd_294385 := by
    simpa [prefixWord, tailWord_294385, baseEnd_294385] using wordTrace_append hprefix tailTrace_294385
  have hstable : (prefixWord ++ tailWord_294385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294385).length < 2 ^ (prefixWord ++ tailWord_294385).sum := by decide
  have hdescent : baseEnd_294385 < baseStart_294385 := by decide
  rcases family_descends (prefixWord ++ tailWord_294385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294402 : List Nat := [3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_294402 : Nat := 118140960795 + 294402 * 2 ^ 59
def prefixEnd_294402 : Nat := 4983230072969 + 3 ^ 40 * 294402 * 2
def baseEnd_294402 : Nat := 89582063197074005642119

theorem tailTrace_294402 : CollatzResearch.WordTrace tailWord_294402 prefixEnd_294402 89582063197074005642119 := by
  unfold tailWord_294402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684430769859827175931365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7158482052959539135816973 2684430769859827175931365)
  ·
    refine ⟨503330769348717595487131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2684430769859827175931365 503330769348717595487131)
    ·
      refine ⟨754996154023076393230697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503330769348717595487131 754996154023076393230697)
      ·
        refine ⟨566247115517307294923023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 754996154023076393230697 566247115517307294923023)
        ·
          refine ⟨849370673275960942384535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566247115517307294923023 849370673275960942384535)
          ·
            refine ⟨1274056009913941413576803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849370673275960942384535 1274056009913941413576803)
            ·
              refine ⟨1911084014870912120365205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274056009913941413576803 1911084014870912120365205)
              ·
                refine ⟨89582063197074005642119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1911084014870912120365205 89582063197074005642119)
                ·
                  rfl

theorem cell19_294402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_294402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294402 prefixEnd_294402 := by exact prefixLift 294402
  have htrace : WordTrace (prefixWord ++ tailWord_294402) baseStart_294402 baseEnd_294402 := by
    simpa [prefixWord, tailWord_294402, baseEnd_294402] using wordTrace_append hprefix tailTrace_294402
  have hstable : (prefixWord ++ tailWord_294402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294402).length < 2 ^ (prefixWord ++ tailWord_294402).sum := by decide
  have hdescent : baseEnd_294402 < baseStart_294402 := by decide
  rcases family_descends (prefixWord ++ tailWord_294402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294440 : List Nat := [2, 1, 5, 2, 3, 6]
def baseStart_294440 : Nat := 118140960795 + 294440 * 2 ^ 59
def prefixEnd_294440 : Nat := 4983230072969 + 3 ^ 40 * 294440 * 2
def baseEnd_294440 : Nat := 9954847335633464088619

theorem tailTrace_294440 : CollatzResearch.WordTrace tailWord_294440 prefixEnd_294440 9954847335633464088619 := by
  unfold tailWord_294440
  simp only [CollatzResearch.WordTrace]
  refine ⟨5369554526650820596804387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7159406035534427462405849 5369554526650820596804387)
  ·
    refine ⟨8054331789976230895206581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5369554526650820596804387 8054331789976230895206581)
    ·
      refine ⟨755093605310271646425617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8054331789976230895206581 755093605310271646425617)
      ·
        refine ⟨566320203982703734819213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 755093605310271646425617 566320203982703734819213)
        ·
          refine ⟨212370076493513900557205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 566320203982703734819213 212370076493513900557205)
          ·
            refine ⟨9954847335633464088619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 212370076493513900557205 9954847335633464088619)
            ·
              rfl

theorem cell19_294440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_294440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294440 prefixEnd_294440 := by exact prefixLift 294440
  have htrace : WordTrace (prefixWord ++ tailWord_294440) baseStart_294440 baseEnd_294440 := by
    simpa [prefixWord, tailWord_294440, baseEnd_294440] using wordTrace_append hprefix tailTrace_294440
  have hstable : (prefixWord ++ tailWord_294440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294440).length < 2 ^ (prefixWord ++ tailWord_294440).sum := by decide
  have hdescent : baseEnd_294440 < baseStart_294440 := by decide
  rcases family_descends (prefixWord ++ tailWord_294440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294480 : List Nat := [2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_294480 : Nat := 118140960795 + 294480 * 2 ^ 59
def prefixEnd_294480 : Nat := 4983230072969 + 3 ^ 40 * 294480 * 2
def baseEnd_294480 : Nat := 89605797413992935908573

theorem tailTrace_294480 : CollatzResearch.WordTrace tailWord_294480 prefixEnd_294480 89605797413992935908573 := by
  unfold tailWord_294480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370283986578364012532447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7160378648771152016709929 5370283986578364012532447)
  ·
    refine ⟨8055425979867546018798671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5370283986578364012532447 8055425979867546018798671)
    ·
      refine ⟨12083138969801319028198007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8055425979867546018798671 12083138969801319028198007)
      ·
        refine ⟨18124708454701978542297011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12083138969801319028198007 18124708454701978542297011)
        ·
          refine ⟨27187062682052967813445517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18124708454701978542297011 27187062682052967813445517)
          ·
            refine ⟨10195148505769862930042069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27187062682052967813445517 10195148505769862930042069)
            ·
              refine ⟨238948793103981162422861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10195148505769862930042069 238948793103981162422861)
              ·
                refine ⟨89605797413992935908573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238948793103981162422861 89605797413992935908573)
                ·
                  rfl

theorem cell19_294480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_294480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294480 prefixEnd_294480 := by exact prefixLift 294480
  have htrace : WordTrace (prefixWord ++ tailWord_294480) baseStart_294480 baseEnd_294480 := by
    simpa [prefixWord, tailWord_294480, baseEnd_294480] using wordTrace_append hprefix tailTrace_294480
  have hstable : (prefixWord ++ tailWord_294480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294480).length < 2 ^ (prefixWord ++ tailWord_294480).sum := by decide
  have hdescent : baseEnd_294480 < baseStart_294480 := by decide
  rcases family_descends (prefixWord ++ tailWord_294480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294535 : List Nat := [1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_294535 : Nat := 118140960795 + 294535 * 2 ^ 59
def prefixEnd_294535 : Nat := 4983230072969 + 3 ^ 40 * 294535 * 2
def baseEnd_294535 : Nat := 89622533079769104686201

theorem tailTrace_294535 : CollatzResearch.WordTrace tailWord_294535 prefixEnd_294535 89622533079769104686201 := by
  unfold tailWord_294535
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742573987957472418317059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7161715991971648278878039 10742573987957472418317059)
  ·
    refine ⟨16113860981936208627475589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10742573987957472418317059 16113860981936208627475589)
    ·
      refine ⟨3021348934113039117651673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16113860981936208627475589 3021348934113039117651673)
      ·
        refine ⟨2266011700584779338238755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3021348934113039117651673 2266011700584779338238755)
        ·
          refine ⟨3399017550877169007358133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266011700584779338238755 3399017550877169007358133)
          ·
            refine ⟨318657895394734594439825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3399017550877169007358133 318657895394734594439825)
            ·
              refine ⟨238993421546050945829869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318657895394734594439825 238993421546050945829869)
              ·
                refine ⟨89622533079769104686201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238993421546050945829869 89622533079769104686201)
                ·
                  rfl

theorem cell19_294535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_294535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294535 prefixEnd_294535 := by exact prefixLift 294535
  have htrace : WordTrace (prefixWord ++ tailWord_294535) baseStart_294535 baseEnd_294535 := by
    simpa [prefixWord, tailWord_294535, baseEnd_294535] using wordTrace_append hprefix tailTrace_294535
  have hstable : (prefixWord ++ tailWord_294535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294535).length < 2 ^ (prefixWord ++ tailWord_294535).sum := by decide
  have hdescent : baseEnd_294535 < baseStart_294535 := by decide
  rcases family_descends (prefixWord ++ tailWord_294535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294537 : List Nat := [1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_294537 : Nat := 118140960795 + 294537 * 2 ^ 59
def prefixEnd_294537 : Nat := 4983230072969 + 3 ^ 40 * 294537 * 2
def baseEnd_294537 : Nat := 89623141649433692641751

theorem tailTrace_294537 : CollatzResearch.WordTrace tailWord_294537 prefixEnd_294537 89623141649433692641751 := by
  unfold tailWord_294537
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742646933950226759889865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7161764622633484506593243 10742646933950226759889865)
  ·
    refine ⟨8056985200462670069917399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10742646933950226759889865 8056985200462670069917399)
    ·
      refine ⟨12085477800694005104876099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8056985200462670069917399 12085477800694005104876099)
      ·
        refine ⟨18128216701041007657314149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085477800694005104876099 18128216701041007657314149)
        ·
          refine ⟨3399040631445188935746403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18128216701041007657314149 3399040631445188935746403)
          ·
            refine ⟨5098560947167783403619605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399040631445188935746403 5098560947167783403619605)
            ·
              refine ⟨238995044398489847044669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5098560947167783403619605 238995044398489847044669)
              ·
                refine ⟨89623141649433692641751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238995044398489847044669 89623141649433692641751)
                ·
                  rfl

theorem cell19_294537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_294537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294537 prefixEnd_294537 := by exact prefixLift 294537
  have htrace : WordTrace (prefixWord ++ tailWord_294537) baseStart_294537 baseEnd_294537 := by
    simpa [prefixWord, tailWord_294537, baseEnd_294537] using wordTrace_append hprefix tailTrace_294537
  have hstable : (prefixWord ++ tailWord_294537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294537).length < 2 ^ (prefixWord ++ tailWord_294537).sum := by decide
  have hdescent : baseEnd_294537 < baseStart_294537 := by decide
  rcases family_descends (prefixWord ++ tailWord_294537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294539 : List Nat := [1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_294539 : Nat := 118140960795 + 294539 * 2 ^ 59
def prefixEnd_294539 : Nat := 4983230072969 + 3 ^ 40 * 294539 * 2
def baseEnd_294539 : Nat := 89623750219098280597301

theorem tailTrace_294539 : CollatzResearch.WordTrace tailWord_294539 prefixEnd_294539 89623750219098280597301 := by
  unfold tailWord_294539
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742719879942981101462671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7161813253295320734308447 10742719879942981101462671)
  ·
    refine ⟨16114079819914471652194007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10742719879942981101462671 16114079819914471652194007)
    ·
      refine ⟨24171119729871707478291011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16114079819914471652194007 24171119729871707478291011)
      ·
        refine ⟨36256679594807561217436517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24171119729871707478291011 36256679594807561217436517)
        ·
          refine ⟨6798127424026417728269347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36256679594807561217436517 6798127424026417728269347)
          ·
            refine ⟨10197191136039626592404021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798127424026417728269347 10197191136039626592404021)
            ·
              refine ⟨955986669003714993037877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10197191136039626592404021 955986669003714993037877)
              ·
                refine ⟨89623750219098280597301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 955986669003714993037877 89623750219098280597301)
                ·
                  rfl

theorem cell19_294539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_294539 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294539 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294539 prefixEnd_294539 := by exact prefixLift 294539
  have htrace : WordTrace (prefixWord ++ tailWord_294539) baseStart_294539 baseEnd_294539 := by
    simpa [prefixWord, tailWord_294539, baseEnd_294539] using wordTrace_append hprefix tailTrace_294539
  have hstable : (prefixWord ++ tailWord_294539).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294539).length < 2 ^ (prefixWord ++ tailWord_294539).sum := by decide
  have hdescent : baseEnd_294539 < baseStart_294539 := by decide
  rcases family_descends (prefixWord ++ tailWord_294539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294632 : List Nat := [2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_294632 : Nat := 118140960795 + 294632 * 2 ^ 59
def prefixEnd_294632 : Nat := 4983230072969 + 3 ^ 40 * 294632 * 2
def baseEnd_294632 : Nat := 89652048708501620530381

theorem tailTrace_294632 : CollatzResearch.WordTrace tailWord_294632 prefixEnd_294632 89652048708501620530381 := by
  unfold tailWord_294632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373055934303028992299075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7164074579070705323065433 5373055934303028992299075)
  ·
    refine ⟨8059583901454543488448613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5373055934303028992299075 8059583901454543488448613)
    ·
      refine ⟨1511171981522726904084115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8059583901454543488448613 1511171981522726904084115)
      ·
        refine ⟨2266757972284090356126173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511171981522726904084115 2266757972284090356126173)
        ·
          refine ⟨850034239606533883547315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2266757972284090356126173 850034239606533883547315)
          ·
            refine ⟨1275051359409800825320973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850034239606533883547315 1275051359409800825320973)
            ·
              refine ⟨478144259778675309495365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275051359409800825320973 478144259778675309495365)
              ·
                refine ⟨89652048708501620530381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478144259778675309495365 89652048708501620530381)
                ·
                  rfl

theorem cell19_294632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_294632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294632 prefixEnd_294632 := by exact prefixLift 294632
  have htrace : WordTrace (prefixWord ++ tailWord_294632) baseStart_294632 baseEnd_294632 := by
    simpa [prefixWord, tailWord_294632, baseEnd_294632] using wordTrace_append hprefix tailTrace_294632
  have hstable : (prefixWord ++ tailWord_294632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294632).length < 2 ^ (prefixWord ++ tailWord_294632).sum := by decide
  have hdescent : baseEnd_294632 < baseStart_294632 := by decide
  rcases family_descends (prefixWord ++ tailWord_294632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294662 : List Nat := [6, 2, 2, 1, 1, 1, 6]
def baseStart_294662 : Nat := 118140960795 + 294662 * 2 ^ 59
def prefixEnd_294662 : Nat := 4983230072969 + 3 ^ 40 * 294662 * 2
def baseEnd_294662 : Nat := 29887059084490146621211

theorem tailTrace_294662 : CollatzResearch.WordTrace tailWord_294662 prefixEnd_294662 29887059084490146621211 := by
  unfold tailWord_294662
  simp only [CollatzResearch.WordTrace]
  refine ⟨335850189328042909630945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7164804038998248738793493 335850189328042909630945)
  ·
    refine ⟨251887641996032182223209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 335850189328042909630945 251887641996032182223209)
    ·
      refine ⟨188915731497024136667407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251887641996032182223209 188915731497024136667407)
      ·
        refine ⟨283373597245536205001111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188915731497024136667407 283373597245536205001111)
        ·
          refine ⟨425060395868304307501667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283373597245536205001111 425060395868304307501667)
          ·
            refine ⟨637590593802456461252501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425060395868304307501667 637590593802456461252501)
            ·
              refine ⟨29887059084490146621211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 637590593802456461252501 29887059084490146621211)
              ·
                rfl

theorem cell19_294662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_294662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294662 prefixEnd_294662 := by exact prefixLift 294662
  have htrace : WordTrace (prefixWord ++ tailWord_294662) baseStart_294662 baseEnd_294662 := by
    simpa [prefixWord, tailWord_294662, baseEnd_294662] using wordTrace_append hprefix tailTrace_294662
  have hstable : (prefixWord ++ tailWord_294662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294662).length < 2 ^ (prefixWord ++ tailWord_294662).sum := by decide
  have hdescent : baseEnd_294662 < baseStart_294662 := by decide
  rcases family_descends (prefixWord ++ tailWord_294662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294702 : List Nat := [4, 1, 3, 2, 3, 1, 2, 3]
def baseStart_294702 : Nat := 118140960795 + 294702 * 2 ^ 59
def prefixEnd_294702 : Nat := 4983230072969 + 3 ^ 40 * 294702 * 2
def baseEnd_294702 : Nat := 89673348646762198974635

theorem tailTrace_294702 : CollatzResearch.WordTrace tailWord_294702 prefixEnd_294702 89673348646762198974635 := by
  unfold tailWord_294702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343583122294057492455795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7165776652234973293097573 1343583122294057492455795)
  ·
    refine ⟨2015374683441086238683693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343583122294057492455795 2015374683441086238683693)
    ·
      refine ⟨755765506290407339506385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2015374683441086238683693 755765506290407339506385)
      ·
        refine ⟨566824129717805504629789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 755765506290407339506385 566824129717805504629789)
        ·
          refine ⟨212559048644177064236171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 566824129717805504629789 212559048644177064236171)
          ·
            refine ⟨318838572966265596354257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212559048644177064236171 318838572966265596354257)
            ·
              refine ⟨239128929724699197265693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318838572966265596354257 239128929724699197265693)
              ·
                refine ⟨89673348646762198974635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239128929724699197265693 89673348646762198974635)
                ·
                  rfl

theorem cell19_294702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_294702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294702 prefixEnd_294702 := by exact prefixLift 294702
  have htrace : WordTrace (prefixWord ++ tailWord_294702) baseStart_294702 baseEnd_294702 := by
    simpa [prefixWord, tailWord_294702, baseEnd_294702] using wordTrace_append hprefix tailTrace_294702
  have hstable : (prefixWord ++ tailWord_294702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294702).length < 2 ^ (prefixWord ++ tailWord_294702).sum := by decide
  have hdescent : baseEnd_294702 < baseStart_294702 := by decide
  rcases family_descends (prefixWord ++ tailWord_294702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294706 : List Nat := [3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_294706 : Nat := 118140960795 + 294706 * 2 ^ 59
def prefixEnd_294706 : Nat := 4983230072969 + 3 ^ 40 * 294706 * 2
def baseEnd_294706 : Nat := 89674565786091374885735

theorem tailTrace_294706 : CollatzResearch.WordTrace tailWord_294706 prefixEnd_294706 89674565786091374885735 := by
  unfold tailWord_294706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687202717584492155697993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7165873913558645748527981 2687202717584492155697993)
  ·
    refine ⟨2015402038188369116773495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2687202717584492155697993 2015402038188369116773495)
    ·
      refine ⟨3023103057282553675160243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015402038188369116773495 3023103057282553675160243)
      ·
        refine ⟨4534654585923830512740365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023103057282553675160243 4534654585923830512740365)
        ·
          refine ⟨1700495469721436442277637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4534654585923830512740365 1700495469721436442277637)
          ·
            refine ⟨318842900572769332927057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1700495469721436442277637 318842900572769332927057)
            ·
              refine ⟨239132175429576999695293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318842900572769332927057 239132175429576999695293)
              ·
                refine ⟨89674565786091374885735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239132175429576999695293 89674565786091374885735)
                ·
                  rfl

theorem cell19_294706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_294706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294706 prefixEnd_294706 := by exact prefixLift 294706
  have htrace : WordTrace (prefixWord ++ tailWord_294706) baseStart_294706 baseEnd_294706 := by
    simpa [prefixWord, tailWord_294706, baseEnd_294706] using wordTrace_append hprefix tailTrace_294706
  have hstable : (prefixWord ++ tailWord_294706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294706).length < 2 ^ (prefixWord ++ tailWord_294706).sum := by decide
  have hdescent : baseEnd_294706 < baseStart_294706 := by decide
  rcases family_descends (prefixWord ++ tailWord_294706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294862 : List Nat := [4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_294862 : Nat := 118140960795 + 294862 * 2 ^ 59
def prefixEnd_294862 : Nat := 4983230072969 + 3 ^ 40 * 294862 * 2
def baseEnd_294862 : Nat := 89722034219929235418643

theorem tailTrace_294862 : CollatzResearch.WordTrace tailWord_294862 prefixEnd_294862 89722034219929235418643 := by
  unfold tailWord_294862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344312582221600908183855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7169667105181871510313893 1344312582221600908183855)
  ·
    refine ⟨2016468873332401362275783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1344312582221600908183855 2016468873332401362275783)
    ·
      refine ⟨3024703309998602043413675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016468873332401362275783 3024703309998602043413675)
      ·
        refine ⟨4537054964997903065120513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024703309998602043413675 4537054964997903065120513)
        ·
          refine ⟨3402791223748427298840385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4537054964997903065120513 3402791223748427298840385)
          ·
            refine ⟨2552093417811320474130289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3402791223748427298840385 2552093417811320474130289)
            ·
              refine ⟨1914070063358490355597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552093417811320474130289 1914070063358490355597717)
              ·
                refine ⟨89722034219929235418643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1914070063358490355597717 89722034219929235418643)
                ·
                  rfl

theorem cell19_294862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_294862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294862 prefixEnd_294862 := by exact prefixLift 294862
  have htrace : WordTrace (prefixWord ++ tailWord_294862) baseStart_294862 baseEnd_294862 := by
    simpa [prefixWord, tailWord_294862, baseEnd_294862] using wordTrace_append hprefix tailTrace_294862
  have hstable : (prefixWord ++ tailWord_294862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294862).length < 2 ^ (prefixWord ++ tailWord_294862).sum := by decide
  have hdescent : baseEnd_294862 < baseStart_294862 := by decide
  rcases family_descends (prefixWord ++ tailWord_294862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294879 : List Nat := [1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_294879 : Nat := 118140960795 + 294879 * 2 ^ 59
def prefixEnd_294879 : Nat := 4983230072969 + 3 ^ 40 * 294879 * 2
def baseEnd_294879 : Nat := 89727207062078233040819

theorem tailTrace_294879 : CollatzResearch.WordTrace tailWord_294879 prefixEnd_294879 89727207062078233040819 := by
  unfold tailWord_294879
  simp only [CollatzResearch.WordTrace]
  refine ⟨10755120698711219168839691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7170080465807479445893127 10755120698711219168839691)
  ·
    refine ⟨16132681048066828753259537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10755120698711219168839691 16132681048066828753259537)
    ·
      refine ⟨12099510786050121564944653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16132681048066828753259537 12099510786050121564944653)
      ·
        refine ⟨4537316544768795586854245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12099510786050121564944653 4537316544768795586854245)
        ·
          refine ⟨850746852144149172535171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4537316544768795586854245 850746852144149172535171)
          ·
            refine ⟨1276120278216223758802757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850746852144149172535171 1276120278216223758802757)
            ·
              refine ⟨239272552165541954775517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1276120278216223758802757 239272552165541954775517)
              ·
                refine ⟨89727207062078233040819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239272552165541954775517 89727207062078233040819)
                ·
                  rfl

theorem cell19_294879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_294879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294879 prefixEnd_294879 := by exact prefixLift 294879
  have htrace : WordTrace (prefixWord ++ tailWord_294879) baseStart_294879 baseEnd_294879 := by
    simpa [prefixWord, tailWord_294879, baseEnd_294879] using wordTrace_append hprefix tailTrace_294879
  have hstable : (prefixWord ++ tailWord_294879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294879).length < 2 ^ (prefixWord ++ tailWord_294879).sum := by decide
  have hdescent : baseEnd_294879 < baseStart_294879 := by decide
  rcases family_descends (prefixWord ++ tailWord_294879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294919 : List Nat := [1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_294919 : Nat := 118140960795 + 294919 * 2 ^ 59
def prefixEnd_294919 : Nat := 4983230072969 + 3 ^ 40 * 294919 * 2
def baseEnd_294919 : Nat := 89739378455369992151821

theorem tailTrace_294919 : CollatzResearch.WordTrace tailWord_294919 prefixEnd_294919 89739378455369992151821 := by
  unfold tailWord_294919
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756579618566306000295811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7171053079044204000197207 10756579618566306000295811)
  ·
    refine ⟨16134869427849459000443717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10756579618566306000295811 16134869427849459000443717)
    ·
      refine ⟨3025288017721773562583197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16134869427849459000443717 3025288017721773562583197)
      ·
        refine ⟨1134483006645665085968699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3025288017721773562583197 1134483006645665085968699)
        ·
          refine ⟨1701724509968497628953049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134483006645665085968699 1701724509968497628953049)
          ·
            refine ⟨1276293382476373221714787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701724509968497628953049 1276293382476373221714787)
            ·
              refine ⟨1914440073714559832572181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276293382476373221714787 1914440073714559832572181)
              ·
                refine ⟨89739378455369992151821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1914440073714559832572181 89739378455369992151821)
                ·
                  rfl

theorem cell19_294919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_294919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294919 prefixEnd_294919 := by exact prefixLift 294919
  have htrace : WordTrace (prefixWord ++ tailWord_294919) baseStart_294919 baseEnd_294919 := by
    simpa [prefixWord, tailWord_294919, baseEnd_294919] using wordTrace_append hprefix tailTrace_294919
  have hstable : (prefixWord ++ tailWord_294919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294919).length < 2 ^ (prefixWord ++ tailWord_294919).sum := by decide
  have hdescent : baseEnd_294919 < baseStart_294919 := by decide
  rcases family_descends (prefixWord ++ tailWord_294919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294938 : List Nat := [3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_294938 : Nat := 118140960795 + 294938 * 2 ^ 59
def prefixEnd_294938 : Nat := 4983230072969 + 3 ^ 40 * 294938 * 2
def baseEnd_294938 : Nat := 89745159867183577729547

theorem tailTrace_294938 : CollatzResearch.WordTrace tailWord_294938 prefixEnd_294938 89745159867183577729547 := by
  unfold tailWord_294938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689318151374368061309367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7171515070331648163491645 2689318151374368061309367)
  ·
    refine ⟨4033977227061552091964051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2689318151374368061309367 4033977227061552091964051)
    ·
      refine ⟨6050965840592328137946077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033977227061552091964051 6050965840592328137946077)
      ·
        refine ⟨2269112190222123051729779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6050965840592328137946077 2269112190222123051729779)
        ·
          refine ⟨3403668285333184577594669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269112190222123051729779 3403668285333184577594669)
          ·
            refine ⟨1276375606999944216598001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3403668285333184577594669 1276375606999944216598001)
            ·
              refine ⟨957281705249958162448501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276375606999944216598001 957281705249958162448501)
              ·
                refine ⟨89745159867183577729547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 957281705249958162448501 89745159867183577729547)
                ·
                  rfl

theorem cell19_294938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_294938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294938 prefixEnd_294938 := by exact prefixLift 294938
  have htrace : WordTrace (prefixWord ++ tailWord_294938) baseStart_294938 baseEnd_294938 := by
    simpa [prefixWord, tailWord_294938, baseEnd_294938] using wordTrace_append hprefix tailTrace_294938
  have hstable : (prefixWord ++ tailWord_294938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294938).length < 2 ^ (prefixWord ++ tailWord_294938).sum := by decide
  have hdescent : baseEnd_294938 < baseStart_294938 := by decide
  rcases family_descends (prefixWord ++ tailWord_294938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294976 : List Nat := [2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_294976 : Nat := 118140960795 + 294976 * 2 ^ 59
def prefixEnd_294976 : Nat := 4983230072969 + 3 ^ 40 * 294976 * 2
def baseEnd_294976 : Nat := 89756722690810748884999

theorem tailTrace_294976 : CollatzResearch.WordTrace tailWord_294976 prefixEnd_294976 89756722690810748884999 := by
  unfold tailWord_294976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379329289679902367560391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7172439052906536490080521 5379329289679902367560391)
  ·
    refine ⟨8068993934519853551340587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5379329289679902367560391 8068993934519853551340587)
    ·
      refine ⟨12103490901779780327010881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068993934519853551340587 12103490901779780327010881)
      ·
        refine ⟨9077618176334835245258161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12103490901779780327010881 9077618176334835245258161)
        ·
          refine ⟨6808213632251126433943621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9077618176334835245258161 6808213632251126433943621)
          ·
            refine ⟨1276540056047086206364429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6808213632251126433943621 1276540056047086206364429)
            ·
              refine ⟨478702521017657327386661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1276540056047086206364429 478702521017657327386661)
              ·
                refine ⟨89756722690810748884999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478702521017657327386661 89756722690810748884999)
                ·
                  rfl

theorem cell19_294976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_294976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_294976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_294976 prefixEnd_294976 := by exact prefixLift 294976
  have htrace : WordTrace (prefixWord ++ tailWord_294976) baseStart_294976 baseEnd_294976 := by
    simpa [prefixWord, tailWord_294976, baseEnd_294976] using wordTrace_append hprefix tailTrace_294976
  have hstable : (prefixWord ++ tailWord_294976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294976).length < 2 ^ (prefixWord ++ tailWord_294976).sum := by decide
  have hdescent : baseEnd_294976 < baseStart_294976 := by decide
  rcases family_descends (prefixWord ++ tailWord_294976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295048 : List Nat := [2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_295048 : Nat := 118140960795 + 295048 * 2 ^ 59
def prefixEnd_295048 : Nat := 4983230072969 + 3 ^ 40 * 295048 * 2
def baseEnd_295048 : Nat := 89778631198735915284803

theorem tailTrace_295048 : CollatzResearch.WordTrace tailWord_295048 prefixEnd_295048 89778631198735915284803 := by
  unfold tailWord_295048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380642317549480515870899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7174189756732640687827865 5380642317549480515870899)
  ·
    refine ⟨8070963476324220773806349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5380642317549480515870899 8070963476324220773806349)
    ·
      refine ⟨3026611303621582790177381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8070963476324220773806349 3026611303621582790177381)
      ·
        refine ⟨567489619429046773158259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3026611303621582790177381 567489619429046773158259)
        ·
          refine ⟨851234429143570159737389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567489619429046773158259 851234429143570159737389)
          ·
            refine ⟨319212910928838809901521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 851234429143570159737389 319212910928838809901521)
            ·
              refine ⟨239409683196629107426141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319212910928838809901521 239409683196629107426141)
              ·
                refine ⟨89778631198735915284803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239409683196629107426141 89778631198735915284803)
                ·
                  rfl

theorem cell19_295048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_295048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295048 prefixEnd_295048 := by exact prefixLift 295048
  have htrace : WordTrace (prefixWord ++ tailWord_295048) baseStart_295048 baseEnd_295048 := by
    simpa [prefixWord, tailWord_295048, baseEnd_295048] using wordTrace_append hprefix tailTrace_295048
  have hstable : (prefixWord ++ tailWord_295048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295048).length < 2 ^ (prefixWord ++ tailWord_295048).sum := by decide
  have hdescent : baseEnd_295048 < baseStart_295048 := by decide
  rcases family_descends (prefixWord ++ tailWord_295048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295050 : List Nat := [3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_295050 : Nat := 118140960795 + 295050 * 2 ^ 59
def prefixEnd_295050 : Nat := 4983230072969 + 3 ^ 40 * 295050 * 2
def baseEnd_295050 : Nat := 89779239768400503240353

theorem tailTrace_295050 : CollatzResearch.WordTrace tailWord_295050 prefixEnd_295050 89779239768400503240353 := by
  unfold tailWord_295050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690339395272928843328651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7174238387394476915543069 2690339395272928843328651)
  ·
    refine ⟨4035509092909393264992977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2690339395272928843328651 4035509092909393264992977)
    ·
      refine ⟨3026631819682044948744733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4035509092909393264992977 3026631819682044948744733)
      ·
        refine ⟨1134986932380766855779275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3026631819682044948744733 1134986932380766855779275)
        ·
          refine ⟨1702480398571150283668913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134986932380766855779275 1702480398571150283668913)
          ·
            refine ⟨1276860298928362712751685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702480398571150283668913 1276860298928362712751685)
            ·
              refine ⟨239411306049068008640941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1276860298928362712751685 239411306049068008640941)
              ·
                refine ⟨89779239768400503240353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239411306049068008640941 89779239768400503240353)
                ·
                  rfl

theorem cell19_295050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_295050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295050 prefixEnd_295050 := by exact prefixLift 295050
  have htrace : WordTrace (prefixWord ++ tailWord_295050) baseStart_295050 baseEnd_295050 := by
    simpa [prefixWord, tailWord_295050, baseEnd_295050] using wordTrace_append hprefix tailTrace_295050
  have hstable : (prefixWord ++ tailWord_295050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295050).length < 2 ^ (prefixWord ++ tailWord_295050).sum := by decide
  have hdescent : baseEnd_295050 < baseStart_295050 := by decide
  rcases family_descends (prefixWord ++ tailWord_295050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295071 : List Nat := [1, 1, 2, 6, 1, 1, 7]
def baseStart_295071 : Nat := 118140960795 + 295071 * 2 ^ 59
def prefixEnd_295071 : Nat := 4983230072969 + 3 ^ 40 * 295071 * 2
def baseEnd_295071 : Nat := 29928543249959558924543

theorem tailTrace_295071 : CollatzResearch.WordTrace tailWord_295071 prefixEnd_295071 29928543249959558924543 := by
  unfold tailWord_295071
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762123514015635959829067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7174749009343757306552711 10762123514015635959829067)
  ·
    refine ⟨16143185271023453939743601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10762123514015635959829067 16143185271023453939743601)
    ·
      refine ⟨12107388953267590454807701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16143185271023453939743601 12107388953267590454807701)
      ·
        refine ⟨567533857184418302569111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12107388953267590454807701 567533857184418302569111)
        ·
          refine ⟨851300785776627453853667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567533857184418302569111 851300785776627453853667)
          ·
            refine ⟨1276951178664941180780501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851300785776627453853667 1276951178664941180780501)
            ·
              refine ⟨29928543249959558924543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1276951178664941180780501 29928543249959558924543)
              ·
                rfl

theorem cell19_295071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_295071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295071 prefixEnd_295071 := by exact prefixLift 295071
  have htrace : WordTrace (prefixWord ++ tailWord_295071) baseStart_295071 baseEnd_295071 := by
    simpa [prefixWord, tailWord_295071, baseEnd_295071] using wordTrace_append hprefix tailTrace_295071
  have hstable : (prefixWord ++ tailWord_295071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295071).length < 2 ^ (prefixWord ++ tailWord_295071).sum := by decide
  have hdescent : baseEnd_295071 < baseStart_295071 := by decide
  rcases family_descends (prefixWord ++ tailWord_295071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295090 : List Nat := [3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_295090 : Nat := 118140960795 + 295090 * 2 ^ 59
def prefixEnd_295090 : Nat := 4983230072969 + 3 ^ 40 * 295090 * 2
def baseEnd_295090 : Nat := 89791411161692262351355

theorem tailTrace_295090 : CollatzResearch.WordTrace tailWord_295090 prefixEnd_295090 89791411161692262351355 := by
  unfold tailWord_295090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690704125236700551192681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7175211000631201469847149 2690704125236700551192681)
  ·
    refine ⟨2018028093927525413394511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2690704125236700551192681 2018028093927525413394511)
    ·
      refine ⟨3027042140891288120091767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018028093927525413394511 3027042140891288120091767)
      ·
        refine ⟨4540563211336932180137651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027042140891288120091767 4540563211336932180137651)
        ·
          refine ⟨6810844817005398270206477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540563211336932180137651 6810844817005398270206477)
          ·
            refine ⟨2554066806377024351327429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6810844817005398270206477 2554066806377024351327429)
            ·
              refine ⟨478887526195692065873893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2554066806377024351327429 478887526195692065873893)
              ·
                refine ⟨89791411161692262351355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478887526195692065873893 89791411161692262351355)
                ·
                  rfl

theorem cell19_295090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_295090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295090 prefixEnd_295090 := by exact prefixLift 295090
  have htrace : WordTrace (prefixWord ++ tailWord_295090) baseStart_295090 baseEnd_295090 := by
    simpa [prefixWord, tailWord_295090, baseEnd_295090] using wordTrace_append hprefix tailTrace_295090
  have hstable : (prefixWord ++ tailWord_295090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295090).length < 2 ^ (prefixWord ++ tailWord_295090).sum := by decide
  have hdescent : baseEnd_295090 < baseStart_295090 := by decide
  rcases family_descends (prefixWord ++ tailWord_295090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295126 : List Nat := [5, 2, 1, 2, 1, 8]
def baseStart_295126 : Nat := 118140960795 + 295126 * 2 ^ 59
def prefixEnd_295126 : Nat := 4983230072969 + 3 ^ 40 * 295126 * 2
def baseEnd_295126 : Nat := 9978040601739427283473

theorem tailTrace_295126 : CollatzResearch.WordTrace tailWord_295126 prefixEnd_295126 9978040601739427283473 := by
  unfold tailWord_295126
  simp only [CollatzResearch.WordTrace]
  refine ⟨672758095551023772067577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7176086352544253568720821 672758095551023772067577)
  ·
    refine ⟨504568571663267829050683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 672758095551023772067577 504568571663267829050683)
    ·
      refine ⟨756852857494901743576025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504568571663267829050683 756852857494901743576025)
      ·
        refine ⟨567639643121176307682019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756852857494901743576025 567639643121176307682019)
        ·
          refine ⟨851459464681764461523029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567639643121176307682019 851459464681764461523029)
          ·
            refine ⟨9978040601739427283473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 851459464681764461523029 9978040601739427283473)
            ·
              rfl

theorem cell19_295126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_295126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295126 prefixEnd_295126 := by exact prefixLift 295126
  have htrace : WordTrace (prefixWord ++ tailWord_295126) baseStart_295126 baseEnd_295126 := by
    simpa [prefixWord, tailWord_295126, baseEnd_295126] using wordTrace_append hprefix tailTrace_295126
  have hstable : (prefixWord ++ tailWord_295126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295126).length < 2 ^ (prefixWord ++ tailWord_295126).sum := by decide
  have hdescent : baseEnd_295126 < baseStart_295126 := by decide
  rcases family_descends (prefixWord ++ tailWord_295126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295164 : List Nat := [2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_295164 : Nat := 118140960795 + 295164 * 2 ^ 59
def prefixEnd_295164 : Nat := 4983230072969 + 3 ^ 40 * 295164 * 2
def baseEnd_295164 : Nat := 89813928239282016706709

theorem tailTrace_295164 : CollatzResearch.WordTrace tailWord_295164 prefixEnd_295164 89813928239282016706709 := by
  unfold tailWord_295164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382757751339356421482273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7177010335119141895309697 5382757751339356421482273)
  ·
    refine ⟨4037068313504517316111705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5382757751339356421482273 4037068313504517316111705)
    ·
      refine ⟨3027801235128387987083779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4037068313504517316111705 3027801235128387987083779)
      ·
        refine ⟨4541701852692581980625669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027801235128387987083779 4541701852692581980625669)
        ·
          refine ⟨851569097379859121367313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4541701852692581980625669 851569097379859121367313)
          ·
            refine ⟨638676823034894341025485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 851569097379859121367313 638676823034894341025485)
            ·
              refine ⟨239503808638085377884557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 638676823034894341025485 239503808638085377884557)
              ·
                refine ⟨89813928239282016706709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239503808638085377884557 89813928239282016706709)
                ·
                  rfl

theorem cell19_295164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_295164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295164 prefixEnd_295164 := by exact prefixLift 295164
  have htrace : WordTrace (prefixWord ++ tailWord_295164) baseStart_295164 baseEnd_295164 := by
    simpa [prefixWord, tailWord_295164, baseEnd_295164] using wordTrace_append hprefix tailTrace_295164
  have hstable : (prefixWord ++ tailWord_295164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295164).length < 2 ^ (prefixWord ++ tailWord_295164).sum := by decide
  have hdescent : baseEnd_295164 < baseStart_295164 := by decide
  rcases family_descends (prefixWord ++ tailWord_295164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295168 : List Nat := [2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_295168 : Nat := 118140960795 + 295168 * 2 ^ 59
def prefixEnd_295168 : Nat := 4983230072969 + 3 ^ 40 * 295168 * 2
def baseEnd_295168 : Nat := 89815145378611192617809

theorem tailTrace_295168 : CollatzResearch.WordTrace tailWord_295168 prefixEnd_295168 89815145378611192617809 := by
  unfold tailWord_295168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382830697332110763055079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7177107596442814350740105 5382830697332110763055079)
  ·
    refine ⟨8074246045998166144582619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5382830697332110763055079 8074246045998166144582619)
    ·
      refine ⟨12111369068997249216873929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8074246045998166144582619 12111369068997249216873929)
      ·
        refine ⟨9083526801747936912655447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12111369068997249216873929 9083526801747936912655447)
        ·
          refine ⟨13625290202621905368983171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9083526801747936912655447 13625290202621905368983171)
          ·
            refine ⟨20437935303932858053474757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13625290202621905368983171 20437935303932858053474757)
            ·
              refine ⟨3832112869487410885026517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20437935303932858053474757 3832112869487410885026517)
              ·
                refine ⟨89815145378611192617809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3832112869487410885026517 89815145378611192617809)
                ·
                  rfl

theorem cell19_295168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_295168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295168 prefixEnd_295168 := by exact prefixLift 295168
  have htrace : WordTrace (prefixWord ++ tailWord_295168) baseStart_295168 baseEnd_295168 := by
    simpa [prefixWord, tailWord_295168, baseEnd_295168] using wordTrace_append hprefix tailTrace_295168
  have hstable : (prefixWord ++ tailWord_295168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295168).length < 2 ^ (prefixWord ++ tailWord_295168).sum := by decide
  have hdescent : baseEnd_295168 < baseStart_295168 := by decide
  rcases family_descends (prefixWord ++ tailWord_295168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295263 : List Nat := [1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_295263 : Nat := 118140960795 + 295263 * 2 ^ 59
def prefixEnd_295263 : Nat := 4983230072969 + 3 ^ 40 * 295263 * 2
def baseEnd_295263 : Nat := 89844052437679120506439

theorem tailTrace_295263 : CollatzResearch.WordTrace tailWord_295263 prefixEnd_295263 89844052437679120506439 := by
  unfold tailWord_295263
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769126329320052750818443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7179417552880035167212295 10769126329320052750818443)
  ·
    refine ⟨16153689493980079126227665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10769126329320052750818443 16153689493980079126227665)
    ·
      refine ⟨12115267120485059344670749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16153689493980079126227665 12115267120485059344670749)
      ·
        refine ⟨4543225170181897254251531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12115267120485059344670749 4543225170181897254251531)
        ·
          refine ⟨6814837755272845881377297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543225170181897254251531 6814837755272845881377297)
          ·
            refine ⟨5111128316454634411032973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6814837755272845881377297 5111128316454634411032973)
            ·
              refine ⟨1916673118670487904137365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5111128316454634411032973 1916673118670487904137365)
              ·
                refine ⟨89844052437679120506439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1916673118670487904137365 89844052437679120506439)
                ·
                  rfl

theorem cell19_295263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_295263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295263 prefixEnd_295263 := by exact prefixLift 295263
  have htrace : WordTrace (prefixWord ++ tailWord_295263) baseStart_295263 baseEnd_295263 := by
    simpa [prefixWord, tailWord_295263, baseEnd_295263] using wordTrace_append hprefix tailTrace_295263
  have hstable : (prefixWord ++ tailWord_295263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295263).length < 2 ^ (prefixWord ++ tailWord_295263).sum := by decide
  have hdescent : baseEnd_295263 < baseStart_295263 := by decide
  rcases family_descends (prefixWord ++ tailWord_295263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295299 : List Nat := [1, 1, 1, 3, 7, 6]
def baseStart_295299 : Nat := 118140960795 + 295299 * 2 ^ 59
def prefixEnd_295299 : Nat := 4983230072969 + 3 ^ 40 * 295299 * 2
def baseEnd_295299 : Nat := 9983889632404633745149

theorem tailTrace_295299 : CollatzResearch.WordTrace tailWord_295299 prefixEnd_295299 9983889632404633745149 := by
  unfold tailWord_295299
  simp only [CollatzResearch.WordTrace]
  refine ⟨10770439357189630899128951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7180292904793087266085967 10770439357189630899128951)
  ·
    refine ⟨16155659035784446348693427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10770439357189630899128951 16155659035784446348693427)
    ·
      refine ⟨24233488553676669523040141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16155659035784446348693427 24233488553676669523040141)
      ·
        refine ⟨9087558207628751071140053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24233488553676669523040141 9087558207628751071140053)
        ·
          refine ⟨212989645491298853229845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9087558207628751071140053 212989645491298853229845)
          ·
            refine ⟨9983889632404633745149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 212989645491298853229845 9983889632404633745149)
            ·
              rfl

theorem cell19_295299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_295299 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295299 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295299 prefixEnd_295299 := by exact prefixLift 295299
  have htrace : WordTrace (prefixWord ++ tailWord_295299) baseStart_295299 baseEnd_295299 := by
    simpa [prefixWord, tailWord_295299, baseEnd_295299] using wordTrace_append hprefix tailTrace_295299
  have hstable : (prefixWord ++ tailWord_295299).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295299).length < 2 ^ (prefixWord ++ tailWord_295299).sum := by decide
  have hdescent : baseEnd_295299 < baseStart_295299 := by decide
  rcases family_descends (prefixWord ++ tailWord_295299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295335 : List Nat := [1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_295335 : Nat := 118140960795 + 295335 * 2 ^ 59
def prefixEnd_295335 : Nat := 4983230072969 + 3 ^ 40 * 295335 * 2
def baseEnd_295335 : Nat := 89865960945604286906243

theorem tailTrace_295335 : CollatzResearch.WordTrace tailWord_295335 prefixEnd_295335 89865960945604286906243 := by
  unfold tailWord_295335
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771752385059209047439459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7181168256706139364959639 10771752385059209047439459)
  ·
    refine ⟨16157628577588813571159189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10771752385059209047439459 16157628577588813571159189)
    ·
      refine ⟨757388839574475636148087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16157628577588813571159189 757388839574475636148087)
      ·
        refine ⟨1136083259361713454222131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757388839574475636148087 1136083259361713454222131)
        ·
          refine ⟨1704124889042570181333197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136083259361713454222131 1704124889042570181333197)
          ·
            refine ⟨639046833390963817999949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1704124889042570181333197 639046833390963817999949)
            ·
              refine ⟨239642562521611431749981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 639046833390963817999949 239642562521611431749981)
              ·
                refine ⟨89865960945604286906243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239642562521611431749981 89865960945604286906243)
                ·
                  rfl

theorem cell19_295335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_295335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295335 prefixEnd_295335 := by exact prefixLift 295335
  have htrace : WordTrace (prefixWord ++ tailWord_295335) baseStart_295335 baseEnd_295335 := by
    simpa [prefixWord, tailWord_295335, baseEnd_295335] using wordTrace_append hprefix tailTrace_295335
  have hstable : (prefixWord ++ tailWord_295335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295335).length < 2 ^ (prefixWord ++ tailWord_295335).sum := by decide
  have hdescent : baseEnd_295335 < baseStart_295335 := by decide
  rcases family_descends (prefixWord ++ tailWord_295335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295356 : List Nat := [2, 2, 2, 4, 1, 2, 6]
def baseStart_295356 : Nat := 118140960795 + 295356 * 2 ^ 59
def prefixEnd_295356 : Nat := 4983230072969 + 3 ^ 40 * 295356 * 2
def baseEnd_295356 : Nat := 29957450309027486813173

theorem tailTrace_295356 : CollatzResearch.WordTrace tailWord_295356 prefixEnd_295356 29957450309027486813173 := by
  unfold tailWord_295356
  simp only [CollatzResearch.WordTrace]
  refine ⟨5386259158991564816976961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7181678878655419755969281 5386259158991564816976961)
  ·
    refine ⟨4039694369243673612732721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5386259158991564816976961 4039694369243673612732721)
    ·
      refine ⟨3029770776932755209549541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4039694369243673612732721 3029770776932755209549541)
      ·
        refine ⟨568082020674891601790539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3029770776932755209549541 568082020674891601790539)
        ·
          refine ⟨852123031012337402685809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568082020674891601790539 852123031012337402685809)
          ·
            refine ⟨639092273259253052014357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852123031012337402685809 639092273259253052014357)
            ·
              refine ⟨29957450309027486813173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 639092273259253052014357 29957450309027486813173)
              ·
                rfl

theorem cell19_295356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_295356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295356 prefixEnd_295356 := by exact prefixLift 295356
  have htrace : WordTrace (prefixWord ++ tailWord_295356) baseStart_295356 baseEnd_295356 := by
    simpa [prefixWord, tailWord_295356, baseEnd_295356] using wordTrace_append hprefix tailTrace_295356
  have hstable : (prefixWord ++ tailWord_295356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295356).length < 2 ^ (prefixWord ++ tailWord_295356).sum := by decide
  have hdescent : baseEnd_295356 < baseStart_295356 := by decide
  rcases family_descends (prefixWord ++ tailWord_295356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295470 : List Nat := [4, 1, 3, 1, 3, 7]
def baseStart_295470 : Nat := 118140960795 + 295470 * 2 ^ 59
def prefixEnd_295470 : Nat := 4983230072969 + 3 ^ 40 * 295470 * 2
def baseEnd_295470 : Nat := 9989671044218219322875

theorem tailTrace_295470 : CollatzResearch.WordTrace tailWord_295470 prefixEnd_295470 9989671044218219322875 := by
  unfold tailWord_295470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347084529946265887950483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7184450826380084735735909 1347084529946265887950483)
  ·
    refine ⟨2020626794919398831925725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1347084529946265887950483 2020626794919398831925725)
    ·
      refine ⟨757735048094774561972147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2020626794919398831925725 757735048094774561972147)
      ·
        refine ⟨1136602572142161842958221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757735048094774561972147 1136602572142161842958221)
        ·
          refine ⟨426225964553310691109333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1136602572142161842958221 426225964553310691109333)
          ·
            refine ⟨9989671044218219322875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 426225964553310691109333 9989671044218219322875)
            ·
              rfl

theorem cell19_295470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_295470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295470 prefixEnd_295470 := by exact prefixLift 295470
  have htrace : WordTrace (prefixWord ++ tailWord_295470) baseStart_295470 baseEnd_295470 := by
    simpa [prefixWord, tailWord_295470, baseEnd_295470] using wordTrace_append hprefix tailTrace_295470
  have hstable : (prefixWord ++ tailWord_295470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295470).length < 2 ^ (prefixWord ++ tailWord_295470).sum := by decide
  have hdescent : baseEnd_295470 < baseStart_295470 := by decide
  rcases family_descends (prefixWord ++ tailWord_295470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295489 : List Nat := [1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_295489 : Nat := 118140960795 + 295489 * 2 ^ 59
def prefixEnd_295489 : Nat := 4983230072969 + 3 ^ 40 * 295489 * 2
def baseEnd_295489 : Nat := 89912820809777559483601

theorem tailTrace_295489 : CollatzResearch.WordTrace tailWord_295489 prefixEnd_295489 89912820809777559483601 := by
  unfold tailWord_295489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777369226501293348545521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7184912817667528899030347 10777369226501293348545521)
  ·
    refine ⟨8083026919875970011409141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10777369226501293348545521 8083026919875970011409141)
    ·
      refine ⟨757783773738372188569607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8083026919875970011409141 757783773738372188569607)
      ·
        refine ⟨1136675660607558282854411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757783773738372188569607 1136675660607558282854411)
        ·
          refine ⟨1705013490911337424281617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136675660607558282854411 1705013490911337424281617)
          ·
            refine ⟨1278760118183503068211213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1705013490911337424281617 1278760118183503068211213)
            ·
              refine ⟨479535044318813650579205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278760118183503068211213 479535044318813650579205)
              ·
                refine ⟨89912820809777559483601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 479535044318813650579205 89912820809777559483601)
                ·
                  rfl

theorem cell19_295489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_295489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295489 prefixEnd_295489 := by exact prefixLift 295489
  have htrace : WordTrace (prefixWord ++ tailWord_295489) baseStart_295489 baseEnd_295489 := by
    simpa [prefixWord, tailWord_295489, baseEnd_295489] using wordTrace_append hprefix tailTrace_295489
  have hstable : (prefixWord ++ tailWord_295489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295489).length < 2 ^ (prefixWord ++ tailWord_295489).sum := by decide
  have hdescent : baseEnd_295489 < baseStart_295489 := by decide
  rcases family_descends (prefixWord ++ tailWord_295489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295584 : List Nat := [2, 1, 1, 4, 4, 2, 5]
def baseStart_295584 : Nat := 118140960795 + 295584 * 2 ^ 59
def prefixEnd_295584 : Nat := 4983230072969 + 3 ^ 40 * 295584 * 2
def baseEnd_295584 : Nat := 29980575956281829124077

theorem tailTrace_295584 : CollatzResearch.WordTrace tailWord_295584 prefixEnd_295584 29980575956281829124077 := by
  unfold tailWord_295584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5390417080578562286626903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7187222774104749715502537 5390417080578562286626903)
  ·
    refine ⟨8085625620867843429940355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5390417080578562286626903 8085625620867843429940355)
    ·
      refine ⟨12128438431301765144910533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8085625620867843429940355 12128438431301765144910533)
      ·
        refine ⟨2274082205869080964670725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12128438431301765144910533 2274082205869080964670725)
        ·
          refine ⟨426390413600452680875761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2274082205869080964670725 426390413600452680875761)
          ·
            refine ⟨319792810200339510656821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426390413600452680875761 319792810200339510656821)
            ·
              refine ⟨29980575956281829124077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 319792810200339510656821 29980575956281829124077)
              ·
                rfl

theorem cell19_295584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_295584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295584 prefixEnd_295584 := by exact prefixLift 295584
  have htrace : WordTrace (prefixWord ++ tailWord_295584) baseStart_295584 baseEnd_295584 := by
    simpa [prefixWord, tailWord_295584, baseEnd_295584] using wordTrace_append hprefix tailTrace_295584
  have hstable : (prefixWord ++ tailWord_295584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295584).length < 2 ^ (prefixWord ++ tailWord_295584).sum := by decide
  have hdescent : baseEnd_295584 < baseStart_295584 := by decide
  rcases family_descends (prefixWord ++ tailWord_295584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295601 : List Nat := [1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_295601 : Nat := 118140960795 + 295601 * 2 ^ 59
def prefixEnd_295601 : Nat := 4983230072969 + 3 ^ 40 * 295601 * 2
def baseEnd_295601 : Nat := 89946900710994484994407

theorem tailTrace_295601 : CollatzResearch.WordTrace tailWord_295601 prefixEnd_295601 89946900710994484994407 := by
  unfold tailWord_295601
  simp only [CollatzResearch.WordTrace]
  refine ⟨10781454202095536476622657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7187636134730357651081771 10781454202095536476622657)
  ·
    refine ⟨8086090651571652357466993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10781454202095536476622657 8086090651571652357466993)
    ·
      refine ⟨6064567988678739268100245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8086090651571652357466993 6064567988678739268100245)
      ·
        refine ⟨284276624469315903192199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6064567988678739268100245 284276624469315903192199)
        ·
          refine ⟨426414936703973854788299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284276624469315903192199 426414936703973854788299)
          ·
            refine ⟨639622405055960782182449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426414936703973854788299 639622405055960782182449)
            ·
              refine ⟨479716803791970586636837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639622405055960782182449 479716803791970586636837)
              ·
                refine ⟨89946900710994484994407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 479716803791970586636837 89946900710994484994407)
                ·
                  rfl

theorem cell19_295601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_295601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295601 prefixEnd_295601 := by exact prefixLift 295601
  have htrace : WordTrace (prefixWord ++ tailWord_295601) baseStart_295601 baseEnd_295601 := by
    simpa [prefixWord, tailWord_295601, baseEnd_295601] using wordTrace_append hprefix tailTrace_295601
  have hstable : (prefixWord ++ tailWord_295601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295601).length < 2 ^ (prefixWord ++ tailWord_295601).sum := by decide
  have hdescent : baseEnd_295601 < baseStart_295601 := by decide
  rcases family_descends (prefixWord ++ tailWord_295601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295624 : List Nat := [2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_295624 : Nat := 118140960795 + 295624 * 2 ^ 59
def prefixEnd_295624 : Nat := 4983230072969 + 3 ^ 40 * 295624 * 2
def baseEnd_295624 : Nat := 89953899262137246483233

theorem tailTrace_295624 : CollatzResearch.WordTrace tailWord_295624 prefixEnd_295624 89953899262137246483233 := by
  unfold tailWord_295624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391146540506105702354963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7188195387341474269806617 5391146540506105702354963)
  ·
    refine ⟨8086719810759158553532445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5391146540506105702354963 8086719810759158553532445)
    ·
      refine ⟨3032519929034684457574667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8086719810759158553532445 3032519929034684457574667)
      ·
        refine ⟨4548779893552026686362001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3032519929034684457574667 4548779893552026686362001)
        ·
          refine ⟨3411584920164020014771501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4548779893552026686362001 3411584920164020014771501)
          ·
            refine ⟨1279344345061507505539313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3411584920164020014771501 1279344345061507505539313)
            ·
              refine ⟨959508258796130629154485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279344345061507505539313 959508258796130629154485)
              ·
                refine ⟨89953899262137246483233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959508258796130629154485 89953899262137246483233)
                ·
                  rfl

theorem cell19_295624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_295624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295624 prefixEnd_295624 := by exact prefixLift 295624
  have htrace : WordTrace (prefixWord ++ tailWord_295624) baseStart_295624 baseEnd_295624 := by
    simpa [prefixWord, tailWord_295624, baseEnd_295624] using wordTrace_append hprefix tailTrace_295624
  have hstable : (prefixWord ++ tailWord_295624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295624).length < 2 ^ (prefixWord ++ tailWord_295624).sum := by decide
  have hdescent : baseEnd_295624 < baseStart_295624 := by decide
  rcases family_descends (prefixWord ++ tailWord_295624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295732 : List Nat := [2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_295732 : Nat := 118140960795 + 295732 * 2 ^ 59
def prefixEnd_295732 : Nat := 4983230072969 + 3 ^ 40 * 295732 * 2
def baseEnd_295732 : Nat := 89986762024024996082939

theorem tailTrace_295732 : CollatzResearch.WordTrace tailWord_295732 prefixEnd_295732 89986762024024996082939 := by
  unfold tailWord_295732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393116082310472924820725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7190821443080630566427633 5393116082310472924820725)
  ·
    refine ⟨505604632716606836701943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5393116082310472924820725 505604632716606836701943)
    ·
      refine ⟨758406949074910255052915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505604632716606836701943 758406949074910255052915)
      ·
        refine ⟨1137610423612365382579373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758406949074910255052915 1137610423612365382579373)
        ·
          refine ⟨426603908854637018467265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1137610423612365382579373 426603908854637018467265)
          ·
            refine ⟨319952931640977763850449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426603908854637018467265 319952931640977763850449)
            ·
              refine ⟨239964698730733322887837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319952931640977763850449 239964698730733322887837)
              ·
                refine ⟨89986762024024996082939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239964698730733322887837 89986762024024996082939)
                ·
                  rfl

theorem cell19_295732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_295732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295732 prefixEnd_295732 := by exact prefixLift 295732
  have htrace : WordTrace (prefixWord ++ tailWord_295732) baseStart_295732 baseEnd_295732 := by
    simpa [prefixWord, tailWord_295732, baseEnd_295732] using wordTrace_append hprefix tailTrace_295732
  have hstable : (prefixWord ++ tailWord_295732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295732).length < 2 ^ (prefixWord ++ tailWord_295732).sum := by decide
  have hdescent : baseEnd_295732 < baseStart_295732 := by decide
  rcases family_descends (prefixWord ++ tailWord_295732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295734 : List Nat := [5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_295734 : Nat := 118140960795 + 295734 * 2 ^ 59
def prefixEnd_295734 : Nat := 4983230072969 + 3 ^ 40 * 295734 * 2
def baseEnd_295734 : Nat := 89987370593689584038489

theorem tailTrace_295734 : CollatzResearch.WordTrace tailWord_295734 prefixEnd_295734 89987370593689584038489 := by
  unfold tailWord_295734
  simp only [CollatzResearch.WordTrace]
  refine ⟨674144069413356261950891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7190870073742466794142837 674144069413356261950891)
  ·
    refine ⟨1011216104120034392926337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674144069413356261950891 1011216104120034392926337)
    ·
      refine ⟨758412078090025794694753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011216104120034392926337 758412078090025794694753)
      ·
        refine ⟨568809058567519346021065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758412078090025794694753 568809058567519346021065)
        ·
          refine ⟨426606793925639509515799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568809058567519346021065 426606793925639509515799)
          ·
            refine ⟨639910190888459264273699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426606793925639509515799 639910190888459264273699)
            ·
              refine ⟨959865286332688896410549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639910190888459264273699 959865286332688896410549)
              ·
                refine ⟨89987370593689584038489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959865286332688896410549 89987370593689584038489)
                ·
                  rfl

theorem cell19_295734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_295734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295734 prefixEnd_295734 := by exact prefixLift 295734
  have htrace : WordTrace (prefixWord ++ tailWord_295734) baseStart_295734 baseEnd_295734 := by
    simpa [prefixWord, tailWord_295734, baseEnd_295734] using wordTrace_append hprefix tailTrace_295734
  have hstable : (prefixWord ++ tailWord_295734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295734).length < 2 ^ (prefixWord ++ tailWord_295734).sum := by decide
  have hdescent : baseEnd_295734 < baseStart_295734 := by decide
  rcases family_descends (prefixWord ++ tailWord_295734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295776 : List Nat := [2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_295776 : Nat := 118140960795 + 295776 * 2 ^ 59
def prefixEnd_295776 : Nat := 4983230072969 + 3 ^ 40 * 295776 * 2
def baseEnd_295776 : Nat := 90000150556645931105041

theorem tailTrace_295776 : CollatzResearch.WordTrace tailWord_295776 prefixEnd_295776 90000150556645931105041 := by
  unfold tailWord_295776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393918488230770682121591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7191891317641027576162121 5393918488230770682121591)
  ·
    refine ⟨8090877732346156023182387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5393918488230770682121591 8090877732346156023182387)
    ·
      refine ⟨12136316598519234034773581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8090877732346156023182387 12136316598519234034773581)
      ·
        refine ⟨4551118724444712763040093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12136316598519234034773581 4551118724444712763040093)
        ·
          refine ⟨1706669521666767286140035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4551118724444712763040093 1706669521666767286140035)
          ·
            refine ⟨2560004282500150929210053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706669521666767286140035 2560004282500150929210053)
            ·
              refine ⟨480000802968778299226885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2560004282500150929210053 480000802968778299226885)
              ·
                refine ⟨90000150556645931105041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480000802968778299226885 90000150556645931105041)
                ·
                  rfl

theorem cell19_295776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_295776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295776 prefixEnd_295776 := by exact prefixLift 295776
  have htrace : WordTrace (prefixWord ++ tailWord_295776) baseStart_295776 baseEnd_295776 := by
    simpa [prefixWord, tailWord_295776, baseEnd_295776] using wordTrace_append hprefix tailTrace_295776
  have hstable : (prefixWord ++ tailWord_295776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295776).length < 2 ^ (prefixWord ++ tailWord_295776).sum := by decide
  have hdescent : baseEnd_295776 < baseStart_295776 := by decide
  rcases family_descends (prefixWord ++ tailWord_295776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295810 : List Nat := [3, 4, 2, 2, 1, 7]
def baseStart_295810 : Nat := 118140960795 + 295810 * 2 ^ 59
def prefixEnd_295810 : Nat := 4983230072969 + 3 ^ 40 * 295810 * 2
def baseEnd_295810 : Nat := 10001166248993769594377

theorem tailTrace_295810 : CollatzResearch.WordTrace tailWord_295810 prefixEnd_295810 10001166248993769594377 := by
  unfold tailWord_295810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697269264584591292745221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7192718038892243447320589 2697269264584591292745221)
  ·
    refine ⟨505737987109610867389729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2697269264584591292745221 505737987109610867389729)
    ·
      refine ⟨379303490332208150542297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 505737987109610867389729 379303490332208150542297)
      ·
        refine ⟨284477617749156112906723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379303490332208150542297 284477617749156112906723)
        ·
          refine ⟨426716426623734169360085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284477617749156112906723 426716426623734169360085)
          ·
            refine ⟨10001166248993769594377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 426716426623734169360085 10001166248993769594377)
            ·
              rfl

theorem cell19_295810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_295810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295810 prefixEnd_295810 := by exact prefixLift 295810
  have htrace : WordTrace (prefixWord ++ tailWord_295810) baseStart_295810 baseEnd_295810 := by
    simpa [prefixWord, tailWord_295810, baseEnd_295810] using wordTrace_append hprefix tailTrace_295810
  have hstable : (prefixWord ++ tailWord_295810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295810).length < 2 ^ (prefixWord ++ tailWord_295810).sum := by decide
  have hdescent : baseEnd_295810 < baseStart_295810 := by decide
  rcases family_descends (prefixWord ++ tailWord_295810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295926 : List Nat := [5, 1, 1, 1, 3, 3, 5]
def baseStart_295926 : Nat := 118140960795 + 295926 * 2 ^ 59
def prefixEnd_295926 : Nat := 4983230072969 + 3 ^ 40 * 295926 * 2
def baseEnd_295926 : Nat := 30015264427163342590433

theorem tailTrace_295926 : CollatzResearch.WordTrace tailWord_295926 prefixEnd_295926 30015264427163342590433 := by
  unfold tailWord_295926
  simp only [CollatzResearch.WordTrace]
  refine ⟨674581745369882311387727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7195538617278744654802421 674581745369882311387727)
  ·
    refine ⟨1011872618054823467081591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674581745369882311387727 1011872618054823467081591)
    ·
      refine ⟨1517808927082235200622387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011872618054823467081591 1517808927082235200622387)
      ·
        refine ⟨2276713390623352800933581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517808927082235200622387 2276713390623352800933581)
        ·
          refine ⟨853767521483757300350093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2276713390623352800933581 853767521483757300350093)
          ·
            refine ⟨320162820556408987631285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853767521483757300350093 320162820556408987631285)
            ·
              refine ⟨30015264427163342590433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 320162820556408987631285 30015264427163342590433)
              ·
                rfl

theorem cell19_295926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_295926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295926 prefixEnd_295926 := by exact prefixLift 295926
  have htrace : WordTrace (prefixWord ++ tailWord_295926) baseStart_295926 baseEnd_295926 := by
    simpa [prefixWord, tailWord_295926, baseEnd_295926] using wordTrace_append hprefix tailTrace_295926
  have hstable : (prefixWord ++ tailWord_295926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295926).length < 2 ^ (prefixWord ++ tailWord_295926).sum := by decide
  have hdescent : baseEnd_295926 < baseStart_295926 := by decide
  rcases family_descends (prefixWord ++ tailWord_295926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295947 : List Nat := [1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_295947 : Nat := 118140960795 + 295947 * 2 ^ 59
def prefixEnd_295947 : Nat := 4983230072969 + 3 ^ 40 * 295947 * 2
def baseEnd_295947 : Nat := 90052183262968201304575

theorem tailTrace_295947 : CollatzResearch.WordTrace tailWord_295947 prefixEnd_295947 90052183262968201304575 := by
  unfold tailWord_295947
  simp only [CollatzResearch.WordTrace]
  refine ⟨10794073858842037568718095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7196049239228025045812063 10794073858842037568718095)
  ·
    refine ⟨16191110788263056353077143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10794073858842037568718095 16191110788263056353077143)
    ·
      refine ⟨24286666182394584529615715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16191110788263056353077143 24286666182394584529615715)
      ·
        refine ⟨36429999273591876794423573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24286666182394584529615715 36429999273591876794423573)
        ·
          refine ⟨1707656215949619224738605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36429999273591876794423573 1707656215949619224738605)
          ·
            refine ⟨640371080981107209276977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1707656215949619224738605 640371080981107209276977)
            ·
              refine ⟨480278310735830406957733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640371080981107209276977 480278310735830406957733)
              ·
                refine ⟨90052183262968201304575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480278310735830406957733 90052183262968201304575)
                ·
                  rfl

theorem cell19_295947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_295947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_295947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_295947 prefixEnd_295947 := by exact prefixLift 295947
  have htrace : WordTrace (prefixWord ++ tailWord_295947) baseStart_295947 baseEnd_295947 := by
    simpa [prefixWord, tailWord_295947, baseEnd_295947] using wordTrace_append hprefix tailTrace_295947
  have hstable : (prefixWord ++ tailWord_295947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295947).length < 2 ^ (prefixWord ++ tailWord_295947).sum := by decide
  have hdescent : baseEnd_295947 < baseStart_295947 := by decide
  rcases family_descends (prefixWord ++ tailWord_295947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296040 : List Nat := [2, 1, 4, 4, 1, 1, 6]
def baseStart_296040 : Nat := 118140960795 + 296040 * 2 ^ 59
def prefixEnd_296040 : Nat := 4983230072969 + 3 ^ 40 * 296040 * 2
def baseEnd_296040 : Nat := 30026827250790513745885

theorem tailTrace_296040 : CollatzResearch.WordTrace tailWord_296040 prefixEnd_296040 30026827250790513745885 := by
  unfold tailWord_296040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398732923752557225926787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7198310565003409634569049 5398732923752557225926787)
  ·
    refine ⟨8098099385628835838890181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5398732923752557225926787 8098099385628835838890181)
    ·
      refine ⟨1518393634805406719791909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8098099385628835838890181 1518393634805406719791909)
      ·
        refine ⟨284698806526013759960983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1518393634805406719791909 284698806526013759960983)
        ·
          refine ⟨427048209789020639941475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284698806526013759960983 427048209789020639941475)
          ·
            refine ⟨640572314683530959912213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427048209789020639941475 640572314683530959912213)
            ·
              refine ⟨30026827250790513745885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 640572314683530959912213 30026827250790513745885)
              ·
                rfl

theorem cell19_296040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_296040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296040 prefixEnd_296040 := by exact prefixLift 296040
  have htrace : WordTrace (prefixWord ++ tailWord_296040) baseStart_296040 baseEnd_296040 := by
    simpa [prefixWord, tailWord_296040, baseEnd_296040] using wordTrace_append hprefix tailTrace_296040
  have hstable : (prefixWord ++ tailWord_296040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296040).length < 2 ^ (prefixWord ++ tailWord_296040).sum := by decide
  have hdescent : baseEnd_296040 < baseStart_296040 := by decide
  rcases family_descends (prefixWord ++ tailWord_296040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296042 : List Nat := [3, 1, 3, 2, 2, 2, 6]
def baseStart_296042 : Nat := 118140960795 + 296042 * 2 ^ 59
def prefixEnd_296042 : Nat := 4983230072969 + 3 ^ 40 * 296042 * 2
def baseEnd_296042 : Nat := 30027030107345376397735

theorem tailTrace_296042 : CollatzResearch.WordTrace tailWord_296042 prefixEnd_296042 30027030107345376397735 := by
  unfold tailWord_296042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699384698374467198356595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7198359195665245862284253 2699384698374467198356595)
  ·
    refine ⟨4049077047561700797534893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699384698374467198356595 4049077047561700797534893)
    ·
      refine ⟨1518403892835637799075585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4049077047561700797534893 1518403892835637799075585)
      ·
        refine ⟨1138802919626728349306689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1518403892835637799075585 1138802919626728349306689)
        ·
          refine ⟨854102189720046261980017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138802919626728349306689 854102189720046261980017)
          ·
            refine ⟨640576642290034696485013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854102189720046261980017 640576642290034696485013)
            ·
              refine ⟨30027030107345376397735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 640576642290034696485013 30027030107345376397735)
              ·
                rfl

theorem cell19_296042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_296042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296042 prefixEnd_296042 := by exact prefixLift 296042
  have htrace : WordTrace (prefixWord ++ tailWord_296042) baseStart_296042 baseEnd_296042 := by
    simpa [prefixWord, tailWord_296042, baseEnd_296042] using wordTrace_append hprefix tailTrace_296042
  have hstable : (prefixWord ++ tailWord_296042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296042).length < 2 ^ (prefixWord ++ tailWord_296042).sum := by decide
  have hdescent : baseEnd_296042 < baseStart_296042 := by decide
  rcases family_descends (prefixWord ++ tailWord_296042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296044 : List Nat := [2, 2, 1, 1, 3, 2, 8]
def baseStart_296044 : Nat := 118140960795 + 296044 * 2 ^ 59
def prefixEnd_296044 : Nat := 4983230072969 + 3 ^ 40 * 296044 * 2
def baseEnd_296044 : Nat := 30027232963900239049585

theorem tailTrace_296044 : CollatzResearch.WordTrace tailWord_296044 prefixEnd_296044 30027232963900239049585 := by
  unfold tailWord_296044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398805869745311567499593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7198407826327082089999457 5398805869745311567499593)
  ·
    refine ⟨4049104402308983675624695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5398805869745311567499593 4049104402308983675624695)
    ·
      refine ⟨6073656603463475513437043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049104402308983675624695 6073656603463475513437043)
      ·
        refine ⟨9110484905195213270155565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073656603463475513437043 9110484905195213270155565)
        ·
          refine ⟨3416431839448204976308337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9110484905195213270155565 3416431839448204976308337)
          ·
            refine ⟨2562323879586153732231253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416431839448204976308337 2562323879586153732231253)
            ·
              refine ⟨30027232963900239049585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2562323879586153732231253 30027232963900239049585)
              ·
                rfl

theorem cell19_296044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_296044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296044 prefixEnd_296044 := by exact prefixLift 296044
  have htrace : WordTrace (prefixWord ++ tailWord_296044) baseStart_296044 baseEnd_296044 := by
    simpa [prefixWord, tailWord_296044, baseEnd_296044] using wordTrace_append hprefix tailTrace_296044
  have hstable : (prefixWord ++ tailWord_296044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296044).length < 2 ^ (prefixWord ++ tailWord_296044).sum := by decide
  have hdescent : baseEnd_296044 < baseStart_296044 := by decide
  rcases family_descends (prefixWord ++ tailWord_296044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296078 : List Nat := [4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_296078 : Nat := 118140960795 + 296078 * 2 ^ 59
def prefixEnd_296078 : Nat := 4983230072969 + 3 ^ 40 * 296078 * 2
def baseEnd_296078 : Nat := 90092044575998712393107

theorem tailTrace_296078 : CollatzResearch.WordTrace tailWord_296078 prefixEnd_296078 90092044575998712393107 := by
  unfold tailWord_296078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349856477670930867717111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7199234547578297961157925 1349856477670930867717111)
  ·
    refine ⟨2024784716506396301575667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1349856477670930867717111 2024784716506396301575667)
    ·
      refine ⟨3037177074759594452363501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024784716506396301575667 3037177074759594452363501)
      ·
        refine ⟨1138941403034847919636313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3037177074759594452363501 1138941403034847919636313)
        ·
          refine ⟨854206052276135939727235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138941403034847919636313 854206052276135939727235)
          ·
            refine ⟨1281309078414203909590853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854206052276135939727235 1281309078414203909590853)
            ·
              refine ⟨240245452202663233048285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1281309078414203909590853 240245452202663233048285)
              ·
                refine ⟨90092044575998712393107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240245452202663233048285 90092044575998712393107)
                ·
                  rfl

theorem cell19_296078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_296078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296078 prefixEnd_296078 := by exact prefixLift 296078
  have htrace : WordTrace (prefixWord ++ tailWord_296078) baseStart_296078 baseEnd_296078 := by
    simpa [prefixWord, tailWord_296078, baseEnd_296078] using wordTrace_append hprefix tailTrace_296078
  have hstable : (prefixWord ++ tailWord_296078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296078).length < 2 ^ (prefixWord ++ tailWord_296078).sum := by decide
  have hdescent : baseEnd_296078 < baseStart_296078 := by decide
  rcases family_descends (prefixWord ++ tailWord_296078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296101 : List Nat := [1, 3, 1, 2, 1, 4, 7]
def baseStart_296101 : Nat := 118140960795 + 296101 * 2 ^ 59
def prefixEnd_296101 : Nat := 4983230072969 + 3 ^ 40 * 296101 * 2
def baseEnd_296101 : Nat := 30033014375713824627311

theorem tailTrace_296101 : CollatzResearch.WordTrace tailWord_296101 prefixEnd_296101 30033014375713824627311 := by
  unfold tailWord_296101
  simp only [CollatzResearch.WordTrace]
  refine ⟨10799690700284121869824157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7199793800189414579882771 10799690700284121869824157)
  ·
    refine ⟨4049884012606545701184059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10799690700284121869824157 4049884012606545701184059)
    ·
      refine ⟨6074826018909818551776089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049884012606545701184059 6074826018909818551776089)
      ·
        refine ⟨4556119514182363913832067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6074826018909818551776089 4556119514182363913832067)
        ·
          refine ⟨6834179271273545870748101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556119514182363913832067 6834179271273545870748101)
          ·
            refine ⟨1281408613363789850765269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6834179271273545870748101 1281408613363789850765269)
            ·
              refine ⟨30033014375713824627311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1281408613363789850765269 30033014375713824627311)
              ·
                rfl

theorem cell19_296101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_296101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296101 prefixEnd_296101 := by exact prefixLift 296101
  have htrace : WordTrace (prefixWord ++ tailWord_296101) baseStart_296101 baseEnd_296101 := by
    simpa [prefixWord, tailWord_296101, baseEnd_296101] using wordTrace_append hprefix tailTrace_296101
  have hstable : (prefixWord ++ tailWord_296101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296101).length < 2 ^ (prefixWord ++ tailWord_296101).sum := by decide
  have hdescent : baseEnd_296101 < baseStart_296101 := by decide
  rcases family_descends (prefixWord ++ tailWord_296101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296173 : List Nat := [1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_296173 : Nat := 118140960795 + 296173 * 2 ^ 59
def prefixEnd_296173 : Nat := 4983230072969 + 3 ^ 40 * 296173 * 2
def baseEnd_296173 : Nat := 90120951635066640281737

theorem tailTrace_296173 : CollatzResearch.WordTrace tailWord_296173 prefixEnd_296173 90120951635066640281737 := by
  unfold tailWord_296173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10802316756023278166445173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7201544504015518777630115 10802316756023278166445173)
  ·
    refine ⟨1012717195877182328104235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10802316756023278166445173 1012717195877182328104235)
    ·
      refine ⟨1519075793815773492156353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1012717195877182328104235 1519075793815773492156353)
      ·
        refine ⟨1139306845361830119117265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1519075793815773492156353 1139306845361830119117265)
        ·
          refine ⟨854480134021372589337949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1139306845361830119117265 854480134021372589337949)
          ·
            refine ⟨320430050258014721001731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 854480134021372589337949 320430050258014721001731)
            ·
              refine ⟨480645075387022081502597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320430050258014721001731 480645075387022081502597)
              ·
                refine ⟨90120951635066640281737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480645075387022081502597 90120951635066640281737)
                ·
                  rfl

theorem cell19_296173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_296173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296173 prefixEnd_296173 := by exact prefixLift 296173
  have htrace : WordTrace (prefixWord ++ tailWord_296173) baseStart_296173 baseEnd_296173 := by
    simpa [prefixWord, tailWord_296173, baseEnd_296173] using wordTrace_append hprefix tailTrace_296173
  have hstable : (prefixWord ++ tailWord_296173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296173).length < 2 ^ (prefixWord ++ tailWord_296173).sum := by decide
  have hdescent : baseEnd_296173 < baseStart_296173 := by decide
  rcases family_descends (prefixWord ++ tailWord_296173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296215 : List Nat := [1, 1, 3, 4, 1, 1, 8]
def baseStart_296215 : Nat := 118140960795 + 296215 * 2 ^ 59
def prefixEnd_296215 : Nat := 4983230072969 + 3 ^ 40 * 296215 * 2
def baseEnd_296215 : Nat := 30044577199340995782763

theorem tailTrace_296215 : CollatzResearch.WordTrace tailWord_296215 prefixEnd_296215 30044577199340995782763 := by
  unfold tailWord_296215
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803848621871119339474099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7202565747914079559649399 10803848621871119339474099)
  ·
    refine ⟨16205772932806679009211149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10803848621871119339474099 16205772932806679009211149)
    ·
      refine ⟨6077164849802504628454181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16205772932806679009211149 6077164849802504628454181)
      ·
        refine ⟨1139468409337969617835159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6077164849802504628454181 1139468409337969617835159)
        ·
          refine ⟨1709202614006954426752739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139468409337969617835159 1709202614006954426752739)
          ·
            refine ⟨2563803921010431640129109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709202614006954426752739 2563803921010431640129109)
            ·
              refine ⟨30044577199340995782763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2563803921010431640129109 30044577199340995782763)
              ·
                rfl

theorem cell19_296215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_296215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296215 prefixEnd_296215 := by exact prefixLift 296215
  have htrace : WordTrace (prefixWord ++ tailWord_296215) baseStart_296215 baseEnd_296215 := by
    simpa [prefixWord, tailWord_296215, baseEnd_296215] using wordTrace_append hprefix tailTrace_296215
  have hstable : (prefixWord ++ tailWord_296215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296215).length < 2 ^ (prefixWord ++ tailWord_296215).sum := by decide
  have hdescent : baseEnd_296215 < baseStart_296215 := by decide
  rcases family_descends (prefixWord ++ tailWord_296215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296291 : List Nat := [1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_296291 : Nat := 118140960795 + 296291 * 2 ^ 59
def prefixEnd_296291 : Nat := 4983230072969 + 3 ^ 40 * 296291 * 2
def baseEnd_296291 : Nat := 90156857245277329659193

theorem tailTrace_296291 : CollatzResearch.WordTrace tailWord_296291 prefixEnd_296291 90156857245277329659193 := by
  unfold tailWord_296291
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806620569595784319240727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7204413713063856212827151 10806620569595784319240727)
  ·
    refine ⟨16209930854393676478861091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10806620569595784319240727 16209930854393676478861091)
    ·
      refine ⟨24314896281590514718291637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16209930854393676478861091 24314896281590514718291637)
      ·
        refine ⟨2279521526399110754839841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24314896281590514718291637 2279521526399110754839841)
        ·
          refine ⟨1709641144799333066129881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2279521526399110754839841 1709641144799333066129881)
          ·
            refine ⟨1282230858599499799597411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709641144799333066129881 1282230858599499799597411)
            ·
              refine ⟨1923346287899249699396117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282230858599499799597411 1923346287899249699396117)
              ·
                refine ⟨90156857245277329659193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1923346287899249699396117 90156857245277329659193)
                ·
                  rfl

theorem cell19_296291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_296291 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296291 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296291 prefixEnd_296291 := by exact prefixLift 296291
  have htrace : WordTrace (prefixWord ++ tailWord_296291) baseStart_296291 baseEnd_296291 := by
    simpa [prefixWord, tailWord_296291, baseEnd_296291] using wordTrace_append hprefix tailTrace_296291
  have hstable : (prefixWord ++ tailWord_296291).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296291).length < 2 ^ (prefixWord ++ tailWord_296291).sum := by decide
  have hdescent : baseEnd_296291 < baseStart_296291 := by decide
  rcases family_descends (prefixWord ++ tailWord_296291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296329 : List Nat := [1, 2, 1, 1, 7, 7]
def baseStart_296329 : Nat := 118140960795 + 296329 * 2 ^ 59
def prefixEnd_296329 : Nat := 4983230072969 + 3 ^ 40 * 296329 * 2
def baseEnd_296329 : Nat := 10018713340989388979405

theorem tailTrace_296329 : CollatzResearch.WordTrace tailWord_296329 prefixEnd_296329 10018713340989388979405 := by
  unfold tailWord_296329
  simp only [CollatzResearch.WordTrace]
  refine ⟨10808006543458116809124041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7205337695638744539416027 10808006543458116809124041)
  ·
    refine ⟨8106004907593587606843031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10808006543458116809124041 8106004907593587606843031)
    ·
      refine ⟨12159007361390381410264547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8106004907593587606843031 12159007361390381410264547)
      ·
        refine ⟨18238511042085572115396821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12159007361390381410264547 18238511042085572115396821)
        ·
          refine ⟨427465102548880596454613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18238511042085572115396821 427465102548880596454613)
          ·
            refine ⟨10018713340989388979405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 427465102548880596454613 10018713340989388979405)
            ·
              rfl

theorem cell19_296329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_296329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296329 prefixEnd_296329 := by exact prefixLift 296329
  have htrace : WordTrace (prefixWord ++ tailWord_296329) baseStart_296329 baseEnd_296329 := by
    simpa [prefixWord, tailWord_296329, baseEnd_296329] using wordTrace_append hprefix tailTrace_296329
  have hstable : (prefixWord ++ tailWord_296329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296329).length < 2 ^ (prefixWord ++ tailWord_296329).sum := by decide
  have hdescent : baseEnd_296329 < baseStart_296329 := by decide
  rcases family_descends (prefixWord ++ tailWord_296329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296344 : List Nat := [2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_296344 : Nat := 118140960795 + 296344 * 2 ^ 59
def prefixEnd_296344 : Nat := 4983230072969 + 3 ^ 40 * 296344 * 2
def baseEnd_296344 : Nat := 90172984341388910481271

theorem tailTrace_296344 : CollatzResearch.WordTrace tailWord_296344 prefixEnd_296344 90172984341388910481271 := by
  unfold tailWord_296344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5404276819201887185460043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7205702425602516247280057 5404276819201887185460043)
  ·
    refine ⟨8106415228802830778190065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5404276819201887185460043 8106415228802830778190065)
    ·
      refine ⟨6079811421602123083642549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8106415228802830778190065 6079811421602123083642549)
      ·
        refine ⟨569982320775199039091489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6079811421602123083642549 569982320775199039091489)
        ·
          refine ⟨427486740581399279318617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569982320775199039091489 427486740581399279318617)
          ·
            refine ⟨320615055436049459488963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427486740581399279318617 320615055436049459488963)
            ·
              refine ⟨480922583154074189233445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320615055436049459488963 480922583154074189233445)
              ·
                refine ⟨90172984341388910481271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480922583154074189233445 90172984341388910481271)
                ·
                  rfl

theorem cell19_296344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_296344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296344 prefixEnd_296344 := by exact prefixLift 296344
  have htrace : WordTrace (prefixWord ++ tailWord_296344) baseStart_296344 baseEnd_296344 := by
    simpa [prefixWord, tailWord_296344, baseEnd_296344] using wordTrace_append hprefix tailTrace_296344
  have hstable : (prefixWord ++ tailWord_296344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296344).length < 2 ^ (prefixWord ++ tailWord_296344).sum := by decide
  have hdescent : baseEnd_296344 < baseStart_296344 := by decide
  rcases family_descends (prefixWord ++ tailWord_296344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296405 : List Nat := [1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_296405 : Nat := 118140960795 + 296405 * 2 ^ 59
def prefixEnd_296405 : Nat := 4983230072969 + 3 ^ 40 * 296405 * 2
def baseEnd_296405 : Nat := 90191545716158843125549

theorem tailTrace_296405 : CollatzResearch.WordTrace tailWord_296405 prefixEnd_296405 90191545716158843125549 := by
  unfold tailWord_296405
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810778491182781788890669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207185660788521192593779 10810778491182781788890669)
  ·
    refine ⟨4054041934193543170834001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10810778491182781788890669 4054041934193543170834001)
    ·
      refine ⟨3040531450645157378125501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4054041934193543170834001 3040531450645157378125501)
      ·
        refine ⟨1140199293991934016797063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3040531450645157378125501 1140199293991934016797063)
        ·
          refine ⟨1710298940987901025195595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140199293991934016797063 1710298940987901025195595)
          ·
            refine ⟨2565448411481851537793393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710298940987901025195595 2565448411481851537793393)
            ·
              refine ⟨1924086308611388653345045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2565448411481851537793393 1924086308611388653345045)
              ·
                refine ⟨90191545716158843125549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1924086308611388653345045 90191545716158843125549)
                ·
                  rfl

theorem cell19_296405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_296405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296405 prefixEnd_296405 := by exact prefixLift 296405
  have htrace : WordTrace (prefixWord ++ tailWord_296405) baseStart_296405 baseEnd_296405 := by
    simpa [prefixWord, tailWord_296405, baseEnd_296405] using wordTrace_append hprefix tailTrace_296405
  have hstable : (prefixWord ++ tailWord_296405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296405).length < 2 ^ (prefixWord ++ tailWord_296405).sum := by decide
  have hdescent : baseEnd_296405 < baseStart_296405 := by decide
  rcases family_descends (prefixWord ++ tailWord_296405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296424 : List Nat := [2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_296424 : Nat := 118140960795 + 296424 * 2 ^ 59
def prefixEnd_296424 : Nat := 4983230072969 + 3 ^ 40 * 296424 * 2
def baseEnd_296424 : Nat := 90197327127972428703275

theorem tailTrace_296424 : CollatzResearch.WordTrace tailWord_296424 prefixEnd_296424 90197327127972428703275 := by
  unfold tailWord_296424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405735739056974016916163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7207647652075965355888217 5405735739056974016916163)
  ·
    refine ⟨8108603608585461025374245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405735739056974016916163 8108603608585461025374245)
    ·
      refine ⟨1520363176609773942257671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8108603608585461025374245 1520363176609773942257671)
      ·
        refine ⟨2280544764914660913386507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520363176609773942257671 2280544764914660913386507)
        ·
          refine ⟨3420817147371991370079761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280544764914660913386507 3420817147371991370079761)
          ·
            refine ⟨2565612860528993527559821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3420817147371991370079761 2565612860528993527559821)
            ·
              refine ⟨962104822698372572834933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565612860528993527559821 962104822698372572834933)
              ·
                refine ⟨90197327127972428703275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 962104822698372572834933 90197327127972428703275)
                ·
                  rfl

theorem cell19_296424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_296424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296424 prefixEnd_296424 := by exact prefixLift 296424
  have htrace : WordTrace (prefixWord ++ tailWord_296424) baseStart_296424 baseEnd_296424 := by
    simpa [prefixWord, tailWord_296424, baseEnd_296424] using wordTrace_append hprefix tailTrace_296424
  have hstable : (prefixWord ++ tailWord_296424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296424).length < 2 ^ (prefixWord ++ tailWord_296424).sum := by decide
  have hdescent : baseEnd_296424 < baseStart_296424 := by decide
  rcases family_descends (prefixWord ++ tailWord_296424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296454 : List Nat := [6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_296454 : Nat := 118140960795 + 296454 * 2 ^ 59
def prefixEnd_296454 : Nat := 4983230072969 + 3 ^ 40 * 296454 * 2
def baseEnd_296454 : Nat := 90206455672941248036527

theorem tailTrace_296454 : CollatzResearch.WordTrace tailWord_296454 prefixEnd_296454 90206455672941248036527 := by
  unfold tailWord_296454
  simp only [CollatzResearch.WordTrace]
  refine ⟨337892677125164473669513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7208377112003508771616277 337892677125164473669513)
  ·
    refine ⟨253419507843873355252135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 337892677125164473669513 253419507843873355252135)
    ·
      refine ⟨380129261765810032878203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253419507843873355252135 380129261765810032878203)
      ·
        refine ⟨570193892648715049317305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380129261765810032878203 570193892648715049317305)
        ·
          refine ⟨427645419486536286987979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570193892648715049317305 427645419486536286987979)
          ·
            refine ⟨641468129229804430481969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427645419486536286987979 641468129229804430481969)
            ·
              refine ⟨481101096922353322861477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641468129229804430481969 481101096922353322861477)
              ·
                refine ⟨90206455672941248036527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481101096922353322861477 90206455672941248036527)
                ·
                  rfl

theorem cell19_296454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_296454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296454 prefixEnd_296454 := by exact prefixLift 296454
  have htrace : WordTrace (prefixWord ++ tailWord_296454) baseStart_296454 baseEnd_296454 := by
    simpa [prefixWord, tailWord_296454, baseEnd_296454] using wordTrace_append hprefix tailTrace_296454
  have hstable : (prefixWord ++ tailWord_296454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296454).length < 2 ^ (prefixWord ++ tailWord_296454).sum := by decide
  have hdescent : baseEnd_296454 < baseStart_296454 := by decide
  rcases family_descends (prefixWord ++ tailWord_296454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296460 : List Nat := [2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_296460 : Nat := 118140960795 + 296460 * 2 ^ 59
def prefixEnd_296460 : Nat := 4983230072969 + 3 ^ 40 * 296460 * 2
def baseEnd_296460 : Nat := 90208281381935011903177

theorem tailTrace_296460 : CollatzResearch.WordTrace tailWord_296460 prefixEnd_296460 90208281381935011903177 := by
  unfold tailWord_296460
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406392252991763091071417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7208523003989017454761889 5406392252991763091071417)
  ·
    refine ⟨4054794189743822318303563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5406392252991763091071417 4054794189743822318303563)
    ·
      refine ⟨6082191284615733477455345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054794189743822318303563 6082191284615733477455345)
      ·
        refine ⟨4561643463461800108091509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6082191284615733477455345 4561643463461800108091509)
        ·
          refine ⟨427654074699543760133579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4561643463461800108091509 427654074699543760133579)
          ·
            refine ⟨641481112049315640200369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427654074699543760133579 641481112049315640200369)
            ·
              refine ⟨481110834036986730150277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641481112049315640200369 481110834036986730150277)
              ·
                refine ⟨90208281381935011903177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481110834036986730150277 90208281381935011903177)
                ·
                  rfl

theorem cell19_296460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_296460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296460 prefixEnd_296460 := by exact prefixLift 296460
  have htrace : WordTrace (prefixWord ++ tailWord_296460) baseStart_296460 baseEnd_296460 := by
    simpa [prefixWord, tailWord_296460, baseEnd_296460] using wordTrace_append hprefix tailTrace_296460
  have hstable : (prefixWord ++ tailWord_296460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296460).length < 2 ^ (prefixWord ++ tailWord_296460).sum := by decide
  have hdescent : baseEnd_296460 < baseStart_296460 := by decide
  rcases family_descends (prefixWord ++ tailWord_296460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296481 : List Nat := [1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_296481 : Nat := 118140960795 + 296481 * 2 ^ 59
def prefixEnd_296481 : Nat := 4983230072969 + 3 ^ 40 * 296481 * 2
def baseEnd_296481 : Nat := 90214671363413185436453

theorem tailTrace_296481 : CollatzResearch.WordTrace tailWord_296481 prefixEnd_296481 90214671363413185436453 := by
  unfold tailWord_296481
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813550438907446768657297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7209033625938297845771531 10813550438907446768657297)
  ·
    refine ⟨8110162829180585076492973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10813550438907446768657297 8110162829180585076492973)
    ·
      refine ⟨3041311060942719403684865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8110162829180585076492973 3041311060942719403684865)
      ·
        refine ⟨2280983295707039552763649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3041311060942719403684865 2280983295707039552763649)
        ·
          refine ⟨1710737471780279664572737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2280983295707039552763649 1710737471780279664572737)
          ·
            refine ⟨1283053103835209748429553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710737471780279664572737 1283053103835209748429553)
            ·
              refine ⟨962289827876407311322165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283053103835209748429553 962289827876407311322165)
              ·
                refine ⟨90214671363413185436453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 962289827876407311322165 90214671363413185436453)
                ·
                  rfl

theorem cell19_296481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_296481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296481 prefixEnd_296481 := by exact prefixLift 296481
  have htrace : WordTrace (prefixWord ++ tailWord_296481) baseStart_296481 baseEnd_296481 := by
    simpa [prefixWord, tailWord_296481, baseEnd_296481] using wordTrace_append hprefix tailTrace_296481
  have hstable : (prefixWord ++ tailWord_296481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296481).length < 2 ^ (prefixWord ++ tailWord_296481).sum := by decide
  have hdescent : baseEnd_296481 < baseStart_296481 := by decide
  rcases family_descends (prefixWord ++ tailWord_296481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296500 : List Nat := [2, 5, 1, 11]
def baseStart_296500 : Nat := 118140960795 + 296500 * 2 ^ 59
def prefixEnd_296500 : Nat := 4983230072969 + 3 ^ 40 * 296500 * 2
def baseEnd_296500 : Nat := 1113832750311441617459

theorem tailTrace_296500 : CollatzResearch.WordTrace tailWord_296500 prefixEnd_296500 1113832750311441617459 := by
  unfold tailWord_296500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407121712919306506799477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7209495617225742009065969 5407121712919306506799477)
  ·
    refine ⟨506917660586184985012451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5407121712919306506799477 506917660586184985012451)
    ·
      refine ⟨760376490879277477518677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506917660586184985012451 760376490879277477518677)
      ·
        refine ⟨1113832750311441617459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 760376490879277477518677 1113832750311441617459)
        ·
          rfl

theorem cell19_296500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 11].length) (baseStart_296500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296500 prefixEnd_296500 := by exact prefixLift 296500
  have htrace : WordTrace (prefixWord ++ tailWord_296500) baseStart_296500 baseEnd_296500 := by
    simpa [prefixWord, tailWord_296500, baseEnd_296500] using wordTrace_append hprefix tailTrace_296500
  have hstable : (prefixWord ++ tailWord_296500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296500).length < 2 ^ (prefixWord ++ tailWord_296500).sum := by decide
  have hdescent : baseEnd_296500 < baseStart_296500 := by decide
  rcases family_descends (prefixWord ++ tailWord_296500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296610 : List Nat := [3, 3, 1, 4, 1, 2, 5]
def baseStart_296610 : Nat := 118140960795 + 296610 * 2 ^ 59
def prefixEnd_296610 : Nat := 4983230072969 + 3 ^ 40 * 296610 * 2
def baseEnd_296610 : Nat := 30084641368926369523145

theorem tailTrace_296610 : CollatzResearch.WordTrace tailWord_296610 prefixEnd_296610 30084641368926369523145 := by
  unfold tailWord_296610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704563863860025450025821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7212170303626734533402189 2704563863860025450025821)
  ·
    refine ⟨1014211448947509543759683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2704563863860025450025821 1014211448947509543759683)
    ·
      refine ⟨1521317173421264315639525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014211448947509543759683 1521317173421264315639525)
      ·
        refine ⟨285246970016487059182411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1521317173421264315639525 285246970016487059182411)
        ·
          refine ⟨427870455024730588773617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285246970016487059182411 427870455024730588773617)
          ·
            refine ⟨320902841268547941580213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427870455024730588773617 320902841268547941580213)
            ·
              refine ⟨30084641368926369523145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 320902841268547941580213 30084641368926369523145)
              ·
                rfl

theorem cell19_296610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_296610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296610 prefixEnd_296610 := by exact prefixLift 296610
  have htrace : WordTrace (prefixWord ++ tailWord_296610) baseStart_296610 baseEnd_296610 := by
    simpa [prefixWord, tailWord_296610, baseEnd_296610] using wordTrace_append hprefix tailTrace_296610
  have hstable : (prefixWord ++ tailWord_296610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296610).length < 2 ^ (prefixWord ++ tailWord_296610).sum := by decide
  have hdescent : baseEnd_296610 < baseStart_296610 := by decide
  rcases family_descends (prefixWord ++ tailWord_296610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296669 : List Nat := [1, 4, 3, 3, 1, 7]
def baseStart_296669 : Nat := 118140960795 + 296669 * 2 ^ 59
def prefixEnd_296669 : Nat := 4983230072969 + 3 ^ 40 * 296669 * 2
def baseEnd_296669 : Nat := 10030208545764939250907

theorem tailTrace_296669 : CollatzResearch.WordTrace tailWord_296669 prefixEnd_296669 10030208545764939250907 := by
  unfold tailWord_296669
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820407362226354876501061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7213604908150903251000707 10820407362226354876501061)
  ·
    refine ⟨2028826380417441539343949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10820407362226354876501061 2028826380417441539343949)
    ·
      refine ⟨760809892656540577253981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2028826380417441539343949 760809892656540577253981)
      ·
        refine ⟨285303709746202716470243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 760809892656540577253981 285303709746202716470243)
        ·
          refine ⟨427955564619304074705365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285303709746202716470243 427955564619304074705365)
          ·
            refine ⟨10030208545764939250907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 427955564619304074705365 10030208545764939250907)
            ·
              rfl

theorem cell19_296669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_296669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296669 prefixEnd_296669 := by exact prefixLift 296669
  have htrace : WordTrace (prefixWord ++ tailWord_296669) baseStart_296669 baseEnd_296669 := by
    simpa [prefixWord, tailWord_296669, baseEnd_296669] using wordTrace_append hprefix tailTrace_296669
  have hstable : (prefixWord ++ tailWord_296669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296669).length < 2 ^ (prefixWord ++ tailWord_296669).sum := by decide
  have hdescent : baseEnd_296669 < baseStart_296669 := by decide
  rcases family_descends (prefixWord ++ tailWord_296669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296673 : List Nat := [1, 2, 3, 1, 12]
def baseStart_296673 : Nat := 118140960795 + 296673 * 2 ^ 59
def prefixEnd_296673 : Nat := 4983230072969 + 3 ^ 40 * 296673 * 2
def baseEnd_296673 : Nat := 3343447927822727006269

theorem tailTrace_296673 : CollatzResearch.WordTrace tailWord_296673 prefixEnd_296673 3343447927822727006269 := by
  unfold tailWord_296673
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820553254211863559646673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7213702169474575706431115 10820553254211863559646673)
  ·
    refine ⟨8115414940658897669735005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10820553254211863559646673 8115414940658897669735005)
    ·
      refine ⟨3043280602747086626150627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8115414940658897669735005 3043280602747086626150627)
      ·
        refine ⟨4564920904120629939225941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3043280602747086626150627 4564920904120629939225941)
        ·
          refine ⟨3343447927822727006269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4564920904120629939225941 3343447927822727006269)
          ·
            rfl

theorem cell19_296673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 12].length) (baseStart_296673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296673 prefixEnd_296673 := by exact prefixLift 296673
  have htrace : WordTrace (prefixWord ++ tailWord_296673) baseStart_296673 baseEnd_296673 := by
    simpa [prefixWord, tailWord_296673, baseEnd_296673] using wordTrace_append hprefix tailTrace_296673
  have hstable : (prefixWord ++ tailWord_296673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296673).length < 2 ^ (prefixWord ++ tailWord_296673).sum := by decide
  have hdescent : baseEnd_296673 < baseStart_296673 := by decide
  rcases family_descends (prefixWord ++ tailWord_296673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296785 : List Nat := [1, 2, 2, 1, 5, 3, 5]
def baseStart_296785 : Nat := 118140960795 + 296785 * 2 ^ 59
def prefixEnd_296785 : Nat := 4983230072969 + 3 ^ 40 * 296785 * 2
def baseEnd_296785 : Nat := 30102391317476851560023

theorem tailTrace_296785 : CollatzResearch.WordTrace tailWord_296785 prefixEnd_296785 30102391317476851560023 := by
  unfold tailWord_296785
  simp only [CollatzResearch.WordTrace]
  refine ⟨10824638229806106687723809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7216425486537404458482539 10824638229806106687723809)
  ·
    refine ⟨8118478672354580015792857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10824638229806106687723809 8118478672354580015792857)
    ·
      refine ⟨6088859004265935011844643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8118478672354580015792857 6088859004265935011844643)
      ·
        refine ⟨9133288506398902517766965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088859004265935011844643 9133288506398902517766965)
        ·
          refine ⟨856245797474897111040653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9133288506398902517766965 856245797474897111040653)
          ·
            refine ⟨321092174053086416640245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 856245797474897111040653 321092174053086416640245)
            ·
              refine ⟨30102391317476851560023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 321092174053086416640245 30102391317476851560023)
              ·
                rfl

theorem cell19_296785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_296785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296785 prefixEnd_296785 := by exact prefixLift 296785
  have htrace : WordTrace (prefixWord ++ tailWord_296785) baseStart_296785 baseEnd_296785 := by
    simpa [prefixWord, tailWord_296785, baseEnd_296785] using wordTrace_append hprefix tailTrace_296785
  have hstable : (prefixWord ++ tailWord_296785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296785).length < 2 ^ (prefixWord ++ tailWord_296785).sum := by decide
  have hdescent : baseEnd_296785 < baseStart_296785 := by decide
  rcases family_descends (prefixWord ++ tailWord_296785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296802 : List Nat := [3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_296802 : Nat := 118140960795 + 296802 * 2 ^ 59
def prefixEnd_296802 : Nat := 4983230072969 + 3 ^ 40 * 296802 * 2
def baseEnd_296802 : Nat := 90312346794579552302245

theorem tailTrace_296802 : CollatzResearch.WordTrace tailWord_296802 prefixEnd_296802 90312346794579552302245 := by
  unfold tailWord_296802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706314567686129647773165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7216838847163012394061773 2706314567686129647773165)
  ·
    refine ⟨1014867962882298617914937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2706314567686129647773165 1014867962882298617914937)
    ·
      refine ⟨761150972161723963436203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1014867962882298617914937 761150972161723963436203)
      ·
        refine ⟨1141726458242585945154305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761150972161723963436203 1141726458242585945154305)
        ·
          refine ⟨856294843681939458865729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141726458242585945154305 856294843681939458865729)
          ·
            refine ⟨642221132761454594149297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856294843681939458865729 642221132761454594149297)
            ·
              refine ⟨481665849571090945611973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642221132761454594149297 481665849571090945611973)
              ·
                refine ⟨90312346794579552302245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481665849571090945611973 90312346794579552302245)
                ·
                  rfl

theorem cell19_296802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_296802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296802 prefixEnd_296802 := by exact prefixLift 296802
  have htrace : WordTrace (prefixWord ++ tailWord_296802) baseStart_296802 baseEnd_296802 := by
    simpa [prefixWord, tailWord_296802, baseEnd_296802] using wordTrace_append hprefix tailTrace_296802
  have hstable : (prefixWord ++ tailWord_296802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296802).length < 2 ^ (prefixWord ++ tailWord_296802).sum := by decide
  have hdescent : baseEnd_296802 < baseStart_296802 := by decide
  rcases family_descends (prefixWord ++ tailWord_296802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296825 : List Nat := [1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_296825 : Nat := 118140960795 + 296825 * 2 ^ 59
def prefixEnd_296825 : Nat := 4983230072969 + 3 ^ 40 * 296825 * 2
def baseEnd_296825 : Nat := 90319345345722313791071

theorem tailTrace_296825 : CollatzResearch.WordTrace tailWord_296825 prefixEnd_296825 90319345345722313791071 := by
  unfold tailWord_296825
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826097149661193519179929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7217398099774129012786619 10826097149661193519179929)
  ·
    refine ⟨8119572862245895139384947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10826097149661193519179929 8119572862245895139384947)
    ·
      refine ⟨12179359293368842709077421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8119572862245895139384947 12179359293368842709077421)
      ·
        refine ⟨4567259735013316015904033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12179359293368842709077421 4567259735013316015904033)
        ·
          refine ⟨3425444801259987011928025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567259735013316015904033 3425444801259987011928025)
          ·
            refine ⟨2569083600944990258946019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3425444801259987011928025 2569083600944990258946019)
            ·
              refine ⟨3853625401417485388419029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569083600944990258946019 3853625401417485388419029)
              ·
                refine ⟨90319345345722313791071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3853625401417485388419029 90319345345722313791071)
                ·
                  rfl

theorem cell19_296825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_296825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296825 prefixEnd_296825 := by exact prefixLift 296825
  have htrace : WordTrace (prefixWord ++ tailWord_296825) baseStart_296825 baseEnd_296825 := by
    simpa [prefixWord, tailWord_296825, baseEnd_296825] using wordTrace_append hprefix tailTrace_296825
  have hstable : (prefixWord ++ tailWord_296825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296825).length < 2 ^ (prefixWord ++ tailWord_296825).sum := by decide
  have hdescent : baseEnd_296825 < baseStart_296825 := by decide
  rcases family_descends (prefixWord ++ tailWord_296825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296842 : List Nat := [3, 1, 2, 4, 2, 7]
def baseStart_296842 : Nat := 118140960795 + 296842 * 2 ^ 59
def prefixEnd_296842 : Nat := 4983230072969 + 3 ^ 40 * 296842 * 2
def baseEnd_296842 : Nat := 10036057576430145712583

theorem tailTrace_296842 : CollatzResearch.WordTrace tailWord_296842 prefixEnd_296842 10036057576430145712583 := by
  unfold tailWord_296842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706679297649901355637195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7217811460399736948365853 2706679297649901355637195)
  ·
    refine ⟨4060018946474852033455793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2706679297649901355637195 4060018946474852033455793)
    ·
      refine ⟨3045014209856139025091845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060018946474852033455793 3045014209856139025091845)
      ·
        refine ⟨570940164348026067204721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3045014209856139025091845 570940164348026067204721)
        ·
          refine ⟨428205123261019550403541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570940164348026067204721 428205123261019550403541)
          ·
            refine ⟨10036057576430145712583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 428205123261019550403541 10036057576430145712583)
            ·
              rfl

theorem cell19_296842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_296842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296842 prefixEnd_296842 := by exact prefixLift 296842
  have htrace : WordTrace (prefixWord ++ tailWord_296842) baseStart_296842 baseEnd_296842 := by
    simpa [prefixWord, tailWord_296842, baseEnd_296842] using wordTrace_append hprefix tailTrace_296842
  have hstable : (prefixWord ++ tailWord_296842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296842).length < 2 ^ (prefixWord ++ tailWord_296842).sum := by decide
  have hdescent : baseEnd_296842 < baseStart_296842 := by decide
  rcases family_descends (prefixWord ++ tailWord_296842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296861 : List Nat := [1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_296861 : Nat := 118140960795 + 296861 * 2 ^ 59
def prefixEnd_296861 : Nat := 4983230072969 + 3 ^ 40 * 296861 * 2
def baseEnd_296861 : Nat := 90330299599684896990973

theorem tailTrace_296861 : CollatzResearch.WordTrace tailWord_296861 prefixEnd_296861 90330299599684896990973 := by
  unfold tailWord_296861
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827410177530771667490437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7218273451687181111660291 10827410177530771667490437)
  ·
    refine ⟨2030139408287019687654457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10827410177530771667490437 2030139408287019687654457)
    ·
      refine ⟨1522604556215264765740843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2030139408287019687654457 1522604556215264765740843)
      ·
        refine ⟨2283906834322897148611265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522604556215264765740843 2283906834322897148611265)
        ·
          refine ⟨1712930125742172861458449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283906834322897148611265 1712930125742172861458449)
          ·
            refine ⟨1284697594306629646093837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712930125742172861458449 1284697594306629646093837)
            ·
              refine ⟨481761597864986117285189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284697594306629646093837 481761597864986117285189)
              ·
                refine ⟨90330299599684896990973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481761597864986117285189 90330299599684896990973)
                ·
                  rfl

theorem cell19_296861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_296861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296861 prefixEnd_296861 := by exact prefixLift 296861
  have htrace : WordTrace (prefixWord ++ tailWord_296861) baseStart_296861 baseEnd_296861 := by
    simpa [prefixWord, tailWord_296861, baseEnd_296861] using wordTrace_append hprefix tailTrace_296861
  have hstable : (prefixWord ++ tailWord_296861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296861).length < 2 ^ (prefixWord ++ tailWord_296861).sum := by decide
  have hdescent : baseEnd_296861 < baseStart_296861 := by decide
  rcases family_descends (prefixWord ++ tailWord_296861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296882 : List Nat := [3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_296882 : Nat := 118140960795 + 296882 * 2 ^ 59
def prefixEnd_296882 : Nat := 4983230072969 + 3 ^ 40 * 296882 * 2
def baseEnd_296882 : Nat := 90336689581163070524249

theorem tailTrace_296882 : CollatzResearch.WordTrace tailWord_296882 prefixEnd_296882 90336689581163070524249 := by
  unfold tailWord_296882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707044027613673063501225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7218784073636461502669933 2707044027613673063501225)
  ·
    refine ⟨2030283020710254797625919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2707044027613673063501225 2030283020710254797625919)
    ·
      refine ⟨3045424531065382196438879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030283020710254797625919 3045424531065382196438879)
      ·
        refine ⟨4568136796598073294658319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045424531065382196438879 4568136796598073294658319)
        ·
          refine ⟨6852205194897109941987479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568136796598073294658319 6852205194897109941987479)
          ·
            refine ⟨10278307792345664912981219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852205194897109941987479 10278307792345664912981219)
            ·
              refine ⟨15417461688518497369471829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10278307792345664912981219 15417461688518497369471829)
              ·
                refine ⟨90336689581163070524249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15417461688518497369471829 90336689581163070524249)
                ·
                  rfl

theorem cell19_296882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_296882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296882 prefixEnd_296882 := by exact prefixLift 296882
  have htrace : WordTrace (prefixWord ++ tailWord_296882) baseStart_296882 baseEnd_296882 := by
    simpa [prefixWord, tailWord_296882, baseEnd_296882] using wordTrace_append hprefix tailTrace_296882
  have hstable : (prefixWord ++ tailWord_296882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296882).length < 2 ^ (prefixWord ++ tailWord_296882).sum := by decide
  have hdescent : baseEnd_296882 < baseStart_296882 := by decide
  rcases family_descends (prefixWord ++ tailWord_296882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296920 : List Nat := [2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_296920 : Nat := 118140960795 + 296920 * 2 ^ 59
def prefixEnd_296920 : Nat := 4983230072969 + 3 ^ 40 * 296920 * 2
def baseEnd_296920 : Nat := 90348252404790241679701

theorem tailTrace_296920 : CollatzResearch.WordTrace tailWord_296920 prefixEnd_296920 90348252404790241679701 := by
  unfold tailWord_296920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5414781042158512371944107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7219708056211349829258809 5414781042158512371944107)
  ·
    refine ⟨8122171563237768557916161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5414781042158512371944107 8122171563237768557916161)
    ·
      refine ⟨6091628672428326418437121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8122171563237768557916161 6091628672428326418437121)
      ·
        refine ⟨4568721504321244813827841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6091628672428326418437121 4568721504321244813827841)
        ·
          refine ⟨3426541128240933610370881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4568721504321244813827841 3426541128240933610370881)
          ·
            refine ⟨2569905846180700207778161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3426541128240933610370881 2569905846180700207778161)
            ·
              refine ⟨1927429384635525155833621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569905846180700207778161 1927429384635525155833621)
              ·
                refine ⟨90348252404790241679701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1927429384635525155833621 90348252404790241679701)
                ·
                  rfl

theorem cell19_296920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_296920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_296920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_296920 prefixEnd_296920 := by exact prefixLift 296920
  have htrace : WordTrace (prefixWord ++ tailWord_296920) baseStart_296920 baseEnd_296920 := by
    simpa [prefixWord, tailWord_296920, baseEnd_296920] using wordTrace_append hprefix tailTrace_296920
  have hstable : (prefixWord ++ tailWord_296920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296920).length < 2 ^ (prefixWord ++ tailWord_296920).sum := by decide
  have hdescent : baseEnd_296920 < baseStart_296920 := by decide
  rcases family_descends (prefixWord ++ tailWord_296920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297072 : List Nat := [2, 1, 1, 1, 5, 3, 6]
def baseStart_297072 : Nat := 118140960795 + 297072 * 2 ^ 59
def prefixEnd_297072 : Nat := 4983230072969 + 3 ^ 40 * 297072 * 2
def baseEnd_297072 : Nat := 30131501233099642100503

theorem tailTrace_297072 : CollatzResearch.WordTrace tailWord_297072 prefixEnd_297072 30131501233099642100503 := by
  unfold tailWord_297072
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417552989883177351710735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7223403986510903135614313 5417552989883177351710735)
  ·
    refine ⟨8126329484824766027566103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5417552989883177351710735 8126329484824766027566103)
    ·
      refine ⟨12189494227237149041349155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8126329484824766027566103 12189494227237149041349155)
      ·
        refine ⟨18284241340855723562023733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12189494227237149041349155 18284241340855723562023733)
        ·
          refine ⟨1714147625705224083939725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18284241340855723562023733 1714147625705224083939725)
          ·
            refine ⟨642805359639459031477397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1714147625705224083939725 642805359639459031477397)
            ·
              refine ⟨30131501233099642100503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 642805359639459031477397 30131501233099642100503)
              ·
                rfl

theorem cell19_297072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_297072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297072 prefixEnd_297072 := by exact prefixLift 297072
  have htrace : WordTrace (prefixWord ++ tailWord_297072) baseStart_297072 baseEnd_297072 := by
    simpa [prefixWord, tailWord_297072, baseEnd_297072] using wordTrace_append hprefix tailTrace_297072
  have hstable : (prefixWord ++ tailWord_297072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297072).length < 2 ^ (prefixWord ++ tailWord_297072).sum := by decide
  have hdescent : baseEnd_297072 < baseStart_297072 := by decide
  rcases family_descends (prefixWord ++ tailWord_297072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297140 : List Nat := [2, 5, 3, 1, 1, 1, 2, 4]
def baseStart_297140 : Nat := 118140960795 + 297140 * 2 ^ 59
def prefixEnd_297140 : Nat := 4983230072969 + 3 ^ 40 * 297140 * 2
def baseEnd_297140 : Nat := 90415195067894916790213

theorem tailTrace_297140 : CollatzResearch.WordTrace tailWord_297140 prefixEnd_297140 90415195067894916790213 := by
  unfold tailWord_297140
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418793071760001158448437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7225057429013334877931249 5418793071760001158448437)
  ·
    refine ⟨508011850477500108604541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5418793071760001158448437 508011850477500108604541)
    ·
      refine ⟨190504443929062540726703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 508011850477500108604541 190504443929062540726703)
      ·
        refine ⟨285756665893593811090055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190504443929062540726703 285756665893593811090055)
        ·
          refine ⟨428634998840390716635083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285756665893593811090055 428634998840390716635083)
          ·
            refine ⟨642952498260586074952625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428634998840390716635083 642952498260586074952625)
            ·
              refine ⟨482214373695439556214469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642952498260586074952625 482214373695439556214469)
              ·
                refine ⟨90415195067894916790213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482214373695439556214469 90415195067894916790213)
                ·
                  rfl

theorem cell19_297140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_297140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297140 prefixEnd_297140 := by exact prefixLift 297140
  have htrace : WordTrace (prefixWord ++ tailWord_297140) baseStart_297140 baseEnd_297140 := by
    simpa [prefixWord, tailWord_297140, baseEnd_297140] using wordTrace_append hprefix tailTrace_297140
  have hstable : (prefixWord ++ tailWord_297140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297140).length < 2 ^ (prefixWord ++ tailWord_297140).sum := by decide
  have hdescent : baseEnd_297140 < baseStart_297140 := by decide
  rcases family_descends (prefixWord ++ tailWord_297140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297220 : List Nat := [2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_297220 : Nat := 118140960795 + 297220 * 2 ^ 59
def prefixEnd_297220 : Nat := 4983230072969 + 3 ^ 40 * 297220 * 2
def baseEnd_297220 : Nat := 90439537854478435012217

theorem tailTrace_297220 : CollatzResearch.WordTrace tailWord_297220 prefixEnd_297220 90439537854478435012217 := by
  unfold tailWord_297220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420251991615087989904557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7227002655486783986539409 5420251991615087989904557)
  ·
    refine ⟨2032594496855657996214209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5420251991615087989904557 2032594496855657996214209)
    ·
      refine ⟨1524445872641743497160657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2032594496855657996214209 1524445872641743497160657)
      ·
        refine ⟨1143334404481307622870493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1524445872641743497160657 1143334404481307622870493)
        ·
          refine ⟨428750401680490358576435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1143334404481307622870493 428750401680490358576435)
          ·
            refine ⟨643125602520735537864653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428750401680490358576435 643125602520735537864653)
            ·
              refine ⟨241172100945275826699245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 643125602520735537864653 241172100945275826699245)
              ·
                refine ⟨90439537854478435012217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241172100945275826699245 90439537854478435012217)
                ·
                  rfl

theorem cell19_297220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_297220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297220 prefixEnd_297220 := by exact prefixLift 297220
  have htrace : WordTrace (prefixWord ++ tailWord_297220) baseStart_297220 baseEnd_297220 := by
    simpa [prefixWord, tailWord_297220, baseEnd_297220] using wordTrace_append hprefix tailTrace_297220
  have hstable : (prefixWord ++ tailWord_297220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297220).length < 2 ^ (prefixWord ++ tailWord_297220).sum := by decide
  have hdescent : baseEnd_297220 < baseStart_297220 := by decide
  rcases family_descends (prefixWord ++ tailWord_297220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297300 : List Nat := [2, 4, 1, 1, 2, 2, 7]
def baseStart_297300 : Nat := 118140960795 + 297300 * 2 ^ 59
def prefixEnd_297300 : Nat := 4983230072969 + 3 ^ 40 * 297300 * 2
def baseEnd_297300 : Nat := 30154626880353984411407

theorem tailTrace_297300 : CollatzResearch.WordTrace tailWord_297300 prefixEnd_297300 30154626880353984411407 := by
  unfold tailWord_297300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421710911470174821360677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7228947881960233095147569 5421710911470174821360677)
  ·
    refine ⟨1016570795900657779005127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5421710911470174821360677 1016570795900657779005127)
    ·
      refine ⟨1524856193850986668507691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016570795900657779005127 1524856193850986668507691)
      ·
        refine ⟨2287284290776480002761537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524856193850986668507691 2287284290776480002761537)
        ·
          refine ⟨1715463218082360002071153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2287284290776480002761537 1715463218082360002071153)
          ·
            refine ⟨1286597413561770001553365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715463218082360002071153 1286597413561770001553365)
            ·
              refine ⟨30154626880353984411407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1286597413561770001553365 30154626880353984411407)
              ·
                rfl

theorem cell19_297300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_297300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297300 prefixEnd_297300 := by exact prefixLift 297300
  have htrace : WordTrace (prefixWord ++ tailWord_297300) baseStart_297300 baseEnd_297300 := by
    simpa [prefixWord, tailWord_297300, baseEnd_297300] using wordTrace_append hprefix tailTrace_297300
  have hstable : (prefixWord ++ tailWord_297300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297300).length < 2 ^ (prefixWord ++ tailWord_297300).sum := by decide
  have hdescent : baseEnd_297300 < baseStart_297300 := by decide
  rcases family_descends (prefixWord ++ tailWord_297300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297319 : List Nat := [1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_297319 : Nat := 118140960795 + 297319 * 2 ^ 59
def prefixEnd_297319 : Nat := 4983230072969 + 3 ^ 40 * 297319 * 2
def baseEnd_297319 : Nat := 90469662052875538811947

theorem tailTrace_297319 : CollatzResearch.WordTrace tailWord_297319 prefixEnd_297319 90469662052875538811947 := by
  unfold tailWord_297319
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844114809871515887663011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7229409873247677258442007 10844114809871515887663011)
  ·
    refine ⟨16266172214807273831494517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10844114809871515887663011 16266172214807273831494517)
    ·
      refine ⟨1524953645138181921702611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16266172214807273831494517 1524953645138181921702611)
      ·
        refine ⟨2287430467707272882553917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524953645138181921702611 2287430467707272882553917)
        ·
          refine ⟨857786425390227330957719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2287430467707272882553917 857786425390227330957719)
          ·
            refine ⟨1286679638085340996436579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857786425390227330957719 1286679638085340996436579)
            ·
              refine ⟨1930019457128011494654869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286679638085340996436579 1930019457128011494654869)
              ·
                refine ⟨90469662052875538811947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1930019457128011494654869 90469662052875538811947)
                ·
                  rfl

theorem cell19_297319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_297319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297319 prefixEnd_297319 := by exact prefixLift 297319
  have htrace : WordTrace (prefixWord ++ tailWord_297319) baseStart_297319 baseEnd_297319 := by
    simpa [prefixWord, tailWord_297319, baseEnd_297319] using wordTrace_append hprefix tailTrace_297319
  have hstable : (prefixWord ++ tailWord_297319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297319).length < 2 ^ (prefixWord ++ tailWord_297319).sum := by decide
  have hdescent : baseEnd_297319 < baseStart_297319 := by decide
  rcases family_descends (prefixWord ++ tailWord_297319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297366 : List Nat := [5, 3, 1, 2, 2, 1, 1, 4]
def baseStart_297366 : Nat := 118140960795 + 297366 * 2 ^ 59
def prefixEnd_297366 : Nat := 4983230072969 + 3 ^ 40 * 297366 * 2
def baseEnd_297366 : Nat := 90483963439993355767375

theorem tailTrace_297366 : CollatzResearch.WordTrace tailWord_297366 prefixEnd_297366 90483963439993355767375 := by
  unfold tailWord_297366
  simp only [CollatzResearch.WordTrace]
  refine ⟨677864315043827682163997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7230552693800828609749301 677864315043827682163997)
  ·
    refine ⟨254199118141435380811499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 677864315043827682163997 254199118141435380811499)
    ·
      refine ⟨381298677212153071217249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254199118141435380811499 381298677212153071217249)
      ·
        refine ⟨285974007909114803412937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381298677212153071217249 285974007909114803412937)
        ·
          refine ⟨214480505931836102559703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285974007909114803412937 214480505931836102559703)
          ·
            refine ⟨321720758897754153839555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214480505931836102559703 321720758897754153839555)
            ·
              refine ⟨482581138346631230759333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321720758897754153839555 482581138346631230759333)
              ·
                refine ⟨90483963439993355767375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482581138346631230759333 90483963439993355767375)
                ·
                  rfl

theorem cell19_297366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_297366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297366 prefixEnd_297366 := by exact prefixLift 297366
  have htrace : WordTrace (prefixWord ++ tailWord_297366) baseStart_297366 baseEnd_297366 := by
    simpa [prefixWord, tailWord_297366, baseEnd_297366] using wordTrace_append hprefix tailTrace_297366
  have hstable : (prefixWord ++ tailWord_297366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297366).length < 2 ^ (prefixWord ++ tailWord_297366).sum := by decide
  have hdescent : baseEnd_297366 < baseStart_297366 := by decide
  rcases family_descends (prefixWord ++ tailWord_297366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297376 : List Nat := [2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_297376 : Nat := 118140960795 + 297376 * 2 ^ 59
def prefixEnd_297376 : Nat := 4983230072969 + 3 ^ 40 * 297376 * 2
def baseEnd_297376 : Nat := 90487006288316295545125

theorem tailTrace_297376 : CollatzResearch.WordTrace tailWord_297376 prefixEnd_297376 90487006288316295545125 := by
  unfold tailWord_297376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423096885332507311243991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7230795847110009748325321 5423096885332507311243991)
  ·
    refine ⟨8134645327998760966865987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5423096885332507311243991 8134645327998760966865987)
    ·
      refine ⟨12201967991998141450298981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8134645327998760966865987 12201967991998141450298981)
      ·
        refine ⟨2287868998499651521931059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12201967991998141450298981 2287868998499651521931059)
        ·
          refine ⟨3431803497749477282896589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287868998499651521931059 3431803497749477282896589)
          ·
            refine ⟨1286926311656053981086221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3431803497749477282896589 1286926311656053981086221)
            ·
              refine ⟨482597366871020242907333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1286926311656053981086221 482597366871020242907333)
              ·
                refine ⟨90487006288316295545125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482597366871020242907333 90487006288316295545125)
                ·
                  rfl

theorem cell19_297376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_297376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297376 prefixEnd_297376 := by exact prefixLift 297376
  have htrace : WordTrace (prefixWord ++ tailWord_297376) baseStart_297376 baseEnd_297376 := by
    simpa [prefixWord, tailWord_297376, baseEnd_297376] using wordTrace_append hprefix tailTrace_297376
  have hstable : (prefixWord ++ tailWord_297376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297376).length < 2 ^ (prefixWord ++ tailWord_297376).sum := by decide
  have hdescent : baseEnd_297376 < baseStart_297376 := by decide
  rcases family_descends (prefixWord ++ tailWord_297376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297393 : List Nat := [1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_297393 : Nat := 118140960795 + 297393 * 2 ^ 59
def prefixEnd_297393 : Nat := 4983230072969 + 3 ^ 40 * 297393 * 2
def baseEnd_297393 : Nat := 90492179130465293167301

theorem tailTrace_297393 : CollatzResearch.WordTrace tailWord_297393 prefixEnd_297393 90492179130465293167301 := by
  unfold tailWord_297393
  simp only [CollatzResearch.WordTrace]
  refine ⟨10846813811603426525856833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7231209207735617683904555 10846813811603426525856833)
  ·
    refine ⟨8135110358702569894392625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10846813811603426525856833 8135110358702569894392625)
    ·
      refine ⟨6101332769026927420794469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8135110358702569894392625 6101332769026927420794469)
      ·
        refine ⟨1143999894192548891398963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6101332769026927420794469 1143999894192548891398963)
        ·
          refine ⟨1715999841288823337098445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143999894192548891398963 1715999841288823337098445)
          ·
            refine ⟨643499940483308751411917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1715999841288823337098445 643499940483308751411917)
            ·
              refine ⟨241312477681240781779469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 643499940483308751411917 241312477681240781779469)
              ·
                refine ⟨90492179130465293167301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241312477681240781779469 90492179130465293167301)
                ·
                  rfl

theorem cell19_297393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_297393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297393 prefixEnd_297393 := by exact prefixLift 297393
  have htrace : WordTrace (prefixWord ++ tailWord_297393) baseStart_297393 baseEnd_297393 := by
    simpa [prefixWord, tailWord_297393, baseEnd_297393] using wordTrace_append hprefix tailTrace_297393
  have hstable : (prefixWord ++ tailWord_297393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297393).length < 2 ^ (prefixWord ++ tailWord_297393).sum := by decide
  have hdescent : baseEnd_297393 < baseStart_297393 := by decide
  rcases family_descends (prefixWord ++ tailWord_297393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297412 : List Nat := [2, 3, 3, 2, 2, 1, 6]
def baseStart_297412 : Nat := 118140960795 + 297412 * 2 ^ 59
def prefixEnd_297412 : Nat := 4983230072969 + 3 ^ 40 * 297412 * 2
def baseEnd_297412 : Nat := 30165986847426292915009

theorem tailTrace_297412 : CollatzResearch.WordTrace tailWord_297412 prefixEnd_297412 30165986847426292915009 := by
  unfold tailWord_297412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423753399267296385399245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7231671199023061847198993 5423753399267296385399245)
  ·
    refine ⟨2033907524725236144524717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5423753399267296385399245 2033907524725236144524717)
    ·
      refine ⟨762715321771963554196769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2033907524725236144524717 762715321771963554196769)
      ·
        refine ⟨572036491328972665647577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 762715321771963554196769 572036491328972665647577)
        ·
          refine ⟨429027368496729499235683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572036491328972665647577 429027368496729499235683)
          ·
            refine ⟨643541052745094248853525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429027368496729499235683 643541052745094248853525)
            ·
              refine ⟨30165986847426292915009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 643541052745094248853525 30165986847426292915009)
              ·
                rfl

theorem cell19_297412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_297412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297412 prefixEnd_297412 := by exact prefixLift 297412
  have htrace : WordTrace (prefixWord ++ tailWord_297412) baseStart_297412 baseEnd_297412 := by
    simpa [prefixWord, tailWord_297412, baseEnd_297412] using wordTrace_append hprefix tailTrace_297412
  have hstable : (prefixWord ++ tailWord_297412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297412).length < 2 ^ (prefixWord ++ tailWord_297412).sum := by decide
  have hdescent : baseEnd_297412 < baseStart_297412 := by decide
  rcases family_descends (prefixWord ++ tailWord_297412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297450 : List Nat := [3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_297450 : Nat := 118140960795 + 297450 * 2 ^ 59
def prefixEnd_297450 : Nat := 4983230072969 + 3 ^ 40 * 297450 * 2
def baseEnd_297450 : Nat := 90509523365906049900479

theorem tailTrace_297450 : CollatzResearch.WordTrace tailWord_297450 prefixEnd_297450 90509523365906049900479 := by
  unfold tailWord_297450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712223193099231315170451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7232595181597950173787869 2712223193099231315170451)
  ·
    refine ⟨4068334789648846972755677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2712223193099231315170451 4068334789648846972755677)
    ·
      refine ⟨1525625546118317614783379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4068334789648846972755677 1525625546118317614783379)
      ·
        refine ⟨2288438319177476422175069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525625546118317614783379 2288438319177476422175069)
        ·
          refine ⟨858164369691553658315651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2288438319177476422175069 858164369691553658315651)
          ·
            refine ⟨1287246554537330487473477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858164369691553658315651 1287246554537330487473477)
            ·
              refine ⟨241358728975749466401277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1287246554537330487473477 241358728975749466401277)
              ·
                refine ⟨90509523365906049900479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241358728975749466401277 90509523365906049900479)
                ·
                  rfl

theorem cell19_297450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_297450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297450 prefixEnd_297450 := by exact prefixLift 297450
  have htrace : WordTrace (prefixWord ++ tailWord_297450) baseStart_297450 baseEnd_297450 := by
    simpa [prefixWord, tailWord_297450, baseEnd_297450] using wordTrace_append hprefix tailTrace_297450
  have hstable : (prefixWord ++ tailWord_297450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297450).length < 2 ^ (prefixWord ++ tailWord_297450).sum := by decide
  have hdescent : baseEnd_297450 < baseStart_297450 := by decide
  rcases family_descends (prefixWord ++ tailWord_297450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297524 : List Nat := [2, 5, 1, 3, 2, 6]
def baseStart_297524 : Nat := 118140960795 + 297524 * 2 ^ 59
def prefixEnd_297524 : Nat := 4983230072969 + 3 ^ 40 * 297524 * 2
def baseEnd_297524 : Nat := 10059115604832867139537

theorem tailTrace_297524 : CollatzResearch.WordTrace tailWord_297524 prefixEnd_297524 10059115604832867139537 := by
  unfold tailWord_297524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425795887064417949437813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7234394516085890599250417 5425795887064417949437813)
  ·
    refine ⟨508668364412289182759795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5425795887064417949437813 508668364412289182759795)
    ·
      refine ⟨763002546618433774139693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508668364412289182759795 763002546618433774139693)
      ·
        refine ⟨286125954981912665302385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 763002546618433774139693 286125954981912665302385)
        ·
          refine ⟨214594466236434498976789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286125954981912665302385 214594466236434498976789)
          ·
            refine ⟨10059115604832867139537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 214594466236434498976789 10059115604832867139537)
            ·
              rfl

theorem cell19_297524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_297524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297524 prefixEnd_297524 := by exact prefixLift 297524
  have htrace : WordTrace (prefixWord ++ tailWord_297524) baseStart_297524 baseEnd_297524 := by
    simpa [prefixWord, tailWord_297524, baseEnd_297524] using wordTrace_append hprefix tailTrace_297524
  have hstable : (prefixWord ++ tailWord_297524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297524).length < 2 ^ (prefixWord ++ tailWord_297524).sum := by decide
  have hdescent : baseEnd_297524 < baseStart_297524 := by decide
  rcases family_descends (prefixWord ++ tailWord_297524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297530 : List Nat := [3, 1, 1, 1, 3, 10]
def baseStart_297530 : Nat := 118140960795 + 297530 * 2 ^ 59
def prefixEnd_297530 : Nat := 4983230072969 + 3 ^ 40 * 297530 * 2
def baseEnd_297530 : Nat := 10059318461387729791387

theorem tailTrace_297530 : CollatzResearch.WordTrace tailWord_297530 prefixEnd_297530 10059318461387729791387 := by
  unfold tailWord_297530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712952653026774730898511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7234540408071399282396029 2712952653026774730898511)
  ·
    refine ⟨4069428979540162096347767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2712952653026774730898511 4069428979540162096347767)
    ·
      refine ⟨6104143469310243144521651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4069428979540162096347767 6104143469310243144521651)
      ·
        refine ⟨9156215203965364716782477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6104143469310243144521651 9156215203965364716782477)
        ·
          refine ⟨3433580701487011768793429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9156215203965364716782477 3433580701487011768793429)
          ·
            refine ⟨10059318461387729791387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3433580701487011768793429 10059318461387729791387)
            ·
              rfl

theorem cell19_297530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_297530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297530 prefixEnd_297530 := by exact prefixLift 297530
  have htrace : WordTrace (prefixWord ++ tailWord_297530) baseStart_297530 baseEnd_297530 := by
    simpa [prefixWord, tailWord_297530, baseEnd_297530] using wordTrace_append hprefix tailTrace_297530
  have hstable : (prefixWord ++ tailWord_297530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297530).length < 2 ^ (prefixWord ++ tailWord_297530).sum := by decide
  have hdescent : baseEnd_297530 < baseStart_297530 := by decide
  rcases family_descends (prefixWord ++ tailWord_297530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297568 : List Nat := [2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_297568 : Nat := 118140960795 + 297568 * 2 ^ 59
def prefixEnd_297568 : Nat := 4983230072969 + 3 ^ 40 * 297568 * 2
def baseEnd_297568 : Nat := 90545428976116739277935

theorem tailTrace_297568 : CollatzResearch.WordTrace tailWord_297568 prefixEnd_297568 90545428976116739277935 := by
  unfold tailWord_297568
  simp only [CollatzResearch.WordTrace]
  refine ⟨5426598292984715706738679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7235464390646287608984905 5426598292984715706738679)
  ·
    refine ⟨8139897439477073560108019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5426598292984715706738679 8139897439477073560108019)
    ·
      refine ⟨12209846159215610340162029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8139897439477073560108019 12209846159215610340162029)
      ·
        refine ⟨4578692309705853877560761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12209846159215610340162029 4578692309705853877560761)
        ·
          refine ⟨3434019232279390408170571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4578692309705853877560761 3434019232279390408170571)
          ·
            refine ⟨5151028848419085612255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434019232279390408170571 5151028848419085612255857)
            ·
              refine ⟨3863271636314314209191893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5151028848419085612255857 3863271636314314209191893)
              ·
                refine ⟨90545428976116739277935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3863271636314314209191893 90545428976116739277935)
                ·
                  rfl

theorem cell19_297568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_297568 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297568 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297568 prefixEnd_297568 := by exact prefixLift 297568
  have htrace : WordTrace (prefixWord ++ tailWord_297568) baseStart_297568 baseEnd_297568 := by
    simpa [prefixWord, tailWord_297568, baseEnd_297568] using wordTrace_append hprefix tailTrace_297568
  have hstable : (prefixWord ++ tailWord_297568).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297568).length < 2 ^ (prefixWord ++ tailWord_297568).sum := by decide
  have hdescent : baseEnd_297568 < baseStart_297568 := by decide
  rcases family_descends (prefixWord ++ tailWord_297568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297625 : List Nat := [1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_297625 : Nat := 118140960795 + 297625 * 2 ^ 59
def prefixEnd_297625 : Nat := 4983230072969 + 3 ^ 40 * 297625 * 2
def baseEnd_297625 : Nat := 90562773211557496011113

theorem tailTrace_297625 : CollatzResearch.WordTrace tailWord_297625 prefixEnd_297625 90562773211557496011113 := by
  unfold tailWord_297625
  simp only [CollatzResearch.WordTrace]
  refine ⟨10855275546762930148302329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7236850364508620098868219 10855275546762930148302329)
  ·
    refine ⟨8141456660072197611226747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10855275546762930148302329 8141456660072197611226747)
    ·
      refine ⟨12212184990108296416840121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8141456660072197611226747 12212184990108296416840121)
      ·
        refine ⟨9159138742581222312630091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12212184990108296416840121 9159138742581222312630091)
        ·
          refine ⟨13738708113871833468945137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9159138742581222312630091 13738708113871833468945137)
          ·
            refine ⟨10304031085403875101708853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13738708113871833468945137 10304031085403875101708853)
            ·
              refine ⟨966002914256613290785205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10304031085403875101708853 966002914256613290785205)
              ·
                refine ⟨90562773211557496011113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966002914256613290785205 90562773211557496011113)
                ·
                  rfl

theorem cell19_297625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_297625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297625 prefixEnd_297625 := by exact prefixLift 297625
  have htrace : WordTrace (prefixWord ++ tailWord_297625) baseStart_297625 baseEnd_297625 := by
    simpa [prefixWord, tailWord_297625, baseEnd_297625] using wordTrace_append hprefix tailTrace_297625
  have hstable : (prefixWord ++ tailWord_297625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297625).length < 2 ^ (prefixWord ++ tailWord_297625).sum := by decide
  have hdescent : baseEnd_297625 < baseStart_297625 := by decide
  rcases family_descends (prefixWord ++ tailWord_297625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297661 : List Nat := [1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_297661 : Nat := 118140960795 + 297661 * 2 ^ 59
def prefixEnd_297661 : Nat := 4983230072969 + 3 ^ 40 * 297661 * 2
def baseEnd_297661 : Nat := 90573727465520079211015

theorem tailTrace_297661 : CollatzResearch.WordTrace tailWord_297661 prefixEnd_297661 90573727465520079211015 := by
  unfold tailWord_297661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856588574632508296612837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7237725716421672197741891 10856588574632508296612837)
  ·
    refine ⟨2035610357743595305614907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10856588574632508296612837 2035610357743595305614907)
    ·
      refine ⟨3053415536615392958422361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2035610357743595305614907 3053415536615392958422361)
      ·
        refine ⟨2290061652461544718816771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3053415536615392958422361 2290061652461544718816771)
        ·
          refine ⟨3435092478692317078225157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290061652461544718816771 3435092478692317078225157)
          ·
            refine ⟨644079839754809452167217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3435092478692317078225157 644079839754809452167217)
            ·
              refine ⟨483059879816107089125413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644079839754809452167217 483059879816107089125413)
              ·
                refine ⟨90573727465520079211015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483059879816107089125413 90573727465520079211015)
                ·
                  rfl

theorem cell19_297661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_297661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297661 prefixEnd_297661 := by exact prefixLift 297661
  have htrace : WordTrace (prefixWord ++ tailWord_297661) baseStart_297661 baseEnd_297661 := by
    simpa [prefixWord, tailWord_297661, baseEnd_297661] using wordTrace_append hprefix tailTrace_297661
  have hstable : (prefixWord ++ tailWord_297661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297661).length < 2 ^ (prefixWord ++ tailWord_297661).sum := by decide
  have hdescent : baseEnd_297661 < baseStart_297661 := by decide
  rcases family_descends (prefixWord ++ tailWord_297661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297663 : List Nat := [1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_297663 : Nat := 118140960795 + 297663 * 2 ^ 59
def prefixEnd_297663 : Nat := 4983230072969 + 3 ^ 40 * 297663 * 2
def baseEnd_297663 : Nat := 90574336035184667166565

theorem tailTrace_297663 : CollatzResearch.WordTrace tailWord_297663 prefixEnd_297663 90574336035184667166565 := by
  unfold tailWord_297663
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856661520625262638185643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7237774347083508425457095 10856661520625262638185643)
  ·
    refine ⟨16284992280937893957278465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10856661520625262638185643 16284992280937893957278465)
    ·
      refine ⟨12213744210703420467958849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16284992280937893957278465 12213744210703420467958849)
      ·
        refine ⟨9160308158027565350969137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12213744210703420467958849 9160308158027565350969137)
        ·
          refine ⟨6870231118520674013226853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9160308158027565350969137 6870231118520674013226853)
          ·
            refine ⟨1288168334722626377480035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6870231118520674013226853 1288168334722626377480035)
            ·
              refine ⟨1932252502083939566220053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288168334722626377480035 1932252502083939566220053)
              ·
                refine ⟨90574336035184667166565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1932252502083939566220053 90574336035184667166565)
                ·
                  rfl

theorem cell19_297663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_297663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297663 prefixEnd_297663 := by exact prefixLift 297663
  have htrace : WordTrace (prefixWord ++ tailWord_297663) baseStart_297663 baseEnd_297663 := by
    simpa [prefixWord, tailWord_297663, baseEnd_297663] using wordTrace_append hprefix tailTrace_297663
  have hstable : (prefixWord ++ tailWord_297663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297663).length < 2 ^ (prefixWord ++ tailWord_297663).sum := by decide
  have hdescent : baseEnd_297663 < baseStart_297663 := by decide
  rcases family_descends (prefixWord ++ tailWord_297663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297701 : List Nat := [1, 3, 1, 4, 1, 9]
def baseStart_297701 : Nat := 118140960795 + 297701 * 2 ^ 59
def prefixEnd_297701 : Nat := 4983230072969 + 3 ^ 40 * 297701 * 2
def baseEnd_297701 : Nat := 10065099873201315369113

theorem tailTrace_297701 : CollatzResearch.WordTrace tailWord_297701 prefixEnd_297701 10065099873201315369113 := by
  unfold tailWord_297701
  simp only [CollatzResearch.WordTrace]
  refine ⟨10858047494487595128068957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7238698329658396752045971 10858047494487595128068957)
  ·
    refine ⟨4071767810432848173025859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10858047494487595128068957 4071767810432848173025859)
    ·
      refine ⟨6107651715649272259538789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071767810432848173025859 6107651715649272259538789)
      ·
        refine ⟨1145184696684238548663523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6107651715649272259538789 1145184696684238548663523)
        ·
          refine ⟨1717777045026357822995285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145184696684238548663523 1717777045026357822995285)
          ·
            refine ⟨10065099873201315369113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1717777045026357822995285 10065099873201315369113)
            ·
              rfl

theorem cell19_297701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_297701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297701 prefixEnd_297701 := by exact prefixLift 297701
  have htrace : WordTrace (prefixWord ++ tailWord_297701) baseStart_297701 baseEnd_297701 := by
    simpa [prefixWord, tailWord_297701, baseEnd_297701] using wordTrace_append hprefix tailTrace_297701
  have hstable : (prefixWord ++ tailWord_297701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297701).length < 2 ^ (prefixWord ++ tailWord_297701).sum := by decide
  have hdescent : baseEnd_297701 < baseStart_297701 := by decide
  rcases family_descends (prefixWord ++ tailWord_297701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297735 : List Nat := [1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_297735 : Nat := 118140960795 + 297735 * 2 ^ 59
def prefixEnd_297735 : Nat := 4983230072969 + 3 ^ 40 * 297735 * 2
def baseEnd_297735 : Nat := 90596244543109833566369

theorem tailTrace_297735 : CollatzResearch.WordTrace tailWord_297735 prefixEnd_297735 90596244543109833566369 := by
  unfold tailWord_297735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859287576364418934806659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7239525050909612623204439 10859287576364418934806659)
  ·
    refine ⟨16288931364546628402209989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10859287576364418934806659 16288931364546628402209989)
    ·
      refine ⟨3054174630852492825414373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16288931364546628402209989 3054174630852492825414373)
      ·
        refine ⟨572657743284842404765195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3054174630852492825414373 572657743284842404765195)
        ·
          refine ⟨858986614927263607147793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572657743284842404765195 858986614927263607147793)
          ·
            refine ⟨644239961195447705360845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858986614927263607147793 644239961195447705360845)
            ·
              refine ⟨241589985448292889510317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 644239961195447705360845 241589985448292889510317)
              ·
                refine ⟨90596244543109833566369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241589985448292889510317 90596244543109833566369)
                ·
                  rfl

theorem cell19_297735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_297735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297735 prefixEnd_297735 := by exact prefixLift 297735
  have htrace : WordTrace (prefixWord ++ tailWord_297735) baseStart_297735 baseEnd_297735 := by
    simpa [prefixWord, tailWord_297735, baseEnd_297735] using wordTrace_append hprefix tailTrace_297735
  have hstable : (prefixWord ++ tailWord_297735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297735).length < 2 ^ (prefixWord ++ tailWord_297735).sum := by decide
  have hdescent : baseEnd_297735 < baseStart_297735 := by decide
  rcases family_descends (prefixWord ++ tailWord_297735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297777 : List Nat := [1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_297777 : Nat := 118140960795 + 297777 * 2 ^ 59
def prefixEnd_297777 : Nat := 4983230072969 + 3 ^ 40 * 297777 * 2
def baseEnd_297777 : Nat := 90609024506066180632921

theorem tailTrace_297777 : CollatzResearch.WordTrace tailWord_297777 prefixEnd_297777 90609024506066180632921 := by
  unfold tailWord_297777
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860819442212260107835585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7240546294808173405223723 10860819442212260107835585)
  ·
    refine ⟨8145614581659195080876689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10860819442212260107835585 8145614581659195080876689)
    ·
      refine ⟨6109210936244396310657517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8145614581659195080876689 6109210936244396310657517)
      ·
        refine ⟨2290954101091648616496569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6109210936244396310657517 2290954101091648616496569)
        ·
          refine ⟨1718215575818736462372427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2290954101091648616496569 1718215575818736462372427)
          ·
            refine ⟨2577323363728104693558641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718215575818736462372427 2577323363728104693558641)
            ·
              refine ⟨1932992522796078520168981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577323363728104693558641 1932992522796078520168981)
              ·
                refine ⟨90609024506066180632921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1932992522796078520168981 90609024506066180632921)
                ·
                  rfl

theorem cell19_297777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_297777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297777 prefixEnd_297777 := by exact prefixLift 297777
  have htrace : WordTrace (prefixWord ++ tailWord_297777) baseStart_297777 baseEnd_297777 := by
    simpa [prefixWord, tailWord_297777, baseEnd_297777] using wordTrace_append hprefix tailTrace_297777
  have hstable : (prefixWord ++ tailWord_297777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297777).length < 2 ^ (prefixWord ++ tailWord_297777).sum := by decide
  have hdescent : baseEnd_297777 < baseStart_297777 := by decide
  rcases family_descends (prefixWord ++ tailWord_297777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297790 : List Nat := [4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_297790 : Nat := 118140960795 + 297790 * 2 ^ 59
def prefixEnd_297790 : Nat := 4983230072969 + 3 ^ 40 * 297790 * 2
def baseEnd_297790 : Nat := 90612980208886002343997

theorem tailTrace_297790 : CollatzResearch.WordTrace tailWord_297790 prefixEnd_297790 90612980208886002343997 := by
  unfold tailWord_297790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357661698895645416007353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7240862394110108885372549 1357661698895645416007353)
  ·
    refine ⟨1018246274171734062005515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1357661698895645416007353 1018246274171734062005515)
    ·
      refine ⟨1527369411257601093008273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018246274171734062005515 1527369411257601093008273)
      ·
        refine ⟨1145527058443200819756205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1527369411257601093008273 1145527058443200819756205)
        ·
          refine ⟨429572646916200307408577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1145527058443200819756205 429572646916200307408577)
          ·
            refine ⟨322179485187150230556433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429572646916200307408577 322179485187150230556433)
            ·
              refine ⟨241634613890362672917325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322179485187150230556433 241634613890362672917325)
              ·
                refine ⟨90612980208886002343997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241634613890362672917325 90612980208886002343997)
                ·
                  rfl

theorem cell19_297790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_297790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297790 prefixEnd_297790 := by exact prefixLift 297790
  have htrace : WordTrace (prefixWord ++ tailWord_297790) baseStart_297790 baseEnd_297790 := by
    simpa [prefixWord, tailWord_297790, baseEnd_297790] using wordTrace_append hprefix tailTrace_297790
  have hstable : (prefixWord ++ tailWord_297790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297790).length < 2 ^ (prefixWord ++ tailWord_297790).sum := by decide
  have hdescent : baseEnd_297790 < baseStart_297790 := by decide
  rcases family_descends (prefixWord ++ tailWord_297790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297815 : List Nat := [1, 1, 3, 2, 4, 1, 7]
def baseStart_297815 : Nat := 118140960795 + 297815 * 2 ^ 59
def prefixEnd_297815 : Nat := 4983230072969 + 3 ^ 40 * 297815 * 2
def baseEnd_297815 : Nat := 30206862443231117262791

theorem tailTrace_297815 : CollatzResearch.WordTrace tailWord_297815 prefixEnd_297815 30206862443231117262791 := by
  unfold tailWord_297815
  simp only [CollatzResearch.WordTrace]
  refine ⟨10862205416074592597718899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7241470277383061731812599 10862205416074592597718899)
  ·
    refine ⟨16293308124111888896578349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10862205416074592597718899 16293308124111888896578349)
    ·
      refine ⟨6109990546541958336216881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16293308124111888896578349 6109990546541958336216881)
      ·
        refine ⟨4582492909906468752162661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6109990546541958336216881 4582492909906468752162661)
        ·
          refine ⟨859217420607462891030499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4582492909906468752162661 859217420607462891030499)
          ·
            refine ⟨1288826130911194336545749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859217420607462891030499 1288826130911194336545749)
            ·
              refine ⟨30206862443231117262791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1288826130911194336545749 30206862443231117262791)
              ·
                rfl

theorem cell19_297815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_297815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297815 prefixEnd_297815 := by exact prefixLift 297815
  have htrace : WordTrace (prefixWord ++ tailWord_297815) baseStart_297815 baseEnd_297815 := by
    simpa [prefixWord, tailWord_297815, baseEnd_297815] using wordTrace_append hprefix tailTrace_297815
  have hstable : (prefixWord ++ tailWord_297815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297815).length < 2 ^ (prefixWord ++ tailWord_297815).sum := by decide
  have hdescent : baseEnd_297815 < baseStart_297815 := by decide
  rcases family_descends (prefixWord ++ tailWord_297815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297832 : List Nat := [2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_297832 : Nat := 118140960795 + 297832 * 2 ^ 59
def prefixEnd_297832 : Nat := 4983230072969 + 3 ^ 40 * 297832 * 2
def baseEnd_297832 : Nat := 90625760171842349410549

theorem tailTrace_297832 : CollatzResearch.WordTrace tailWord_297832 prefixEnd_297832 90625760171842349410549 := by
  unfold tailWord_297832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5431412728506502250543875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7241883638008669667391833 5431412728506502250543875)
  ·
    refine ⟨8147119092759753375815813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5431412728506502250543875 8147119092759753375815813)
    ·
      refine ⟨1527584829892453757965465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8147119092759753375815813 1527584829892453757965465)
      ·
        refine ⟨1145688622419340318474099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1527584829892453757965465 1145688622419340318474099)
        ·
          refine ⟨1718532933629010477711149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145688622419340318474099 1718532933629010477711149)
          ·
            refine ⟨644449850110878929141681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1718532933629010477711149 644449850110878929141681)
            ·
              refine ⟨483337387583159196856261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644449850110878929141681 483337387583159196856261)
              ·
                refine ⟨90625760171842349410549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483337387583159196856261 90625760171842349410549)
                ·
                  rfl

theorem cell19_297832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_297832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297832 prefixEnd_297832 := by exact prefixLift 297832
  have htrace : WordTrace (prefixWord ++ tailWord_297832) baseStart_297832 baseEnd_297832 := by
    simpa [prefixWord, tailWord_297832, baseEnd_297832] using wordTrace_append hprefix tailTrace_297832
  have hstable : (prefixWord ++ tailWord_297832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297832).length < 2 ^ (prefixWord ++ tailWord_297832).sum := by decide
  have hdescent : baseEnd_297832 < baseStart_297832 := by decide
  rcases family_descends (prefixWord ++ tailWord_297832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297853 : List Nat := [1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_297853 : Nat := 118140960795 + 297853 * 2 ^ 59
def prefixEnd_297853 : Nat := 4983230072969 + 3 ^ 40 * 297853 * 2
def baseEnd_297853 : Nat := 90632150153320522943825

theorem tailTrace_297853 : CollatzResearch.WordTrace tailWord_297853 prefixEnd_297853 90632150153320522943825 := by
  unfold tailWord_297853
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863591389936925087602213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7242394259957950058401475 10863591389936925087602213)
  ·
    refine ⟨2036923385613173453925415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10863591389936925087602213 2036923385613173453925415)
    ·
      refine ⟨3055385078419760180888123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036923385613173453925415 3055385078419760180888123)
      ·
        refine ⟨4583077617629640271332185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3055385078419760180888123 4583077617629640271332185)
        ·
          refine ⟨3437308213222230203499139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4583077617629640271332185 3437308213222230203499139)
          ·
            refine ⟨5155962319833345305248709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437308213222230203499139 5155962319833345305248709)
            ·
              refine ⟨966742934968752244734133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5155962319833345305248709 966742934968752244734133)
              ·
                refine ⟨90632150153320522943825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966742934968752244734133 90632150153320522943825)
                ·
                  rfl

theorem cell19_297853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_297853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297853 prefixEnd_297853 := by exact prefixLift 297853
  have htrace : WordTrace (prefixWord ++ tailWord_297853) baseStart_297853 baseEnd_297853 := by
    simpa [prefixWord, tailWord_297853, baseEnd_297853] using wordTrace_append hprefix tailTrace_297853
  have hstable : (prefixWord ++ tailWord_297853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297853).length < 2 ^ (prefixWord ++ tailWord_297853).sum := by decide
  have hdescent : baseEnd_297853 < baseStart_297853 := by decide
  rcases family_descends (prefixWord ++ tailWord_297853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297889 : List Nat := [1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_297889 : Nat := 118140960795 + 297889 * 2 ^ 59
def prefixEnd_297889 : Nat := 4983230072969 + 3 ^ 40 * 297889 * 2
def baseEnd_297889 : Nat := 90643104407283106143727

theorem tailTrace_297889 : CollatzResearch.WordTrace tailWord_297889 prefixEnd_297889 90643104407283106143727 := by
  unfold tailWord_297889
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864904417806503235912721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7243269611871002157275147 10864904417806503235912721)
  ·
    refine ⟨8148678313354877426934541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10864904417806503235912721 8148678313354877426934541)
    ·
      refine ⟨3055754367508079035100453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8148678313354877426934541 3055754367508079035100453)
      ·
        refine ⟨572953943907764819081335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3055754367508079035100453 572953943907764819081335)
        ·
          refine ⟨859430915861647228622003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572953943907764819081335 859430915861647228622003)
          ·
            refine ⟨1289146373792470842933005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859430915861647228622003 1289146373792470842933005)
            ·
              refine ⟨483429890172176566099877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1289146373792470842933005 483429890172176566099877)
              ·
                refine ⟨90643104407283106143727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483429890172176566099877 90643104407283106143727)
                ·
                  rfl

theorem cell19_297889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_297889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297889 prefixEnd_297889 := by exact prefixLift 297889
  have htrace : WordTrace (prefixWord ++ tailWord_297889) baseStart_297889 baseEnd_297889 := by
    simpa [prefixWord, tailWord_297889, baseEnd_297889] using wordTrace_append hprefix tailTrace_297889
  have hstable : (prefixWord ++ tailWord_297889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297889).length < 2 ^ (prefixWord ++ tailWord_297889).sum := by decide
  have hdescent : baseEnd_297889 < baseStart_297889 := by decide
  rcases family_descends (prefixWord ++ tailWord_297889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297891 : List Nat := [1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_297891 : Nat := 118140960795 + 297891 * 2 ^ 59
def prefixEnd_297891 : Nat := 4983230072969 + 3 ^ 40 * 297891 * 2
def baseEnd_297891 : Nat := 90643712976947694099277

theorem tailTrace_297891 : CollatzResearch.WordTrace tailWord_297891 prefixEnd_297891 90643712976947694099277 := by
  unfold tailWord_297891
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864977363799257577485527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7243318242532838384990351 10864977363799257577485527)
  ·
    refine ⟨16297466045698886366228291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10864977363799257577485527 16297466045698886366228291)
    ·
      refine ⟨24446199068548329549342437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16297466045698886366228291 24446199068548329549342437)
      ·
        refine ⟨4583662325352811790501707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24446199068548329549342437 4583662325352811790501707)
        ·
          refine ⟨6875493488029217685752561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4583662325352811790501707 6875493488029217685752561)
          ·
            refine ⟨5156620116021913264314421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6875493488029217685752561 5156620116021913264314421)
            ·
              refine ⟨483433135877054368529477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5156620116021913264314421 483433135877054368529477)
              ·
                refine ⟨90643712976947694099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483433135877054368529477 90643712976947694099277)
                ·
                  rfl

theorem cell19_297891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_297891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297891 prefixEnd_297891 := by exact prefixLift 297891
  have htrace : WordTrace (prefixWord ++ tailWord_297891) baseStart_297891 baseEnd_297891 := by
    simpa [prefixWord, tailWord_297891, baseEnd_297891] using wordTrace_append hprefix tailTrace_297891
  have hstable : (prefixWord ++ tailWord_297891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297891).length < 2 ^ (prefixWord ++ tailWord_297891).sum := by decide
  have hdescent : baseEnd_297891 < baseStart_297891 := by decide
  rcases family_descends (prefixWord ++ tailWord_297891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297967 : List Nat := [1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_297967 : Nat := 118140960795 + 297967 * 2 ^ 59
def prefixEnd_297967 : Nat := 4983230072969 + 3 ^ 40 * 297967 * 2
def baseEnd_297967 : Nat := 90666838624202036410181

theorem tailTrace_297967 : CollatzResearch.WordTrace tailWord_297967 prefixEnd_297967 90666838624202036410181 := by
  unfold tailWord_297967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10867749311523922557252155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7245166207682615038168103 10867749311523922557252155)
  ·
    refine ⟨16301623967285883835878233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10867749311523922557252155 16301623967285883835878233)
    ·
      refine ⟨12226217975464412876908675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16301623967285883835878233 12226217975464412876908675)
      ·
        refine ⟨18339326963196619315363013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12226217975464412876908675 18339326963196619315363013)
        ·
          refine ⟨3438623805599366121630565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18339326963196619315363013 3438623805599366121630565)
          ·
            refine ⟨644741963549881147805731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3438623805599366121630565 644741963549881147805731)
            ·
              refine ⟨967112945324821721708597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644741963549881147805731 967112945324821721708597)
              ·
                refine ⟨90666838624202036410181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 967112945324821721708597 90666838624202036410181)
                ·
                  rfl

theorem cell19_297967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_297967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297967 prefixEnd_297967 := by exact prefixLift 297967
  have htrace : WordTrace (prefixWord ++ tailWord_297967) baseStart_297967 baseEnd_297967 := by
    simpa [prefixWord, tailWord_297967, baseEnd_297967] using wordTrace_append hprefix tailTrace_297967
  have hstable : (prefixWord ++ tailWord_297967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297967).length < 2 ^ (prefixWord ++ tailWord_297967).sum := by decide
  have hdescent : baseEnd_297967 < baseStart_297967 := by decide
  rcases family_descends (prefixWord ++ tailWord_297967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297982 : List Nat := [4, 2, 2, 2, 2, 2, 5]
def baseStart_297982 : Nat := 118140960795 + 297982 * 2 ^ 59
def prefixEnd_297982 : Nat := 4983230072969 + 3 ^ 40 * 297982 * 2
def baseEnd_297982 : Nat := 30223800965562148692269

theorem tailTrace_297982 : CollatzResearch.WordTrace tailWord_297982 prefixEnd_297982 30223800965562148692269 := by
  unfold tailWord_297982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358537050808697514881025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7245530937646386746032133 1358537050808697514881025)
  ·
    refine ⟨1018902788106523136160769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1358537050808697514881025 1018902788106523136160769)
    ·
      refine ⟨764177091079892352120577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1018902788106523136160769 764177091079892352120577)
      ·
        refine ⟨573132818309919264090433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 764177091079892352120577 573132818309919264090433)
        ·
          refine ⟨429849613732439448067825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573132818309919264090433 429849613732439448067825)
          ·
            refine ⟨322387210299329586050869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429849613732439448067825 322387210299329586050869)
            ·
              refine ⟨30223800965562148692269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322387210299329586050869 30223800965562148692269)
              ·
                rfl

theorem cell19_297982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_297982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_297982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_297982 prefixEnd_297982 := by exact prefixLift 297982
  have htrace : WordTrace (prefixWord ++ tailWord_297982) baseStart_297982 baseEnd_297982 := by
    simpa [prefixWord, tailWord_297982, baseEnd_297982] using wordTrace_append hprefix tailTrace_297982
  have hstable : (prefixWord ++ tailWord_297982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297982).length < 2 ^ (prefixWord ++ tailWord_297982).sum := by decide
  have hdescent : baseEnd_297982 < baseStart_297982 := by decide
  rcases family_descends (prefixWord ++ tailWord_297982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298005 : List Nat := [1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_298005 : Nat := 118140960795 + 298005 * 2 ^ 59
def prefixEnd_298005 : Nat := 4983230072969 + 3 ^ 40 * 298005 * 2
def baseEnd_298005 : Nat := 90678401447829207565633

theorem tailTrace_298005 : CollatzResearch.WordTrace tailWord_298005 prefixEnd_298005 90678401447829207565633 := by
  unfold tailWord_298005
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869135285386255047135469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7246090190257503364756979 10869135285386255047135469)
  ·
    refine ⟨4075925732019845642675801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10869135285386255047135469 4075925732019845642675801)
    ·
      refine ⟨3056944299014884232006851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4075925732019845642675801 3056944299014884232006851)
      ·
        refine ⟨4585416448522326348010277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056944299014884232006851 4585416448522326348010277)
        ·
          refine ⟨859765584097936190251927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4585416448522326348010277 859765584097936190251927)
          ·
            refine ⟨1289648376146904285377891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859765584097936190251927 1289648376146904285377891)
            ·
              refine ⟨1934472564220356428066837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289648376146904285377891 1934472564220356428066837)
              ·
                refine ⟨90678401447829207565633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1934472564220356428066837 90678401447829207565633)
                ·
                  rfl

theorem cell19_298005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_298005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298005 prefixEnd_298005 := by exact prefixLift 298005
  have htrace : WordTrace (prefixWord ++ tailWord_298005) baseStart_298005 baseEnd_298005 := by
    simpa [prefixWord, tailWord_298005, baseEnd_298005] using wordTrace_append hprefix tailTrace_298005
  have hstable : (prefixWord ++ tailWord_298005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298005).length < 2 ^ (prefixWord ++ tailWord_298005).sum := by decide
  have hdescent : baseEnd_298005 < baseStart_298005 := by decide
  rcases family_descends (prefixWord ++ tailWord_298005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298136 : List Nat := [2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_298136 : Nat := 118140960795 + 298136 * 2 ^ 59
def prefixEnd_298136 : Nat := 4983230072969 + 3 ^ 40 * 298136 * 2
def baseEnd_298136 : Nat := 90718262760859718654165

theorem tailTrace_298136 : CollatzResearch.WordTrace tailWord_298136 prefixEnd_298136 90718262760859718654165 := by
  unfold tailWord_298136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436956623955832210077131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7249275498607776280102841 5436956623955832210077131)
  ·
    refine ⟨8155434935933748315115697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5436956623955832210077131 8155434935933748315115697)
    ·
      refine ⟨6116576201950311236336773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8155434935933748315115697 6116576201950311236336773)
      ·
        refine ⟨1146858037865683356813145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6116576201950311236336773 1146858037865683356813145)
        ·
          refine ⟨860143528399262517609859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146858037865683356813145 860143528399262517609859)
          ·
            refine ⟨1290215292598893776414789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860143528399262517609859 1290215292598893776414789)
            ·
              refine ⟨241915367362292583077773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1290215292598893776414789 241915367362292583077773)
              ·
                refine ⟨90718262760859718654165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241915367362292583077773 90718262760859718654165)
                ·
                  rfl

theorem cell19_298136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_298136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298136 prefixEnd_298136 := by exact prefixLift 298136
  have htrace : WordTrace (prefixWord ++ tailWord_298136) baseStart_298136 baseEnd_298136 := by
    simpa [prefixWord, tailWord_298136, baseEnd_298136] using wordTrace_append hprefix tailTrace_298136
  have hstable : (prefixWord ++ tailWord_298136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298136).length < 2 ^ (prefixWord ++ tailWord_298136).sum := by decide
  have hdescent : baseEnd_298136 < baseStart_298136 := by decide
  rcases family_descends (prefixWord ++ tailWord_298136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298159 : List Nat := [1, 1, 2, 1, 2, 3, 9]
def baseStart_298159 : Nat := 118140960795 + 298159 * 2 ^ 59
def prefixEnd_298159 : Nat := 4983230072969 + 3 ^ 40 * 298159 * 2
def baseEnd_298159 : Nat := 30241753770667493380997

theorem tailTrace_298159 : CollatzResearch.WordTrace tailWord_298159 prefixEnd_298159 30241753770667493380997 := by
  unfold tailWord_298159
  simp only [CollatzResearch.WordTrace]
  refine ⟨10874752126828339348241531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7249834751218892898827687 10874752126828339348241531)
  ·
    refine ⟨16312128190242509022362297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10874752126828339348241531 16312128190242509022362297)
    ·
      refine ⟨12234096142681881766771723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16312128190242509022362297 12234096142681881766771723)
      ·
        refine ⟨18351144214022822650157585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12234096142681881766771723 18351144214022822650157585)
        ·
          refine ⟨13763358160517116987618189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18351144214022822650157585 13763358160517116987618189)
          ·
            refine ⟨5161259310193918870356821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13763358160517116987618189 5161259310193918870356821)
            ·
              refine ⟨30241753770667493380997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5161259310193918870356821 30241753770667493380997)
              ·
                rfl

theorem cell19_298159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_298159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298159 prefixEnd_298159 := by exact prefixLift 298159
  have htrace : WordTrace (prefixWord ++ tailWord_298159) baseStart_298159 baseEnd_298159 := by
    simpa [prefixWord, tailWord_298159, baseEnd_298159] using wordTrace_append hprefix tailTrace_298159
  have hstable : (prefixWord ++ tailWord_298159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298159).length < 2 ^ (prefixWord ++ tailWord_298159).sum := by decide
  have hdescent : baseEnd_298159 < baseStart_298159 := by decide
  rcases family_descends (prefixWord ++ tailWord_298159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298174 : List Nat := [4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_298174 : Nat := 118140960795 + 298174 * 2 ^ 59
def prefixEnd_298174 : Nat := 4983230072969 + 3 ^ 40 * 298174 * 2
def baseEnd_298174 : Nat := 90729825584486889809617

theorem tailTrace_298174 : CollatzResearch.WordTrace tailWord_298174 prefixEnd_298174 90729825584486889809617 := by
  unfold tailWord_298174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359412402721749613754697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7250199481182664606691717 1359412402721749613754697)
  ·
    refine ⟨1019559302041312210316023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1359412402721749613754697 1019559302041312210316023)
    ·
      refine ⟨1529338953061968315474035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019559302041312210316023 1529338953061968315474035)
      ·
        refine ⟨2294008429592952473211053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529338953061968315474035 2294008429592952473211053)
        ·
          refine ⟨860253161097357177454145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2294008429592952473211053 860253161097357177454145)
          ·
            refine ⟨645189870823017883090609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860253161097357177454145 645189870823017883090609)
            ·
              refine ⟨483892403117263412317957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645189870823017883090609 483892403117263412317957)
              ·
                refine ⟨90729825584486889809617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483892403117263412317957 90729825584486889809617)
                ·
                  rfl

theorem cell19_298174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_298174 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298174 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298174 prefixEnd_298174 := by exact prefixLift 298174
  have htrace : WordTrace (prefixWord ++ tailWord_298174) baseStart_298174 baseEnd_298174 := by
    simpa [prefixWord, tailWord_298174, baseEnd_298174] using wordTrace_append hprefix tailTrace_298174
  have hstable : (prefixWord ++ tailWord_298174).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298174).length < 2 ^ (prefixWord ++ tailWord_298174).sum := by decide
  have hdescent : baseEnd_298174 < baseStart_298174 := by decide
  rcases family_descends (prefixWord ++ tailWord_298174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298271 : List Nat := [1, 1, 2, 4, 4, 1, 6]
def baseStart_298271 : Nat := 118140960795 + 298271 * 2 ^ 59
def prefixEnd_298271 : Nat := 4983230072969 + 3 ^ 40 * 298271 * 2
def baseEnd_298271 : Nat := 30253113737739801884599

theorem tailTrace_298271 : CollatzResearch.WordTrace tailWord_298271 prefixEnd_298271 30253113737739801884599 := by
  unfold tailWord_298271
  simp only [CollatzResearch.WordTrace]
  refine ⟨10878837102422582476318667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7252558068281721650879111 10878837102422582476318667)
  ·
    refine ⟨16318255653633873714478001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10878837102422582476318667 16318255653633873714478001)
    ·
      refine ⟨12238691740225405285858501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16318255653633873714478001 12238691740225405285858501)
      ·
        refine ⟨2294754701292263491098469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12238691740225405285858501 2294754701292263491098469)
        ·
          refine ⟨430266506492299404580963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2294754701292263491098469 430266506492299404580963)
          ·
            refine ⟨645399759738449106871445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430266506492299404580963 645399759738449106871445)
            ·
              refine ⟨30253113737739801884599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 645399759738449106871445 30253113737739801884599)
              ·
                rfl

theorem cell19_298271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_298271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298271 prefixEnd_298271 := by exact prefixLift 298271
  have htrace : WordTrace (prefixWord ++ tailWord_298271) baseStart_298271 baseEnd_298271 := by
    simpa [prefixWord, tailWord_298271, baseEnd_298271] using wordTrace_append hprefix tailTrace_298271
  have hstable : (prefixWord ++ tailWord_298271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298271).length < 2 ^ (prefixWord ++ tailWord_298271).sum := by decide
  have hdescent : baseEnd_298271 < baseStart_298271 := by decide
  rcases family_descends (prefixWord ++ tailWord_298271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298305 : List Nat := [1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_298305 : Nat := 118140960795 + 298305 * 2 ^ 59
def prefixEnd_298305 : Nat := 4983230072969 + 3 ^ 40 * 298305 * 2
def baseEnd_298305 : Nat := 90769686897517400898149

theorem tailTrace_298305 : CollatzResearch.WordTrace tailWord_298305 prefixEnd_298305 90769686897517400898149 := by
  unfold tailWord_298305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880077184299406283056369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7253384789532937522037579 10880077184299406283056369)
  ·
    refine ⟨8160057888224554712292277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10880077184299406283056369 8160057888224554712292277)
    ·
      refine ⟨765005427021052004277401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8160057888224554712292277 765005427021052004277401)
      ·
        refine ⟨573754070265789003208051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 765005427021052004277401 573754070265789003208051)
        ·
          refine ⟨860631105398683504812077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573754070265789003208051 860631105398683504812077)
          ·
            refine ⟨322736664524506314304529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 860631105398683504812077 322736664524506314304529)
            ·
              refine ⟨242052498393379735728397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322736664524506314304529 242052498393379735728397)
              ·
                refine ⟨90769686897517400898149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242052498393379735728397 90769686897517400898149)
                ·
                  rfl

theorem cell19_298305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_298305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298305 prefixEnd_298305 := by exact prefixLift 298305
  have htrace : WordTrace (prefixWord ++ tailWord_298305) baseStart_298305 baseEnd_298305 := by
    simpa [prefixWord, tailWord_298305, baseEnd_298305] using wordTrace_append hprefix tailTrace_298305
  have hstable : (prefixWord ++ tailWord_298305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298305).length < 2 ^ (prefixWord ++ tailWord_298305).sum := by decide
  have hdescent : baseEnd_298305 < baseStart_298305 := by decide
  rcases family_descends (prefixWord ++ tailWord_298305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298330 : List Nat := [3, 1, 1, 2, 1, 2, 9]
def baseStart_298330 : Nat := 118140960795 + 298330 * 2 ^ 59
def prefixEnd_298330 : Nat := 4983230072969 + 3 ^ 40 * 298330 * 2
def baseEnd_298330 : Nat := 30259098006108250114175

theorem tailTrace_298330 : CollatzResearch.WordTrace tailWord_298330 prefixEnd_298330 30259098006108250114175 := by
  unfold tailWord_298330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720247252302208888179111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7253992672805890368477629 2720247252302208888179111)
  ·
    refine ⟨4080370878453313332268667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2720247252302208888179111 4080370878453313332268667)
    ·
      refine ⟨6120556317679969998403001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4080370878453313332268667 6120556317679969998403001)
      ·
        refine ⟨4590417238259977498802251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6120556317679969998403001 4590417238259977498802251)
        ·
          refine ⟨6885625857389966248203377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4590417238259977498802251 6885625857389966248203377)
          ·
            refine ⟨5164219393042474686152533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6885625857389966248203377 5164219393042474686152533)
            ·
              refine ⟨30259098006108250114175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5164219393042474686152533 30259098006108250114175)
              ·
                rfl

theorem cell19_298330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_298330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298330 prefixEnd_298330 := by exact prefixLift 298330
  have htrace : WordTrace (prefixWord ++ tailWord_298330) baseStart_298330 baseEnd_298330 := by
    simpa [prefixWord, tailWord_298330, baseEnd_298330] using wordTrace_append hprefix tailTrace_298330
  have hstable : (prefixWord ++ tailWord_298330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298330).length < 2 ^ (prefixWord ++ tailWord_298330).sum := by decide
  have hdescent : baseEnd_298330 < baseStart_298330 := by decide
  rcases family_descends (prefixWord ++ tailWord_298330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298398 : List Nat := [4, 3, 1, 2, 3, 1, 1, 4]
def baseStart_298398 : Nat := 118140960795 + 298398 * 2 ^ 59
def prefixEnd_298398 : Nat := 4983230072969 + 3 ^ 40 * 298398 * 2
def baseEnd_298398 : Nat := 90797985386920740831229

theorem tailTrace_298398 : CollatzResearch.WordTrace tailWord_298398 prefixEnd_298398 90797985386920740831229 := by
  unfold tailWord_298398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360433646620310395773981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7255646115308322110794565 1360433646620310395773981)
  ·
    refine ⟨510162617482616398415243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1360433646620310395773981 510162617482616398415243)
    ·
      refine ⟨765243926223924597622865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510162617482616398415243 765243926223924597622865)
      ·
        refine ⟨573932944667943448217149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 765243926223924597622865 573932944667943448217149)
        ·
          refine ⟨215224854250478793081431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573932944667943448217149 215224854250478793081431)
          ·
            refine ⟨322837281375718189622147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215224854250478793081431 322837281375718189622147)
            ·
              refine ⟨484255922063577284433221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322837281375718189622147 484255922063577284433221)
              ·
                refine ⟨90797985386920740831229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484255922063577284433221 90797985386920740831229)
                ·
                  rfl

theorem cell19_298398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_298398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298398 prefixEnd_298398 := by exact prefixLift 298398
  have htrace : WordTrace (prefixWord ++ tailWord_298398) baseStart_298398 baseEnd_298398 := by
    simpa [prefixWord, tailWord_298398, baseEnd_298398] using wordTrace_append hprefix tailTrace_298398
  have hstable : (prefixWord ++ tailWord_298398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298398).length < 2 ^ (prefixWord ++ tailWord_298398).sum := by decide
  have hdescent : baseEnd_298398 < baseStart_298398 := by decide
  rcases family_descends (prefixWord ++ tailWord_298398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298402 : List Nat := [3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_298402 : Nat := 118140960795 + 298402 * 2 ^ 59
def prefixEnd_298402 : Nat := 4983230072969 + 3 ^ 40 * 298402 * 2
def baseEnd_298402 : Nat := 90799202526249916742329

theorem tailTrace_298402 : CollatzResearch.WordTrace tailWord_298402 prefixEnd_298402 90799202526249916742329 := by
  unfold tailWord_298402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720903766236997962334365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7255743376631994566224973 2720903766236997962334365)
  ·
    refine ⟨1020338912338874235875387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2720903766236997962334365 1020338912338874235875387)
    ·
      refine ⟨1530508368508311353813081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020338912338874235875387 1530508368508311353813081)
      ·
        refine ⟨1147881276381233515359811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1530508368508311353813081 1147881276381233515359811)
        ·
          refine ⟨1721821914571850273039717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147881276381233515359811 1721821914571850273039717)
          ·
            refine ⟨322841608982221926194947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1721821914571850273039717 322841608982221926194947)
            ·
              refine ⟨484262413473332889292421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322841608982221926194947 484262413473332889292421)
              ·
                refine ⟨90799202526249916742329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484262413473332889292421 90799202526249916742329)
                ·
                  rfl

theorem cell19_298402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_298402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298402 prefixEnd_298402 := by exact prefixLift 298402
  have htrace : WordTrace (prefixWord ++ tailWord_298402) baseStart_298402 baseEnd_298402 := by
    simpa [prefixWord, tailWord_298402, baseEnd_298402] using wordTrace_append hprefix tailTrace_298402
  have hstable : (prefixWord ++ tailWord_298402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298402).length < 2 ^ (prefixWord ++ tailWord_298402).sum := by decide
  have hdescent : baseEnd_298402 < baseStart_298402 := by decide
  rcases family_descends (prefixWord ++ tailWord_298402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298421 : List Nat := [1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_298421 : Nat := 118140960795 + 298421 * 2 ^ 59
def prefixEnd_298421 : Nat := 4983230072969 + 3 ^ 40 * 298421 * 2
def baseEnd_298421 : Nat := 90804983938063502320055

theorem tailTrace_298421 : CollatzResearch.WordTrace tailWord_298421 prefixEnd_298421 90804983938063502320055 := by
  unfold tailWord_298421
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884308051879158094279117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7256205367919438729519411 10884308051879158094279117)
  ·
    refine ⟨4081615519454684285354669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10884308051879158094279117 4081615519454684285354669)
    ·
      refine ⟨1530605819795506607008001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4081615519454684285354669 1530605819795506607008001)
      ·
        refine ⟨1147954364846629955256001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1530605819795506607008001 1147954364846629955256001)
        ·
          refine ⟨860965773634972466442001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147954364846629955256001 860965773634972466442001)
          ·
            refine ⟨645724330226229349831501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860965773634972466442001 645724330226229349831501)
            ·
              refine ⟨242146623834836006186813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 645724330226229349831501 242146623834836006186813)
              ·
                refine ⟨90804983938063502320055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242146623834836006186813 90804983938063502320055)
                ·
                  rfl

theorem cell19_298421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_298421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298421 prefixEnd_298421 := by exact prefixLift 298421
  have htrace : WordTrace (prefixWord ++ tailWord_298421) baseStart_298421 baseEnd_298421 := by
    simpa [prefixWord, tailWord_298421, baseEnd_298421] using wordTrace_append hprefix tailTrace_298421
  have hstable : (prefixWord ++ tailWord_298421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298421).length < 2 ^ (prefixWord ++ tailWord_298421).sum := by decide
  have hdescent : baseEnd_298421 < baseStart_298421 := by decide
  rcases family_descends (prefixWord ++ tailWord_298421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298423 : List Nat := [1, 1, 3, 1, 3, 2, 5, 3]
def baseStart_298423 : Nat := 118140960795 + 298423 * 2 ^ 59
def prefixEnd_298423 : Nat := 4983230072969 + 3 ^ 40 * 298423 * 2
def baseEnd_298423 : Nat := 90805592507728090275605

theorem tailTrace_298423 : CollatzResearch.WordTrace tailWord_298423 prefixEnd_298423 90805592507728090275605 := by
  unfold tailWord_298423
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884380997871912435851923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7256253998581274957234615 10884380997871912435851923)
  ·
    refine ⟨16326571496807868653777885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10884380997871912435851923 16326571496807868653777885)
    ·
      refine ⟨6122464311302950745166707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16326571496807868653777885 6122464311302950745166707)
      ·
        refine ⟨9183696466954426117750061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122464311302950745166707 9183696466954426117750061)
        ·
          refine ⟨3443886175107909794156273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9183696466954426117750061 3443886175107909794156273)
          ·
            refine ⟨2582914631330932345617205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3443886175107909794156273 2582914631330932345617205)
            ·
              refine ⟨242148246687274907401613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2582914631330932345617205 242148246687274907401613)
              ·
                refine ⟨90805592507728090275605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242148246687274907401613 90805592507728090275605)
                ·
                  rfl

theorem cell19_298423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_298423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298423 prefixEnd_298423 := by exact prefixLift 298423
  have htrace : WordTrace (prefixWord ++ tailWord_298423) baseStart_298423 baseEnd_298423 := by
    simpa [prefixWord, tailWord_298423, baseEnd_298423] using wordTrace_append hprefix tailTrace_298423
  have hstable : (prefixWord ++ tailWord_298423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298423).length < 2 ^ (prefixWord ++ tailWord_298423).sum := by decide
  have hdescent : baseEnd_298423 < baseStart_298423 := by decide
  rcases family_descends (prefixWord ++ tailWord_298423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298463 : List Nat := [1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_298463 : Nat := 118140960795 + 298463 * 2 ^ 59
def prefixEnd_298463 : Nat := 4983230072969 + 3 ^ 40 * 298463 * 2
def baseEnd_298463 : Nat := 90817763901019849386607

theorem tailTrace_298463 : CollatzResearch.WordTrace tailWord_298463 prefixEnd_298463 90817763901019849386607 := by
  unfold tailWord_298463
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885839917726999267308043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7257226611817999511538695 10885839917726999267308043)
  ·
    refine ⟨16328759876590498900962065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10885839917726999267308043 16328759876590498900962065)
    ·
      refine ⟨12246569907442874175721549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16328759876590498900962065 12246569907442874175721549)
      ·
        refine ⟨4592463715291077815895581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12246569907442874175721549 4592463715291077815895581)
        ·
          refine ⟨1722173893234154180960843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4592463715291077815895581 1722173893234154180960843)
          ·
            refine ⟨2583260839851231271441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722173893234154180960843 2583260839851231271441265)
            ·
              refine ⟨1937445629888423453580949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583260839851231271441265 1937445629888423453580949)
              ·
                refine ⟨90817763901019849386607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1937445629888423453580949 90817763901019849386607)
                ·
                  rfl

theorem cell19_298463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_298463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298463 prefixEnd_298463 := by exact prefixLift 298463
  have htrace : WordTrace (prefixWord ++ tailWord_298463) baseStart_298463 baseEnd_298463 := by
    simpa [prefixWord, tailWord_298463, baseEnd_298463] using wordTrace_append hprefix tailTrace_298463
  have hstable : (prefixWord ++ tailWord_298463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298463).length < 2 ^ (prefixWord ++ tailWord_298463).sum := by decide
  have hdescent : baseEnd_298463 < baseStart_298463 := by decide
  rcases family_descends (prefixWord ++ tailWord_298463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298480 : List Nat := [2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_298480 : Nat := 118140960795 + 298480 * 2 ^ 59
def prefixEnd_298480 : Nat := 4983230072969 + 3 ^ 40 * 298480 * 2
def baseEnd_298480 : Nat := 90822936743168847008783

theorem tailTrace_298480 : CollatzResearch.WordTrace tailWord_298480 prefixEnd_298480 90822936743168847008783 := by
  unfold tailWord_298480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443229979332705585338447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7257639972443607447117929 5443229979332705585338447)
  ·
    refine ⟨8164844968999058378007671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443229979332705585338447 8164844968999058378007671)
    ·
      refine ⟨12247267453498587567011507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8164844968999058378007671 12247267453498587567011507)
      ·
        refine ⟨18370901180247881350517261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12247267453498587567011507 18370901180247881350517261)
        ·
          refine ⟨6889087942592955506443973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18370901180247881350517261 6889087942592955506443973)
          ·
            refine ⟨1291703989236179157458245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6889087942592955506443973 1291703989236179157458245)
            ·
              refine ⟨242194497981783592023421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1291703989236179157458245 242194497981783592023421)
              ·
                refine ⟨90822936743168847008783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242194497981783592023421 90822936743168847008783)
                ·
                  rfl

theorem cell19_298480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_298480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298480 prefixEnd_298480 := by exact prefixLift 298480
  have htrace : WordTrace (prefixWord ++ tailWord_298480) baseStart_298480 baseEnd_298480 := by
    simpa [prefixWord, tailWord_298480, baseEnd_298480] using wordTrace_append hprefix tailTrace_298480
  have hstable : (prefixWord ++ tailWord_298480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298480).length < 2 ^ (prefixWord ++ tailWord_298480).sum := by decide
  have hdescent : baseEnd_298480 < baseStart_298480 := by decide
  rcases family_descends (prefixWord ++ tailWord_298480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298497 : List Nat := [1, 2, 4, 1, 5, 1, 5]
def baseStart_298497 : Nat := 118140960795 + 298497 * 2 ^ 59
def prefixEnd_298497 : Nat := 4983230072969 + 3 ^ 40 * 298497 * 2
def baseEnd_298497 : Nat := 30276036528439281543653

theorem tailTrace_298497 : CollatzResearch.WordTrace tailWord_298497 prefixEnd_298497 30276036528439281543653 := by
  unfold tailWord_298497
  simp only [CollatzResearch.WordTrace]
  refine ⟨10887079999603823074045745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7258053333069215382697163 10887079999603823074045745)
  ·
    refine ⟨8165309999702867305534309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10887079999603823074045745 8165309999702867305534309)
    ·
      refine ⟨1530995624944287619787683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8165309999702867305534309 1530995624944287619787683)
      ·
        refine ⟨2296493437416431429681525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530995624944287619787683 2296493437416431429681525)
        ·
          refine ⟨215296259757790446532643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2296493437416431429681525 215296259757790446532643)
          ·
            refine ⟨322944389636685669798965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215296259757790446532643 322944389636685669798965)
            ·
              refine ⟨30276036528439281543653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322944389636685669798965 30276036528439281543653)
              ·
                rfl

theorem cell19_298497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_298497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298497 prefixEnd_298497 := by exact prefixLift 298497
  have htrace : WordTrace (prefixWord ++ tailWord_298497) baseStart_298497 baseEnd_298497 := by
    simpa [prefixWord, tailWord_298497, baseEnd_298497] using wordTrace_append hprefix tailTrace_298497
  have hstable : (prefixWord ++ tailWord_298497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298497).length < 2 ^ (prefixWord ++ tailWord_298497).sum := by decide
  have hdescent : baseEnd_298497 < baseStart_298497 := by decide
  rcases family_descends (prefixWord ++ tailWord_298497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298556 : List Nat := [2, 2, 2, 2, 5, 6]
def baseStart_298556 : Nat := 118140960795 + 298556 * 2 ^ 59
def prefixEnd_298556 : Nat := 4983230072969 + 3 ^ 40 * 298556 * 2
def baseEnd_298556 : Nat := 10094006932269243257743

theorem tailTrace_298556 : CollatzResearch.WordTrace tailWord_298556 prefixEnd_298556 10094006932269243257743 := by
  unfold tailWord_298556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5444615953195038075221761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7259487937593384100295681 5444615953195038075221761)
  ·
    refine ⟨4083461964896278556416321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5444615953195038075221761 4083461964896278556416321)
    ·
      refine ⟨3062596473672208917312241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4083461964896278556416321 3062596473672208917312241)
      ·
        refine ⟨2296947355254156687984181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3062596473672208917312241 2296947355254156687984181)
        ·
          refine ⟨215338814555077189498517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2296947355254156687984181 215338814555077189498517)
          ·
            refine ⟨10094006932269243257743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 215338814555077189498517 10094006932269243257743)
            ·
              rfl

theorem cell19_298556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_298556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298556 prefixEnd_298556 := by exact prefixLift 298556
  have htrace : WordTrace (prefixWord ++ tailWord_298556) baseStart_298556 baseEnd_298556 := by
    simpa [prefixWord, tailWord_298556, baseEnd_298556] using wordTrace_append hprefix tailTrace_298556
  have hstable : (prefixWord ++ tailWord_298556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298556).length < 2 ^ (prefixWord ++ tailWord_298556).sum := by decide
  have hdescent : baseEnd_298556 < baseStart_298556 := by decide
  rcases family_descends (prefixWord ++ tailWord_298556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298558 : List Nat := [4, 2, 1, 12]
def baseStart_298558 : Nat := 118140960795 + 298558 * 2 ^ 59
def prefixEnd_298558 : Nat := 4983230072969 + 3 ^ 40 * 298558 * 2
def baseEnd_298558 : Nat := 1121563839013429349077

theorem tailTrace_298558 : CollatzResearch.WordTrace tailWord_298558 prefixEnd_298558 1121563839013429349077 := by
  unfold tailWord_298558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361163106547853811502041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7259536568255220328010885 1361163106547853811502041)
  ·
    refine ⟨1020872329910890358626531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1361163106547853811502041 1020872329910890358626531)
    ·
      refine ⟨1531308494866335537939797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020872329910890358626531 1531308494866335537939797)
      ·
        refine ⟨1121563839013429349077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1531308494866335537939797 1121563839013429349077)
        ·
          rfl

theorem cell19_298558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 12].length) (baseStart_298558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298558 prefixEnd_298558 := by exact prefixLift 298558
  have htrace : WordTrace (prefixWord ++ tailWord_298558) baseStart_298558 baseEnd_298558 := by
    simpa [prefixWord, tailWord_298558, baseEnd_298558] using wordTrace_append hprefix tailTrace_298558
  have hstable : (prefixWord ++ tailWord_298558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298558).length < 2 ^ (prefixWord ++ tailWord_298558).sum := by decide
  have hdescent : baseEnd_298558 < baseStart_298558 := by decide
  rcases family_descends (prefixWord ++ tailWord_298558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298613 : List Nat := [1, 3, 4, 2, 1, 2, 6]
def baseStart_298613 : Nat := 118140960795 + 298613 * 2 ^ 59
def prefixEnd_298613 : Nat := 4983230072969 + 3 ^ 40 * 298613 * 2
def baseEnd_298613 : Nat := 30287802208621315350955

theorem tailTrace_298613 : CollatzResearch.WordTrace tailWord_298613 prefixEnd_298613 30287802208621315350955 := by
  unfold tailWord_298613
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891310867183574885268493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7260873911455716590178995 10891310867183574885268493)
  ·
    refine ⟨4084241575193840581975685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10891310867183574885268493 4084241575193840581975685)
    ·
      refine ⟨765795295348845109120441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4084241575193840581975685 765795295348845109120441)
      ·
        refine ⟨574346471511633831840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 765795295348845109120441 574346471511633831840331)
        ·
          refine ⟨861519707267450747760497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574346471511633831840331 861519707267450747760497)
          ·
            refine ⟨646139780450588060820373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861519707267450747760497 646139780450588060820373)
            ·
              refine ⟨30287802208621315350955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 646139780450588060820373 30287802208621315350955)
              ·
                rfl

theorem cell19_298613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_298613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298613 prefixEnd_298613 := by exact prefixLift 298613
  have htrace : WordTrace (prefixWord ++ tailWord_298613) baseStart_298613 baseEnd_298613 := by
    simpa [prefixWord, tailWord_298613, baseEnd_298613] using wordTrace_append hprefix tailTrace_298613
  have hstable : (prefixWord ++ tailWord_298613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298613).length < 2 ^ (prefixWord ++ tailWord_298613).sum := by decide
  have hdescent : baseEnd_298613 < baseStart_298613 := by decide
  rcases family_descends (prefixWord ++ tailWord_298613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298664 : List Nat := [2, 1, 7, 1, 2, 1, 5]
def baseStart_298664 : Nat := 118140960795 + 298664 * 2 ^ 59
def prefixEnd_298664 : Nat := 4983230072969 + 3 ^ 40 * 298664 * 2
def baseEnd_298664 : Nat := 30292975050770312973131

theorem tailTrace_298664 : CollatzResearch.WordTrace tailWord_298664 prefixEnd_298664 30292975050770312973131 := by
  unfold tailWord_298664
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446585494999405297687523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7262113993332540396916697 5446585494999405297687523)
  ·
    refine ⟨8169878242499107946531285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5446585494999405297687523 8169878242499107946531285)
    ·
      refine ⟨191481521308572842496827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8169878242499107946531285 191481521308572842496827)
      ·
        refine ⟨287222281962859263745241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191481521308572842496827 287222281962859263745241)
        ·
          refine ⟨215416711472144447808931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287222281962859263745241 215416711472144447808931)
          ·
            refine ⟨323125067208216671713397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215416711472144447808931 323125067208216671713397)
            ·
              refine ⟨30292975050770312973131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 323125067208216671713397 30292975050770312973131)
              ·
                rfl

theorem cell19_298664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_298664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298664 prefixEnd_298664 := by exact prefixLift 298664
  have htrace : WordTrace (prefixWord ++ tailWord_298664) baseStart_298664 baseEnd_298664 := by
    simpa [prefixWord, tailWord_298664, baseEnd_298664] using wordTrace_append hprefix tailTrace_298664
  have hstable : (prefixWord ++ tailWord_298664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298664).length < 2 ^ (prefixWord ++ tailWord_298664).sum := by decide
  have hdescent : baseEnd_298664 < baseStart_298664 := by decide
  rcases family_descends (prefixWord ++ tailWord_298664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298708 : List Nat := [2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_298708 : Nat := 118140960795 + 298708 * 2 ^ 59
def prefixEnd_298708 : Nat := 4983230072969 + 3 ^ 40 * 298708 * 2
def baseEnd_298708 : Nat := 90892313684931873941495

theorem tailTrace_298708 : CollatzResearch.WordTrace tailWord_298708 prefixEnd_298708 90892313684931873941495 := by
  unfold tailWord_298708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5447387900919703054988389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7263183867892937406651185 5447387900919703054988389)
  ·
    refine ⟨1021385231422444322810323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5447387900919703054988389 1021385231422444322810323)
    ·
      refine ⟨1532077847133666484215485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021385231422444322810323 1532077847133666484215485)
      ·
        refine ⟨574529192675124931580807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1532077847133666484215485 574529192675124931580807)
        ·
          refine ⟨861793789012687397371211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574529192675124931580807 861793789012687397371211)
          ·
            refine ⟨1292690683519031096056817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861793789012687397371211 1292690683519031096056817)
            ·
              refine ⟨969518012639273322042613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292690683519031096056817 969518012639273322042613)
              ·
                refine ⟨90892313684931873941495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 969518012639273322042613 90892313684931873941495)
                ·
                  rfl

theorem cell19_298708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_298708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298708 prefixEnd_298708 := by exact prefixLift 298708
  have htrace : WordTrace (prefixWord ++ tailWord_298708) baseStart_298708 baseEnd_298708 := by
    simpa [prefixWord, tailWord_298708, baseEnd_298708] using wordTrace_append hprefix tailTrace_298708
  have hstable : (prefixWord ++ tailWord_298708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298708).length < 2 ^ (prefixWord ++ tailWord_298708).sum := by decide
  have hdescent : baseEnd_298708 < baseStart_298708 := by decide
  rcases family_descends (prefixWord ++ tailWord_298708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298727 : List Nat := [1, 1, 5, 4, 1, 7]
def baseStart_298727 : Nat := 118140960795 + 298727 * 2 ^ 59
def prefixEnd_298727 : Nat := 4983230072969 + 3 ^ 40 * 298727 * 2
def baseEnd_298727 : Nat := 10099788344082828835469

theorem tailTrace_298727 : CollatzResearch.WordTrace tailWord_298727 prefixEnd_298727 10099788344082828835469 := by
  unfold tailWord_298727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895468788770572354918435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7263645859180381569945623 10895468788770572354918435)
  ·
    refine ⟨16343203183155858532377653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10895468788770572354918435 16343203183155858532377653)
    ·
      refine ⟨1532175298420861737410405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16343203183155858532377653 1532175298420861737410405)
      ·
        refine ⟨287282868453911575764451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1532175298420861737410405 287282868453911575764451)
        ·
          refine ⟨430924302680867363646677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287282868453911575764451 430924302680867363646677)
          ·
            refine ⟨10099788344082828835469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 430924302680867363646677 10099788344082828835469)
            ·
              rfl

theorem cell19_298727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_298727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298727 prefixEnd_298727 := by exact prefixLift 298727
  have htrace : WordTrace (prefixWord ++ tailWord_298727) baseStart_298727 baseEnd_298727 := by
    simpa [prefixWord, tailWord_298727, baseEnd_298727] using wordTrace_append hprefix tailTrace_298727
  have hstable : (prefixWord ++ tailWord_298727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298727).length < 2 ^ (prefixWord ++ tailWord_298727).sum := by decide
  have hdescent : baseEnd_298727 < baseStart_298727 := by decide
  rcases family_descends (prefixWord ++ tailWord_298727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298786 : List Nat := [3, 3, 1, 1, 2, 1, 8]
def baseStart_298786 : Nat := 118140960795 + 298786 * 2 ^ 59
def prefixEnd_298786 : Nat := 4983230072969 + 3 ^ 40 * 298786 * 2
def baseEnd_298786 : Nat := 30305349300616934735983

theorem tailTrace_298786 : CollatzResearch.WordTrace tailWord_298786 prefixEnd_298786 30305349300616934735983 := by
  unfold tailWord_298786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724405173889206357829053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7265080463704550287544141 2724405173889206357829053)
  ·
    refine ⟨1021651940208452384185895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2724405173889206357829053 1021651940208452384185895)
    ·
      refine ⟨1532477910312678576278843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021651940208452384185895 1532477910312678576278843)
      ·
        refine ⟨2298716865469017864418265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532477910312678576278843 2298716865469017864418265)
        ·
          refine ⟨1724037649101763398313699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298716865469017864418265 1724037649101763398313699)
          ·
            refine ⟨2586056473652645097470549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724037649101763398313699 2586056473652645097470549)
            ·
              refine ⟨30305349300616934735983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2586056473652645097470549 30305349300616934735983)
              ·
                rfl

theorem cell19_298786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_298786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298786 prefixEnd_298786 := by exact prefixLift 298786
  have htrace : WordTrace (prefixWord ++ tailWord_298786) baseStart_298786 baseEnd_298786 := by
    simpa [prefixWord, tailWord_298786, baseEnd_298786] using wordTrace_append hprefix tailTrace_298786
  have hstable : (prefixWord ++ tailWord_298786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298786).length < 2 ^ (prefixWord ++ tailWord_298786).sum := by decide
  have hdescent : baseEnd_298786 < baseStart_298786 := by decide
  rcases family_descends (prefixWord ++ tailWord_298786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298824 : List Nat := [2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_298824 : Nat := 118140960795 + 298824 * 2 ^ 59
def prefixEnd_298824 : Nat := 4983230072969 + 3 ^ 40 * 298824 * 2
def baseEnd_298824 : Nat := 90927610725477975363401

theorem tailTrace_298824 : CollatzResearch.WordTrace tailWord_298824 prefixEnd_298824 90927610725477975363401 := by
  unfold tailWord_298824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449503334709578960599763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7266004446279438614133017 5449503334709578960599763)
  ·
    refine ⟨8174255002064368440899645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5449503334709578960599763 8174255002064368440899645)
    ·
      refine ⟨3065345625774138165337367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8174255002064368440899645 3065345625774138165337367)
      ·
        refine ⟨4598018438661207248006051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065345625774138165337367 4598018438661207248006051)
        ·
          refine ⟨6897027657991810872009077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598018438661207248006051 6897027657991810872009077)
          ·
            refine ⟨646596342936732269250851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6897027657991810872009077 646596342936732269250851)
            ·
              refine ⟨969894514405098403876277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646596342936732269250851 969894514405098403876277)
              ·
                refine ⟨90927610725477975363401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 969894514405098403876277 90927610725477975363401)
                ·
                  rfl

theorem cell19_298824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_298824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298824 prefixEnd_298824 := by exact prefixLift 298824
  have htrace : WordTrace (prefixWord ++ tailWord_298824) baseStart_298824 baseEnd_298824 := by
    simpa [prefixWord, tailWord_298824, baseEnd_298824] using wordTrace_append hprefix tailTrace_298824
  have hstable : (prefixWord ++ tailWord_298824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298824).length < 2 ^ (prefixWord ++ tailWord_298824).sum := by decide
  have hdescent : baseEnd_298824 < baseStart_298824 := by decide
  rcases family_descends (prefixWord ++ tailWord_298824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298858 : List Nat := [3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_298858 : Nat := 118140960795 + 298858 * 2 ^ 59
def prefixEnd_298858 : Nat := 4983230072969 + 3 ^ 40 * 298858 * 2
def baseEnd_298858 : Nat := 90937956409775970607753

theorem tailTrace_298858 : CollatzResearch.WordTrace tailWord_298858 prefixEnd_298858 90937956409775970607753 := by
  unfold tailWord_298858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725061687823995431984307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7266831167530654485291485 2725061687823995431984307)
  ·
    refine ⟨4087592531735993147976461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725061687823995431984307 4087592531735993147976461)
    ·
      refine ⟨1532847199400997430491173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4087592531735993147976461 1532847199400997430491173)
      ·
        refine ⟨287408849887687018217095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1532847199400997430491173 287408849887687018217095)
        ·
          refine ⟨431113274831530527325643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287408849887687018217095 431113274831530527325643)
          ·
            refine ⟨646669912247295790988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431113274831530527325643 646669912247295790988465)
            ·
              refine ⟨485002434185471843241349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646669912247295790988465 485002434185471843241349)
              ·
                refine ⟨90937956409775970607753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485002434185471843241349 90937956409775970607753)
                ·
                  rfl

theorem cell19_298858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_298858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298858 prefixEnd_298858 := by exact prefixLift 298858
  have htrace : WordTrace (prefixWord ++ tailWord_298858) baseStart_298858 baseEnd_298858 := by
    simpa [prefixWord, tailWord_298858, baseEnd_298858] using wordTrace_append hprefix tailTrace_298858
  have hstable : (prefixWord ++ tailWord_298858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298858).length < 2 ^ (prefixWord ++ tailWord_298858).sum := by decide
  have hdescent : baseEnd_298858 < baseStart_298858 := by decide
  rcases family_descends (prefixWord ++ tailWord_298858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298900 : List Nat := [2, 4, 2, 1, 1, 9]
def baseStart_298900 : Nat := 118140960795 + 298900 * 2 ^ 59
def prefixEnd_298900 : Nat := 4983230072969 + 3 ^ 40 * 298900 * 2
def baseEnd_298900 : Nat := 10105637374748035297145

theorem tailTrace_298900 : CollatzResearch.WordTrace tailWord_298900 prefixEnd_298900 10105637374748035297145 := by
  unfold tailWord_298900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450889308571911450483077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7267852411429215267310769 5450889308571911450483077)
  ·
    refine ⟨1022041745357233396965577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5450889308571911450483077 1022041745357233396965577)
    ·
      refine ⟨766531309017925047724183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1022041745357233396965577 766531309017925047724183)
      ·
        refine ⟨1149796963526887571586275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766531309017925047724183 1149796963526887571586275)
        ·
          refine ⟨1724695445290331357379413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149796963526887571586275 1724695445290331357379413)
          ·
            refine ⟨10105637374748035297145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1724695445290331357379413 10105637374748035297145)
            ·
              rfl

theorem cell19_298900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_298900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298900 prefixEnd_298900 := by exact prefixLift 298900
  have htrace : WordTrace (prefixWord ++ tailWord_298900) baseStart_298900 baseEnd_298900 := by
    simpa [prefixWord, tailWord_298900, baseEnd_298900] using wordTrace_append hprefix tailTrace_298900
  have hstable : (prefixWord ++ tailWord_298900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298900).length < 2 ^ (prefixWord ++ tailWord_298900).sum := by decide
  have hdescent : baseEnd_298900 < baseStart_298900 := by decide
  rcases family_descends (prefixWord ++ tailWord_298900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298921 : List Nat := [1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_298921 : Nat := 118140960795 + 298921 * 2 ^ 59
def prefixEnd_298921 : Nat := 4983230072969 + 3 ^ 40 * 298921 * 2
def baseEnd_298921 : Nat := 90957126354210491207581

theorem tailTrace_298921 : CollatzResearch.WordTrace tailWord_298921 prefixEnd_298921 90957126354210491207581 := by
  unfold tailWord_298921
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902544550067743487480617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7268363033378495658320411 10902544550067743487480617)
  ·
    refine ⟨8176908412550807615610463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10902544550067743487480617 8176908412550807615610463)
    ·
      refine ⟨12265362618826211423415695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8176908412550807615610463 12265362618826211423415695)
      ·
        refine ⟨18398043928239317135123543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12265362618826211423415695 18398043928239317135123543)
        ·
          refine ⟨27597065892358975702685315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18398043928239317135123543 27597065892358975702685315)
          ·
            refine ⟨41395598838538463554027973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27597065892358975702685315 41395598838538463554027973)
            ·
              refine ⟨7761674782225961916380245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41395598838538463554027973 7761674782225961916380245)
              ·
                refine ⟨90957126354210491207581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7761674782225961916380245 90957126354210491207581)
                ·
                  rfl

theorem cell19_298921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_298921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298921 prefixEnd_298921 := by exact prefixLift 298921
  have htrace : WordTrace (prefixWord ++ tailWord_298921) baseStart_298921 baseEnd_298921 := by
    simpa [prefixWord, tailWord_298921, baseEnd_298921] using wordTrace_append hprefix tailTrace_298921
  have hstable : (prefixWord ++ tailWord_298921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298921).length < 2 ^ (prefixWord ++ tailWord_298921).sum := by decide
  have hdescent : baseEnd_298921 < baseStart_298921 := by decide
  rcases family_descends (prefixWord ++ tailWord_298921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298932 : List Nat := [2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_298932 : Nat := 118140960795 + 298932 * 2 ^ 59
def prefixEnd_298932 : Nat := 4983230072969 + 3 ^ 40 * 298932 * 2
def baseEnd_298932 : Nat := 90960473487365724963107

theorem tailTrace_298932 : CollatzResearch.WordTrace tailWord_298932 prefixEnd_298932 90960473487365724963107 := by
  unfold tailWord_298932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5451472876513946183065525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7268630502018594910754033 5451472876513946183065525)
  ·
    refine ⟨511075582173182454662393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5451472876513946183065525 511075582173182454662393)
    ·
      refine ⟨383306686629886840996795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 511075582173182454662393 383306686629886840996795)
      ·
        refine ⟨574960029944830261495193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383306686629886840996795 574960029944830261495193)
        ·
          refine ⟨431220022458622696121395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574960029944830261495193 431220022458622696121395)
          ·
            refine ⟨646830033687934044182093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431220022458622696121395 646830033687934044182093)
            ·
              refine ⟨242561262632975266568285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646830033687934044182093 242561262632975266568285)
              ·
                refine ⟨90960473487365724963107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242561262632975266568285 90960473487365724963107)
                ·
                  rfl

theorem cell19_298932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_298932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298932 prefixEnd_298932 := by exact prefixLift 298932
  have htrace : WordTrace (prefixWord ++ tailWord_298932) baseStart_298932 baseEnd_298932 := by
    simpa [prefixWord, tailWord_298932, baseEnd_298932] using wordTrace_append hprefix tailTrace_298932
  have hstable : (prefixWord ++ tailWord_298932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298932).length < 2 ^ (prefixWord ++ tailWord_298932).sum := by decide
  have hdescent : baseEnd_298932 < baseStart_298932 := by decide
  rcases family_descends (prefixWord ++ tailWord_298932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298959 : List Nat := [1, 1, 2, 1, 1, 5, 8]
def baseStart_298959 : Nat := 118140960795 + 298959 * 2 ^ 59
def prefixEnd_298959 : Nat := 4983230072969 + 3 ^ 40 * 298959 * 2
def baseEnd_298959 : Nat := 30322896392612554121011

theorem tailTrace_298959 : CollatzResearch.WordTrace tailWord_298959 prefixEnd_298959 30322896392612554121011 := by
  unfold tailWord_298959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10903930523930075977363931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7269287015953383984909287 10903930523930075977363931)
  ·
    refine ⟨16355895785895113966045897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10903930523930075977363931 16355895785895113966045897)
    ·
      refine ⟨12266921839421335474534423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16355895785895113966045897 12266921839421335474534423)
      ·
        refine ⟨18400382759132003211801635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12266921839421335474534423 18400382759132003211801635)
        ·
          refine ⟨27600574138698004817702453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18400382759132003211801635 27600574138698004817702453)
          ·
            refine ⟨2587553825502937951659605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27600574138698004817702453 2587553825502937951659605)
            ·
              refine ⟨30322896392612554121011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2587553825502937951659605 30322896392612554121011)
              ·
                rfl

theorem cell19_298959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_298959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298959 prefixEnd_298959 := by exact prefixLift 298959
  have htrace : WordTrace (prefixWord ++ tailWord_298959) baseStart_298959 baseEnd_298959 := by
    simpa [prefixWord, tailWord_298959, baseEnd_298959] using wordTrace_append hprefix tailTrace_298959
  have hstable : (prefixWord ++ tailWord_298959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298959).length < 2 ^ (prefixWord ++ tailWord_298959).sum := by decide
  have hdescent : baseEnd_298959 < baseStart_298959 := by decide
  rcases family_descends (prefixWord ++ tailWord_298959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298989 : List Nat := [1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_298989 : Nat := 118140960795 + 298989 * 2 ^ 59
def prefixEnd_298989 : Nat := 4983230072969 + 3 ^ 40 * 298989 * 2
def baseEnd_298989 : Nat := 90977817722806481696285

theorem tailTrace_298989 : CollatzResearch.WordTrace tailWord_298989 prefixEnd_298989 90977817722806481696285 := by
  unfold tailWord_298989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905024713821391100956021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7270016475880927400637347 10905024713821391100956021)
  ·
    refine ⟨1022346066920755415714627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10905024713821391100956021 1022346066920755415714627)
    ·
      refine ⟨1533519100381133123571941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022346066920755415714627 1533519100381133123571941)
      ·
        refine ⟨287534831321462460669739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1533519100381133123571941 287534831321462460669739)
        ·
          refine ⟨431302246982193691004609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287534831321462460669739 431302246982193691004609)
          ·
            refine ⟨323476685236645268253457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431302246982193691004609 323476685236645268253457)
            ·
              refine ⟨242607513927483951190093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323476685236645268253457 242607513927483951190093)
              ·
                refine ⟨90977817722806481696285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242607513927483951190093 90977817722806481696285)
                ·
                  rfl

theorem cell19_298989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_298989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_298989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_298989 prefixEnd_298989 := by exact prefixLift 298989
  have htrace : WordTrace (prefixWord ++ tailWord_298989) baseStart_298989 baseEnd_298989 := by
    simpa [prefixWord, tailWord_298989, baseEnd_298989] using wordTrace_append hprefix tailTrace_298989
  have hstable : (prefixWord ++ tailWord_298989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298989).length < 2 ^ (prefixWord ++ tailWord_298989).sum := by decide
  have hdescent : baseEnd_298989 < baseStart_298989 := by decide
  rcases family_descends (prefixWord ++ tailWord_298989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299031 : List Nat := [1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_299031 : Nat := 118140960795 + 299031 * 2 ^ 59
def prefixEnd_299031 : Nat := 4983230072969 + 3 ^ 40 * 299031 * 2
def baseEnd_299031 : Nat := 90990597685762828762837

theorem tailTrace_299031 : CollatzResearch.WordTrace tailWord_299031 prefixEnd_299031 90990597685762828762837 := by
  unfold tailWord_299031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906556579669232273984947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7271037719779488182656631 10906556579669232273984947)
  ·
    refine ⟨16359834869503848410977421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10906556579669232273984947 16359834869503848410977421)
    ·
      refine ⟨6134938076063943154116533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16359834869503848410977421 6134938076063943154116533)
      ·
        refine ⟨575150444630994670698425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6134938076063943154116533 575150444630994670698425)
        ·
          refine ⟨431362833473246003023819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575150444630994670698425 431362833473246003023819)
          ·
            refine ⟨647044250209869004535729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431362833473246003023819 647044250209869004535729)
            ·
              refine ⟨485283187657401753401797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647044250209869004535729 485283187657401753401797)
              ·
                refine ⟨90990597685762828762837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485283187657401753401797 90990597685762828762837)
                ·
                  rfl

theorem cell19_299031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_299031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299031 prefixEnd_299031 := by exact prefixLift 299031
  have htrace : WordTrace (prefixWord ++ tailWord_299031) baseStart_299031 baseEnd_299031 := by
    simpa [prefixWord, tailWord_299031, baseEnd_299031] using wordTrace_append hprefix tailTrace_299031
  have hstable : (prefixWord ++ tailWord_299031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299031).length < 2 ^ (prefixWord ++ tailWord_299031).sum := by decide
  have hdescent : baseEnd_299031 < baseStart_299031 := by decide
  rcases family_descends (prefixWord ++ tailWord_299031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299158 : List Nat := [5, 3, 2, 1, 1, 1, 1, 5]
def baseStart_299158 : Nat := 118140960795 + 299158 * 2 ^ 59
def prefixEnd_299158 : Nat := 4983230072969 + 3 ^ 40 * 299158 * 2
def baseEnd_299158 : Nat := 91029241859464163940269

theorem tailTrace_299158 : CollatzResearch.WordTrace tailWord_299158 prefixEnd_299158 91029241859464163940269 := by
  unfold tailWord_299158
  simp only [CollatzResearch.WordTrace]
  refine ⟨681949290638070810241133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7274125766806088642572085 681949290638070810241133)
  ·
    refine ⟨255730983989276553840425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 681949290638070810241133 255730983989276553840425)
    ·
      refine ⟨191798237991957415380319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255730983989276553840425 191798237991957415380319)
      ·
        refine ⟨287697356987936123070479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191798237991957415380319 287697356987936123070479)
        ·
          refine ⟨431546035481904184605719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287697356987936123070479 431546035481904184605719)
          ·
            refine ⟨647319053222856276908579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431546035481904184605719 647319053222856276908579)
            ·
              refine ⟨970978579834284415362869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647319053222856276908579 970978579834284415362869)
              ·
                refine ⟨91029241859464163940269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 970978579834284415362869 91029241859464163940269)
                ·
                  rfl

theorem cell19_299158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_299158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299158 prefixEnd_299158 := by exact prefixLift 299158
  have htrace : WordTrace (prefixWord ++ tailWord_299158) baseStart_299158 baseEnd_299158 := by
    simpa [prefixWord, tailWord_299158, baseEnd_299158] using wordTrace_append hprefix tailTrace_299158
  have hstable : (prefixWord ++ tailWord_299158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299158).length < 2 ^ (prefixWord ++ tailWord_299158).sum := by decide
  have hdescent : baseEnd_299158 < baseStart_299158 := by decide
  rcases family_descends (prefixWord ++ tailWord_299158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299162 : List Nat := [3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_299162 : Nat := 118140960795 + 299162 * 2 ^ 59
def prefixEnd_299162 : Nat := 4983230072969 + 3 ^ 40 * 299162 * 2
def baseEnd_299162 : Nat := 91030458998793339851369

theorem tailTrace_299162 : CollatzResearch.WordTrace tailWord_299162 prefixEnd_299162 91030458998793339851369 := by
  unfold tailWord_299162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2727833635548660411750935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7274223028129761098002493 2727833635548660411750935)
  ·
    refine ⟨4091750453322990617626403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2727833635548660411750935 4091750453322990617626403)
    ·
      refine ⟨6137625679984485926439605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4091750453322990617626403 6137625679984485926439605)
      ·
        refine ⟨575402407498545555603713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6137625679984485926439605 575402407498545555603713)
        ·
          refine ⟨431551805623909166702785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575402407498545555603713 431551805623909166702785)
          ·
            refine ⟨323663854217931875027089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431551805623909166702785 323663854217931875027089)
            ·
              refine ⟨242747890663448906270317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323663854217931875027089 242747890663448906270317)
              ·
                refine ⟨91030458998793339851369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242747890663448906270317 91030458998793339851369)
                ·
                  rfl

theorem cell19_299162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_299162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299162 prefixEnd_299162 := by exact prefixLift 299162
  have htrace : WordTrace (prefixWord ++ tailWord_299162) baseStart_299162 baseEnd_299162 := by
    simpa [prefixWord, tailWord_299162, baseEnd_299162] using wordTrace_append hprefix tailTrace_299162
  have hstable : (prefixWord ++ tailWord_299162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299162).length < 2 ^ (prefixWord ++ tailWord_299162).sum := by decide
  have hdescent : baseEnd_299162 < baseStart_299162 := by decide
  rcases family_descends (prefixWord ++ tailWord_299162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299204 : List Nat := [2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_299204 : Nat := 118140960795 + 299204 * 2 ^ 59
def prefixEnd_299204 : Nat := 4983230072969 + 3 ^ 40 * 299204 * 2
def baseEnd_299204 : Nat := 91043238961749686917921

theorem tailTrace_299204 : CollatzResearch.WordTrace tailWord_299204 prefixEnd_299204 91043238961749686917921 := by
  unfold tailWord_299204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456433204021241410016333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7275244272028321880021777 5456433204021241410016333)
  ·
    refine ⟨2046162451507965528756125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5456433204021241410016333 2046162451507965528756125)
    ·
      refine ⟨767310919315487073283547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2046162451507965528756125 767310919315487073283547)
      ·
        refine ⟨1150966378973230609925321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767310919315487073283547 1150966378973230609925321)
        ·
          refine ⟨863224784229922957443991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150966378973230609925321 863224784229922957443991)
          ·
            refine ⟨1294837176344884436165987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863224784229922957443991 1294837176344884436165987)
            ·
              refine ⟨1942255764517326654248981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294837176344884436165987 1942255764517326654248981)
              ·
                refine ⟨91043238961749686917921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1942255764517326654248981 91043238961749686917921)
                ·
                  rfl

theorem cell19_299204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_299204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299204 prefixEnd_299204 := by exact prefixLift 299204
  have htrace : WordTrace (prefixWord ++ tailWord_299204) baseStart_299204 baseEnd_299204 := by
    simpa [prefixWord, tailWord_299204, baseEnd_299204] using wordTrace_append hprefix tailTrace_299204
  have hstable : (prefixWord ++ tailWord_299204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299204).length < 2 ^ (prefixWord ++ tailWord_299204).sum := by decide
  have hdescent : baseEnd_299204 < baseStart_299204 := by decide
  rcases family_descends (prefixWord ++ tailWord_299204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299225 : List Nat := [1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_299225 : Nat := 118140960795 + 299225 * 2 ^ 59
def prefixEnd_299225 : Nat := 4983230072969 + 3 ^ 40 * 299225 * 2
def baseEnd_299225 : Nat := 91049628943227860451197

theorem tailTrace_299225 : CollatzResearch.WordTrace tailWord_299225 prefixEnd_299225 91049628943227860451197 := by
  unfold tailWord_299225
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913632340966403406547129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7275754893977602271031419 10913632340966403406547129)
  ·
    refine ⟨8185224255724802554910347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10913632340966403406547129 8185224255724802554910347)
    ·
      refine ⟨12277836383587203832365521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8185224255724802554910347 12277836383587203832365521)
      ·
        refine ⟨9208377287690402874274141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12277836383587203832365521 9208377287690402874274141)
        ·
          refine ⟨3453141482883901077852803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9208377287690402874274141 3453141482883901077852803)
          ·
            refine ⟨5179712224325851616779205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453141482883901077852803 5179712224325851616779205)
            ·
              refine ⟨971196042061097178146101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5179712224325851616779205 971196042061097178146101)
              ·
                refine ⟨91049628943227860451197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 971196042061097178146101 91049628943227860451197)
                ·
                  rfl

theorem cell19_299225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_299225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299225 prefixEnd_299225 := by exact prefixLift 299225
  have htrace : WordTrace (prefixWord ++ tailWord_299225) baseStart_299225 baseEnd_299225 := by
    simpa [prefixWord, tailWord_299225, baseEnd_299225] using wordTrace_append hprefix tailTrace_299225
  have hstable : (prefixWord ++ tailWord_299225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299225).length < 2 ^ (prefixWord ++ tailWord_299225).sum := by decide
  have hdescent : baseEnd_299225 < baseStart_299225 := by decide
  rcases family_descends (prefixWord ++ tailWord_299225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299396 : List Nat := [2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_299396 : Nat := 118140960795 + 299396 * 2 ^ 59
def prefixEnd_299396 : Nat := 4983230072969 + 3 ^ 40 * 299396 * 2
def baseEnd_299396 : Nat := 91101661649550130650731

theorem tailTrace_299396 : CollatzResearch.WordTrace tailWord_299396 prefixEnd_299396 91101661649550130650731 := by
  unfold tailWord_299396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459934611673449805511021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7279912815564599740681361 5459934611673449805511021)
  ·
    refine ⟨2047475479377543677066633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5459934611673449805511021 2047475479377543677066633)
    ·
      refine ⟨1535606609533157757799975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2047475479377543677066633 1535606609533157757799975)
      ·
        refine ⟨2303409914299736636699963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535606609533157757799975 2303409914299736636699963)
        ·
          refine ⟨3455114871449604955049945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303409914299736636699963 3455114871449604955049945)
          ·
            refine ⟨2591336153587203716287459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455114871449604955049945 2591336153587203716287459)
            ·
              refine ⟨3887004230380805574431189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591336153587203716287459 3887004230380805574431189)
              ·
                refine ⟨91101661649550130650731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3887004230380805574431189 91101661649550130650731)
                ·
                  rfl

theorem cell19_299396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_299396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299396 prefixEnd_299396 := by exact prefixLift 299396
  have htrace : WordTrace (prefixWord ++ tailWord_299396) baseStart_299396 baseEnd_299396 := by
    simpa [prefixWord, tailWord_299396, baseEnd_299396] using wordTrace_append hprefix tailTrace_299396
  have hstable : (prefixWord ++ tailWord_299396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299396).length < 2 ^ (prefixWord ++ tailWord_299396).sum := by decide
  have hdescent : baseEnd_299396 < baseStart_299396 := by decide
  rcases family_descends (prefixWord ++ tailWord_299396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299527 : List Nat := [1, 1, 4, 3, 3, 2, 5]
def baseStart_299527 : Nat := 118140960795 + 299527 * 2 ^ 59
def prefixEnd_299527 : Nat := 4983230072969 + 3 ^ 40 * 299527 * 2
def baseEnd_299527 : Nat := 30380507654193547246421

theorem tailTrace_299527 : CollatzResearch.WordTrace tailWord_299527 prefixEnd_299527 30380507654193547246421 := by
  unfold tailWord_299527
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924647185872308984040835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7283098123914872656027223 10924647185872308984040835)
  ·
    refine ⟨16386970778808463476061253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10924647185872308984040835 16386970778808463476061253)
    ·
      refine ⟨3072557021026586901761485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16386970778808463476061253 3072557021026586901761485)
      ·
        refine ⟨1152208882884970088160557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3072557021026586901761485 1152208882884970088160557)
        ·
          refine ⟨432078331081863783060209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1152208882884970088160557 432078331081863783060209)
          ·
            refine ⟨324058748311397837295157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432078331081863783060209 324058748311397837295157)
            ·
              refine ⟨30380507654193547246421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324058748311397837295157 30380507654193547246421)
              ·
                rfl

theorem cell19_299527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_299527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299527 prefixEnd_299527 := by exact prefixLift 299527
  have htrace : WordTrace (prefixWord ++ tailWord_299527) baseStart_299527 baseEnd_299527 := by
    simpa [prefixWord, tailWord_299527, baseEnd_299527] using wordTrace_append hprefix tailTrace_299527
  have hstable : (prefixWord ++ tailWord_299527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299527).length < 2 ^ (prefixWord ++ tailWord_299527).sum := by decide
  have hdescent : baseEnd_299527 < baseStart_299527 := by decide
  rcases family_descends (prefixWord ++ tailWord_299527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299548 : List Nat := [2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_299548 : Nat := 118140960795 + 299548 * 2 ^ 59
def prefixEnd_299548 : Nat := 4983230072969 + 3 ^ 40 * 299548 * 2
def baseEnd_299548 : Nat := 91147912944058815272539

theorem tailTrace_299548 : CollatzResearch.WordTrace tailWord_299548 prefixEnd_299548 91147912944058815272539 := by
  unfold tailWord_299548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462706559398114785277649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7283608745864153047036865 5462706559398114785277649)
  ·
    refine ⟨4097029919548586088958237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5462706559398114785277649 4097029919548586088958237)
    ·
      refine ⟨1536386219830719783359339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4097029919548586088958237 1536386219830719783359339)
      ·
        refine ⟨2304579329746079675039009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536386219830719783359339 2304579329746079675039009)
        ·
          refine ⟨1728434497309559756279257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304579329746079675039009 1728434497309559756279257)
          ·
            refine ⟨1296325872982169817209443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728434497309559756279257 1296325872982169817209443)
            ·
              refine ⟨1944488809473254725814165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296325872982169817209443 1944488809473254725814165)
              ·
                refine ⟨91147912944058815272539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1944488809473254725814165 91147912944058815272539)
                ·
                  rfl

theorem cell19_299548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_299548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299548 prefixEnd_299548 := by exact prefixLift 299548
  have htrace : WordTrace (prefixWord ++ tailWord_299548) baseStart_299548 baseEnd_299548 := by
    simpa [prefixWord, tailWord_299548, baseEnd_299548] using wordTrace_append hprefix tailTrace_299548
  have hstable : (prefixWord ++ tailWord_299548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299548).length < 2 ^ (prefixWord ++ tailWord_299548).sum := by decide
  have hdescent : baseEnd_299548 < baseStart_299548 := by decide
  rcases family_descends (prefixWord ++ tailWord_299548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299582 : List Nat := [4, 2, 1, 4, 2, 6]
def baseStart_299582 : Nat := 118140960795 + 299582 * 2 ^ 59
def prefixEnd_299582 : Nat := 4983230072969 + 3 ^ 40 * 299582 * 2
def baseEnd_299582 : Nat := 10128695403150756724099

theorem tailTrace_299582 : CollatzResearch.WordTrace tailWord_299582 prefixEnd_299582 10128695403150756724099 := by
  unfold tailWord_299582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365831650084131672161625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7284435467115368918195333 1365831650084131672161625)
  ·
    refine ⟨1024373737563098754121219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1365831650084131672161625 1024373737563098754121219)
    ·
      refine ⟨1536560606344648131181829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024373737563098754121219 1536560606344648131181829)
      ·
        refine ⟨288105113689621524596593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1536560606344648131181829 288105113689621524596593)
        ·
          refine ⟨216078835267216143447445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288105113689621524596593 216078835267216143447445)
          ·
            refine ⟨10128695403150756724099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 216078835267216143447445 10128695403150756724099)
            ·
              rfl

theorem cell19_299582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_299582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299582 prefixEnd_299582 := by exact prefixLift 299582
  have htrace : WordTrace (prefixWord ++ tailWord_299582) baseStart_299582 baseEnd_299582 := by
    simpa [prefixWord, tailWord_299582, baseEnd_299582] using wordTrace_append hprefix tailTrace_299582
  have hstable : (prefixWord ++ tailWord_299582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299582).length < 2 ^ (prefixWord ++ tailWord_299582).sum := by decide
  have hdescent : baseEnd_299582 < baseStart_299582 := by decide
  rcases family_descends (prefixWord ++ tailWord_299582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299605 : List Nat := [1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_299605 : Nat := 118140960795 + 299605 * 2 ^ 59
def prefixEnd_299605 : Nat := 4983230072969 + 3 ^ 40 * 299605 * 2
def baseEnd_299605 : Nat := 91165257179499572005717

theorem tailTrace_299605 : CollatzResearch.WordTrace tailWord_299605 prefixEnd_299605 91165257179499572005717 := by
  unfold tailWord_299605
  simp only [CollatzResearch.WordTrace]
  refine ⟨10927492079589728305380269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7284994719726485536920179 10927492079589728305380269)
  ·
    refine ⟨4097809529846148114517601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10927492079589728305380269 4097809529846148114517601)
    ·
      refine ⟨3073357147384611085888201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4097809529846148114517601 3073357147384611085888201)
      ·
        refine ⟨2305017860538458314416151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3073357147384611085888201 2305017860538458314416151)
        ·
          refine ⟨3457526790807687471624227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305017860538458314416151 3457526790807687471624227)
          ·
            refine ⟨5186290186211531207436341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457526790807687471624227 5186290186211531207436341)
            ·
              refine ⟨486214704957331050697157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5186290186211531207436341 486214704957331050697157)
              ·
                refine ⟨91165257179499572005717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 486214704957331050697157 91165257179499572005717)
                ·
                  rfl

theorem cell19_299605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_299605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299605 prefixEnd_299605 := by exact prefixLift 299605
  have htrace : WordTrace (prefixWord ++ tailWord_299605) baseStart_299605 baseEnd_299605 := by
    simpa [prefixWord, tailWord_299605, baseEnd_299605] using wordTrace_append hprefix tailTrace_299605
  have hstable : (prefixWord ++ tailWord_299605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299605).length < 2 ^ (prefixWord ++ tailWord_299605).sum := by decide
  have hdescent : baseEnd_299605 < baseStart_299605 := by decide
  rcases family_descends (prefixWord ++ tailWord_299605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299618 : List Nat := [3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_299618 : Nat := 118140960795 + 299618 * 2 ^ 59
def prefixEnd_299618 : Nat := 4983230072969 + 3 ^ 40 * 299618 * 2
def baseEnd_299618 : Nat := 91169212882319393716793

theorem tailTrace_299618 : CollatzResearch.WordTrace tailWord_299618 prefixEnd_299618 91169212882319393716793 := by
  unfold tailWord_299618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731991557135657881400877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7285310819028421017069005 2731991557135657881400877)
  ·
    refine ⟨1024496833925871705525329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2731991557135657881400877 1024496833925871705525329)
    ·
      refine ⟨768372625444403779143997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1024496833925871705525329 768372625444403779143997)
      ·
        refine ⟨288139734541651417178999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 768372625444403779143997 288139734541651417178999)
        ·
          refine ⟨432209601812477125768499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288139734541651417178999 432209601812477125768499)
          ·
            refine ⟨648314402718715688652749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432209601812477125768499 648314402718715688652749)
            ·
              refine ⟨243117901019518383244781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 648314402718715688652749 243117901019518383244781)
              ·
                refine ⟨91169212882319393716793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243117901019518383244781 91169212882319393716793)
                ·
                  rfl

theorem cell19_299618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_299618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299618 prefixEnd_299618 := by exact prefixLift 299618
  have htrace : WordTrace (prefixWord ++ tailWord_299618) baseStart_299618 baseEnd_299618 := by
    simpa [prefixWord, tailWord_299618, baseEnd_299618] using wordTrace_append hprefix tailTrace_299618
  have hstable : (prefixWord ++ tailWord_299618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299618).length < 2 ^ (prefixWord ++ tailWord_299618).sum := by decide
  have hdescent : baseEnd_299618 < baseStart_299618 := by decide
  rcases family_descends (prefixWord ++ tailWord_299618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299662 : List Nat := [4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_299662 : Nat := 118140960795 + 299662 * 2 ^ 59
def prefixEnd_299662 : Nat := 4983230072969 + 3 ^ 40 * 299662 * 2
def baseEnd_299662 : Nat := 91182601414940328738895

theorem tailTrace_299662 : CollatzResearch.WordTrace tailWord_299662 prefixEnd_299662 91182601414940328738895 := by
  unfold tailWord_299662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366196380047903380025655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7286380693588818026803493 1366196380047903380025655)
  ·
    refine ⟨2049294570071855070038483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1366196380047903380025655 2049294570071855070038483)
    ·
      refine ⟨3073941855107782605057725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2049294570071855070038483 3073941855107782605057725)
      ·
        refine ⟨1152728195665418476896647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3073941855107782605057725 1152728195665418476896647)
        ·
          refine ⟨1729092293498127715344971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152728195665418476896647 1729092293498127715344971)
          ·
            refine ⟨2593638440247191573017457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729092293498127715344971 2593638440247191573017457)
            ·
              refine ⟨1945228830185393679763093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2593638440247191573017457 1945228830185393679763093)
              ·
                refine ⟨91182601414940328738895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1945228830185393679763093 91182601414940328738895)
                ·
                  rfl

theorem cell19_299662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_299662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299662 prefixEnd_299662 := by exact prefixLift 299662
  have htrace : WordTrace (prefixWord ++ tailWord_299662) baseStart_299662 baseEnd_299662 := by
    simpa [prefixWord, tailWord_299662, baseEnd_299662] using wordTrace_append hprefix tailTrace_299662
  have hstable : (prefixWord ++ tailWord_299662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299662).length < 2 ^ (prefixWord ++ tailWord_299662).sum := by decide
  have hdescent : baseEnd_299662 < baseStart_299662 := by decide
  rcases family_descends (prefixWord ++ tailWord_299662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299759 : List Nat := [1, 1, 2, 1, 5, 9]
def baseStart_299759 : Nat := 118140960795 + 299759 * 2 ^ 59
def prefixEnd_299759 : Nat := 4983230072969 + 3 ^ 40 * 299759 * 2
def baseEnd_299759 : Nat := 10134679671519204953675

theorem tailTrace_299759 : CollatzResearch.WordTrace tailWord_299759 prefixEnd_299759 10134679671519204953675 := by
  unfold tailWord_299759
  simp only [CollatzResearch.WordTrace]
  refine ⟨10933108921031812606486331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7288739280687875070990887 10933108921031812606486331)
  ·
    refine ⟨16399663381547718909729497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10933108921031812606486331 16399663381547718909729497)
    ·
      refine ⟨12299747536160789182297123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16399663381547718909729497 12299747536160789182297123)
      ·
        refine ⟨18449621304241183773445685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12299747536160789182297123 18449621304241183773445685)
        ·
          refine ⟨1729651997272610978760533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18449621304241183773445685 1729651997272610978760533)
          ·
            refine ⟨10134679671519204953675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1729651997272610978760533 10134679671519204953675)
            ·
              rfl

theorem cell19_299759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_299759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299759 prefixEnd_299759 := by exact prefixLift 299759
  have htrace : WordTrace (prefixWord ++ tailWord_299759) baseStart_299759 baseEnd_299759 := by
    simpa [prefixWord, tailWord_299759, baseEnd_299759] using wordTrace_append hprefix tailTrace_299759
  have hstable : (prefixWord ++ tailWord_299759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299759).length < 2 ^ (prefixWord ++ tailWord_299759).sum := by decide
  have hdescent : baseEnd_299759 < baseStart_299759 := by decide
  rcases family_descends (prefixWord ++ tailWord_299759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299774 : List Nat := [4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_299774 : Nat := 118140960795 + 299774 * 2 ^ 59
def prefixEnd_299774 : Nat := 4983230072969 + 3 ^ 40 * 299774 * 2
def baseEnd_299774 : Nat := 91216681316157254249701

theorem tailTrace_299774 : CollatzResearch.WordTrace tailWord_299774 prefixEnd_299774 91216681316157254249701 := by
  unfold tailWord_299774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366707001997183771035297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7289104010651646778854917 1366707001997183771035297)
  ·
    refine ⟨1025030251497887828276473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1366707001997183771035297 1025030251497887828276473)
    ·
      refine ⟨768772688623415871207355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1025030251497887828276473 768772688623415871207355)
      ·
        refine ⟨1153159032935123806811033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768772688623415871207355 1153159032935123806811033)
        ·
          refine ⟨864869274701342855108275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153159032935123806811033 864869274701342855108275)
          ·
            refine ⟨1297303912052014282662413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864869274701342855108275 1297303912052014282662413)
            ·
              refine ⟨486488967019505355998405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1297303912052014282662413 486488967019505355998405)
              ·
                refine ⟨91216681316157254249701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 486488967019505355998405 91216681316157254249701)
                ·
                  rfl

theorem cell19_299774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_299774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299774 prefixEnd_299774 := by exact prefixLift 299774
  have htrace : WordTrace (prefixWord ++ tailWord_299774) baseStart_299774 baseEnd_299774 := by
    simpa [prefixWord, tailWord_299774, baseEnd_299774] using wordTrace_append hprefix tailTrace_299774
  have hstable : (prefixWord ++ tailWord_299774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299774).length < 2 ^ (prefixWord ++ tailWord_299774).sum := by decide
  have hdescent : baseEnd_299774 < baseStart_299774 := by decide
  rcases family_descends (prefixWord ++ tailWord_299774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299795 : List Nat := [1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_299795 : Nat := 118140960795 + 299795 * 2 ^ 59
def prefixEnd_299795 : Nat := 4983230072969 + 3 ^ 40 * 299795 * 2
def baseEnd_299795 : Nat := 91223071297635427782977

theorem tailTrace_299795 : CollatzResearch.WordTrace tailWord_299795 prefixEnd_299795 91223071297635427782977 := by
  unfold tailWord_299795
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934421948901390754796839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7289614632600927169864559 10934421948901390754796839)
  ·
    refine ⟨16401632923352086132195259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934421948901390754796839 16401632923352086132195259)
    ·
      refine ⟨24602449385028129198292889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16401632923352086132195259 24602449385028129198292889)
      ·
        refine ⟨18451837038771096898719667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24602449385028129198292889 18451837038771096898719667)
        ·
          refine ⟨27677755558156645348079501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18451837038771096898719667 27677755558156645348079501)
          ·
            refine ⟨10379158334308742005529813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27677755558156645348079501 10379158334308742005529813)
            ·
              refine ⟨243261523460361140754605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10379158334308742005529813 243261523460361140754605)
              ·
                refine ⟨91223071297635427782977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243261523460361140754605 91223071297635427782977)
                ·
                  rfl

theorem cell19_299795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_299795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299795 prefixEnd_299795 := by exact prefixLift 299795
  have htrace : WordTrace (prefixWord ++ tailWord_299795) baseStart_299795 baseEnd_299795 := by
    simpa [prefixWord, tailWord_299795, baseEnd_299795] using wordTrace_append hprefix tailTrace_299795
  have hstable : (prefixWord ++ tailWord_299795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299795).length < 2 ^ (prefixWord ++ tailWord_299795).sum := by decide
  have hdescent : baseEnd_299795 < baseStart_299795 := by decide
  rcases family_descends (prefixWord ++ tailWord_299795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299844 : List Nat := [2, 3, 4, 2, 2, 1, 2, 3]
def baseStart_299844 : Nat := 118140960795 + 299844 * 2 ^ 59
def prefixEnd_299844 : Nat := 4983230072969 + 3 ^ 40 * 299844 * 2
def baseEnd_299844 : Nat := 91237981254417832693955

theorem tailTrace_299844 : CollatzResearch.WordTrace tailWord_299844 prefixEnd_299844 91237981254417832693955 := by
  unfold tailWord_299844
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468104562861936061665293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7290806083815914748887057 5468104562861936061665293)
  ·
    refine ⟨2050539211073226023124485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5468104562861936061665293 2050539211073226023124485)
    ·
      refine ⟨384476102076229879335841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2050539211073226023124485 384476102076229879335841)
      ·
        refine ⟨288357076557172409501881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384476102076229879335841 288357076557172409501881)
        ·
          refine ⟨216267807417879307126411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288357076557172409501881 216267807417879307126411)
          ·
            refine ⟨324401711126818960689617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216267807417879307126411 324401711126818960689617)
            ·
              refine ⟨243301283345114220517213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324401711126818960689617 243301283345114220517213)
              ·
                refine ⟨91237981254417832693955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243301283345114220517213 91237981254417832693955)
                ·
                  rfl

theorem cell19_299844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_299844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299844 prefixEnd_299844 := by exact prefixLift 299844
  have htrace : WordTrace (prefixWord ++ tailWord_299844) baseStart_299844 baseEnd_299844 := by
    simpa [prefixWord, tailWord_299844, baseEnd_299844] using wordTrace_append hprefix tailTrace_299844
  have hstable : (prefixWord ++ tailWord_299844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299844).length < 2 ^ (prefixWord ++ tailWord_299844).sum := by decide
  have hdescent : baseEnd_299844 < baseStart_299844 := by decide
  rcases family_descends (prefixWord ++ tailWord_299844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299852 : List Nat := [2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_299852 : Nat := 118140960795 + 299852 * 2 ^ 59
def prefixEnd_299852 : Nat := 4983230072969 + 3 ^ 40 * 299852 * 2
def baseEnd_299852 : Nat := 91240415533076184516155

theorem tailTrace_299852 : CollatzResearch.WordTrace tailWord_299852 prefixEnd_299852 91240415533076184516155 := by
  unfold tailWord_299852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468250454847444744810905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7291000606463259659747873 5468250454847444744810905)
  ·
    refine ⟨4101187841135583558608179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5468250454847444744810905 4101187841135583558608179)
    ·
      refine ⟨6151781761703375337912269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101187841135583558608179 6151781761703375337912269)
      ·
        refine ⟨2306918160638765751717101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6151781761703375337912269 2306918160638765751717101)
        ·
          refine ⟨865094310239537156893913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2306918160638765751717101 865094310239537156893913)
          ·
            refine ⟨648820732679652867670435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865094310239537156893913 648820732679652867670435)
            ·
              refine ⟨973231099019479301505653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648820732679652867670435 973231099019479301505653)
              ·
                refine ⟨91240415533076184516155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973231099019479301505653 91240415533076184516155)
                ·
                  rfl

theorem cell19_299852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_299852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299852 prefixEnd_299852 := by exact prefixLift 299852
  have htrace : WordTrace (prefixWord ++ tailWord_299852) baseStart_299852 baseEnd_299852 := by
    simpa [prefixWord, tailWord_299852, baseEnd_299852] using wordTrace_append hprefix tailTrace_299852
  have hstable : (prefixWord ++ tailWord_299852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299852).length < 2 ^ (prefixWord ++ tailWord_299852).sum := by decide
  have hdescent : baseEnd_299852 < baseStart_299852 := by decide
  rcases family_descends (prefixWord ++ tailWord_299852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299930 : List Nat := [3, 1, 1, 4, 10]
def baseStart_299930 : Nat := 118140960795 + 299930 * 2 ^ 59
def prefixEnd_299930 : Nat := 4983230072969 + 3 ^ 40 * 299930 * 2
def baseEnd_299930 : Nat := 3380153694444263510467

theorem tailTrace_299930 : CollatzResearch.WordTrace tailWord_299930 prefixEnd_299930 3380153694444263510467 := by
  unfold tailWord_299930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734836450853077202740311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7292897202274872540640829 2734836450853077202740311)
  ·
    refine ⟨4102254676279615804110467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2734836450853077202740311 4102254676279615804110467)
    ·
      refine ⟨6153382014419423706165701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4102254676279615804110467 6153382014419423706165701)
      ·
        refine ⟨1153759127703641944906069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6153382014419423706165701 1153759127703641944906069)
        ·
          refine ⟨3380153694444263510467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1153759127703641944906069 3380153694444263510467)
          ·
            rfl

theorem cell19_299930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 10].length) (baseStart_299930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299930 prefixEnd_299930 := by exact prefixLift 299930
  have htrace : WordTrace (prefixWord ++ tailWord_299930) baseStart_299930 baseEnd_299930 := by
    simpa [prefixWord, tailWord_299930, baseEnd_299930] using wordTrace_append hprefix tailTrace_299930
  have hstable : (prefixWord ++ tailWord_299930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299930).length < 2 ^ (prefixWord ++ tailWord_299930).sum := by decide
  have hdescent : baseEnd_299930 < baseStart_299930 := by decide
  rcases family_descends (prefixWord ++ tailWord_299930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299943 : List Nat := [1, 1, 6, 1, 4, 1, 1, 4]
def baseStart_299943 : Nat := 118140960795 + 299943 * 2 ^ 59
def prefixEnd_299943 : Nat := 4983230072969 + 3 ^ 40 * 299943 * 2
def baseEnd_299943 : Nat := 91268105452814936493685

theorem tailTrace_299943 : CollatzResearch.WordTrace tailWord_299943 prefixEnd_299943 91268105452814936493685 := by
  unfold tailWord_299943
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939819952365212031184483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7293213301576808020789655 10939819952365212031184483)
  ·
    refine ⟨16409729928547818046776725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10939819952365212031184483 16409729928547818046776725)
    ·
      refine ⟨769206090400678970942659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16409729928547818046776725 769206090400678970942659)
      ·
        refine ⟨1153809135601018456413989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769206090400678970942659 1153809135601018456413989)
        ·
          refine ⟨216339212925190960577623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1153809135601018456413989 216339212925190960577623)
          ·
            refine ⟨324508819387786440866435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216339212925190960577623 324508819387786440866435)
            ·
              refine ⟨486763229081679661299653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324508819387786440866435 486763229081679661299653)
              ·
                refine ⟨91268105452814936493685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 486763229081679661299653 91268105452814936493685)
                ·
                  rfl

theorem cell19_299943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_299943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299943 prefixEnd_299943 := by exact prefixLift 299943
  have htrace : WordTrace (prefixWord ++ tailWord_299943) baseStart_299943 baseEnd_299943 := by
    simpa [prefixWord, tailWord_299943, baseEnd_299943] using wordTrace_append hprefix tailTrace_299943
  have hstable : (prefixWord ++ tailWord_299943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299943).length < 2 ^ (prefixWord ++ tailWord_299943).sum := by decide
  have hdescent : baseEnd_299943 < baseStart_299943 := by decide
  rcases family_descends (prefixWord ++ tailWord_299943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299958 : List Nat := [5, 1, 4, 1, 1, 1, 3, 3]
def baseStart_299958 : Nat := 118140960795 + 299958 * 2 ^ 59
def prefixEnd_299958 : Nat := 4983230072969 + 3 ^ 40 * 299958 * 2
def baseEnd_299958 : Nat := 91272669725299346160311

theorem tailTrace_299958 : CollatzResearch.WordTrace tailWord_299958 prefixEnd_299958 91272669725299346160311 := by
  unfold tailWord_299958
  simp only [CollatzResearch.WordTrace]
  refine ⟨683772940456929349561283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7293578031540579728653685 683772940456929349561283)
  ·
    refine ⟨1025659410685394024341925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683772940456929349561283 1025659410685394024341925)
    ·
      refine ⟨192311139503511379564111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1025659410685394024341925 192311139503511379564111)
      ·
        refine ⟨288466709255267069346167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192311139503511379564111 288466709255267069346167)
        ·
          refine ⟨432700063882900604019251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288466709255267069346167 432700063882900604019251)
          ·
            refine ⟨649050095824350906028877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432700063882900604019251 649050095824350906028877)
            ·
              refine ⟨243393785934131589760829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649050095824350906028877 243393785934131589760829)
              ·
                refine ⟨91272669725299346160311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243393785934131589760829 91272669725299346160311)
                ·
                  rfl

theorem cell19_299958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_299958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_299958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_299958 prefixEnd_299958 := by exact prefixLift 299958
  have htrace : WordTrace (prefixWord ++ tailWord_299958) baseStart_299958 baseEnd_299958 := by
    simpa [prefixWord, tailWord_299958, baseEnd_299958] using wordTrace_append hprefix tailTrace_299958
  have hstable : (prefixWord ++ tailWord_299958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299958).length < 2 ^ (prefixWord ++ tailWord_299958).sum := by decide
  have hdescent : baseEnd_299958 < baseStart_299958 := by decide
  rcases family_descends (prefixWord ++ tailWord_299958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300025 : List Nat := [1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_300025 : Nat := 118140960795 + 300025 * 2 ^ 59
def prefixEnd_300025 : Nat := 4983230072969 + 3 ^ 40 * 300025 * 2
def baseEnd_300025 : Nat := 91293056809063042671239

theorem tailTrace_300025 : CollatzResearch.WordTrace tailWord_300025 prefixEnd_300025 91293056809063042671239 := by
  unfold tailWord_300025
  simp only [CollatzResearch.WordTrace]
  refine ⟨10942810738068140035669529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7295207158712093357113019 10942810738068140035669529)
  ·
    refine ⟨8207108053551105026752147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10942810738068140035669529 8207108053551105026752147)
    ·
      refine ⟨12310662080326657540128221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8207108053551105026752147 12310662080326657540128221)
      ·
        refine ⟨4616498280122496577548083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12310662080326657540128221 4616498280122496577548083)
        ·
          refine ⟨6924747420183744866322125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616498280122496577548083 6924747420183744866322125)
          ·
            refine ⟨2596780282568904324870797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6924747420183744866322125 2596780282568904324870797)
            ·
              refine ⟨973792605963339121826549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2596780282568904324870797 973792605963339121826549)
              ·
                refine ⟨91293056809063042671239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973792605963339121826549 91293056809063042671239)
                ·
                  rfl

theorem cell19_300025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_300025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300025 prefixEnd_300025 := by exact prefixLift 300025
  have htrace : WordTrace (prefixWord ++ tailWord_300025) baseStart_300025 baseEnd_300025 := by
    simpa [prefixWord, tailWord_300025, baseEnd_300025] using wordTrace_append hprefix tailTrace_300025
  have hstable : (prefixWord ++ tailWord_300025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300025).length < 2 ^ (prefixWord ++ tailWord_300025).sum := by decide
  have hdescent : baseEnd_300025 < baseStart_300025 := by decide
  rcases family_descends (prefixWord ++ tailWord_300025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300042 : List Nat := [3, 1, 2, 2, 3, 3, 5]
def baseStart_300042 : Nat := 118140960795 + 300042 * 2 ^ 59
def prefixEnd_300042 : Nat := 4983230072969 + 3 ^ 40 * 300042 * 2
def baseEnd_300042 : Nat := 30432743217070680097805

theorem tailTrace_300042 : CollatzResearch.WordTrace tailWord_300042 prefixEnd_300042 30432743217070680097805 := by
  unfold tailWord_300042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735857694751637984759595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7295620519337701292692253 2735857694751637984759595)
  ·
    refine ⟨4103786542127456977139393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2735857694751637984759595 4103786542127456977139393)
    ·
      refine ⟨3077839906595592732854545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4103786542127456977139393 3077839906595592732854545)
      ·
        refine ⟨2308379929946694549640909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3077839906595592732854545 2308379929946694549640909)
        ·
          refine ⟨865642473730010456115341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2308379929946694549640909 865642473730010456115341)
          ·
            refine ⟨324615927648753921043253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 865642473730010456115341 324615927648753921043253)
            ·
              refine ⟨30432743217070680097805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324615927648753921043253 30432743217070680097805)
              ·
                rfl

theorem cell19_300042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_300042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300042 prefixEnd_300042 := by exact prefixLift 300042
  have htrace : WordTrace (prefixWord ++ tailWord_300042) baseStart_300042 baseEnd_300042 := by
    simpa [prefixWord, tailWord_300042, baseEnd_300042] using wordTrace_append hprefix tailTrace_300042
  have hstable : (prefixWord ++ tailWord_300042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300042).length < 2 ^ (prefixWord ++ tailWord_300042).sum := by decide
  have hdescent : baseEnd_300042 < baseStart_300042 := by decide
  rcases family_descends (prefixWord ++ tailWord_300042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300044 : List Nat := [2, 2, 1, 2, 3, 2, 7]
def baseStart_300044 : Nat := 118140960795 + 300044 * 2 ^ 59
def prefixEnd_300044 : Nat := 4983230072969 + 3 ^ 40 * 300044 * 2
def baseEnd_300044 : Nat := 30432946073625542749655

theorem tailTrace_300044 : CollatzResearch.WordTrace tailWord_300044 prefixEnd_300044 30432946073625542749655 := by
  unfold tailWord_300044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5471751862499653140305593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7295669149999537520407457 5471751862499653140305593)
  ·
    refine ⟨4103813896874739855229195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5471751862499653140305593 4103813896874739855229195)
    ·
      refine ⟨6155720845312109782843793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4103813896874739855229195 6155720845312109782843793)
      ·
        refine ⟨4616790633984082337132845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6155720845312109782843793 4616790633984082337132845)
        ·
          refine ⟨1731296487744030876424817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4616790633984082337132845 1731296487744030876424817)
          ·
            refine ⟨1298472365808023157318613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731296487744030876424817 1298472365808023157318613)
            ·
              refine ⟨30432946073625542749655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1298472365808023157318613 30432946073625542749655)
              ·
                rfl

theorem cell19_300044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_300044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300044 prefixEnd_300044 := by exact prefixLift 300044
  have htrace : WordTrace (prefixWord ++ tailWord_300044) baseStart_300044 baseEnd_300044 := by
    simpa [prefixWord, tailWord_300044, baseEnd_300044] using wordTrace_append hprefix tailTrace_300044
  have hstable : (prefixWord ++ tailWord_300044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300044).length < 2 ^ (prefixWord ++ tailWord_300044).sum := by decide
  have hdescent : baseEnd_300044 < baseStart_300044 := by decide
  rcases family_descends (prefixWord ++ tailWord_300044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300063 : List Nat := [1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_300063 : Nat := 118140960795 + 300063 * 2 ^ 59
def prefixEnd_300063 : Nat := 4983230072969 + 3 ^ 40 * 300063 * 2
def baseEnd_300063 : Nat := 91304619632690213826691

theorem tailTrace_300063 : CollatzResearch.WordTrace tailWord_300063 prefixEnd_300063 91304619632690213826691 := by
  unfold tailWord_300063
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944196711930472525552843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7296131141286981683701895 10944196711930472525552843)
  ·
    refine ⟨16416295067895708788329265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10944196711930472525552843 16416295067895708788329265)
    ·
      refine ⟨12312221300921781591246949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16416295067895708788329265 12312221300921781591246949)
      ·
        refine ⟨2308541493922834048358803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12312221300921781591246949 2308541493922834048358803)
        ·
          refine ⟨3462812240884251072538205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308541493922834048358803 3462812240884251072538205)
          ·
            refine ⟨1298554590331594152201827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3462812240884251072538205 1298554590331594152201827)
            ·
              refine ⟨1947831885497391228302741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298554590331594152201827 1947831885497391228302741)
              ·
                refine ⟨91304619632690213826691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1947831885497391228302741 91304619632690213826691)
                ·
                  rfl

theorem cell19_300063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_300063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300063 prefixEnd_300063 := by exact prefixLift 300063
  have htrace : WordTrace (prefixWord ++ tailWord_300063) baseStart_300063 baseEnd_300063 := by
    simpa [prefixWord, tailWord_300063, baseEnd_300063] using wordTrace_append hprefix tailTrace_300063
  have hstable : (prefixWord ++ tailWord_300063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300063).length < 2 ^ (prefixWord ++ tailWord_300063).sum := by decide
  have hdescent : baseEnd_300063 < baseStart_300063 := by decide
  rcases family_descends (prefixWord ++ tailWord_300063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300082 : List Nat := [3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_300082 : Nat := 118140960795 + 300082 * 2 ^ 59
def prefixEnd_300082 : Nat := 4983230072969 + 3 ^ 40 * 300082 * 2
def baseEnd_300082 : Nat := 91310401044503799404417

theorem tailTrace_300082 : CollatzResearch.WordTrace tailWord_300082 prefixEnd_300082 91310401044503799404417 := by
  unfold tailWord_300082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736222424715409692623625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7296593132574425846996333 2736222424715409692623625)
  ·
    refine ⟨2052166818536557269467719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2736222424715409692623625 2052166818536557269467719)
    ·
      refine ⟨3078250227804835904201579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052166818536557269467719 3078250227804835904201579)
      ·
        refine ⟨4617375341707253856302369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078250227804835904201579 4617375341707253856302369)
        ·
          refine ⟨3463031506280440392226777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4617375341707253856302369 3463031506280440392226777)
          ·
            refine ⟨2597273629710330294170083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3463031506280440392226777 2597273629710330294170083)
            ·
              refine ⟨3895910444565495441255125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597273629710330294170083 3895910444565495441255125)
              ·
                refine ⟨91310401044503799404417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3895910444565495441255125 91310401044503799404417)
                ·
                  rfl

theorem cell19_300082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_300082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300082 prefixEnd_300082 := by exact prefixLift 300082
  have htrace : WordTrace (prefixWord ++ tailWord_300082) baseStart_300082 baseEnd_300082 := by
    simpa [prefixWord, tailWord_300082, baseEnd_300082] using wordTrace_append hprefix tailTrace_300082
  have hstable : (prefixWord ++ tailWord_300082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300082).length < 2 ^ (prefixWord ++ tailWord_300082).sum := by decide
  have hdescent : baseEnd_300082 < baseStart_300082 := by decide
  rcases family_descends (prefixWord ++ tailWord_300082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300137 : List Nat := [1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_300137 : Nat := 118140960795 + 300137 * 2 ^ 59
def prefixEnd_300137 : Nat := 4983230072969 + 3 ^ 40 * 300137 * 2
def baseEnd_300137 : Nat := 91327136710279968182045

theorem tailTrace_300137 : CollatzResearch.WordTrace tailWord_300137 prefixEnd_300137 91327136710279968182045 := by
  unfold tailWord_300137
  simp only [CollatzResearch.WordTrace]
  refine ⟨10946895713662383163746665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7297930475774922109164443 10946895713662383163746665)
  ·
    refine ⟨8210171785246787372809999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10946895713662383163746665 8210171785246787372809999)
    ·
      refine ⟨12315257677870181059214999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8210171785246787372809999 12315257677870181059214999)
      ·
        refine ⟨18472886516805271588822499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12315257677870181059214999 18472886516805271588822499)
        ·
          refine ⟨27709329775207907383233749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18472886516805271588822499 27709329775207907383233749)
          ·
            refine ⟨649437416606435329294541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27709329775207907383233749 649437416606435329294541)
            ·
              refine ⟨243539031227413248485453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649437416606435329294541 243539031227413248485453)
              ·
                refine ⟨91327136710279968182045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243539031227413248485453 91327136710279968182045)
                ·
                  rfl

theorem cell19_300137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_300137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300137 prefixEnd_300137 := by exact prefixLift 300137
  have htrace : WordTrace (prefixWord ++ tailWord_300137) baseStart_300137 baseEnd_300137 := by
    simpa [prefixWord, tailWord_300137, baseEnd_300137] using wordTrace_append hprefix tailTrace_300137
  have hstable : (prefixWord ++ tailWord_300137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300137).length < 2 ^ (prefixWord ++ tailWord_300137).sum := by decide
  have hdescent : baseEnd_300137 < baseStart_300137 := by decide
  rcases family_descends (prefixWord ++ tailWord_300137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300190 : List Nat := [4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_300190 : Nat := 118140960795 + 300190 * 2 ^ 59
def prefixEnd_300190 : Nat := 4983230072969 + 3 ^ 40 * 300190 * 2
def baseEnd_300190 : Nat := 91343263806391549004123

theorem tailTrace_300190 : CollatzResearch.WordTrace tailWord_300190 prefixEnd_300190 91343263806391549004123 := by
  unfold tailWord_300190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368603597808796651928253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7299219188313582143617349 1368603597808796651928253)
  ·
    refine ⟨513226349178298744473095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1368603597808796651928253 513226349178298744473095)
    ·
      refine ⟨769839523767448116709643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513226349178298744473095 769839523767448116709643)
      ·
        refine ⟨1154759285651172175064465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769839523767448116709643 1154759285651172175064465)
        ·
          refine ⟨866069464238379131298349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154759285651172175064465 866069464238379131298349)
          ·
            refine ⟨324776049089392174236881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 866069464238379131298349 324776049089392174236881)
            ·
              refine ⟨243582036817044130677661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324776049089392174236881 243582036817044130677661)
              ·
                refine ⟨91343263806391549004123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243582036817044130677661 91343263806391549004123)
                ·
                  rfl

theorem cell19_300190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_300190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300190 prefixEnd_300190 := by exact prefixLift 300190
  have htrace : WordTrace (prefixWord ++ tailWord_300190) baseStart_300190 baseEnd_300190 := by
    simpa [prefixWord, tailWord_300190, baseEnd_300190] using wordTrace_append hprefix tailTrace_300190
  have hstable : (prefixWord ++ tailWord_300190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300190).length < 2 ^ (prefixWord ++ tailWord_300190).sum := by decide
  have hdescent : baseEnd_300190 < baseStart_300190 := by decide
  rcases family_descends (prefixWord ++ tailWord_300190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300234 : List Nat := [3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_300234 : Nat := 118140960795 + 300234 * 2 ^ 59
def prefixEnd_300234 : Nat := 4983230072969 + 3 ^ 40 * 300234 * 2
def baseEnd_300234 : Nat := 91356652339012484026225

theorem tailTrace_300234 : CollatzResearch.WordTrace tailWord_300234 prefixEnd_300234 91356652339012484026225 := by
  unfold tailWord_300234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2737608398577742182506939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7300289062873979153351837 2737608398577742182506939)
  ·
    refine ⟨4106412597866613273760409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2737608398577742182506939 4106412597866613273760409)
    ·
      refine ⟨3079809448399959955320307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4106412597866613273760409 3079809448399959955320307)
      ·
        refine ⟨4619714172599939932980461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079809448399959955320307 4619714172599939932980461)
        ·
          refine ⟨1732392814724977474867673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4619714172599939932980461 1732392814724977474867673)
          ·
            refine ⟨1299294611043733106150755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1732392814724977474867673 1299294611043733106150755)
            ·
              refine ⟨1948941916565599659226133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299294611043733106150755 1948941916565599659226133)
              ·
                refine ⟨91356652339012484026225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1948941916565599659226133 91356652339012484026225)
                ·
                  rfl

theorem cell19_300234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_300234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300234 prefixEnd_300234 := by exact prefixLift 300234
  have htrace : WordTrace (prefixWord ++ tailWord_300234) baseStart_300234 baseEnd_300234 := by
    simpa [prefixWord, tailWord_300234, baseEnd_300234] using wordTrace_append hprefix tailTrace_300234
  have hstable : (prefixWord ++ tailWord_300234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300234).length < 2 ^ (prefixWord ++ tailWord_300234).sum := by decide
  have hdescent : baseEnd_300234 < baseStart_300234 := by decide
  rcases family_descends (prefixWord ++ tailWord_300234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300289 : List Nat := [1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_300289 : Nat := 118140960795 + 300289 * 2 ^ 59
def prefixEnd_300289 : Nat := 4983230072969 + 3 ^ 40 * 300289 * 2
def baseEnd_300289 : Nat := 91373388004788652803853

theorem tailTrace_300289 : CollatzResearch.WordTrace tailWord_300289 prefixEnd_300289 91373388004788652803853 := by
  unfold tailWord_300289
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952439609111713123279921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7301626406074475415519947 10952439609111713123279921)
  ·
    refine ⟨8214329706833784842459941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10952439609111713123279921 8214329706833784842459941)
    ·
      refine ⟨1540186820031334657961239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8214329706833784842459941 1540186820031334657961239)
      ·
        refine ⟨2310280230047001986941859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540186820031334657961239 2310280230047001986941859)
        ·
          refine ⟨3465420345070502980412789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310280230047001986941859 3465420345070502980412789)
          ·
            refine ⟨324883157350359654413699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3465420345070502980412789 324883157350359654413699)
            ·
              refine ⟨487324736025539481620549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324883157350359654413699 487324736025539481620549)
              ·
                refine ⟨91373388004788652803853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487324736025539481620549 91373388004788652803853)
                ·
                  rfl

theorem cell19_300289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_300289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300289 prefixEnd_300289 := by exact prefixLift 300289
  have htrace : WordTrace (prefixWord ++ tailWord_300289) baseStart_300289 baseEnd_300289 := by
    simpa [prefixWord, tailWord_300289, baseEnd_300289] using wordTrace_append hprefix tailTrace_300289
  have hstable : (prefixWord ++ tailWord_300289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300289).length < 2 ^ (prefixWord ++ tailWord_300289).sum := by decide
  have hdescent : baseEnd_300289 < baseStart_300289 := by decide
  rcases family_descends (prefixWord ++ tailWord_300289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300291 : List Nat := [1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_300291 : Nat := 118140960795 + 300291 * 2 ^ 59
def prefixEnd_300291 : Nat := 4983230072969 + 3 ^ 40 * 300291 * 2
def baseEnd_300291 : Nat := 91373996574453240759403

theorem tailTrace_300291 : CollatzResearch.WordTrace tailWord_300291 prefixEnd_300291 91373996574453240759403 := by
  unfold tailWord_300291
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952512555104467464852727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7301675036736311643235151 10952512555104467464852727)
  ·
    refine ⟨16428768832656701197279091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10952512555104467464852727 16428768832656701197279091)
    ·
      refine ⟨24643153248985051795918637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16428768832656701197279091 24643153248985051795918637)
      ·
        refine ⟨9241182468369394423469489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24643153248985051795918637 9241182468369394423469489)
        ·
          refine ⟨6930886851277045817602117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9241182468369394423469489 6930886851277045817602117)
          ·
            refine ⟨1299541284614446090800397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6930886851277045817602117 1299541284614446090800397)
            ·
              refine ⟨487327981730417284050149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1299541284614446090800397 487327981730417284050149)
              ·
                refine ⟨91373996574453240759403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487327981730417284050149 91373996574453240759403)
                ·
                  rfl

theorem cell19_300291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_300291 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300291 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300291 prefixEnd_300291 := by exact prefixLift 300291
  have htrace : WordTrace (prefixWord ++ tailWord_300291) baseStart_300291 baseEnd_300291 := by
    simpa [prefixWord, tailWord_300291, baseEnd_300291] using wordTrace_append hprefix tailTrace_300291
  have hstable : (prefixWord ++ tailWord_300291).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300291).length < 2 ^ (prefixWord ++ tailWord_300291).sum := by decide
  have hdescent : baseEnd_300291 < baseStart_300291 := by decide
  rcases family_descends (prefixWord ++ tailWord_300291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300424 : List Nat := [2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_300424 : Nat := 118140960795 + 300424 * 2 ^ 59
def prefixEnd_300424 : Nat := 4983230072969 + 3 ^ 40 * 300424 * 2
def baseEnd_300424 : Nat := 91414466457148339803485

theorem tailTrace_300424 : CollatzResearch.WordTrace tailWord_300424 prefixEnd_300424 91414466457148339803485 := by
  unfold tailWord_300424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478681731811315589722163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7304908975748420786296217 5478681731811315589722163)
  ·
    refine ⟨8218022597716973384583245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5478681731811315589722163 8218022597716973384583245)
    ·
      refine ⟨3081758474143865019218717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8218022597716973384583245 3081758474143865019218717)
      ·
        refine ⟨1155659427803949382207019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3081758474143865019218717 1155659427803949382207019)
        ·
          refine ⟨1733489141705924073310529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155659427803949382207019 1733489141705924073310529)
          ·
            refine ⟨1300116856279443054982897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733489141705924073310529 1300116856279443054982897)
            ·
              refine ⟨975087642209582291237173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300116856279443054982897 975087642209582291237173)
              ·
                refine ⟨91414466457148339803485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 975087642209582291237173 91414466457148339803485)
                ·
                  rfl

theorem cell19_300424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_300424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300424 prefixEnd_300424 := by exact prefixLift 300424
  have htrace : WordTrace (prefixWord ++ tailWord_300424) baseStart_300424 baseEnd_300424 := by
    simpa [prefixWord, tailWord_300424, baseEnd_300424] using wordTrace_append hprefix tailTrace_300424
  have hstable : (prefixWord ++ tailWord_300424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300424).length < 2 ^ (prefixWord ++ tailWord_300424).sum := by decide
  have hdescent : baseEnd_300424 < baseStart_300424 := by decide
  rcases family_descends (prefixWord ++ tailWord_300424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300456 : List Nat := [2, 1, 6, 1, 3, 1, 1, 4]
def baseStart_300456 : Nat := 118140960795 + 300456 * 2 ^ 59
def prefixEnd_300456 : Nat := 4983230072969 + 3 ^ 40 * 300456 * 2
def baseEnd_300456 : Nat := 91424203571781747092287

theorem tailTrace_300456 : CollatzResearch.WordTrace tailWord_300456 prefixEnd_300456 91424203571781747092287 := by
  unfold tailWord_300456
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479265299753350322304611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7305687066337800429739481 5479265299753350322304611)
  ·
    refine ⟨8218897949630025483456917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479265299753350322304611 8218897949630025483456917)
    ·
      refine ⟨385260841388907444537043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8218897949630025483456917 385260841388907444537043)
      ·
        refine ⟨577891262083361166805565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385260841388907444537043 577891262083361166805565)
        ·
          refine ⟨216709223281260437552087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 577891262083361166805565 216709223281260437552087)
          ·
            refine ⟨325063834921890656328131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216709223281260437552087 325063834921890656328131)
            ·
              refine ⟨487595752382835984492197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325063834921890656328131 487595752382835984492197)
              ·
                refine ⟨91424203571781747092287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487595752382835984492197 91424203571781747092287)
                ·
                  rfl

theorem cell19_300456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_300456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300456 prefixEnd_300456 := by exact prefixLift 300456
  have htrace : WordTrace (prefixWord ++ tailWord_300456) baseStart_300456 baseEnd_300456 := by
    simpa [prefixWord, tailWord_300456, baseEnd_300456] using wordTrace_append hprefix tailTrace_300456
  have hstable : (prefixWord ++ tailWord_300456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300456).length < 2 ^ (prefixWord ++ tailWord_300456).sum := by decide
  have hdescent : baseEnd_300456 < baseStart_300456 := by decide
  rcases family_descends (prefixWord ++ tailWord_300456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300464 : List Nat := [2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_300464 : Nat := 118140960795 + 300464 * 2 ^ 59
def prefixEnd_300464 : Nat := 4983230072969 + 3 ^ 40 * 300464 * 2
def baseEnd_300464 : Nat := 91426637850440098914487

theorem tailTrace_300464 : CollatzResearch.WordTrace tailWord_300464 prefixEnd_300464 91426637850440098914487 := by
  unfold tailWord_300464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479411191738859005450223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7305881588985145340600297 5479411191738859005450223)
  ·
    refine ⟨8219116787608288508175335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479411191738859005450223 8219116787608288508175335)
    ·
      refine ⟨12328675181412432762263003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219116787608288508175335 12328675181412432762263003)
      ·
        refine ⟨18493012772118649143394505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12328675181412432762263003 18493012772118649143394505)
        ·
          refine ⟨13869759579088986857545879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18493012772118649143394505 13869759579088986857545879)
          ·
            refine ⟨20804639368633480286318819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13869759579088986857545879 20804639368633480286318819)
            ·
              refine ⟨31206959052950220429478229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20804639368633480286318819 31206959052950220429478229)
              ·
                refine ⟨91426637850440098914487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31206959052950220429478229 91426637850440098914487)
                ·
                  rfl

theorem cell19_300464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_300464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300464 prefixEnd_300464 := by exact prefixLift 300464
  have htrace : WordTrace (prefixWord ++ tailWord_300464) baseStart_300464 baseEnd_300464 := by
    simpa [prefixWord, tailWord_300464, baseEnd_300464] using wordTrace_append hprefix tailTrace_300464
  have hstable : (prefixWord ++ tailWord_300464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300464).length < 2 ^ (prefixWord ++ tailWord_300464).sum := by decide
  have hdescent : baseEnd_300464 < baseStart_300464 := by decide
  rcases family_descends (prefixWord ++ tailWord_300464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300483 : List Nat := [1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_300483 : Nat := 118140960795 + 300483 * 2 ^ 59
def prefixEnd_300483 : Nat := 4983230072969 + 3 ^ 40 * 300483 * 2
def baseEnd_300483 : Nat := 91432419262253684492213

theorem tailTrace_300483 : CollatzResearch.WordTrace tailWord_300483 prefixEnd_300483 91432419262253684492213 := by
  unfold tailWord_300483
  simp only [CollatzResearch.WordTrace]
  refine ⟨10959515370408884255842103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7306343580272589503894735 10959515370408884255842103)
  ·
    refine ⟨16439273055613326383763155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10959515370408884255842103 16439273055613326383763155)
    ·
      refine ⟨24658909583419989575644733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16439273055613326383763155 24658909583419989575644733)
      ·
        refine ⟨9247091093782496090866775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24658909583419989575644733 9247091093782496090866775)
        ·
          refine ⟨13870636640673744136300163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9247091093782496090866775 13870636640673744136300163)
          ·
            refine ⟨20805954961010616204450245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13870636640673744136300163 20805954961010616204450245)
            ·
              refine ⟨3901116555189490538334421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20805954961010616204450245 3901116555189490538334421)
              ·
                refine ⟨91432419262253684492213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3901116555189490538334421 91432419262253684492213)
                ·
                  rfl

theorem cell19_300483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_300483 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300483 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300483 prefixEnd_300483 := by exact prefixLift 300483
  have htrace : WordTrace (prefixWord ++ tailWord_300483) baseStart_300483 baseEnd_300483 := by
    simpa [prefixWord, tailWord_300483, baseEnd_300483] using wordTrace_append hprefix tailTrace_300483
  have hstable : (prefixWord ++ tailWord_300483).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300483).length < 2 ^ (prefixWord ++ tailWord_300483).sum := by decide
  have hdescent : baseEnd_300483 < baseStart_300483 := by decide
  rcases family_descends (prefixWord ++ tailWord_300483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300534 : List Nat := [5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_300534 : Nat := 118140960795 + 300534 * 2 ^ 59
def prefixEnd_300534 : Nat := 4983230072969 + 3 ^ 40 * 300534 * 2
def baseEnd_300534 : Nat := 91447937788700677358741

theorem tailTrace_300534 : CollatzResearch.WordTrace tailWord_300534 prefixEnd_300534 91447937788700677358741 := by
  unfold tailWord_300534
  simp only [CollatzResearch.WordTrace]
  refine ⟨685085968326507497871791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7307583662149413310632437 685085968326507497871791)
  ·
    refine ⟨1027628952489761246807687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 685085968326507497871791 1027628952489761246807687)
    ·
      refine ⟨1541443428734641870211531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027628952489761246807687 1541443428734641870211531)
      ·
        refine ⟨2312165143101962805317297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541443428734641870211531 2312165143101962805317297)
        ·
          refine ⟨1734123857326472103987973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312165143101962805317297 1734123857326472103987973)
          ·
            refine ⟨325148223248713519497745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1734123857326472103987973 325148223248713519497745)
            ·
              refine ⟨243861167436535139623309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325148223248713519497745 243861167436535139623309)
              ·
                refine ⟨91447937788700677358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243861167436535139623309 91447937788700677358741)
                ·
                  rfl

theorem cell19_300534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_300534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300534 prefixEnd_300534 := by exact prefixLift 300534
  have htrace : WordTrace (prefixWord ++ tailWord_300534) baseStart_300534 baseEnd_300534 := by
    simpa [prefixWord, tailWord_300534, baseEnd_300534] using wordTrace_append hprefix tailTrace_300534
  have hstable : (prefixWord ++ tailWord_300534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300534).length < 2 ^ (prefixWord ++ tailWord_300534).sum := by decide
  have hdescent : baseEnd_300534 < baseStart_300534 := by decide
  rcases family_descends (prefixWord ++ tailWord_300534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300536 : List Nat := [2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_300536 : Nat := 118140960795 + 300536 * 2 ^ 59
def prefixEnd_300536 : Nat := 4983230072969 + 3 ^ 40 * 300536 * 2
def baseEnd_300536 : Nat := 91448546358365265314291

theorem tailTrace_300536 : CollatzResearch.WordTrace tailWord_300536 prefixEnd_300536 91448546358365265314291 := by
  unfold tailWord_300536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480724219608437153760731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7307632292811249538347641 5480724219608437153760731)
  ·
    refine ⟨8221086329412655730641097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5480724219608437153760731 8221086329412655730641097)
    ·
      refine ⟨6165814747059491797980823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8221086329412655730641097 6165814747059491797980823)
      ·
        refine ⟨9248722120589237696971235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165814747059491797980823 9248722120589237696971235)
        ·
          refine ⟨13873083180883856545456853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9248722120589237696971235 13873083180883856545456853)
          ·
            refine ⟨325150387051965387784145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 13873083180883856545456853 325150387051965387784145)
            ·
              refine ⟨243862790288974040838109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325150387051965387784145 243862790288974040838109)
              ·
                refine ⟨91448546358365265314291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243862790288974040838109 91448546358365265314291)
                ·
                  rfl

theorem cell19_300536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_300536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300536 prefixEnd_300536 := by exact prefixLift 300536
  have htrace : WordTrace (prefixWord ++ tailWord_300536) baseStart_300536 baseEnd_300536 := by
    simpa [prefixWord, tailWord_300536, baseEnd_300536] using wordTrace_append hprefix tailTrace_300536
  have hstable : (prefixWord ++ tailWord_300536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300536).length < 2 ^ (prefixWord ++ tailWord_300536).sum := by decide
  have hdescent : baseEnd_300536 < baseStart_300536 := by decide
  rcases family_descends (prefixWord ++ tailWord_300536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300555 : List Nat := [1, 1, 1, 1, 9, 1, 5]
def baseStart_300555 : Nat := 118140960795 + 300555 * 2 ^ 59
def prefixEnd_300555 : Nat := 4983230072969 + 3 ^ 40 * 300555 * 2
def baseEnd_300555 : Nat := 30484775923392950297339

theorem tailTrace_300555 : CollatzResearch.WordTrace tailWord_300555 prefixEnd_300555 30484775923392950297339 := by
  unfold tailWord_300555
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962141426148040552463119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7308094284098693701642079 10962141426148040552463119)
  ·
    refine ⟨16443212139222060828694679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10962141426148040552463119 16443212139222060828694679)
    ·
      refine ⟨24664818208833091243042019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16443212139222060828694679 24664818208833091243042019)
      ·
        refine ⟨36997227313249636864563029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24664818208833091243042019 36997227313249636864563029)
        ·
          refine ⟨216780628788572091003299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 36997227313249636864563029 216780628788572091003299)
          ·
            refine ⟨325170943182858136504949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216780628788572091003299 325170943182858136504949)
            ·
              refine ⟨30484775923392950297339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 325170943182858136504949 30484775923392950297339)
              ·
                rfl

theorem cell19_300555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_300555 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300555 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300555 prefixEnd_300555 := by exact prefixLift 300555
  have htrace : WordTrace (prefixWord ++ tailWord_300555) baseStart_300555 baseEnd_300555 := by
    simpa [prefixWord, tailWord_300555, baseEnd_300555] using wordTrace_append hprefix tailTrace_300555
  have hstable : (prefixWord ++ tailWord_300555).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300555).length < 2 ^ (prefixWord ++ tailWord_300555).sum := by decide
  have hdescent : baseEnd_300555 < baseStart_300555 := by decide
  rcases family_descends (prefixWord ++ tailWord_300555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300576 : List Nat := [2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_300576 : Nat := 118140960795 + 300576 * 2 ^ 59
def prefixEnd_300576 : Nat := 4983230072969 + 3 ^ 40 * 300576 * 2
def baseEnd_300576 : Nat := 91460717751657024425293

theorem tailTrace_300576 : CollatzResearch.WordTrace tailWord_300576 prefixEnd_300576 91460717751657024425293 := by
  unfold tailWord_300576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481453679535980569488791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7308604906047974092651721 5481453679535980569488791)
  ·
    refine ⟨8222180519303970854233187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5481453679535980569488791 8222180519303970854233187)
    ·
      refine ⟨12333270778955956281349781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8222180519303970854233187 12333270778955956281349781)
      ·
        refine ⟨578122067763560450688271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12333270778955956281349781 578122067763560450688271)
        ·
          refine ⟨867183101645340676032407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578122067763560450688271 867183101645340676032407)
          ·
            refine ⟨1300774652468011014048611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867183101645340676032407 1300774652468011014048611)
            ·
              refine ⟨1951161978702016521072917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300774652468011014048611 1951161978702016521072917)
              ·
                refine ⟨91460717751657024425293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1951161978702016521072917 91460717751657024425293)
                ·
                  rfl

theorem cell19_300576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_300576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300576 prefixEnd_300576 := by exact prefixLift 300576
  have htrace : WordTrace (prefixWord ++ tailWord_300576) baseStart_300576 baseEnd_300576 := by
    simpa [prefixWord, tailWord_300576, baseEnd_300576] using wordTrace_append hprefix tailTrace_300576
  have hstable : (prefixWord ++ tailWord_300576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300576).length < 2 ^ (prefixWord ++ tailWord_300576).sum := by decide
  have hdescent : baseEnd_300576 < baseStart_300576 := by decide
  rcases family_descends (prefixWord ++ tailWord_300576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300650 : List Nat := [3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_300650 : Nat := 118140960795 + 300650 * 2 ^ 59
def prefixEnd_300650 : Nat := 4983230072969 + 3 ^ 40 * 300650 * 2
def baseEnd_300650 : Nat := 91483234829246778780647

theorem tailTrace_300650 : CollatzResearch.WordTrace tailWord_300650 prefixEnd_300650 91483234829246778780647 := by
  unfold tailWord_300650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741401590200967944292851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7310404240535914518114269 2741401590200967944292851)
  ·
    refine ⟨4112102385301451916439277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2741401590200967944292851 4112102385301451916439277)
    ·
      refine ⟨1542038394488044468664729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4112102385301451916439277 1542038394488044468664729)
      ·
        refine ⟨1156528795866033351498547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1542038394488044468664729 1156528795866033351498547)
        ·
          refine ⟨1734793193799050027247821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156528795866033351498547 1734793193799050027247821)
          ·
            refine ⟨650547447674643760217933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1734793193799050027247821 650547447674643760217933)
            ·
              refine ⟨243955292877991410081725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 650547447674643760217933 243955292877991410081725)
              ·
                refine ⟨91483234829246778780647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243955292877991410081725 91483234829246778780647)
                ·
                  rfl

theorem cell19_300650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_300650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300650 prefixEnd_300650 := by exact prefixLift 300650
  have htrace : WordTrace (prefixWord ++ tailWord_300650) baseStart_300650 baseEnd_300650 := by
    simpa [prefixWord, tailWord_300650, baseEnd_300650] using wordTrace_append hprefix tailTrace_300650
  have hstable : (prefixWord ++ tailWord_300650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300650).length < 2 ^ (prefixWord ++ tailWord_300650).sum := by decide
  have hdescent : baseEnd_300650 < baseStart_300650 := by decide
  rcases family_descends (prefixWord ++ tailWord_300650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300703 : List Nat := [1, 1, 2, 7, 2, 1, 2, 3]
def baseStart_300703 : Nat := 118140960795 + 300703 * 2 ^ 59
def prefixEnd_300703 : Nat := 4983230072969 + 3 ^ 40 * 300703 * 2
def baseEnd_300703 : Nat := 91499361925358359602725

theorem tailTrace_300703 : CollatzResearch.WordTrace tailWord_300703 prefixEnd_300703 91499361925358359602725 := by
  unfold tailWord_300703
  simp only [CollatzResearch.WordTrace]
  refine ⟨10967539429611861828850763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7311692953074574552567175 10967539429611861828850763)
  ·
    refine ⟨16451309144417792743276145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10967539429611861828850763 16451309144417792743276145)
    ·
      refine ⟨12338481858313344557457109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16451309144417792743276145 12338481858313344557457109)
      ·
        refine ⟨289183168554219013065401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12338481858313344557457109 289183168554219013065401)
        ·
          refine ⟨216887376415664259799051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289183168554219013065401 216887376415664259799051)
          ·
            refine ⟨325331064623496389698577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216887376415664259799051 325331064623496389698577)
            ·
              refine ⟨243998298467622292273933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325331064623496389698577 243998298467622292273933)
              ·
                refine ⟨91499361925358359602725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243998298467622292273933 91499361925358359602725)
                ·
                  rfl

theorem cell19_300703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_300703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300703 prefixEnd_300703 := by exact prefixLift 300703
  have htrace : WordTrace (prefixWord ++ tailWord_300703) baseStart_300703 baseEnd_300703 := by
    simpa [prefixWord, tailWord_300703, baseEnd_300703] using wordTrace_append hprefix tailTrace_300703
  have hstable : (prefixWord ++ tailWord_300703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300703).length < 2 ^ (prefixWord ++ tailWord_300703).sum := by decide
  have hdescent : baseEnd_300703 < baseStart_300703 := by decide
  rcases family_descends (prefixWord ++ tailWord_300703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300709 : List Nat := [1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_300709 : Nat := 118140960795 + 300709 * 2 ^ 59
def prefixEnd_300709 : Nat := 4983230072969 + 3 ^ 40 * 300709 * 2
def baseEnd_300709 : Nat := 91501187634352123469375

theorem tailTrace_300709 : CollatzResearch.WordTrace tailWord_300709 prefixEnd_300709 91501187634352123469375 := by
  unfold tailWord_300709
  simp only [CollatzResearch.WordTrace]
  refine ⟨10967758267590124853569181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7311838845060083235712787 10967758267590124853569181)
  ·
    refine ⟨4112909350346296820088443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10967758267590124853569181 4112909350346296820088443)
    ·
      refine ⟨6169364025519445230132665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112909350346296820088443 6169364025519445230132665)
      ·
        refine ⟨4627023019139583922599499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6169364025519445230132665 4627023019139583922599499)
        ·
          refine ⟨6940534528709375883899249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627023019139583922599499 6940534528709375883899249)
          ·
            refine ⟨5205400896532031912924437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6940534528709375883899249 5205400896532031912924437)
            ·
              refine ⟨244003167024938995918333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5205400896532031912924437 244003167024938995918333)
              ·
                refine ⟨91501187634352123469375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244003167024938995918333 91501187634352123469375)
                ·
                  rfl

theorem cell19_300709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_300709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300709 prefixEnd_300709 := by exact prefixLift 300709
  have htrace : WordTrace (prefixWord ++ tailWord_300709) baseStart_300709 baseEnd_300709 := by
    simpa [prefixWord, tailWord_300709, baseEnd_300709] using wordTrace_append hprefix tailTrace_300709
  have hstable : (prefixWord ++ tailWord_300709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300709).length < 2 ^ (prefixWord ++ tailWord_300709).sum := by decide
  have hdescent : baseEnd_300709 < baseStart_300709 := by decide
  rcases family_descends (prefixWord ++ tailWord_300709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300726 : List Nat := [5, 1, 3, 1, 1, 1, 7]
def baseStart_300726 : Nat := 118140960795 + 300726 * 2 ^ 59
def prefixEnd_300726 : Nat := 4983230072969 + 3 ^ 40 * 300726 * 2
def baseEnd_300726 : Nat := 30502120158833707030517

theorem tailTrace_300726 : CollatzResearch.WordTrace tailWord_300726 prefixEnd_300726 30502120158833707030517 := by
  unfold tailWord_300726
  simp only [CollatzResearch.WordTrace]
  refine ⟨685523644283033547308627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7312252205685691171292021 685523644283033547308627)
  ·
    refine ⟨1028285466424550320962941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 685523644283033547308627 1028285466424550320962941)
    ·
      refine ⟨385607049909206370361103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1028285466424550320962941 385607049909206370361103)
      ·
        refine ⟨578410574863809555541655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385607049909206370361103 578410574863809555541655)
        ·
          refine ⟨867615862295714333312483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578410574863809555541655 867615862295714333312483)
          ·
            refine ⟨1301423793443571499968725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867615862295714333312483 1301423793443571499968725)
            ·
              refine ⟨30502120158833707030517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1301423793443571499968725 30502120158833707030517)
              ·
                rfl

theorem cell19_300726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_300726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_300726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_300726 prefixEnd_300726 := by exact prefixLift 300726
  have htrace : WordTrace (prefixWord ++ tailWord_300726) baseStart_300726 baseEnd_300726 := by
    simpa [prefixWord, tailWord_300726, baseEnd_300726] using wordTrace_append hprefix tailTrace_300726
  have hstable : (prefixWord ++ tailWord_300726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300726).length < 2 ^ (prefixWord ++ tailWord_300726).sum := by decide
  have hdescent : baseEnd_300726 < baseStart_300726 := by decide
  rcases family_descends (prefixWord ++ tailWord_300726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
