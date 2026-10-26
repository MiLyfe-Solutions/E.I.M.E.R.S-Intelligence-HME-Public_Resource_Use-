import V185TrunkScan19Chunk038

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_391784 : List Nat := [2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_391784 : Nat := 118140960795 + 391784 * 2 ^ 59
def prefixEnd_391784 : Nat := 4983230072969 + 3 ^ 40 * 391784 * 2
def baseEnd_391784 : Nat := 119213928735526149332281

theorem tailTrace_391784 : CollatzResearch.WordTrace tailWord_391784 prefixEnd_391784 119213928735526149332281 := by
  unfold tailWord_391784
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144768206320477112611203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9526357608427302816814937 7144768206320477112611203)
  ·
    refine ⟨10717152309480715668916805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7144768206320477112611203 10717152309480715668916805)
    ·
      refine ⟨2009466058027634187921901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10717152309480715668916805 2009466058027634187921901)
      ·
        refine ⟨753549771760362820470713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2009466058027634187921901 753549771760362820470713)
        ·
          refine ⟨565162328820272115353035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753549771760362820470713 565162328820272115353035)
          ·
            refine ⟨847743493230408173029553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565162328820272115353035 847743493230408173029553)
            ·
              refine ⟨635807619922806129772165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847743493230408173029553 635807619922806129772165)
              ·
                refine ⟨119213928735526149332281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635807619922806129772165 119213928735526149332281)
                ·
                  rfl

theorem cell19_391784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_391784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391784 prefixEnd_391784 := by exact prefixLift 391784
  have htrace : WordTrace (prefixWord ++ tailWord_391784) baseStart_391784 baseEnd_391784 := by
    simpa [prefixWord, tailWord_391784, baseEnd_391784] using wordTrace_append hprefix tailTrace_391784
  have hstable : (prefixWord ++ tailWord_391784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391784).length < 2 ^ (prefixWord ++ tailWord_391784).sum := by decide
  have hdescent : baseEnd_391784 < baseStart_391784 := by decide
  rcases family_descends (prefixWord ++ tailWord_391784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391786 : List Nat := [3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_391786 : Nat := 118140960795 + 391786 * 2 ^ 59
def prefixEnd_391786 : Nat := 4983230072969 + 3 ^ 40 * 391786 * 2
def baseEnd_391786 : Nat := 119214537305190737287831

theorem tailTrace_391786 : CollatzResearch.WordTrace tailWord_391786 prefixEnd_391786 119214537305190737287831 := by
  unfold tailWord_391786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572402339658427141698803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9526406239089139044530141 3572402339658427141698803)
  ·
    refine ⟨5358603509487640712548205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3572402339658427141698803 5358603509487640712548205)
    ·
      refine ⟨2009476316057865267205577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5358603509487640712548205 2009476316057865267205577)
      ·
        refine ⟨1507107237043398950404183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2009476316057865267205577 1507107237043398950404183)
        ·
          refine ⟨2260660855565098425606275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507107237043398950404183 2260660855565098425606275)
          ·
            refine ⟨3390991283347647638409413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260660855565098425606275 3390991283347647638409413)
            ·
              refine ⟨635810865627683932201765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3390991283347647638409413 635810865627683932201765)
              ·
                refine ⟨119214537305190737287831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635810865627683932201765 119214537305190737287831)
                ·
                  rfl

theorem cell19_391786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_391786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391786 prefixEnd_391786 := by exact prefixLift 391786
  have htrace : WordTrace (prefixWord ++ tailWord_391786) baseStart_391786 baseEnd_391786 := by
    simpa [prefixWord, tailWord_391786, baseEnd_391786] using wordTrace_append hprefix tailTrace_391786
  have hstable : (prefixWord ++ tailWord_391786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391786).length < 2 ^ (prefixWord ++ tailWord_391786).sum := by decide
  have hdescent : baseEnd_391786 < baseStart_391786 := by decide
  rcases family_descends (prefixWord ++ tailWord_391786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391788 : List Nat := [2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_391788 : Nat := 118140960795 + 391788 * 2 ^ 59
def prefixEnd_391788 : Nat := 4983230072969 + 3 ^ 40 * 391788 * 2
def baseEnd_391788 : Nat := 119215145874855325243381

theorem tailTrace_391788 : CollatzResearch.WordTrace tailWord_391788 prefixEnd_391788 119215145874855325243381 := by
  unfold tailWord_391788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144841152313231454184009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9526454869750975272245345 7144841152313231454184009)
  ·
    refine ⟨5358630864234923590638007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7144841152313231454184009 5358630864234923590638007)
    ·
      refine ⟨8037946296352385385957011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358630864234923590638007 8037946296352385385957011)
      ·
        refine ⟨12056919444528578078935517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8037946296352385385957011 12056919444528578078935517)
        ·
          refine ⟨4521344791698216779600819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12056919444528578078935517 4521344791698216779600819)
          ·
            refine ⟨6782017187547325169401229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521344791698216779600819 6782017187547325169401229)
            ·
              refine ⟨2543256445330246938525461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6782017187547325169401229 2543256445330246938525461)
              ·
                refine ⟨119215145874855325243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2543256445330246938525461 119215145874855325243381)
                ·
                  rfl

theorem cell19_391788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_391788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391788 prefixEnd_391788 := by exact prefixLift 391788
  have htrace : WordTrace (prefixWord ++ tailWord_391788) baseStart_391788 baseEnd_391788 := by
    simpa [prefixWord, tailWord_391788, baseEnd_391788] using wordTrace_append hprefix tailTrace_391788
  have hstable : (prefixWord ++ tailWord_391788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391788).length < 2 ^ (prefixWord ++ tailWord_391788).sum := by decide
  have hdescent : baseEnd_391788 < baseStart_391788 := by decide
  rcases family_descends (prefixWord ++ tailWord_391788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391841 : List Nat := [1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_391841 : Nat := 118140960795 + 391841 * 2 ^ 59
def prefixEnd_391841 : Nat := 4983230072969 + 3 ^ 40 * 391841 * 2
def baseEnd_391841 : Nat := 119231272970966906065459

theorem tailTrace_391841 : CollatzResearch.WordTrace tailWord_391841 prefixEnd_391841 119231272970966906065459 := by
  unfold tailWord_391841
  simp only [CollatzResearch.WordTrace]
  refine ⟨14291615373434452960047377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9527743582289635306698251 14291615373434452960047377)
  ·
    refine ⟨10718711530075839720035533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14291615373434452960047377 10718711530075839720035533)
    ·
      refine ⟨4019516823778439895013325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10718711530075839720035533 4019516823778439895013325)
      ·
        refine ⟨1507318808916914960629997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4019516823778439895013325 1507318808916914960629997)
        ·
          refine ⟨565244553343843110236249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1507318808916914960629997 565244553343843110236249)
          ·
            refine ⟨423933415007882332677187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565244553343843110236249 423933415007882332677187)
            ·
              refine ⟨635900122511823499015781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423933415007882332677187 635900122511823499015781)
              ·
                refine ⟨119231272970966906065459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635900122511823499015781 119231272970966906065459)
                ·
                  rfl

theorem cell19_391841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_391841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391841 prefixEnd_391841 := by exact prefixLift 391841
  have htrace : WordTrace (prefixWord ++ tailWord_391841) baseStart_391841 baseEnd_391841 := by
    simpa [prefixWord, tailWord_391841, baseEnd_391841] using wordTrace_append hprefix tailTrace_391841
  have hstable : (prefixWord ++ tailWord_391841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391841).length < 2 ^ (prefixWord ++ tailWord_391841).sum := by decide
  have hdescent : baseEnd_391841 < baseStart_391841 := by decide
  rcases family_descends (prefixWord ++ tailWord_391841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391919 : List Nat := [1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_391919 : Nat := 118140960795 + 391919 * 2 ^ 59
def prefixEnd_391919 : Nat := 4983230072969 + 3 ^ 40 * 391919 * 2
def baseEnd_391919 : Nat := 119255007187885836331913

theorem tailTrace_391919 : CollatzResearch.WordTrace tailWord_391919 prefixEnd_391919 119255007187885836331913 := by
  unfold tailWord_391919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14294460267151872281386811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9529640178101248187591207 14294460267151872281386811)
  ·
    refine ⟨21441690400727808422080217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14294460267151872281386811 21441690400727808422080217)
    ·
      refine ⟨16081267800545856316560163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21441690400727808422080217 16081267800545856316560163)
      ·
        refine ⟨24121901700818784474840245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16081267800545856316560163 24121901700818784474840245)
        ·
          refine ⟨2261428284451761044516273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24121901700818784474840245 2261428284451761044516273)
          ·
            refine ⟨1696071213338820783387205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2261428284451761044516273 1696071213338820783387205)
            ·
              refine ⟨318013352501028896885101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1696071213338820783387205 318013352501028896885101)
              ·
                refine ⟨119255007187885836331913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318013352501028896885101 119255007187885836331913)
                ·
                  rfl

theorem cell19_391919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_391919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391919 prefixEnd_391919 := by exact prefixLift 391919
  have htrace : WordTrace (prefixWord ++ tailWord_391919) baseStart_391919 baseEnd_391919 := by
    simpa [prefixWord, tailWord_391919, baseEnd_391919] using wordTrace_append hprefix tailTrace_391919
  have hstable : (prefixWord ++ tailWord_391919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391919).length < 2 ^ (prefixWord ++ tailWord_391919).sum := by decide
  have hdescent : baseEnd_391919 < baseStart_391919 := by decide
  rcases family_descends (prefixWord ++ tailWord_391919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391921 : List Nat := [1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_391921 : Nat := 118140960795 + 391921 * 2 ^ 59
def prefixEnd_391921 : Nat := 4983230072969 + 3 ^ 40 * 391921 * 2
def baseEnd_391921 : Nat := 119255615757550424287463

theorem tailTrace_391921 : CollatzResearch.WordTrace tailWord_391921 prefixEnd_391921 119255615757550424287463 := by
  unfold tailWord_391921
  simp only [CollatzResearch.WordTrace]
  refine ⟨14294533213144626622959617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9529688808763084415306411 14294533213144626622959617)
  ·
    refine ⟨10720899909858469967219713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14294533213144626622959617 10720899909858469967219713)
    ·
      refine ⟨8040674932393852475414785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10720899909858469967219713 8040674932393852475414785)
      ·
        refine ⟨6030506199295389356561089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8040674932393852475414785 6030506199295389356561089)
        ·
          refine ⟨4522879649471542017420817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6030506199295389356561089 4522879649471542017420817)
          ·
            refine ⟨3392159737103656513065613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4522879649471542017420817 3392159737103656513065613)
            ·
              refine ⟨1272059901413871192399605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3392159737103656513065613 1272059901413871192399605)
              ·
                refine ⟨119255615757550424287463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1272059901413871192399605 119255615757550424287463)
                ·
                  rfl

theorem cell19_391921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_391921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391921 prefixEnd_391921 := by exact prefixLift 391921
  have htrace : WordTrace (prefixWord ++ tailWord_391921) baseStart_391921 baseEnd_391921 := by
    simpa [prefixWord, tailWord_391921, baseEnd_391921] using wordTrace_append hprefix tailTrace_391921
  have hstable : (prefixWord ++ tailWord_391921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391921).length < 2 ^ (prefixWord ++ tailWord_391921).sum := by decide
  have hdescent : baseEnd_391921 < baseStart_391921 := by decide
  rcases family_descends (prefixWord ++ tailWord_391921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391938 : List Nat := [3, 4, 1, 1, 1, 2, 7]
def baseStart_391938 : Nat := 118140960795 + 391938 * 2 ^ 59
def prefixEnd_391938 : Nat := 4983230072969 + 3 ^ 40 * 391938 * 2
def baseEnd_391938 : Nat := 39753596199899807303213

theorem tailTrace_391938 : CollatzResearch.WordTrace tailWord_391938 prefixEnd_391938 39753596199899807303213 := by
  unfold tailWord_391938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573788313520759631582117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9530102169388692350885645 3573788313520759631582117)
  ·
    refine ⟨670085308785142430921647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3573788313520759631582117 670085308785142430921647)
    ·
      refine ⟨1005127963177713646382471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670085308785142430921647 1005127963177713646382471)
      ·
        refine ⟨1507691944766570469573707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005127963177713646382471 1507691944766570469573707)
        ·
          refine ⟨2261537917149855704360561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507691944766570469573707 2261537917149855704360561)
          ·
            refine ⟨1696153437862391778270421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2261537917149855704360561 1696153437862391778270421)
            ·
              refine ⟨39753596199899807303213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1696153437862391778270421 39753596199899807303213)
              ·
                rfl

theorem cell19_391938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_391938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391938 prefixEnd_391938 := by exact prefixLift 391938
  have htrace : WordTrace (prefixWord ++ tailWord_391938) baseStart_391938 baseEnd_391938 := by
    simpa [prefixWord, tailWord_391938, baseEnd_391938] using wordTrace_append hprefix tailTrace_391938
  have hstable : (prefixWord ++ tailWord_391938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391938).length < 2 ^ (prefixWord ++ tailWord_391938).sum := by decide
  have hdescent : baseEnd_391938 < baseStart_391938 := by decide
  rcases family_descends (prefixWord ++ tailWord_391938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391997 : List Nat := [1, 4, 1, 4, 9]
def baseStart_391997 : Nat := 118140960795 + 391997 * 2 ^ 59
def prefixEnd_391997 : Nat := 4983230072969 + 3 ^ 40 * 391997 * 2
def baseEnd_391997 : Nat := 4417731163140917281421

theorem tailTrace_391997 : CollatzResearch.WordTrace tailWord_391997 prefixEnd_391997 4417731163140917281421 := by
  unfold tailWord_391997
  simp only [CollatzResearch.WordTrace]
  refine ⟨14297305160869291602726245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9531536773912861068484163 14297305160869291602726245)
  ·
    refine ⟨2680744717662992175511171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14297305160869291602726245 2680744717662992175511171)
    ·
      refine ⟨4021117076494488263266757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680744717662992175511171 4021117076494488263266757)
      ·
        refine ⟨753959451842716549362517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4021117076494488263266757 753959451842716549362517)
        ·
          refine ⟨4417731163140917281421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 753959451842716549362517 4417731163140917281421)
          ·
            rfl

theorem cell19_391997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 9].length) (baseStart_391997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391997 prefixEnd_391997 := by exact prefixLift 391997
  have htrace : WordTrace (prefixWord ++ tailWord_391997) baseStart_391997 baseEnd_391997 := by
    simpa [prefixWord, tailWord_391997, baseEnd_391997] using wordTrace_append hprefix tailTrace_391997
  have hstable : (prefixWord ++ tailWord_391997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391997).length < 2 ^ (prefixWord ++ tailWord_391997).sum := by decide
  have hdescent : baseEnd_391997 < baseStart_391997 := by decide
  rcases family_descends (prefixWord ++ tailWord_391997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392016 : List Nat := [2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_392016 : Nat := 118140960795 + 392016 * 2 ^ 59
def prefixEnd_392016 : Nat := 4983230072969 + 3 ^ 40 * 392016 * 2
def baseEnd_392016 : Nat := 119284522816618352176093

theorem tailTrace_392016 : CollatzResearch.WordTrace tailWord_392016 prefixEnd_392016 119284522816618352176093 := by
  unfold tailWord_392016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148999073900228923833951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9531998765200305231778601 7148999073900228923833951)
  ·
    refine ⟨10723498610850343385750927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7148999073900228923833951 10723498610850343385750927)
    ·
      refine ⟨16085247916275515078626391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10723498610850343385750927 16085247916275515078626391)
      ·
        refine ⟨24127871874413272617939587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16085247916275515078626391 24127871874413272617939587)
        ·
          refine ⟨36191807811619908926909381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24127871874413272617939587 36191807811619908926909381)
          ·
            refine ⟨6785963964678732923795509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36191807811619908926909381 6785963964678732923795509)
            ·
              refine ⟨636184121688631211605829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6785963964678732923795509 636184121688631211605829)
              ·
                refine ⟨119284522816618352176093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636184121688631211605829 119284522816618352176093)
                ·
                  rfl

theorem cell19_392016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_392016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392016 prefixEnd_392016 := by exact prefixLift 392016
  have htrace : WordTrace (prefixWord ++ tailWord_392016) baseStart_392016 baseEnd_392016 := by
    simpa [prefixWord, tailWord_392016, baseEnd_392016] using wordTrace_append hprefix tailTrace_392016
  have hstable : (prefixWord ++ tailWord_392016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392016).length < 2 ^ (prefixWord ++ tailWord_392016).sum := by decide
  have hdescent : baseEnd_392016 < baseStart_392016 := by decide
  rcases family_descends (prefixWord ++ tailWord_392016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392086 : List Nat := [5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_392086 : Nat := 118140960795 + 392086 * 2 ^ 59
def prefixEnd_392086 : Nat := 4983230072969 + 3 ^ 40 * 392086 * 2
def baseEnd_392086 : Nat := 119305822754878930620347

theorem tailTrace_392086 : CollatzResearch.WordTrace tailWord_392086 prefixEnd_392086 119305822754878930620347 := by
  unfold tailWord_392086
  simp only [CollatzResearch.WordTrace]
  refine ⟨893784453596678737669757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9533700838364573201810741 893784453596678737669757)
  ·
    refine ⟨335169170098754526626159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 893784453596678737669757 335169170098754526626159)
    ·
      refine ⟨502753755148131789939239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335169170098754526626159 502753755148131789939239)
      ·
        refine ⟨754130632722197684908859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502753755148131789939239 754130632722197684908859)
        ·
          refine ⟨1131195949083296527363289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754130632722197684908859 1131195949083296527363289)
          ·
            refine ⟨848396961812472395522467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131195949083296527363289 848396961812472395522467)
            ·
              refine ⟨1272595442718708593283701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848396961812472395522467 1272595442718708593283701)
              ·
                refine ⟨119305822754878930620347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1272595442718708593283701 119305822754878930620347)
                ·
                  rfl

theorem cell19_392086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_392086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392086 prefixEnd_392086 := by exact prefixLift 392086
  have htrace : WordTrace (prefixWord ++ tailWord_392086) baseStart_392086 baseEnd_392086 := by
    simpa [prefixWord, tailWord_392086, baseEnd_392086] using wordTrace_append hprefix tailTrace_392086
  have hstable : (prefixWord ++ tailWord_392086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392086).length < 2 ^ (prefixWord ++ tailWord_392086).sum := by decide
  have hdescent : baseEnd_392086 < baseStart_392086 := by decide
  rcases family_descends (prefixWord ++ tailWord_392086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392090 : List Nat := [3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_392090 : Nat := 118140960795 + 392090 * 2 ^ 59
def prefixEnd_392090 : Nat := 4983230072969 + 3 ^ 40 * 392090 * 2
def baseEnd_392090 : Nat := 119307039894208106531447

theorem tailTrace_392090 : CollatzResearch.WordTrace tailWord_392090 prefixEnd_392090 119307039894208106531447 := by
  unfold tailWord_392090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575174287383092121465431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9533798099688245657241149 3575174287383092121465431)
  ·
    refine ⟨5362761431074638182198147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575174287383092121465431 5362761431074638182198147)
    ·
      refine ⟨8044142146611957273297221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362761431074638182198147 8044142146611957273297221)
      ·
        refine ⟨1508276652489741988743229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8044142146611957273297221 1508276652489741988743229)
        ·
          refine ⟨565603744683653245778711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1508276652489741988743229 565603744683653245778711)
          ·
            refine ⟨848405617025479868668067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565603744683653245778711 848405617025479868668067)
            ·
              refine ⟨1272608425538219803002101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848405617025479868668067 1272608425538219803002101)
              ·
                refine ⟨119307039894208106531447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1272608425538219803002101 119307039894208106531447)
                ·
                  rfl

theorem cell19_392090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_392090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392090 prefixEnd_392090 := by exact prefixLift 392090
  have htrace : WordTrace (prefixWord ++ tailWord_392090) baseStart_392090 baseEnd_392090 := by
    simpa [prefixWord, tailWord_392090, baseEnd_392090] using wordTrace_append hprefix tailTrace_392090
  have hstable : (prefixWord ++ tailWord_392090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392090).length < 2 ^ (prefixWord ++ tailWord_392090).sum := by decide
  have hdescent : baseEnd_392090 < baseStart_392090 := by decide
  rcases family_descends (prefixWord ++ tailWord_392090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392181 : List Nat := [1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_392181 : Nat := 118140960795 + 392181 * 2 ^ 59
def prefixEnd_392181 : Nat := 4983230072969 + 3 ^ 40 * 392181 * 2
def baseEnd_392181 : Nat := 119334729813946858508977

theorem tailTrace_392181 : CollatzResearch.WordTrace tailWord_392181 prefixEnd_392181 119334729813946858508977 := by
  unfold tailWord_392181
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304016192202691027424397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9536010794801794018282931 14304016192202691027424397)
  ·
    refine ⟨5364006072076009135284149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14304016192202691027424397 5364006072076009135284149)
    ·
      refine ⟨502875569257125856432889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5364006072076009135284149 502875569257125856432889)
      ·
        refine ⟨377156676942844392324667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502875569257125856432889 377156676942844392324667)
        ·
          refine ⟨565735015414266588487001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377156676942844392324667 565735015414266588487001)
          ·
            refine ⟨424301261560699941365251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565735015414266588487001 424301261560699941365251)
            ·
              refine ⟨636451892341049912047877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424301261560699941365251 636451892341049912047877)
              ·
                refine ⟨119334729813946858508977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636451892341049912047877 119334729813946858508977)
                ·
                  rfl

theorem cell19_392181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_392181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392181 prefixEnd_392181 := by exact prefixLift 392181
  have htrace : WordTrace (prefixWord ++ tailWord_392181) baseStart_392181 baseEnd_392181 := by
    simpa [prefixWord, tailWord_392181, baseEnd_392181] using wordTrace_append hprefix tailTrace_392181
  have hstable : (prefixWord ++ tailWord_392181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392181).length < 2 ^ (prefixWord ++ tailWord_392181).sum := by decide
  have hdescent : baseEnd_392181 < baseStart_392181 := by decide
  rcases family_descends (prefixWord ++ tailWord_392181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392204 : List Nat := [2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_392204 : Nat := 118140960795 + 392204 * 2 ^ 59
def prefixEnd_392204 : Nat := 4983230072969 + 3 ^ 40 * 392204 * 2
def baseEnd_392204 : Nat := 119341728365089619997803

theorem tailTrace_392204 : CollatzResearch.WordTrace tailWord_392204 prefixEnd_392204 119341728365089619997803 := by
  unfold tailWord_392204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152427535559682977755833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9536570047412910637007777 7152427535559682977755833)
  ·
    refine ⟨5364320651669762233316875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7152427535559682977755833 5364320651669762233316875)
    ·
      refine ⟨8046480977504643349975313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364320651669762233316875 8046480977504643349975313)
      ·
        refine ⟨6034860733128482512481485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8046480977504643349975313 6034860733128482512481485)
        ·
          refine ⟨2263072774923180942180557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6034860733128482512481485 2263072774923180942180557)
          ·
            refine ⟨848652290596192853317709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2263072774923180942180557 848652290596192853317709)
            ·
              refine ⟨318244608973572319994141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 848652290596192853317709 318244608973572319994141)
              ·
                refine ⟨119341728365089619997803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318244608973572319994141 119341728365089619997803)
                ·
                  rfl

theorem cell19_392204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_392204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392204 prefixEnd_392204 := by exact prefixLift 392204
  have htrace : WordTrace (prefixWord ++ tailWord_392204) baseStart_392204 baseEnd_392204 := by
    simpa [prefixWord, tailWord_392204, baseEnd_392204] using wordTrace_append hprefix tailTrace_392204
  have hstable : (prefixWord ++ tailWord_392204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392204).length < 2 ^ (prefixWord ++ tailWord_392204).sum := by decide
  have hdescent : baseEnd_392204 < baseStart_392204 := by decide
  rcases family_descends (prefixWord ++ tailWord_392204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392225 : List Nat := [1, 2, 3, 2, 3, 2, 6]
def baseStart_392225 : Nat := 118140960795 + 392225 * 2 ^ 59
def prefixEnd_392225 : Nat := 4983230072969 + 3 ^ 40 * 392225 * 2
def baseEnd_392225 : Nat := 39782706115522597843693

theorem tailTrace_392225 : CollatzResearch.WordTrace tailWord_392225 prefixEnd_392225 39782706115522597843693 := by
  unfold tailWord_392225
  simp only [CollatzResearch.WordTrace]
  refine ⟨14305621004043286542026129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9537080669362191028017419 14305621004043286542026129)
  ·
    refine ⟨10729215753032464906519597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14305621004043286542026129 10729215753032464906519597)
    ·
      refine ⟨4023455907387174339944849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10729215753032464906519597 4023455907387174339944849)
      ·
        refine ⟨3017591930540380754958637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4023455907387174339944849 3017591930540380754958637)
        ·
          refine ⟨1131596973952642783109489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3017591930540380754958637 1131596973952642783109489)
          ·
            refine ⟨848697730464482087332117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131596973952642783109489 848697730464482087332117)
            ·
              refine ⟨39782706115522597843693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 848697730464482087332117 39782706115522597843693)
              ·
                rfl

theorem cell19_392225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_392225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392225 prefixEnd_392225 := by exact prefixLift 392225
  have htrace : WordTrace (prefixWord ++ tailWord_392225) baseStart_392225 baseEnd_392225 := by
    simpa [prefixWord, tailWord_392225, baseEnd_392225] using wordTrace_append hprefix tailTrace_392225
  have hstable : (prefixWord ++ tailWord_392225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392225).length < 2 ^ (prefixWord ++ tailWord_392225).sum := by decide
  have hdescent : baseEnd_392225 < baseStart_392225 := by decide
  rcases family_descends (prefixWord ++ tailWord_392225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392257 : List Nat := [1, 2, 5, 1, 4, 1, 2, 3]
def baseStart_392257 : Nat := 118140960795 + 392257 * 2 ^ 59
def prefixEnd_392257 : Nat := 4983230072969 + 3 ^ 40 * 392257 * 2
def baseEnd_392257 : Nat := 119357855461201200819881

theorem tailTrace_392257 : CollatzResearch.WordTrace tailWord_392257 prefixEnd_392257 119357855461201200819881 := by
  unfold tailWord_392257
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306788139927356007191025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9537858759951570671460683 14306788139927356007191025)
  ·
    refine ⟨10730091104945517005393269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14306788139927356007191025 10730091104945517005393269)
    ·
      refine ⟨1005946041088642219255619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10730091104945517005393269 1005946041088642219255619)
      ·
        refine ⟨1508919061632963328883429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005946041088642219255619 1508919061632963328883429)
        ·
          refine ⟨282922324056180624165643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1508919061632963328883429 282922324056180624165643)
          ·
            refine ⟨424383486084270936248465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282922324056180624165643 424383486084270936248465)
            ·
              refine ⟨318287614563203202186349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424383486084270936248465 318287614563203202186349)
              ·
                refine ⟨119357855461201200819881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318287614563203202186349 119357855461201200819881)
                ·
                  rfl

theorem cell19_392257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_392257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392257 prefixEnd_392257 := by exact prefixLift 392257
  have htrace : WordTrace (prefixWord ++ tailWord_392257) baseStart_392257 baseEnd_392257 := by
    simpa [prefixWord, tailWord_392257, baseEnd_392257] using wordTrace_append hprefix tailTrace_392257
  have hstable : (prefixWord ++ tailWord_392257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392257).length < 2 ^ (prefixWord ++ tailWord_392257).sum := by decide
  have hdescent : baseEnd_392257 < baseStart_392257 := by decide
  rcases family_descends (prefixWord ++ tailWord_392257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392263 : List Nat := [1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_392263 : Nat := 118140960795 + 392263 * 2 ^ 59
def prefixEnd_392263 : Nat := 4983230072969 + 3 ^ 40 * 392263 * 2
def baseEnd_392263 : Nat := 119359681170194964686531

theorem tailTrace_392263 : CollatzResearch.WordTrace tailWord_392263 prefixEnd_392263 119359681170194964686531 := by
  unfold tailWord_392263
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307006977905619031909443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9538004651937079354606295 14307006977905619031909443)
  ·
    refine ⟨21460510466858428547864165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14307006977905619031909443 21460510466858428547864165)
    ·
      refine ⟨4023845712535955352724531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21460510466858428547864165 4023845712535955352724531)
      ·
        refine ⟨6035768568803933029086797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023845712535955352724531 6035768568803933029086797)
        ·
          refine ⟨2263413213301474885907549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6035768568803933029086797 2263413213301474885907549)
          ·
            refine ⟨848779954988053082215331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2263413213301474885907549 848779954988053082215331)
            ·
              refine ⟨1273169932482079623322997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848779954988053082215331 1273169932482079623322997)
              ·
                refine ⟨119359681170194964686531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1273169932482079623322997 119359681170194964686531)
                ·
                  rfl

theorem cell19_392263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_392263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392263 prefixEnd_392263 := by exact prefixLift 392263
  have htrace : WordTrace (prefixWord ++ tailWord_392263) baseStart_392263 baseEnd_392263 := by
    simpa [prefixWord, tailWord_392263, baseEnd_392263] using wordTrace_append hprefix tailTrace_392263
  have hstable : (prefixWord ++ tailWord_392263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392263).length < 2 ^ (prefixWord ++ tailWord_392263).sum := by decide
  have hdescent : baseEnd_392263 < baseStart_392263 := by decide
  rcases family_descends (prefixWord ++ tailWord_392263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392301 : List Nat := [1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_392301 : Nat := 118140960795 + 392301 * 2 ^ 59
def prefixEnd_392301 : Nat := 4983230072969 + 3 ^ 40 * 392301 * 2
def baseEnd_392301 : Nat := 119371243993822135841983

theorem tailTrace_392301 : CollatzResearch.WordTrace tailWord_392301 prefixEnd_392301 119371243993822135841983 := by
  unfold tailWord_392301
  simp only [CollatzResearch.WordTrace]
  refine ⟨14308392951767951521792757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9538928634511967681195171 14308392951767951521792757)
  ·
    refine ⟨1341411839228245455168071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14308392951767951521792757 1341411839228245455168071)
    ·
      refine ⟨2012117758842368182752107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341411839228245455168071 2012117758842368182752107)
      ·
        refine ⟨3018176638263552274128161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012117758842368182752107 3018176638263552274128161)
        ·
          refine ⟨2263632478697664205596121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3018176638263552274128161 2263632478697664205596121)
          ·
            refine ⟨1697724359023248154197091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263632478697664205596121 1697724359023248154197091)
            ·
              refine ⟨2546586538534872231295637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697724359023248154197091 2546586538534872231295637)
              ·
                refine ⟨119371243993822135841983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2546586538534872231295637 119371243993822135841983)
                ·
                  rfl

theorem cell19_392301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_392301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392301 prefixEnd_392301 := by exact prefixLift 392301
  have htrace : WordTrace (prefixWord ++ tailWord_392301) baseStart_392301 baseEnd_392301 := by
    simpa [prefixWord, tailWord_392301, baseEnd_392301] using wordTrace_append hprefix tailTrace_392301
  have hstable : (prefixWord ++ tailWord_392301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392301).length < 2 ^ (prefixWord ++ tailWord_392301).sum := by decide
  have hdescent : baseEnd_392301 < baseStart_392301 := by decide
  rcases family_descends (prefixWord ++ tailWord_392301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392354 : List Nat := [3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_392354 : Nat := 118140960795 + 392354 * 2 ^ 59
def prefixEnd_392354 : Nat := 4983230072969 + 3 ^ 40 * 392354 * 2
def baseEnd_392354 : Nat := 119387371089933716664061

theorem tailTrace_392354 : CollatzResearch.WordTrace tailWord_392354 prefixEnd_392354 119387371089933716664061 := by
  unfold tailWord_392354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577581505143985393368029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9540217347050627715648077 3577581505143985393368029)
  ·
    refine ⟨1341593064428994522513011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3577581505143985393368029 1341593064428994522513011)
    ·
      refine ⟨2012389596643491783769517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341593064428994522513011 2012389596643491783769517)
      ·
        refine ⟨754646098741309418913569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2012389596643491783769517 754646098741309418913569)
        ·
          refine ⟨565984574055982064185177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754646098741309418913569 565984574055982064185177)
          ·
            refine ⟨424488430541986548138883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565984574055982064185177 424488430541986548138883)
            ·
              refine ⟨636732645812979822208325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424488430541986548138883 636732645812979822208325)
              ·
                refine ⟨119387371089933716664061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636732645812979822208325 119387371089933716664061)
                ·
                  rfl

theorem cell19_392354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_392354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392354 prefixEnd_392354 := by exact prefixLift 392354
  have htrace : WordTrace (prefixWord ++ tailWord_392354) baseStart_392354 baseEnd_392354 := by
    simpa [prefixWord, tailWord_392354, baseEnd_392354] using wordTrace_append hprefix tailTrace_392354
  have hstable : (prefixWord ++ tailWord_392354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392354).length < 2 ^ (prefixWord ++ tailWord_392354).sum := by decide
  have hdescent : baseEnd_392354 < baseStart_392354 := by decide
  rcases family_descends (prefixWord ++ tailWord_392354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392356 : List Nat := [2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_392356 : Nat := 118140960795 + 392356 * 2 ^ 59
def prefixEnd_392356 : Nat := 4983230072969 + 3 ^ 40 * 392356 * 2
def baseEnd_392356 : Nat := 119387979659598304619611

theorem tailTrace_392356 : CollatzResearch.WordTrace tailWord_392356 prefixEnd_392356 119387979659598304619611 := by
  unfold tailWord_392356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7155199483284347957522461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9540265977712463943363281 7155199483284347957522461)
  ·
    refine ⟨2683199806231630484070923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7155199483284347957522461 2683199806231630484070923)
    ·
      refine ⟨4024799709347445726106385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683199806231630484070923 4024799709347445726106385)
      ·
        refine ⟨3018599782010584294579789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4024799709347445726106385 3018599782010584294579789)
        ·
          refine ⟨1131974918253969110467421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3018599782010584294579789 1131974918253969110467421)
          ·
            refine ⟨424490594345238416425283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1131974918253969110467421 424490594345238416425283)
            ·
              refine ⟨636735891517857624637925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424490594345238416425283 636735891517857624637925)
              ·
                refine ⟨119387979659598304619611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636735891517857624637925 119387979659598304619611)
                ·
                  rfl

theorem cell19_392356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_392356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392356 prefixEnd_392356 := by exact prefixLift 392356
  have htrace : WordTrace (prefixWord ++ tailWord_392356) baseStart_392356 baseEnd_392356 := by
    simpa [prefixWord, tailWord_392356, baseEnd_392356] using wordTrace_append hprefix tailTrace_392356
  have hstable : (prefixWord ++ tailWord_392356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392356).length < 2 ^ (prefixWord ++ tailWord_392356).sum := by decide
  have hdescent : baseEnd_392356 < baseStart_392356 := by decide
  rcases family_descends (prefixWord ++ tailWord_392356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392390 : List Nat := [6, 1, 2, 2, 1, 1, 6]
def baseStart_392390 : Nat := 118140960795 + 392390 * 2 ^ 59
def prefixEnd_392390 : Nat := 4983230072969 + 3 ^ 40 * 392390 * 2
def baseEnd_392390 : Nat := 39799441781298766621321

theorem tailTrace_392390 : CollatzResearch.WordTrace tailWord_392390 prefixEnd_392390 39799441781298766621321 := by
  unfold tailWord_392390
  simp only [CollatzResearch.WordTrace]
  refine ⟨447238720263922491305707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9541092698963679814521749 447238720263922491305707)
  ·
    refine ⟨670858080395883736958561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 447238720263922491305707 670858080395883736958561)
    ·
      refine ⟨503143560296912802718921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 670858080395883736958561 503143560296912802718921)
      ·
        refine ⟨377357670222684602039191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503143560296912802718921 377357670222684602039191)
        ·
          refine ⟨566036505334026903058787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377357670222684602039191 566036505334026903058787)
          ·
            refine ⟨849054758001040354588181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566036505334026903058787 849054758001040354588181)
            ·
              refine ⟨39799441781298766621321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 849054758001040354588181 39799441781298766621321)
              ·
                rfl

theorem cell19_392390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_392390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392390 prefixEnd_392390 := by exact prefixLift 392390
  have htrace : WordTrace (prefixWord ++ tailWord_392390) baseStart_392390 baseEnd_392390 := by
    simpa [prefixWord, tailWord_392390, baseEnd_392390] using wordTrace_append hprefix tailTrace_392390
  have hstable : (prefixWord ++ tailWord_392390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392390).length < 2 ^ (prefixWord ++ tailWord_392390).sum := by decide
  have hdescent : baseEnd_392390 < baseStart_392390 := by decide
  rcases family_descends (prefixWord ++ tailWord_392390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392472 : List Nat := [2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_392472 : Nat := 118140960795 + 392472 * 2 ^ 59
def prefixEnd_392472 : Nat := 4983230072969 + 3 ^ 40 * 392472 * 2
def baseEnd_392472 : Nat := 119423276700144406041517

theorem tailTrace_392472 : CollatzResearch.WordTrace tailWord_392472 prefixEnd_392472 119423276700144406041517 := by
  unfold tailWord_392472
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157314917074223863133835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9543086556098965150845113 7157314917074223863133835)
  ·
    refine ⟨10735972375611335794700753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7157314917074223863133835 10735972375611335794700753)
    ·
      refine ⟨8051979281708501846025565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10735972375611335794700753 8051979281708501846025565)
      ·
        refine ⟨3019492230640688192259587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8051979281708501846025565 3019492230640688192259587)
        ·
          refine ⟨4529238345961032288389381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019492230640688192259587 4529238345961032288389381)
          ·
            refine ⟨849232189867693554073009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4529238345961032288389381 849232189867693554073009)
            ·
              refine ⟨636924142400770165554757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849232189867693554073009 636924142400770165554757)
              ·
                refine ⟨119423276700144406041517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636924142400770165554757 119423276700144406041517)
                ·
                  rfl

theorem cell19_392472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_392472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392472 prefixEnd_392472 := by exact prefixLift 392472
  have htrace : WordTrace (prefixWord ++ tailWord_392472) baseStart_392472 baseEnd_392472 := by
    simpa [prefixWord, tailWord_392472, baseEnd_392472] using wordTrace_append hprefix tailTrace_392472
  have hstable : (prefixWord ++ tailWord_392472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392472).length < 2 ^ (prefixWord ++ tailWord_392472).sum := by decide
  have hdescent : baseEnd_392472 < baseStart_392472 := by decide
  rcases family_descends (prefixWord ++ tailWord_392472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392546 : List Nat := [3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_392546 : Nat := 118140960795 + 392546 * 2 ^ 59
def prefixEnd_392546 : Nat := 4983230072969 + 3 ^ 40 * 392546 * 2
def baseEnd_392546 : Nat := 119445793777734160396871

theorem tailTrace_392546 : CollatzResearch.WordTrace tailWord_392546 prefixEnd_392546 119445793777734160396871 := by
  unfold tailWord_392546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579332208970089591115373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9544885890586905576307661 3579332208970089591115373)
  ·
    refine ⟨1342249578363783596668265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3579332208970089591115373 1342249578363783596668265)
    ·
      refine ⟨1006687183772837697501199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1342249578363783596668265 1006687183772837697501199)
      ·
        refine ⟨1510030775659256546251799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006687183772837697501199 1510030775659256546251799)
        ·
          refine ⟨2265046163488884819377699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510030775659256546251799 2265046163488884819377699)
          ·
            refine ⟨3397569245233327229066549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265046163488884819377699 3397569245233327229066549)
            ·
              refine ⟨318522116740624427724989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3397569245233327229066549 318522116740624427724989)
              ·
                refine ⟨119445793777734160396871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318522116740624427724989 119445793777734160396871)
                ·
                  rfl

theorem cell19_392546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_392546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392546 prefixEnd_392546 := by exact prefixLift 392546
  have htrace : WordTrace (prefixWord ++ tailWord_392546) baseStart_392546 baseEnd_392546 := by
    simpa [prefixWord, tailWord_392546, baseEnd_392546] using wordTrace_append hprefix tailTrace_392546
  have hstable : (prefixWord ++ tailWord_392546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392546).length < 2 ^ (prefixWord ++ tailWord_392546).sum := by decide
  have hdescent : baseEnd_392546 < baseStart_392546 := by decide
  rcases family_descends (prefixWord ++ tailWord_392546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392588 : List Nat := [2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_392588 : Nat := 118140960795 + 392588 * 2 ^ 59
def prefixEnd_392588 : Nat := 4983230072969 + 3 ^ 40 * 392588 * 2
def baseEnd_392588 : Nat := 119458573740690507463423

theorem tailTrace_392588 : CollatzResearch.WordTrace tailWord_392588 prefixEnd_392588 119458573740690507463423 := by
  unfold tailWord_392588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159430350864099768745209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9545907134485466358326945 7159430350864099768745209)
  ·
    refine ⟨5369572763148074826558907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7159430350864099768745209 5369572763148074826558907)
    ·
      refine ⟨8054359144722112239838361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5369572763148074826558907 8054359144722112239838361)
      ·
        refine ⟨6040769358541584179878771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8054359144722112239838361 6040769358541584179878771)
        ·
          refine ⟨9061154037812376269818157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040769358541584179878771 9061154037812376269818157)
          ·
            refine ⟨3397932764179641101181809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9061154037812376269818157 3397932764179641101181809)
            ·
              refine ⟨2548449573134730825886357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3397932764179641101181809 2548449573134730825886357)
              ·
                refine ⟨119458573740690507463423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2548449573134730825886357 119458573740690507463423)
                ·
                  rfl

theorem cell19_392588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_392588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392588 prefixEnd_392588 := by exact prefixLift 392588
  have htrace : WordTrace (prefixWord ++ tailWord_392588) baseStart_392588 baseEnd_392588 := by
    simpa [prefixWord, tailWord_392588, baseEnd_392588] using wordTrace_append hprefix tailTrace_392588
  have hstable : (prefixWord ++ tailWord_392588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392588).length < 2 ^ (prefixWord ++ tailWord_392588).sum := by decide
  have hdescent : baseEnd_392588 < baseStart_392588 := by decide
  rcases family_descends (prefixWord ++ tailWord_392588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392605 : List Nat := [1, 4, 2, 1, 3, 2, 1, 5]
def baseStart_392605 : Nat := 118140960795 + 392605 * 2 ^ 59
def prefixEnd_392605 : Nat := 4983230072969 + 3 ^ 40 * 392605 * 2
def baseEnd_392605 : Nat := 119463746582839505085599

theorem tailTrace_392605 : CollatzResearch.WordTrace tailWord_392605 prefixEnd_392605 119463746582839505085599 := by
  unfold tailWord_392605
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319480742666611440859269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9546320495111074293906179 14319480742666611440859269)
  ·
    refine ⟨2684902639249989645161113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14319480742666611440859269 2684902639249989645161113)
    ·
      refine ⟨2013676979437492233870835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2684902639249989645161113 2013676979437492233870835)
      ·
        refine ⟨3020515469156238350806253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013676979437492233870835 3020515469156238350806253)
        ·
          refine ⟨1132693300933589381552345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3020515469156238350806253 1132693300933589381552345)
          ·
            refine ⟨849519975700192036164259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132693300933589381552345 849519975700192036164259)
            ·
              refine ⟨1274279963550288054246389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849519975700192036164259 1274279963550288054246389)
              ·
                refine ⟨119463746582839505085599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1274279963550288054246389 119463746582839505085599)
                ·
                  rfl

theorem cell19_392605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_392605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392605 prefixEnd_392605 := by exact prefixLift 392605
  have htrace : WordTrace (prefixWord ++ tailWord_392605) baseStart_392605 baseEnd_392605 := by
    simpa [prefixWord, tailWord_392605, baseEnd_392605] using wordTrace_append hprefix tailTrace_392605
  have hstable : (prefixWord ++ tailWord_392605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392605).length < 2 ^ (prefixWord ++ tailWord_392605).sum := by decide
  have hdescent : baseEnd_392605 < baseStart_392605 := by decide
  rcases family_descends (prefixWord ++ tailWord_392605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392664 : List Nat := [2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_392664 : Nat := 118140960795 + 392664 * 2 ^ 59
def prefixEnd_392664 : Nat := 4983230072969 + 3 ^ 40 * 392664 * 2
def baseEnd_392664 : Nat := 119481699387944849774327

theorem tailTrace_392664 : CollatzResearch.WordTrace tailWord_392664 prefixEnd_392664 119481699387944849774327 := by
  unfold tailWord_392664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160816324726432258628523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9547755099635243011504697 7160816324726432258628523)
  ·
    refine ⟨10741224487089648387942785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160816324726432258628523 10741224487089648387942785)
    ·
      refine ⟨8055918365317236290957089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10741224487089648387942785 8055918365317236290957089)
      ·
        refine ⟨6041938773987927218217817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8055918365317236290957089 6041938773987927218217817)
        ·
          refine ⟨4531454080490945413663363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6041938773987927218217817 4531454080490945413663363)
          ·
            refine ⟨6797181120736418120495045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531454080490945413663363 6797181120736418120495045)
            ·
              refine ⟨1274471460138078397592821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6797181120736418120495045 1274471460138078397592821)
              ·
                refine ⟨119481699387944849774327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1274471460138078397592821 119481699387944849774327)
                ·
                  rfl

theorem cell19_392664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_392664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392664 prefixEnd_392664 := by exact prefixLift 392664
  have htrace : WordTrace (prefixWord ++ tailWord_392664) baseStart_392664 baseEnd_392664 := by
    simpa [prefixWord, tailWord_392664, baseEnd_392664] using wordTrace_append hprefix tailTrace_392664
  have hstable : (prefixWord ++ tailWord_392664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392664).length < 2 ^ (prefixWord ++ tailWord_392664).sum := by decide
  have hdescent : baseEnd_392664 < baseStart_392664 := by decide
  rcases family_descends (prefixWord ++ tailWord_392664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392778 : List Nat := [3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_392778 : Nat := 118140960795 + 392778 * 2 ^ 59
def prefixEnd_392778 : Nat := 4983230072969 + 3 ^ 40 * 392778 * 2
def baseEnd_392778 : Nat := 119516387858826363240683

theorem tailTrace_392778 : CollatzResearch.WordTrace tailWord_392778 prefixEnd_392778 119516387858826363240683 := by
  unfold tailWord_392778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581447642759965496726747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9550527047359907991271325 3581447642759965496726747)
  ·
    refine ⟨5372171464139948245090121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3581447642759965496726747 5372171464139948245090121)
    ·
      refine ⟨4029128598104961183817591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5372171464139948245090121 4029128598104961183817591)
      ·
        refine ⟨6043692897157441775726387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029128598104961183817591 6043692897157441775726387)
        ·
          refine ⟨9065539345736162663589581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6043692897157441775726387 9065539345736162663589581)
          ·
            refine ⟨3399577254651060998846093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9065539345736162663589581 3399577254651060998846093)
            ·
              refine ⟨1274841470494147874567285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3399577254651060998846093 1274841470494147874567285)
              ·
                refine ⟨119516387858826363240683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1274841470494147874567285 119516387858826363240683)
                ·
                  rfl

theorem cell19_392778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_392778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392778 prefixEnd_392778 := by exact prefixLift 392778
  have htrace : WordTrace (prefixWord ++ tailWord_392778) baseStart_392778 baseEnd_392778 := by
    simpa [prefixWord, tailWord_392778, baseEnd_392778] using wordTrace_append hprefix tailTrace_392778
  have hstable : (prefixWord ++ tailWord_392778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392778).length < 2 ^ (prefixWord ++ tailWord_392778).sum := by decide
  have hdescent : baseEnd_392778 < baseStart_392778 := by decide
  rcases family_descends (prefixWord ++ tailWord_392778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392816 : List Nat := [2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_392816 : Nat := 118140960795 + 392816 * 2 ^ 59
def prefixEnd_392816 : Nat := 4983230072969 + 3 ^ 40 * 392816 * 2
def baseEnd_392816 : Nat := 119527950682453534396135

theorem tailTrace_392816 : CollatzResearch.WordTrace tailWord_392816 prefixEnd_392816 119527950682453534396135 := by
  unfold tailWord_392816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163588272451097238395151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9551451029934796317860201 7163588272451097238395151)
  ·
    refine ⟨10745382408676645857592727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7163588272451097238395151 10745382408676645857592727)
    ·
      refine ⟨16118073613014968786389091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10745382408676645857592727 16118073613014968786389091)
      ·
        refine ⟨24177110419522453179583637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16118073613014968786389091 24177110419522453179583637)
        ·
          refine ⟨1133302050915114992792983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24177110419522453179583637 1133302050915114992792983)
          ·
            refine ⟨1699953076372672489189475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133302050915114992792983 1699953076372672489189475)
            ·
              refine ⟨2549929614559008733784213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699953076372672489189475 2549929614559008733784213)
              ·
                refine ⟨119527950682453534396135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2549929614559008733784213 119527950682453534396135)
                ·
                  rfl

theorem cell19_392816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_392816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392816 prefixEnd_392816 := by exact prefixLift 392816
  have htrace : WordTrace (prefixWord ++ tailWord_392816) baseStart_392816 baseEnd_392816 := by
    simpa [prefixWord, tailWord_392816, baseEnd_392816] using wordTrace_append hprefix tailTrace_392816
  have hstable : (prefixWord ++ tailWord_392816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392816).length < 2 ^ (prefixWord ++ tailWord_392816).sum := by decide
  have hdescent : baseEnd_392816 < baseStart_392816 := by decide
  rcases family_descends (prefixWord ++ tailWord_392816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392852 : List Nat := [2, 4, 2, 2, 2, 7]
def baseStart_392852 : Nat := 118140960795 + 392852 * 2 ^ 59
def prefixEnd_392852 : Nat := 4983230072969 + 3 ^ 40 * 392852 * 2
def baseEnd_392852 : Nat := 13282100548490679732893

theorem tailTrace_392852 : CollatzResearch.WordTrace tailWord_392852 prefixEnd_392852 13282100548490679732893 := by
  unfold tailWord_392852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164244786385886312550405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9552326381847848416733873 7164244786385886312550405)
  ·
    refine ⟨1343295897447353683603201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7164244786385886312550405 1343295897447353683603201)
    ·
      refine ⟨1007471923085515262702401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1343295897447353683603201 1007471923085515262702401)
      ·
        refine ⟨755603942314136447026801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1007471923085515262702401 755603942314136447026801)
        ·
          refine ⟨566702956735602335270101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755603942314136447026801 566702956735602335270101)
          ·
            refine ⟨13282100548490679732893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 566702956735602335270101 13282100548490679732893)
            ·
              rfl

theorem cell19_392852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_392852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392852 prefixEnd_392852 := by exact prefixLift 392852
  have htrace : WordTrace (prefixWord ++ tailWord_392852) baseStart_392852 baseEnd_392852 := by
    simpa [prefixWord, tailWord_392852, baseEnd_392852] using wordTrace_append hprefix tailTrace_392852
  have hstable : (prefixWord ++ tailWord_392852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392852).length < 2 ^ (prefixWord ++ tailWord_392852).sum := by decide
  have hdescent : baseEnd_392852 < baseStart_392852 := by decide
  rcases family_descends (prefixWord ++ tailWord_392852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392886 : List Nat := [5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_392886 : Nat := 118140960795 + 392886 * 2 ^ 59
def prefixEnd_392886 : Nat := 4983230072969 + 3 ^ 40 * 392886 * 2
def baseEnd_392886 : Nat := 119549250620714112840389

theorem tailTrace_392886 : CollatzResearch.WordTrace tailWord_392886 prefixEnd_392886 119549250620714112840389 := by
  unfold tailWord_392886
  simp only [CollatzResearch.WordTrace]
  refine ⟨895608103415537276989907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9553153103099064287892341 895608103415537276989907)
  ·
    refine ⟨1343412155123305915484861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 895608103415537276989907 1343412155123305915484861)
    ·
      refine ⟨503779558171239718306823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1343412155123305915484861 503779558171239718306823)
      ·
        refine ⟨755669337256859577460235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503779558171239718306823 755669337256859577460235)
        ·
          refine ⟨1133504005885289366190353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755669337256859577460235 1133504005885289366190353)
          ·
            refine ⟨850128004413967024642765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1133504005885289366190353 850128004413967024642765)
            ·
              refine ⟨318798001655237634241037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 850128004413967024642765 318798001655237634241037)
              ·
                refine ⟨119549250620714112840389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318798001655237634241037 119549250620714112840389)
                ·
                  rfl

theorem cell19_392886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_392886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392886 prefixEnd_392886 := by exact prefixLift 392886
  have htrace : WordTrace (prefixWord ++ tailWord_392886) baseStart_392886 baseEnd_392886 := by
    simpa [prefixWord, tailWord_392886, baseEnd_392886] using wordTrace_append hprefix tailTrace_392886
  have hstable : (prefixWord ++ tailWord_392886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392886).length < 2 ^ (prefixWord ++ tailWord_392886).sum := by decide
  have hdescent : baseEnd_392886 < baseStart_392886 := by decide
  rcases family_descends (prefixWord ++ tailWord_392886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392890 : List Nat := [3, 1, 1, 1, 2, 5, 3, 3]
def baseStart_392890 : Nat := 118140960795 + 392890 * 2 ^ 59
def prefixEnd_392890 : Nat := 4983230072969 + 3 ^ 40 * 392890 * 2
def baseEnd_392890 : Nat := 119550467760043288751489

theorem tailTrace_392890 : CollatzResearch.WordTrace tailWord_392890 prefixEnd_392890 119550467760043288751489 := by
  unfold tailWord_392890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582468886658526278746031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9553250364422736743322749 3582468886658526278746031)
  ·
    refine ⟨5373703329987789418119047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3582468886658526278746031 5373703329987789418119047)
    ·
      refine ⟨8060554994981684127178571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5373703329987789418119047 8060554994981684127178571)
      ·
        refine ⟨12090832492472526190767857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060554994981684127178571 12090832492472526190767857)
        ·
          refine ⟨9068124369354394643075893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12090832492472526190767857 9068124369354394643075893)
          ·
            refine ⟨850136659626974497788365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9068124369354394643075893 850136659626974497788365)
            ·
              refine ⟨318801247360115436670637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 850136659626974497788365 318801247360115436670637)
              ·
                refine ⟨119550467760043288751489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318801247360115436670637 119550467760043288751489)
                ·
                  rfl

theorem cell19_392890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_392890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_392890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_392890 prefixEnd_392890 := by exact prefixLift 392890
  have htrace : WordTrace (prefixWord ++ tailWord_392890) baseStart_392890 baseEnd_392890 := by
    simpa [prefixWord, tailWord_392890, baseEnd_392890] using wordTrace_append hprefix tailTrace_392890
  have hstable : (prefixWord ++ tailWord_392890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392890).length < 2 ^ (prefixWord ++ tailWord_392890).sum := by decide
  have hdescent : baseEnd_392890 < baseStart_392890 := by decide
  rcases family_descends (prefixWord ++ tailWord_392890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393027 : List Nat := [1, 1, 1, 3, 1, 12]
def baseStart_393027 : Nat := 118140960795 + 393027 * 2 ^ 59
def prefixEnd_393027 : Nat := 4983230072969 + 3 ^ 40 * 393027 * 2
def baseEnd_393027 : Nat := 13288017198007507078519

theorem tailTrace_393027 : CollatzResearch.WordTrace tailWord_393027 prefixEnd_393027 13288017198007507078519 := by
  unfold tailWord_393027
  simp only [CollatzResearch.WordTrace]
  refine ⟨14334872347137777512721335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9556581564758518341814223 14334872347137777512721335)
  ·
    refine ⟨21502308520706666269082003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14334872347137777512721335 21502308520706666269082003)
    ·
      refine ⟨32253462781059999403623005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21502308520706666269082003 32253462781059999403623005)
      ·
        refine ⟨12095048542897499776358627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32253462781059999403623005 12095048542897499776358627)
        ·
          refine ⟨18142572814346249664537941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095048542897499776358627 18142572814346249664537941)
          ·
            refine ⟨13288017198007507078519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18142572814346249664537941 13288017198007507078519)
            ·
              rfl

theorem cell19_393027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_393027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393027 prefixEnd_393027 := by exact prefixLift 393027
  have htrace : WordTrace (prefixWord ++ tailWord_393027) baseStart_393027 baseEnd_393027 := by
    simpa [prefixWord, tailWord_393027, baseEnd_393027] using wordTrace_append hprefix tailTrace_393027
  have hstable : (prefixWord ++ tailWord_393027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393027).length < 2 ^ (prefixWord ++ tailWord_393027).sum := by decide
  have hdescent : baseEnd_393027 < baseStart_393027 := by decide
  rcases family_descends (prefixWord ++ tailWord_393027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393042 : List Nat := [3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_393042 : Nat := 118140960795 + 393042 * 2 ^ 59
def prefixEnd_393042 : Nat := 4983230072969 + 3 ^ 40 * 393042 * 2
def baseEnd_393042 : Nat := 119596719054551973373297

theorem tailTrace_393042 : CollatzResearch.WordTrace tailWord_393042 prefixEnd_393042 119596719054551973373297 := by
  unfold tailWord_393042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583854860520858768629345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9556946294722290049678253 3583854860520858768629345)
  ·
    refine ⟨2687891145390644076472009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3583854860520858768629345 2687891145390644076472009)
    ·
      refine ⟨2015918359042983057354007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2687891145390644076472009 2015918359042983057354007)
      ·
        refine ⟨3023877538564474586031011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015918359042983057354007 3023877538564474586031011)
        ·
          refine ⟨4535816307846711879046517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023877538564474586031011 4535816307846711879046517)
          ·
            refine ⟨425232778860629238660611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4535816307846711879046517 425232778860629238660611)
            ·
              refine ⟨637849168290943857990917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425232778860629238660611 637849168290943857990917)
              ·
                refine ⟨119596719054551973373297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637849168290943857990917 119596719054551973373297)
                ·
                  rfl

theorem cell19_393042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_393042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393042 prefixEnd_393042 := by exact prefixLift 393042
  have htrace : WordTrace (prefixWord ++ tailWord_393042) baseStart_393042 baseEnd_393042 := by
    simpa [prefixWord, tailWord_393042, baseEnd_393042] using wordTrace_append hprefix tailTrace_393042
  have hstable : (prefixWord ++ tailWord_393042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393042).length < 2 ^ (prefixWord ++ tailWord_393042).sum := by decide
  have hdescent : baseEnd_393042 < baseStart_393042 := by decide
  rcases family_descends (prefixWord ++ tailWord_393042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393065 : List Nat := [1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_393065 : Nat := 118140960795 + 393065 * 2 ^ 59
def prefixEnd_393065 : Nat := 4983230072969 + 3 ^ 40 * 393065 * 2
def baseEnd_393065 : Nat := 119603717605694734862123

theorem tailTrace_393065 : CollatzResearch.WordTrace tailWord_393065 prefixEnd_393065 119603717605694734862123 := by
  unfold tailWord_393065
  simp only [CollatzResearch.WordTrace]
  refine ⟨14336258321000110002604649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9557505547333406668403099 14336258321000110002604649)
  ·
    refine ⟨10752193740750082501953487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14336258321000110002604649 10752193740750082501953487)
    ·
      refine ⟨16128290611125123752930231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10752193740750082501953487 16128290611125123752930231)
      ·
        refine ⟨24192435916687685629395347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16128290611125123752930231 24192435916687685629395347)
        ·
          refine ⟨36288653875031528444093021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24192435916687685629395347 36288653875031528444093021)
          ·
            refine ⟨13608245203136823166534883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36288653875031528444093021 13608245203136823166534883)
            ·
              refine ⟨20412367804705234749802325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13608245203136823166534883 20412367804705234749802325)
              ·
                refine ⟨119603717605694734862123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20412367804705234749802325 119603717605694734862123)
                ·
                  rfl

theorem cell19_393065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_393065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393065 prefixEnd_393065 := by exact prefixLift 393065
  have htrace : WordTrace (prefixWord ++ tailWord_393065) baseStart_393065 baseEnd_393065 := by
    simpa [prefixWord, tailWord_393065, baseEnd_393065] using wordTrace_append hprefix tailTrace_393065
  have hstable : (prefixWord ++ tailWord_393065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393065).length < 2 ^ (prefixWord ++ tailWord_393065).sum := by decide
  have hdescent : baseEnd_393065 < baseStart_393065 := by decide
  rcases family_descends (prefixWord ++ tailWord_393065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393110 : List Nat := [5, 3, 1, 1, 3, 1, 2, 3]
def baseStart_393110 : Nat := 118140960795 + 393110 * 2 ^ 59
def prefixEnd_393110 : Nat := 4983230072969 + 3 ^ 40 * 393110 * 2
def baseEnd_393110 : Nat := 119617410423147963862001

theorem tailTrace_393110 : CollatzResearch.WordTrace tailWord_393110 prefixEnd_393110 119617410423147963862001 := by
  unfold tailWord_393110
  simp only [CollatzResearch.WordTrace]
  refine ⟨896118725364817667999549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9558599737224721791995189 896118725364817667999549)
  ·
    refine ⟨336044522011806625499831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 896118725364817667999549 336044522011806625499831)
    ·
      refine ⟨504066783017709938249747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336044522011806625499831 504066783017709938249747)
      ·
        refine ⟨756100174526564907374621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504066783017709938249747 756100174526564907374621)
        ·
          refine ⟨283537565447461840265483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 756100174526564907374621 283537565447461840265483)
          ·
            refine ⟨425306348171192760398225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283537565447461840265483 425306348171192760398225)
            ·
              refine ⟨318979761128394570298669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425306348171192760398225 318979761128394570298669)
              ·
                refine ⟨119617410423147963862001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318979761128394570298669 119617410423147963862001)
                ·
                  rfl

theorem cell19_393110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_393110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393110 prefixEnd_393110 := by exact prefixLift 393110
  have htrace : WordTrace (prefixWord ++ tailWord_393110) baseStart_393110 baseEnd_393110 := by
    simpa [prefixWord, tailWord_393110, baseEnd_393110] using wordTrace_append hprefix tailTrace_393110
  have hstable : (prefixWord ++ tailWord_393110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393110).length < 2 ^ (prefixWord ++ tailWord_393110).sum := by decide
  have hdescent : baseEnd_393110 < baseStart_393110 := by decide
  rcases family_descends (prefixWord ++ tailWord_393110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393116 : List Nat := [2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_393116 : Nat := 118140960795 + 393116 * 2 ^ 59
def prefixEnd_393116 : Nat := 4983230072969 + 3 ^ 40 * 393116 * 2
def baseEnd_393116 : Nat := 119619236132141727728651

theorem tailTrace_393116 : CollatzResearch.WordTrace tailWord_393116 prefixEnd_393116 119619236132141727728651 := by
  unfold tailWord_393116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169059221907672856355601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9558745629210230475140801 7169059221907672856355601)
  ·
    refine ⟨5376794416430754642266701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7169059221907672856355601 5376794416430754642266701)
    ·
      refine ⟨2016297906161532990850013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5376794416430754642266701 2016297906161532990850013)
      ·
        refine ⟨756111714810574871568755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2016297906161532990850013 756111714810574871568755)
        ·
          refine ⟨1134167572215862307353133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756111714810574871568755 1134167572215862307353133)
          ·
            refine ⟨425312839580948365257425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1134167572215862307353133 425312839580948365257425)
            ·
              refine ⟨318984629685711273943069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425312839580948365257425 318984629685711273943069)
              ·
                refine ⟨119619236132141727728651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318984629685711273943069 119619236132141727728651)
                ·
                  rfl

theorem cell19_393116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_393116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393116 prefixEnd_393116 := by exact prefixLift 393116
  have htrace : WordTrace (prefixWord ++ tailWord_393116) baseStart_393116 baseEnd_393116 := by
    simpa [prefixWord, tailWord_393116, baseEnd_393116] using wordTrace_append hprefix tailTrace_393116
  have hstable : (prefixWord ++ tailWord_393116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393116).length < 2 ^ (prefixWord ++ tailWord_393116).sum := by decide
  have hdescent : baseEnd_393116 < baseStart_393116 := by decide
  rcases family_descends (prefixWord ++ tailWord_393116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393274 : List Nat := [3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_393274 : Nat := 118140960795 + 393274 * 2 ^ 59
def prefixEnd_393274 : Nat := 4983230072969 + 3 ^ 40 * 393274 * 2
def baseEnd_393274 : Nat := 119667313135644176217109

theorem tailTrace_393274 : CollatzResearch.WordTrace tailWord_393274 prefixEnd_393274 119667313135644176217109 := by
  unfold tailWord_393274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585970294310734674240719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9562587451495292464641917 3585970294310734674240719)
  ·
    refine ⟨5378955441466102011361079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3585970294310734674240719 5378955441466102011361079)
    ·
      refine ⟨8068433162199153017041619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5378955441466102011361079 8068433162199153017041619)
      ·
        refine ⟨12102649743298729525562429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8068433162199153017041619 12102649743298729525562429)
        ·
          refine ⟨4538493653737023572085911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12102649743298729525562429 4538493653737023572085911)
          ·
            refine ⟨6807740480605535358128867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538493653737023572085911 6807740480605535358128867)
            ·
              refine ⟨10211610720908303037193301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807740480605535358128867 10211610720908303037193301)
              ·
                refine ⟨119667313135644176217109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10211610720908303037193301 119667313135644176217109)
                ·
                  rfl

theorem cell19_393274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_393274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393274 prefixEnd_393274 := by exact prefixLift 393274
  have htrace : WordTrace (prefixWord ++ tailWord_393274) baseStart_393274 baseEnd_393274 := by
    simpa [prefixWord, tailWord_393274, baseEnd_393274] using wordTrace_append hprefix tailTrace_393274
  have hstable : (prefixWord ++ tailWord_393274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393274).length < 2 ^ (prefixWord ++ tailWord_393274).sum := by decide
  have hdescent : baseEnd_393274 < baseStart_393274 := by decide
  rcases family_descends (prefixWord ++ tailWord_393274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393312 : List Nat := [2, 1, 1, 3, 2, 3, 7]
def baseStart_393312 : Nat := 118140960795 + 393312 * 2 ^ 59
def prefixEnd_393312 : Nat := 4983230072969 + 3 ^ 40 * 393312 * 2
def baseEnd_393312 : Nat := 39892958653090449124187

theorem tailTrace_393312 : CollatzResearch.WordTrace tailWord_393312 prefixEnd_393312 39892958653090449124187 := by
  unfold tailWord_393312
  simp only [CollatzResearch.WordTrace]
  refine ⟨7172633575552635593423095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9563511434070180791230793 7172633575552635593423095)
  ·
    refine ⟨10758950363328953390134643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7172633575552635593423095 10758950363328953390134643)
    ·
      refine ⟨16138425544993430085201965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10758950363328953390134643 16138425544993430085201965)
      ·
        refine ⟨6051909579372536281950737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16138425544993430085201965 6051909579372536281950737)
        ·
          refine ⟨4538932184529402211463053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6051909579372536281950737 4538932184529402211463053)
          ·
            refine ⟨1702099569198525829298645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4538932184529402211463053 1702099569198525829298645)
            ·
              refine ⟨39892958653090449124187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1702099569198525829298645 39892958653090449124187)
              ·
                rfl

theorem cell19_393312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_393312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393312 prefixEnd_393312 := by exact prefixLift 393312
  have htrace : WordTrace (prefixWord ++ tailWord_393312) baseStart_393312 baseEnd_393312 := by
    simpa [prefixWord, tailWord_393312, baseEnd_393312] using wordTrace_append hprefix tailTrace_393312
  have hstable : (prefixWord ++ tailWord_393312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393312).length < 2 ^ (prefixWord ++ tailWord_393312).sum := by decide
  have hdescent : baseEnd_393312 < baseStart_393312 := by decide
  rcases family_descends (prefixWord ++ tailWord_393312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393367 : List Nat := [1, 1, 3, 3, 5, 6]
def baseStart_393367 : Nat := 118140960795 + 393367 * 2 ^ 59
def prefixEnd_393367 : Nat := 4983230072969 + 3 ^ 40 * 393367 * 2
def baseEnd_393367 : Nat := 13299512402783057350021

theorem tailTrace_393367 : CollatzResearch.WordTrace tailWord_393367 prefixEnd_393367 13299512402783057350021 := by
  unfold tailWord_393367
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347273165906015580098355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9564848777270677053398903 14347273165906015580098355)
  ·
    refine ⟨21520909748859023370147533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14347273165906015580098355 21520909748859023370147533)
    ·
      refine ⟨8070341155822133763805325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21520909748859023370147533 8070341155822133763805325)
      ·
        refine ⟨3026377933433300161426997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8070341155822133763805325 3026377933433300161426997)
        ·
          refine ⟨283722931259371890133781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3026377933433300161426997 283722931259371890133781)
          ·
            refine ⟨13299512402783057350021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 283722931259371890133781 13299512402783057350021)
            ·
              rfl

theorem cell19_393367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_393367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393367 prefixEnd_393367 := by exact prefixLift 393367
  have htrace : WordTrace (prefixWord ++ tailWord_393367) baseStart_393367 baseEnd_393367 := by
    simpa [prefixWord, tailWord_393367, baseEnd_393367] using wordTrace_append hprefix tailTrace_393367
  have hstable : (prefixWord ++ tailWord_393367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393367).length < 2 ^ (prefixWord ++ tailWord_393367).sum := by decide
  have hdescent : baseEnd_393367 < baseStart_393367 := by decide
  rcases family_descends (prefixWord ++ tailWord_393367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393479 : List Nat := [1, 1, 4, 5, 1, 2, 5]
def baseStart_393479 : Nat := 118140960795 + 393479 * 2 ^ 59
def prefixEnd_393479 : Nat := 4983230072969 + 3 ^ 40 * 393479 * 2
def baseEnd_393479 : Nat := 39909897175421480553665

theorem tailTrace_393479 : CollatzResearch.WordTrace tailWord_393479 prefixEnd_393479 39909897175421480553665 := by
  unfold tailWord_393479
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351358141500258708175491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9567572094333505805450327 14351358141500258708175491)
  ·
    refine ⟨21527037212250388062263237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14351358141500258708175491 21527037212250388062263237)
    ·
      refine ⟨4036319477296947761674357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21527037212250388062263237 4036319477296947761674357)
      ·
        refine ⟨378404950996588852656971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4036319477296947761674357 378404950996588852656971)
        ·
          refine ⟨567607426494883278985457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378404950996588852656971 567607426494883278985457)
          ·
            refine ⟨425705569871162459239093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567607426494883278985457 425705569871162459239093)
            ·
              refine ⟨39909897175421480553665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 425705569871162459239093 39909897175421480553665)
              ·
                rfl

theorem cell19_393479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_393479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393479 prefixEnd_393479 := by exact prefixLift 393479
  have htrace : WordTrace (prefixWord ++ tailWord_393479) baseStart_393479 baseEnd_393479 := by
    simpa [prefixWord, tailWord_393479, baseEnd_393479] using wordTrace_append hprefix tailTrace_393479
  have hstable : (prefixWord ++ tailWord_393479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393479).length < 2 ^ (prefixWord ++ tailWord_393479).sum := by decide
  have hdescent : baseEnd_393479 < baseStart_393479 := by decide
  rcases family_descends (prefixWord ++ tailWord_393479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393597 : List Nat := [1, 4, 1, 1, 2, 4, 6]
def baseStart_393597 : Nat := 118140960795 + 393597 * 2 ^ 59
def prefixEnd_393597 : Nat := 4983230072969 + 3 ^ 40 * 393597 * 2
def baseEnd_393597 : Nat := 39921865712158377012817

theorem tailTrace_393597 : CollatzResearch.WordTrace tailWord_393597 prefixEnd_393597 39921865712158377012817 := by
  unfold tailWord_393597
  simp only [CollatzResearch.WordTrace]
  refine ⟨14355661955072764860971045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9570441303381843240647363 14355661955072764860971045)
  ·
    refine ⟨2691686616576143411432071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14355661955072764860971045 2691686616576143411432071)
    ·
      refine ⟨4037529924864215117148107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691686616576143411432071 4037529924864215117148107)
      ·
        refine ⟨6056294887296322675722161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037529924864215117148107 6056294887296322675722161)
        ·
          refine ⟨4542221165472242006791621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6056294887296322675722161 4542221165472242006791621)
          ·
            refine ⟨851666468526045376273429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4542221165472242006791621 851666468526045376273429)
            ·
              refine ⟨39921865712158377012817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 851666468526045376273429 39921865712158377012817)
              ·
                rfl

theorem cell19_393597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_393597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393597 prefixEnd_393597 := by exact prefixLift 393597
  have htrace : WordTrace (prefixWord ++ tailWord_393597) baseStart_393597 baseEnd_393597 := by
    simpa [prefixWord, tailWord_393597, baseEnd_393597] using wordTrace_append hprefix tailTrace_393597
  have hstable : (prefixWord ++ tailWord_393597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393597).length < 2 ^ (prefixWord ++ tailWord_393597).sum := by decide
  have hdescent : baseEnd_393597 < baseStart_393597 := by decide
  rcases family_descends (prefixWord ++ tailWord_393597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393629 : List Nat := [1, 4, 2, 1, 5, 1, 2, 3]
def baseStart_393629 : Nat := 118140960795 + 393629 * 2 ^ 59
def prefixEnd_393629 : Nat := 4983230072969 + 3 ^ 40 * 393629 * 2
def baseEnd_393629 : Nat := 119775334251108538327253

theorem tailTrace_393629 : CollatzResearch.WordTrace tailWord_393629 prefixEnd_393629 119775334251108538327253 := by
  unfold tailWord_393629
  simp only [CollatzResearch.WordTrace]
  refine ⟨14356829090956834326135941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9571219393971222884090627 14356829090956834326135941)
  ·
    refine ⟨2691905454554406436150489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14356829090956834326135941 2691905454554406436150489)
    ·
      refine ⟨2018929090915804827112867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2691905454554406436150489 2018929090915804827112867)
      ·
        refine ⟨3028393636373707240669301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018929090915804827112867 3028393636373707240669301)
        ·
          refine ⟨283911903410035053812747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3028393636373707240669301 283911903410035053812747)
          ·
            refine ⟨425867855115052580719121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283911903410035053812747 425867855115052580719121)
            ·
              refine ⟨319400891336289435539341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425867855115052580719121 319400891336289435539341)
              ·
                refine ⟨119775334251108538327253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319400891336289435539341 119775334251108538327253)
                ·
                  rfl

theorem cell19_393629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_393629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393629 prefixEnd_393629 := by exact prefixLift 393629
  have htrace : WordTrace (prefixWord ++ tailWord_393629) baseStart_393629 baseEnd_393629 := by
    simpa [prefixWord, tailWord_393629, baseEnd_393629] using wordTrace_append hprefix tailTrace_393629
  have hstable : (prefixWord ++ tailWord_393629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393629).length < 2 ^ (prefixWord ++ tailWord_393629).sum := by decide
  have hdescent : baseEnd_393629 < baseStart_393629 := by decide
  rcases family_descends (prefixWord ++ tailWord_393629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393635 : List Nat := [1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_393635 : Nat := 118140960795 + 393635 * 2 ^ 59
def prefixEnd_393635 : Nat := 4983230072969 + 3 ^ 40 * 393635 * 2
def baseEnd_393635 : Nat := 119777159960102302193903

theorem tailTrace_393635 : CollatzResearch.WordTrace tailWord_393635 prefixEnd_393635 119777159960102302193903 := by
  unfold tailWord_393635
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357047928935097350854359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9571365285956731567236239 14357047928935097350854359)
  ·
    refine ⟨21535571893402646026281539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14357047928935097350854359 21535571893402646026281539)
    ·
      refine ⟨32303357840103969039422309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21535571893402646026281539 32303357840103969039422309)
      ·
        refine ⟨6056879595019494194891683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32303357840103969039422309 6056879595019494194891683)
        ·
          refine ⟨9085319392529241292337525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056879595019494194891683 9085319392529241292337525)
          ·
            refine ⟨851748693049616371156643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9085319392529241292337525 851748693049616371156643)
            ·
              refine ⟨1277623039574424556734965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851748693049616371156643 1277623039574424556734965)
              ·
                refine ⟨119777159960102302193903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1277623039574424556734965 119777159960102302193903)
                ·
                  rfl

theorem cell19_393635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_393635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393635 prefixEnd_393635 := by exact prefixLift 393635
  have htrace : WordTrace (prefixWord ++ tailWord_393635) baseStart_393635 baseEnd_393635 := by
    simpa [prefixWord, tailWord_393635, baseEnd_393635] using wordTrace_append hprefix tailTrace_393635
  have hstable : (prefixWord ++ tailWord_393635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393635).length < 2 ^ (prefixWord ++ tailWord_393635).sum := by decide
  have hdescent : baseEnd_393635 < baseStart_393635 := by decide
  rcases family_descends (prefixWord ++ tailWord_393635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393796 : List Nat := [2, 3, 5, 1, 2, 1, 2, 3]
def baseStart_393796 : Nat := 118140960795 + 393796 * 2 ^ 59
def prefixEnd_393796 : Nat := 4983230072969 + 3 ^ 40 * 393796 * 2
def baseEnd_393796 : Nat := 119826149818101632615687

theorem tailTrace_393796 : CollatzResearch.WordTrace tailWord_393796 prefixEnd_393796 119826149818101632615687 := by
  unfold tailWord_393796
  simp only [CollatzResearch.WordTrace]
  refine ⟨7181460040675910923732621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9575280054234547898310161 7181460040675910923732621)
  ·
    refine ⟨2693047515253466596399733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7181460040675910923732621 2693047515253466596399733)
    ·
      refine ⟨252473204555012493412475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2693047515253466596399733 252473204555012493412475)
      ·
        refine ⟨378709806832518740118713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252473204555012493412475 378709806832518740118713)
        ·
          refine ⟨284032355124389055089035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378709806832518740118713 284032355124389055089035)
          ·
            refine ⟨426048532686583582633553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284032355124389055089035 426048532686583582633553)
            ·
              refine ⟨319536399514937686975165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426048532686583582633553 319536399514937686975165)
              ·
                refine ⟨119826149818101632615687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319536399514937686975165 119826149818101632615687)
                ·
                  rfl

theorem cell19_393796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_393796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393796 prefixEnd_393796 := by exact prefixLift 393796
  have htrace : WordTrace (prefixWord ++ tailWord_393796) baseStart_393796 baseEnd_393796 := by
    simpa [prefixWord, tailWord_393796, baseEnd_393796] using wordTrace_append hprefix tailTrace_393796
  have hstable : (prefixWord ++ tailWord_393796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393796).length < 2 ^ (prefixWord ++ tailWord_393796).sum := by decide
  have hdescent : baseEnd_393796 < baseStart_393796 := by decide
  rcases family_descends (prefixWord ++ tailWord_393796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393825 : List Nat := [1, 2, 3, 1, 1, 6, 5]
def baseStart_393825 : Nat := 118140960795 + 393825 * 2 ^ 59
def prefixEnd_393825 : Nat := 4983230072969 + 3 ^ 40 * 393825 * 2
def baseEnd_393825 : Nat := 39944991359412719323721

theorem tailTrace_393825 : CollatzResearch.WordTrace tailWord_393825 prefixEnd_393825 39944991359412719323721 := by
  unfold tailWord_393825
  simp only [CollatzResearch.WordTrace]
  refine ⟨14363977798246759800270929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9575985198831173200180619 14363977798246759800270929)
  ·
    refine ⟨10772983348685069850203197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14363977798246759800270929 10772983348685069850203197)
    ·
      refine ⟨4039868755756901193826199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10772983348685069850203197 4039868755756901193826199)
      ·
        refine ⟨6059803133635351790739299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039868755756901193826199 6059803133635351790739299)
        ·
          refine ⟨9089704700453027686108949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6059803133635351790739299 9089704700453027686108949)
          ·
            refine ⟨426079907833735672786357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9089704700453027686108949 426079907833735672786357)
            ·
              refine ⟨39944991359412719323721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 426079907833735672786357 39944991359412719323721)
              ·
                rfl

theorem cell19_393825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_393825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393825 prefixEnd_393825 := by exact prefixLift 393825
  have htrace : WordTrace (prefixWord ++ tailWord_393825) baseStart_393825 baseEnd_393825 := by
    simpa [prefixWord, tailWord_393825, baseEnd_393825] using wordTrace_append hprefix tailTrace_393825
  have hstable : (prefixWord ++ tailWord_393825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393825).length < 2 ^ (prefixWord ++ tailWord_393825).sum := by decide
  have hdescent : baseEnd_393825 < baseStart_393825 := by decide
  rcases family_descends (prefixWord ++ tailWord_393825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393842 : List Nat := [3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_393842 : Nat := 118140960795 + 393842 * 2 ^ 59
def prefixEnd_393842 : Nat := 4983230072969 + 3 ^ 40 * 393842 * 2
def baseEnd_393842 : Nat := 119840146920387155593339

theorem tailTrace_393842 : CollatzResearch.WordTrace tailWord_393842 prefixEnd_393842 119840146920387155593339 := by
  unfold tailWord_393842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591149459796292925909945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9576398559456781135759853 3591149459796292925909945)
  ·
    refine ⟨2693362094847219694432459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3591149459796292925909945 2693362094847219694432459)
    ·
      refine ⟨4040043142270829541648689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693362094847219694432459 4040043142270829541648689)
      ·
        refine ⟨3030032356703122156236517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4040043142270829541648689 3030032356703122156236517)
        ·
          refine ⟨568131066881835404294347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3030032356703122156236517 568131066881835404294347)
          ·
            refine ⟨852196600322753106441521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568131066881835404294347 852196600322753106441521)
            ·
              refine ⟨639147450242064829831141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852196600322753106441521 639147450242064829831141)
              ·
                refine ⟨119840146920387155593339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639147450242064829831141 119840146920387155593339)
                ·
                  rfl

theorem cell19_393842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_393842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393842 prefixEnd_393842 := by exact prefixLift 393842
  have htrace : WordTrace (prefixWord ++ tailWord_393842) baseStart_393842 baseEnd_393842 := by
    simpa [prefixWord, tailWord_393842, baseEnd_393842] using wordTrace_append hprefix tailTrace_393842
  have hstable : (prefixWord ++ tailWord_393842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393842).length < 2 ^ (prefixWord ++ tailWord_393842).sum := by decide
  have hdescent : baseEnd_393842 < baseStart_393842 := by decide
  rcases family_descends (prefixWord ++ tailWord_393842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393882 : List Nat := [3, 1, 1, 6, 8]
def baseStart_393882 : Nat := 118140960795 + 393882 * 2 ^ 59
def prefixEnd_393882 : Nat := 4983230072969 + 3 ^ 40 * 393882 * 2
def baseEnd_393882 : Nat := 4438974752358478322383

theorem tailTrace_393882 : CollatzResearch.WordTrace tailWord_393882 prefixEnd_393882 4438974752358478322383 := by
  unfold tailWord_393882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591514189760064633773975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9577371172693505690063933 3591514189760064633773975)
  ·
    refine ⟨5387271284640096950660963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3591514189760064633773975 5387271284640096950660963)
    ·
      refine ⟨8080906926960145425991445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5387271284640096950660963 8080906926960145425991445)
      ·
        refine ⟨378792512201256816843349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8080906926960145425991445 378792512201256816843349)
        ·
          refine ⟨4438974752358478322383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 378792512201256816843349 4438974752358478322383)
          ·
            rfl

theorem cell19_393882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 8].length) (baseStart_393882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393882 prefixEnd_393882 := by exact prefixLift 393882
  have htrace : WordTrace (prefixWord ++ tailWord_393882) baseStart_393882 baseEnd_393882 := by
    simpa [prefixWord, tailWord_393882, baseEnd_393882] using wordTrace_append hprefix tailTrace_393882
  have hstable : (prefixWord ++ tailWord_393882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393882).length < 2 ^ (prefixWord ++ tailWord_393882).sum := by decide
  have hdescent : baseEnd_393882 < baseStart_393882 := by decide
  rcases family_descends (prefixWord ++ tailWord_393882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393895 : List Nat := [1, 1, 6, 3, 2, 1, 1, 4]
def baseStart_393895 : Nat := 118140960795 + 393895 * 2 ^ 59
def prefixEnd_393895 : Nat := 4983230072969 + 3 ^ 40 * 393895 * 2
def baseEnd_393895 : Nat := 119856274016498736415417

theorem tailTrace_393895 : CollatzResearch.WordTrace tailWord_393895 prefixEnd_393895 119856274016498736415417 := by
  unfold tailWord_393895
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366530907993161755319139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9577687271995441170212759 14366530907993161755319139)
  ·
    refine ⟨21549796361989742632978709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14366530907993161755319139 21549796361989742632978709)
    ·
      refine ⟨1010146704468269185920877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21549796361989742632978709 1010146704468269185920877)
      ·
        refine ⟨378805014175600944720329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1010146704468269185920877 378805014175600944720329)
        ·
          refine ⟨284103760631700708540247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378805014175600944720329 284103760631700708540247)
          ·
            refine ⟨426155640947551062810371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284103760631700708540247 426155640947551062810371)
            ·
              refine ⟨639233461421326594215557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426155640947551062810371 639233461421326594215557)
              ·
                refine ⟨119856274016498736415417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639233461421326594215557 119856274016498736415417)
                ·
                  rfl

theorem cell19_393895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_393895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393895 prefixEnd_393895 := by exact prefixLift 393895
  have htrace : WordTrace (prefixWord ++ tailWord_393895) baseStart_393895 baseEnd_393895 := by
    simpa [prefixWord, tailWord_393895, baseEnd_393895] using wordTrace_append hprefix tailTrace_393895
  have hstable : (prefixWord ++ tailWord_393895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393895).length < 2 ^ (prefixWord ++ tailWord_393895).sum := by decide
  have hdescent : baseEnd_393895 < baseStart_393895 := by decide
  rcases family_descends (prefixWord ++ tailWord_393895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393918 : List Nat := [4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_393918 : Nat := 118140960795 + 393918 * 2 ^ 59
def prefixEnd_393918 : Nat := 4983230072969 + 3 ^ 40 * 393918 * 2
def baseEnd_393918 : Nat := 119863272567641497904243

theorem tailTrace_393918 : CollatzResearch.WordTrace tailWord_393918 prefixEnd_393918 119863272567641497904243 := by
  unfold tailWord_393918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1795921223363729585425801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9578246524606557788937605 1795921223363729585425801)
  ·
    refine ⟨1346940917522797189069351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1795921223363729585425801 1346940917522797189069351)
    ·
      refine ⟨2020411376284195783604027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346940917522797189069351 2020411376284195783604027)
      ·
        refine ⟨3030617064426293675406041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020411376284195783604027 3030617064426293675406041)
        ·
          refine ⟨2272962798319720256554531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3030617064426293675406041 2272962798319720256554531)
          ·
            refine ⟨3409444197479580384831797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272962798319720256554531 3409444197479580384831797)
            ·
              refine ⟨319635393513710661077981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3409444197479580384831797 319635393513710661077981)
              ·
                refine ⟨119863272567641497904243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319635393513710661077981 119863272567641497904243)
                ·
                  rfl

theorem cell19_393918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_393918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_393918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_393918 prefixEnd_393918 := by exact prefixLift 393918
  have htrace : WordTrace (prefixWord ++ tailWord_393918) baseStart_393918 baseEnd_393918 := by
    simpa [prefixWord, tailWord_393918, baseEnd_393918] using wordTrace_append hprefix tailTrace_393918
  have hstable : (prefixWord ++ tailWord_393918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393918).length < 2 ^ (prefixWord ++ tailWord_393918).sum := by decide
  have hdescent : baseEnd_393918 < baseStart_393918 := by decide
  rcases family_descends (prefixWord ++ tailWord_393918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394015 : List Nat := [1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_394015 : Nat := 118140960795 + 394015 * 2 ^ 59
def prefixEnd_394015 : Nat := 4983230072969 + 3 ^ 40 * 394015 * 2
def baseEnd_394015 : Nat := 119892788196374013748423

theorem tailTrace_394015 : CollatzResearch.WordTrace tailWord_394015 prefixEnd_394015 119892788196374013748423 := by
  unfold tailWord_394015
  simp only [CollatzResearch.WordTrace]
  refine ⟨14370907667558422249687499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9580605111705614833124999 14370907667558422249687499)
  ·
    refine ⟨21556361501337633374531249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14370907667558422249687499 21556361501337633374531249)
    ·
      refine ⟨16167271126003225030898437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21556361501337633374531249 16167271126003225030898437)
      ·
        refine ⟨3031363336125604693293457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16167271126003225030898437 3031363336125604693293457)
        ·
          refine ⟨2273522502094203519970093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031363336125604693293457 2273522502094203519970093)
          ·
            refine ⟨852570938285326319988785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2273522502094203519970093 852570938285326319988785)
            ·
              refine ⟨639428203713994739991589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852570938285326319988785 639428203713994739991589)
              ·
                refine ⟨119892788196374013748423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639428203713994739991589 119892788196374013748423)
                ·
                  rfl

theorem cell19_394015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_394015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394015 prefixEnd_394015 := by exact prefixLift 394015
  have htrace : WordTrace (prefixWord ++ tailWord_394015) baseStart_394015 baseEnd_394015 := by
    simpa [prefixWord, tailWord_394015, baseEnd_394015] using wordTrace_append hprefix tailTrace_394015
  have hstable : (prefixWord ++ tailWord_394015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394015).length < 2 ^ (prefixWord ++ tailWord_394015).sum := by decide
  have hdescent : baseEnd_394015 < baseStart_394015 := by decide
  rcases family_descends (prefixWord ++ tailWord_394015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394068 : List Nat := [2, 4, 1, 1, 5, 1, 1, 4]
def baseStart_394068 : Nat := 118140960795 + 394068 * 2 ^ 59
def prefixEnd_394068 : Nat := 4983230072969 + 3 ^ 40 * 394068 * 2
def baseEnd_394068 : Nat := 119908915292485594570501

theorem tailTrace_394068 : CollatzResearch.WordTrace tailWord_394068 prefixEnd_394068 119908915292485594570501 := by
  unfold tailWord_394068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186420368183206150683429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9581893824244274867577905 7186420368183206150683429)
  ·
    refine ⟨1347453819034351153253143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7186420368183206150683429 1347453819034351153253143)
    ·
      refine ⟨2021180728551526729879715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347453819034351153253143 2021180728551526729879715)
      ·
        refine ⟨3031771092827290094819573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021180728551526729879715 3031771092827290094819573)
        ·
          refine ⟨284228539952558446389335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3031771092827290094819573 284228539952558446389335)
          ·
            refine ⟨426342809928837669584003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284228539952558446389335 426342809928837669584003)
            ·
              refine ⟨639514214893256504376005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426342809928837669584003 639514214893256504376005)
              ·
                refine ⟨119908915292485594570501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639514214893256504376005 119908915292485594570501)
                ·
                  rfl

theorem cell19_394068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_394068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394068 prefixEnd_394068 := by exact prefixLift 394068
  have htrace : WordTrace (prefixWord ++ tailWord_394068) baseStart_394068 baseEnd_394068 := by
    simpa [prefixWord, tailWord_394068, baseEnd_394068] using wordTrace_append hprefix tailTrace_394068
  have hstable : (prefixWord ++ tailWord_394068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394068).length < 2 ^ (prefixWord ++ tailWord_394068).sum := by decide
  have hdescent : baseEnd_394068 < baseStart_394068 := by decide
  rcases family_descends (prefixWord ++ tailWord_394068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394146 : List Nat := [3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_394146 : Nat := 118140960795 + 394146 * 2 ^ 59
def prefixEnd_394146 : Nat := 4983230072969 + 3 ^ 40 * 394146 * 2
def baseEnd_394146 : Nat := 119932649509404524836955

theorem tailTrace_394146 : CollatzResearch.WordTrace tailWord_394146 prefixEnd_394146 119932649509404524836955 := by
  unfold tailWord_394146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593921407520957905676573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9583790420055887748470861 3593921407520957905676573)
  ·
    refine ⟨1347720527820359214628715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3593921407520957905676573 1347720527820359214628715)
    ·
      refine ⟨2021580791730538821943073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347720527820359214628715 2021580791730538821943073)
      ·
        refine ⟨1516185593797904116457305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021580791730538821943073 1516185593797904116457305)
        ·
          refine ⟨1137139195348428087342979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516185593797904116457305 1137139195348428087342979)
          ·
            refine ⟨1705708793022642131014469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137139195348428087342979 1705708793022642131014469)
            ·
              refine ⟨319820398691745399565213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1705708793022642131014469 319820398691745399565213)
              ·
                refine ⟨119932649509404524836955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319820398691745399565213 119932649509404524836955)
                ·
                  rfl

theorem cell19_394146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_394146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394146 prefixEnd_394146 := by exact prefixLift 394146
  have htrace : WordTrace (prefixWord ++ tailWord_394146) baseStart_394146 baseEnd_394146 := by
    simpa [prefixWord, tailWord_394146, baseEnd_394146] using wordTrace_append hprefix tailTrace_394146
  have hstable : (prefixWord ++ tailWord_394146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394146).length < 2 ^ (prefixWord ++ tailWord_394146).sum := by decide
  have hdescent : baseEnd_394146 < baseStart_394146 := by decide
  rcases family_descends (prefixWord ++ tailWord_394146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394169 : List Nat := [1, 2, 1, 4, 2, 2, 7]
def baseStart_394169 : Nat := 118140960795 + 394169 * 2 ^ 59
def prefixEnd_394169 : Nat := 4983230072969 + 3 ^ 40 * 394169 * 2
def baseEnd_394169 : Nat := 39979882686849095441927

theorem tailTrace_394169 : CollatzResearch.WordTrace tailWord_394169 prefixEnd_394169 39979882686849095441927 := by
  unfold tailWord_394169
  simp only [CollatzResearch.WordTrace]
  refine ⟨14376524509000506550793561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9584349672667004367195707 14376524509000506550793561)
  ·
    refine ⟨10782393381750379913095171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14376524509000506550793561 10782393381750379913095171)
    ·
      refine ⟨16173590072625569869642757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782393381750379913095171 16173590072625569869642757)
      ·
        refine ⟨3032548138617294350558017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16173590072625569869642757 3032548138617294350558017)
        ·
          refine ⟨2274411103962970762918513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3032548138617294350558017 2274411103962970762918513)
          ·
            refine ⟨1705808327972228072188885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274411103962970762918513 1705808327972228072188885)
            ·
              refine ⟨39979882686849095441927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1705808327972228072188885 39979882686849095441927)
              ·
                rfl

theorem cell19_394169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_394169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394169 prefixEnd_394169 := by exact prefixLift 394169
  have htrace : WordTrace (prefixWord ++ tailWord_394169) baseStart_394169 baseEnd_394169 := by
    simpa [prefixWord, tailWord_394169, baseEnd_394169] using wordTrace_append hprefix tailTrace_394169
  have hstable : (prefixWord ++ tailWord_394169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394169).length < 2 ^ (prefixWord ++ tailWord_394169).sum := by decide
  have hdescent : baseEnd_394169 < baseStart_394169 := by decide
  rcases family_descends (prefixWord ++ tailWord_394169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394205 : List Nat := [1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_394205 : Nat := 118140960795 + 394205 * 2 ^ 59
def prefixEnd_394205 : Nat := 4983230072969 + 3 ^ 40 * 394205 * 2
def baseEnd_394205 : Nat := 119950602314509869525683

theorem tailTrace_394205 : CollatzResearch.WordTrace tailWord_394205 prefixEnd_394205 119950602314509869525683 := by
  unfold tailWord_394205
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377837536870084699104069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9585225024580056466069379 14377837536870084699104069)
  ·
    refine ⟨2695844538163140881082013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14377837536870084699104069 2695844538163140881082013)
    ·
      refine ⟨1010941701811177830405755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2695844538163140881082013 1010941701811177830405755)
      ·
        refine ⟨1516412552716766745608633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010941701811177830405755 1516412552716766745608633)
        ·
          refine ⟨1137309414537575059206475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516412552716766745608633 1137309414537575059206475)
          ·
            refine ⟨1705964121806362588809713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137309414537575059206475 1705964121806362588809713)
            ·
              refine ⟨1279473091354771941607285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705964121806362588809713 1279473091354771941607285)
              ·
                refine ⟨119950602314509869525683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1279473091354771941607285 119950602314509869525683)
                ·
                  rfl

theorem cell19_394205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_394205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394205 prefixEnd_394205 := by exact prefixLift 394205
  have htrace : WordTrace (prefixWord ++ tailWord_394205) baseStart_394205 baseEnd_394205 := by
    simpa [prefixWord, tailWord_394205, baseEnd_394205] using wordTrace_append hprefix tailTrace_394205
  have hstable : (prefixWord ++ tailWord_394205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394205).length < 2 ^ (prefixWord ++ tailWord_394205).sum := by decide
  have hdescent : baseEnd_394205 < baseStart_394205 := by decide
  rcases family_descends (prefixWord ++ tailWord_394205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394317 : List Nat := [1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_394317 : Nat := 118140960795 + 394317 * 2 ^ 59
def prefixEnd_394317 : Nat := 4983230072969 + 3 ^ 40 * 394317 * 2
def baseEnd_394317 : Nat := 119984682215726795036489

theorem tailTrace_394317 : CollatzResearch.WordTrace tailWord_394317 prefixEnd_394317 119984682215726795036489 := by
  unfold tailWord_394317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381922512464327827181205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9587948341642885218120803 14381922512464327827181205)
  ·
    refine ⟨674152617771765366899119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14381922512464327827181205 674152617771765366899119)
    ·
      refine ⟨1011228926657648050348679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674152617771765366899119 1011228926657648050348679)
      ·
        refine ⟨1516843389986472075523019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011228926657648050348679 1516843389986472075523019)
        ·
          refine ⟨2275265084979708113284529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516843389986472075523019 2275265084979708113284529)
          ·
            refine ⟨1706448813734781084963397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2275265084979708113284529 1706448813734781084963397)
            ·
              refine ⟨319959152575271453430637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1706448813734781084963397 319959152575271453430637)
              ·
                refine ⟨119984682215726795036489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319959152575271453430637 119984682215726795036489)
                ·
                  rfl

theorem cell19_394317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_394317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394317 prefixEnd_394317 := by exact prefixLift 394317
  have htrace : WordTrace (prefixWord ++ tailWord_394317) baseStart_394317 baseEnd_394317 := by
    simpa [prefixWord, tailWord_394317, baseEnd_394317] using wordTrace_append hprefix tailTrace_394317
  have hstable : (prefixWord ++ tailWord_394317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394317).length < 2 ^ (prefixWord ++ tailWord_394317).sum := by decide
  have hdescent : baseEnd_394317 < baseStart_394317 := by decide
  rcases family_descends (prefixWord ++ tailWord_394317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394334 : List Nat := [4, 4, 1, 1, 1, 3, 5]
def baseStart_394334 : Nat := 118140960795 + 394334 * 2 ^ 59
def prefixEnd_394334 : Nat := 4983230072969 + 3 ^ 40 * 394334 * 2
def baseEnd_394334 : Nat := 39996618352625264219555

theorem tailTrace_394334 : CollatzResearch.WordTrace tailWord_394334 prefixEnd_394334 39996618352625264219555 := by
  unfold tailWord_394334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797817819175342466318757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9588361702268493153700037 1797817819175342466318757)
  ·
    refine ⟨337090841095376712434767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1797817819175342466318757 337090841095376712434767)
    ·
      refine ⟨505636261643065068652151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337090841095376712434767 505636261643065068652151)
      ·
        refine ⟨758454392464597602978227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505636261643065068652151 758454392464597602978227)
        ·
          refine ⟨1137681588696896404467341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758454392464597602978227 1137681588696896404467341)
          ·
            refine ⟨426630595761336151675253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1137681588696896404467341 426630595761336151675253)
            ·
              refine ⟨39996618352625264219555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 426630595761336151675253 39996618352625264219555)
              ·
                rfl

theorem cell19_394334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_394334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394334 prefixEnd_394334 := by exact prefixLift 394334
  have htrace : WordTrace (prefixWord ++ tailWord_394334) baseStart_394334 baseEnd_394334 := by
    simpa [prefixWord, tailWord_394334, baseEnd_394334] using wordTrace_append hprefix tailTrace_394334
  have hstable : (prefixWord ++ tailWord_394334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394334).length < 2 ^ (prefixWord ++ tailWord_394334).sum := by decide
  have hdescent : baseEnd_394334 < baseStart_394334 := by decide
  rcases family_descends (prefixWord ++ tailWord_394334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394338 : List Nat := [3, 3, 2, 2, 1, 1, 7]
def baseStart_394338 : Nat := 118140960795 + 394338 * 2 ^ 59
def prefixEnd_394338 : Nat := 4983230072969 + 3 ^ 40 * 394338 * 2
def baseEnd_394338 : Nat := 39997024065734989523255

theorem tailTrace_394338 : CollatzResearch.WordTrace tailWord_394338 prefixEnd_394338 39997024065734989523255 := by
  unfold tailWord_394338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595672111347062103423917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9588458963592165609130445 3595672111347062103423917)
  ·
    refine ⟨1348377041755148288783969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3595672111347062103423917 1348377041755148288783969)
    ·
      refine ⟨1011282781316361216587977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1348377041755148288783969 1011282781316361216587977)
      ·
        refine ⟨758462085987270912440983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011282781316361216587977 758462085987270912440983)
        ·
          refine ⟨1137693128980906368661475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758462085987270912440983 1137693128980906368661475)
          ·
            refine ⟨1706539693471359552992213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137693128980906368661475 1706539693471359552992213)
            ·
              refine ⟨39997024065734989523255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1706539693471359552992213 39997024065734989523255)
              ·
                rfl

theorem cell19_394338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_394338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394338 prefixEnd_394338 := by exact prefixLift 394338
  have htrace : WordTrace (prefixWord ++ tailWord_394338) baseStart_394338 baseEnd_394338 := by
    simpa [prefixWord, tailWord_394338, baseEnd_394338] using wordTrace_append hprefix tailTrace_394338
  have hstable : (prefixWord ++ tailWord_394338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394338).length < 2 ^ (prefixWord ++ tailWord_394338).sum := by decide
  have hdescent : baseEnd_394338 < baseStart_394338 := by decide
  rcases family_descends (prefixWord ++ tailWord_394338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394359 : List Nat := [1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_394359 : Nat := 118140960795 + 394359 * 2 ^ 59
def prefixEnd_394359 : Nat := 4983230072969 + 3 ^ 40 * 394359 * 2
def baseEnd_394359 : Nat := 119997462178683142103041

theorem tailTrace_394359 : CollatzResearch.WordTrace tailWord_394359 prefixEnd_394359 119997462178683142103041 := by
  unfold tailWord_394359
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383454378312169000210131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9588969585541446000140087 14383454378312169000210131)
  ·
    refine ⟨21575181567468253500315197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14383454378312169000210131 21575181567468253500315197)
    ·
      refine ⟨8090693087800595062618199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21575181567468253500315197 8090693087800595062618199)
      ·
        refine ⟨12136039631700892593927299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8090693087800595062618199 12136039631700892593927299)
        ·
          refine ⟨18204059447551338890890949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12136039631700892593927299 18204059447551338890890949)
          ·
            refine ⟨3413261146415876042042053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18204059447551338890890949 3413261146415876042042053)
            ·
              refine ⟨639986464952976757882885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3413261146415876042042053 639986464952976757882885)
              ·
                refine ⟨119997462178683142103041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639986464952976757882885 119997462178683142103041)
                ·
                  rfl

theorem cell19_394359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_394359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394359 prefixEnd_394359 := by exact prefixLift 394359
  have htrace : WordTrace (prefixWord ++ tailWord_394359) baseStart_394359 baseEnd_394359 := by
    simpa [prefixWord, tailWord_394359, baseEnd_394359] using wordTrace_append hprefix tailTrace_394359
  have hstable : (prefixWord ++ tailWord_394359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394359).length < 2 ^ (prefixWord ++ tailWord_394359).sum := by decide
  have hdescent : baseEnd_394359 < baseStart_394359 := by decide
  rcases family_descends (prefixWord ++ tailWord_394359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394378 : List Nat := [3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_394378 : Nat := 118140960795 + 394378 * 2 ^ 59
def prefixEnd_394378 : Nat := 4983230072969 + 3 ^ 40 * 394378 * 2
def baseEnd_394378 : Nat := 120003243590496727680767

theorem tailTrace_394378 : CollatzResearch.WordTrace tailWord_394378 prefixEnd_394378 120003243590496727680767 := by
  unfold tailWord_394378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596036841310833811287947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9589431576828890163434525 3596036841310833811287947)
  ·
    refine ⟨5394055261966250716931921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3596036841310833811287947 5394055261966250716931921)
    ·
      refine ⟨4045541446474688037698941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5394055261966250716931921 4045541446474688037698941)
      ·
        refine ⟨1517078042428008014137103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4045541446474688037698941 1517078042428008014137103)
        ·
          refine ⟨2275617063642012021205655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517078042428008014137103 2275617063642012021205655)
          ·
            refine ⟨3413425595463018031808483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275617063642012021205655 3413425595463018031808483)
            ·
              refine ⟨5120138393194527047712725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413425595463018031808483 5120138393194527047712725)
              ·
                refine ⟨120003243590496727680767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5120138393194527047712725 120003243590496727680767)
                ·
                  rfl

theorem cell19_394378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_394378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394378 prefixEnd_394378 := by exact prefixLift 394378
  have htrace : WordTrace (prefixWord ++ tailWord_394378) baseStart_394378 baseEnd_394378 := by
    simpa [prefixWord, tailWord_394378, baseEnd_394378] using wordTrace_append hprefix tailTrace_394378
  have hstable : (prefixWord ++ tailWord_394378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394378).length < 2 ^ (prefixWord ++ tailWord_394378).sum := by decide
  have hdescent : baseEnd_394378 < baseStart_394378 := by decide
  rcases family_descends (prefixWord ++ tailWord_394378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394528 : List Nat := [2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_394528 : Nat := 118140960795 + 394528 * 2 ^ 59
def prefixEnd_394528 : Nat := 4983230072969 + 3 ^ 40 * 394528 * 2
def baseEnd_394528 : Nat := 120048886315340824347025

theorem tailTrace_394528 : CollatzResearch.WordTrace tailWord_394528 prefixEnd_394528 120048886315340824347025 := by
  unfold tailWord_394528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7194809157349955431556119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9593078876466607242074825 7194809157349955431556119)
  ·
    refine ⟨10792213736024933147334179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7194809157349955431556119 10792213736024933147334179)
    ·
      refine ⟨16188320604037399721001269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10792213736024933147334179 16188320604037399721001269)
      ·
        refine ⟨1517655056628506223843869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16188320604037399721001269 1517655056628506223843869)
        ·
          refine ⟨569120646235689833941451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1517655056628506223843869 569120646235689833941451)
          ·
            refine ⟨853680969353534750912177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569120646235689833941451 853680969353534750912177)
            ·
              refine ⟨640260727015151063184133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853680969353534750912177 640260727015151063184133)
              ·
                refine ⟨120048886315340824347025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640260727015151063184133 120048886315340824347025)
                ·
                  rfl

theorem cell19_394528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_394528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394528 prefixEnd_394528 := by exact prefixLift 394528
  have htrace : WordTrace (prefixWord ++ tailWord_394528) baseStart_394528 baseEnd_394528 := by
    simpa [prefixWord, tailWord_394528, baseEnd_394528] using wordTrace_append hprefix tailTrace_394528
  have hstable : (prefixWord ++ tailWord_394528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394528).length < 2 ^ (prefixWord ++ tailWord_394528).sum := by decide
  have hdescent : baseEnd_394528 < baseStart_394528 := by decide
  rcases family_descends (prefixWord ++ tailWord_394528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394549 : List Nat := [1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_394549 : Nat := 118140960795 + 394549 * 2 ^ 59
def prefixEnd_394549 : Nat := 4983230072969 + 3 ^ 40 * 394549 * 2
def baseEnd_394549 : Nat := 120055276296818997880301

theorem tailTrace_394549 : CollatzResearch.WordTrace tailWord_394549 prefixEnd_394549 120055276296818997880301 := by
  unfold tailWord_394549
  simp only [CollatzResearch.WordTrace]
  refine ⟨14390384247623831449626701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9593589498415887633084467 14390384247623831449626701)
  ·
    refine ⟨5396394092858936793610013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14390384247623831449626701 5396394092858936793610013)
    ·
      refine ⟨2023647784822101297603755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5396394092858936793610013 2023647784822101297603755)
      ·
        refine ⟨3035471677233151946405633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023647784822101297603755 3035471677233151946405633)
        ·
          refine ⟨2276603757924863959804225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035471677233151946405633 2276603757924863959804225)
          ·
            refine ⟨1707452818443647969853169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276603757924863959804225 1707452818443647969853169)
            ·
              refine ⟨1280589613832735977389877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707452818443647969853169 1280589613832735977389877)
              ·
                refine ⟨120055276296818997880301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1280589613832735977389877 120055276296818997880301)
                ·
                  rfl

theorem cell19_394549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_394549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394549 prefixEnd_394549 := by exact prefixLift 394549
  have htrace : WordTrace (prefixWord ++ tailWord_394549) baseStart_394549 baseEnd_394549 := by
    simpa [prefixWord, tailWord_394549, baseEnd_394549] using wordTrace_append hprefix tailTrace_394549
  have hstable : (prefixWord ++ tailWord_394549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394549).length < 2 ^ (prefixWord ++ tailWord_394549).sum := by decide
  have hdescent : baseEnd_394549 < baseStart_394549 := by decide
  rcases family_descends (prefixWord ++ tailWord_394549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394602 : List Nat := [3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_394602 : Nat := 118140960795 + 394602 * 2 ^ 59
def prefixEnd_394602 : Nat := 4983230072969 + 3 ^ 40 * 394602 * 2
def baseEnd_394602 : Nat := 120071403392930578702379

theorem tailTrace_394602 : CollatzResearch.WordTrace tailWord_394602 prefixEnd_394602 120071403392930578702379 := by
  unfold tailWord_394602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598079329107955375326515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9594878210954547667537373 3598079329107955375326515)
  ·
    refine ⟨5397118993661933062989773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3598079329107955375326515 5397118993661933062989773)
    ·
      refine ⟨2023919622623224898621165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5397118993661933062989773 2023919622623224898621165)
      ·
        refine ⟨758969858483709336982937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2023919622623224898621165 758969858483709336982937)
        ·
          refine ⟨569227393862782002737203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758969858483709336982937 569227393862782002737203)
          ·
            refine ⟨853841090794173004105805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569227393862782002737203 853841090794173004105805)
            ·
              refine ⟨320190409047814876539677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853841090794173004105805 320190409047814876539677)
              ·
                refine ⟨120071403392930578702379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320190409047814876539677 120071403392930578702379)
                ·
                  rfl

theorem cell19_394602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_394602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394602 prefixEnd_394602 := by exact prefixLift 394602
  have htrace : WordTrace (prefixWord ++ tailWord_394602) baseStart_394602 baseEnd_394602 := by
    simpa [prefixWord, tailWord_394602, baseEnd_394602] using wordTrace_append hprefix tailTrace_394602
  have hstable : (prefixWord ++ tailWord_394602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394602).length < 2 ^ (prefixWord ++ tailWord_394602).sum := by decide
  have hdescent : baseEnd_394602 < baseStart_394602 := by decide
  rcases family_descends (prefixWord ++ tailWord_394602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394604 : List Nat := [2, 2, 1, 1, 5, 2, 3, 3]
def baseStart_394604 : Nat := 118140960795 + 394604 * 2 ^ 59
def prefixEnd_394604 : Nat := 4983230072969 + 3 ^ 40 * 394604 * 2
def baseEnd_394604 : Nat := 120072011962595166657929

theorem tailTrace_394604 : CollatzResearch.WordTrace tailWord_394604 prefixEnd_394604 120072011962595166657929 := by
  unfold tailWord_394604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196195131212287921439433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9594926841616383895252577 7196195131212287921439433)
  ·
    refine ⟨5397146348409215941079575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7196195131212287921439433 5397146348409215941079575)
    ·
      refine ⟨8095719522613823911619363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5397146348409215941079575 8095719522613823911619363)
      ·
        refine ⟨12143579283920735867429045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8095719522613823911619363 12143579283920735867429045)
        ·
          refine ⟨1138460557867568987571473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12143579283920735867429045 1138460557867568987571473)
          ·
            refine ⟨853845418400676740678605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138460557867568987571473 853845418400676740678605)
            ·
              refine ⟨320192031900253777754477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853845418400676740678605 320192031900253777754477)
              ·
                refine ⟨120072011962595166657929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320192031900253777754477 120072011962595166657929)
                ·
                  rfl

theorem cell19_394604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_394604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394604 prefixEnd_394604 := by exact prefixLift 394604
  have htrace : WordTrace (prefixWord ++ tailWord_394604) baseStart_394604 baseEnd_394604 := by
    simpa [prefixWord, tailWord_394604, baseEnd_394604] using wordTrace_append hprefix tailTrace_394604
  have hstable : (prefixWord ++ tailWord_394604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394604).length < 2 ^ (prefixWord ++ tailWord_394604).sum := by decide
  have hdescent : baseEnd_394604 < baseStart_394604 := by decide
  rcases family_descends (prefixWord ++ tailWord_394604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394663 : List Nat := [1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_394663 : Nat := 118140960795 + 394663 * 2 ^ 59
def prefixEnd_394663 : Nat := 4983230072969 + 3 ^ 40 * 394663 * 2
def baseEnd_394663 : Nat := 120089964767700511346657

theorem tailTrace_394663 : CollatzResearch.WordTrace tailWord_394663 prefixEnd_394663 120089964767700511346657 := by
  unfold tailWord_394663
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394542169210828919276643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9596361446140552612851095 14394542169210828919276643)
  ·
    refine ⟨21591813253816243378914965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14394542169210828919276643 21591813253816243378914965)
    ·
      refine ⟨1012116246272636408386639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21591813253816243378914965 1012116246272636408386639)
      ·
        refine ⟨1518174369408954612579959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012116246272636408386639 1518174369408954612579959)
        ·
          refine ⟨2277261554113431918869939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518174369408954612579959 2277261554113431918869939)
          ·
            refine ⟨3415892331170147878304909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277261554113431918869939 3415892331170147878304909)
            ·
              refine ⟨1280959624188805454364341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3415892331170147878304909 1280959624188805454364341)
              ·
                refine ⟨120089964767700511346657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1280959624188805454364341 120089964767700511346657)
                ·
                  rfl

theorem cell19_394663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_394663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394663 prefixEnd_394663 := by exact prefixLift 394663
  have htrace : WordTrace (prefixWord ++ tailWord_394663) baseStart_394663 baseEnd_394663 := by
    simpa [prefixWord, tailWord_394663, baseEnd_394663] using wordTrace_append hprefix tailTrace_394663
  have hstable : (prefixWord ++ tailWord_394663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394663).length < 2 ^ (prefixWord ++ tailWord_394663).sum := by decide
  have hdescent : baseEnd_394663 < baseStart_394663 := by decide
  rcases family_descends (prefixWord ++ tailWord_394663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394703 : List Nat := [1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_394703 : Nat := 118140960795 + 394703 * 2 ^ 59
def prefixEnd_394703 : Nat := 4983230072969 + 3 ^ 40 * 394703 * 2
def baseEnd_394703 : Nat := 120102136160992270457659

theorem tailTrace_394703 : CollatzResearch.WordTrace tailWord_394703 prefixEnd_394703 120102136160992270457659 := by
  unfold tailWord_394703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14396001089065915750732763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9597334059377277167155175 14396001089065915750732763)
  ·
    refine ⟨21594001633598873626099145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14396001089065915750732763 21594001633598873626099145)
    ·
      refine ⟨16195501225199155219574359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21594001633598873626099145 16195501225199155219574359)
      ·
        refine ⟨24293251837798732829361539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16195501225199155219574359 24293251837798732829361539)
        ·
          refine ⟨36439877756698099244042309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24293251837798732829361539 36439877756698099244042309)
          ·
            refine ⟨6832477079380893608257933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36439877756698099244042309 6832477079380893608257933)
            ·
              refine ⟨2562178904767835103096725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6832477079380893608257933 2562178904767835103096725)
              ·
                refine ⟨120102136160992270457659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2562178904767835103096725 120102136160992270457659)
                ·
                  rfl

theorem cell19_394703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_394703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394703 prefixEnd_394703 := by exact prefixLift 394703
  have htrace : WordTrace (prefixWord ++ tailWord_394703) baseStart_394703 baseEnd_394703 := by
    simpa [prefixWord, tailWord_394703, baseEnd_394703] using wordTrace_append hprefix tailTrace_394703
  have hstable : (prefixWord ++ tailWord_394703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394703).length < 2 ^ (prefixWord ++ tailWord_394703).sum := by decide
  have hdescent : baseEnd_394703 < baseStart_394703 := by decide
  rcases family_descends (prefixWord ++ tailWord_394703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394754 : List Nat := [3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_394754 : Nat := 118140960795 + 394754 * 2 ^ 59
def prefixEnd_394754 : Nat := 4983230072969 + 3 ^ 40 * 394754 * 2
def baseEnd_394754 : Nat := 120117654687439263324187

theorem tailTrace_394754 : CollatzResearch.WordTrace tailWord_394754 prefixEnd_394754 120117654687439263324187 := by
  unfold tailWord_394754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599465302970287865209829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9598574141254100973892877 3599465302970287865209829)
  ·
    refine ⟨674899744306928974726843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3599465302970287865209829 674899744306928974726843)
    ·
      refine ⟨1012349616460393462090265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674899744306928974726843 1012349616460393462090265)
      ·
        refine ⟨759262212345295096567699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1012349616460393462090265 759262212345295096567699)
        ·
          refine ⟨1138893318517942644851549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759262212345295096567699 1138893318517942644851549)
          ·
            refine ⟨427084994444228491819331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1138893318517942644851549 427084994444228491819331)
            ·
              refine ⟨640627491666342737728997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427084994444228491819331 640627491666342737728997)
              ·
                refine ⟨120117654687439263324187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640627491666342737728997 120117654687439263324187)
                ·
                  rfl

theorem cell19_394754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_394754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394754 prefixEnd_394754 := by exact prefixLift 394754
  have htrace : WordTrace (prefixWord ++ tailWord_394754) baseStart_394754 baseEnd_394754 := by
    simpa [prefixWord, tailWord_394754, baseEnd_394754] using wordTrace_append hprefix tailTrace_394754
  have hstable : (prefixWord ++ tailWord_394754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394754).length < 2 ^ (prefixWord ++ tailWord_394754).sum := by decide
  have hdescent : baseEnd_394754 < baseStart_394754 := by decide
  rcases family_descends (prefixWord ++ tailWord_394754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394834 : List Nat := [3, 2, 2, 1, 2, 3, 1, 5]
def baseStart_394834 : Nat := 118140960795 + 394834 * 2 ^ 59
def prefixEnd_394834 : Nat := 4983230072969 + 3 ^ 40 * 394834 * 2
def baseEnd_394834 : Nat := 120141997474022781546191

theorem tailTrace_394834 : CollatzResearch.WordTrace tailWord_394834 prefixEnd_394834 120141997474022781546191 := by
  unfold tailWord_394834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600194762897831280937889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9600519367727550082501037 3600194762897831280937889)
  ·
    refine ⟨2700146072173373460703417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3600194762897831280937889 2700146072173373460703417)
    ·
      refine ⟨2025109554130030095527563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2700146072173373460703417 2025109554130030095527563)
      ·
        refine ⟨3037664331195045143291345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025109554130030095527563 3037664331195045143291345)
        ·
          refine ⟨2278248248396283857468509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3037664331195045143291345 2278248248396283857468509)
          ·
            refine ⟨854343093148606446550691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2278248248396283857468509 854343093148606446550691)
            ·
              refine ⟨1281514639722909669826037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854343093148606446550691 1281514639722909669826037)
              ·
                refine ⟨120141997474022781546191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1281514639722909669826037 120141997474022781546191)
                ·
                  rfl

theorem cell19_394834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_394834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394834 prefixEnd_394834 := by exact prefixLift 394834
  have htrace : WordTrace (prefixWord ++ tailWord_394834) baseStart_394834 baseEnd_394834 := by
    simpa [prefixWord, tailWord_394834, baseEnd_394834] using wordTrace_append hprefix tailTrace_394834
  have hstable : (prefixWord ++ tailWord_394834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394834).length < 2 ^ (prefixWord ++ tailWord_394834).sum := by decide
  have hdescent : baseEnd_394834 < baseStart_394834 := by decide
  rcases family_descends (prefixWord ++ tailWord_394834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394853 : List Nat := [1, 3, 1, 3, 3, 3, 5]
def baseStart_394853 : Nat := 118140960795 + 394853 * 2 ^ 59
def prefixEnd_394853 : Nat := 4983230072969 + 3 ^ 40 * 394853 * 2
def baseEnd_394853 : Nat := 40049259628612122374639

theorem tailTrace_394853 : CollatzResearch.WordTrace tailWord_394853 prefixEnd_394853 40049259628612122374639 := by
  unfold tailWord_394853
  simp only [CollatzResearch.WordTrace]
  refine ⟨14401472038522491368693213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9600981359014994245795475 14401472038522491368693213)
  ·
    refine ⟨5400552014445934263259955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14401472038522491368693213 5400552014445934263259955)
    ·
      refine ⟨8100828021668901394889933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400552014445934263259955 8100828021668901394889933)
      ·
        refine ⟨3037810508125838023083725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8100828021668901394889933 3037810508125838023083725)
        ·
          refine ⟨1139178940547189258656397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3037810508125838023083725 1139178940547189258656397)
          ·
            refine ⟨427192102705195971996149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1139178940547189258656397 427192102705195971996149)
            ·
              refine ⟨40049259628612122374639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 427192102705195971996149 40049259628612122374639)
              ·
                rfl

theorem cell19_394853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_394853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394853 prefixEnd_394853 := by exact prefixLift 394853
  have htrace : WordTrace (prefixWord ++ tailWord_394853) baseStart_394853 baseEnd_394853 := by
    simpa [prefixWord, tailWord_394853, baseEnd_394853] using wordTrace_append hprefix tailTrace_394853
  have hstable : (prefixWord ++ tailWord_394853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394853).length < 2 ^ (prefixWord ++ tailWord_394853).sum := by decide
  have hdescent : baseEnd_394853 < baseStart_394853 := by decide
  rcases family_descends (prefixWord ++ tailWord_394853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394855 : List Nat := [1, 1, 5, 1, 1, 1, 9]
def baseStart_394855 : Nat := 118140960795 + 394855 * 2 ^ 59
def prefixEnd_394855 : Nat := 4983230072969 + 3 ^ 40 * 394855 * 2
def baseEnd_394855 : Nat := 40049462485166985026489

theorem tailTrace_394855 : CollatzResearch.WordTrace tailWord_394855 prefixEnd_394855 40049462485166985026489 := by
  unfold tailWord_394855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14401544984515245710266019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9601029989676830473510679 14401544984515245710266019)
  ·
    refine ⟨21602317476772868565399029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14401544984515245710266019 21602317476772868565399029)
    ·
      refine ⟨2025217263447456428006159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21602317476772868565399029 2025217263447456428006159)
      ·
        refine ⟨3037825895171184642009239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025217263447456428006159 3037825895171184642009239)
        ·
          refine ⟨4556738842756776963013859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037825895171184642009239 4556738842756776963013859)
          ·
            refine ⟨6835108264135165444520789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556738842756776963013859 6835108264135165444520789)
            ·
              refine ⟨40049462485166985026489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6835108264135165444520789 40049462485166985026489)
              ·
                rfl

theorem cell19_394855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_394855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394855 prefixEnd_394855 := by exact prefixLift 394855
  have htrace : WordTrace (prefixWord ++ tailWord_394855) baseStart_394855 baseEnd_394855 := by
    simpa [prefixWord, tailWord_394855, baseEnd_394855] using wordTrace_append hprefix tailTrace_394855
  have hstable : (prefixWord ++ tailWord_394855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394855).length < 2 ^ (prefixWord ++ tailWord_394855).sum := by decide
  have hdescent : baseEnd_394855 < baseStart_394855 := by decide
  rcases family_descends (prefixWord ++ tailWord_394855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394870 : List Nat := [5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_394870 : Nat := 118140960795 + 394870 * 2 ^ 59
def prefixEnd_394870 : Nat := 4983230072969 + 3 ^ 40 * 394870 * 2
def baseEnd_394870 : Nat := 120152951727985364746093

theorem tailTrace_394870 : CollatzResearch.WordTrace tailWord_394870 prefixEnd_394870 120152951727985364746093 := by
  unfold tailWord_394870
  simp only [CollatzResearch.WordTrace]
  refine ⟨900130754966306454503879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9601394719640602181374709 900130754966306454503879)
  ·
    refine ⟨1350196132449459681755819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 900130754966306454503879 1350196132449459681755819)
    ·
      refine ⟨2025294198674189522633729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1350196132449459681755819 2025294198674189522633729)
      ·
        refine ⟨1518970649005642141975297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025294198674189522633729 1518970649005642141975297)
        ·
          refine ⟨1139227986754231606481473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518970649005642141975297 1139227986754231606481473)
          ·
            refine ⟨854420990065673704861105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139227986754231606481473 854420990065673704861105)
            ·
              refine ⟨640815742549255278645829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854420990065673704861105 640815742549255278645829)
              ·
                refine ⟨120152951727985364746093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640815742549255278645829 120152951727985364746093)
                ·
                  rfl

theorem cell19_394870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_394870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394870 prefixEnd_394870 := by exact prefixLift 394870
  have htrace : WordTrace (prefixWord ++ tailWord_394870) baseStart_394870 baseEnd_394870 := by
    simpa [prefixWord, tailWord_394870, baseEnd_394870] using wordTrace_append hprefix tailTrace_394870
  have hstable : (prefixWord ++ tailWord_394870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394870).length < 2 ^ (prefixWord ++ tailWord_394870).sum := by decide
  have hdescent : baseEnd_394870 < baseStart_394870 := by decide
  rcases family_descends (prefixWord ++ tailWord_394870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394910 : List Nat := [4, 3, 1, 1, 1, 9]
def baseStart_394910 : Nat := 118140960795 + 394910 * 2 ^ 59
def prefixEnd_394910 : Nat := 4983230072969 + 3 ^ 40 * 394910 * 2
def baseEnd_394910 : Nat := 13351680346808569317455

theorem tailTrace_394910 : CollatzResearch.WordTrace tailWord_394910 prefixEnd_394910 13351680346808569317455 := by
  unfold tailWord_394910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800443874914498762939773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9602367332877326735678789 1800443874914498762939773)
  ·
    refine ⟨675166453092937036102415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1800443874914498762939773 675166453092937036102415)
    ·
      refine ⟨1012749679639405554153623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675166453092937036102415 1012749679639405554153623)
      ·
        refine ⟨1519124519459108331230435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012749679639405554153623 1519124519459108331230435)
        ·
          refine ⟨2278686779188662496845653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519124519459108331230435 2278686779188662496845653)
          ·
            refine ⟨13351680346808569317455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2278686779188662496845653 13351680346808569317455)
            ·
              rfl

theorem cell19_394910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_394910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394910 prefixEnd_394910 := by exact prefixLift 394910
  have htrace : WordTrace (prefixWord ++ tailWord_394910) baseStart_394910 baseEnd_394910 := by
    simpa [prefixWord, tailWord_394910, baseEnd_394910] using wordTrace_append hprefix tailTrace_394910
  have hstable : (prefixWord ++ tailWord_394910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394910).length < 2 ^ (prefixWord ++ tailWord_394910).sum := by decide
  have hdescent : baseEnd_394910 < baseStart_394910 := by decide
  rcases family_descends (prefixWord ++ tailWord_394910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394912 : List Nat := [2, 1, 1, 4, 3, 8]
def baseStart_394912 : Nat := 118140960795 + 394912 * 2 ^ 59
def prefixEnd_394912 : Nat := 4983230072969 + 3 ^ 40 * 394912 * 2
def baseEnd_394912 : Nat := 13351747965660190201405

theorem tailTrace_394912 : CollatzResearch.WordTrace tailWord_394912 prefixEnd_394912 13351747965660190201405 := by
  unfold tailWord_394912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201811972654372222545495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9602415963539162963393993 7201811972654372222545495)
  ·
    refine ⟨10802717958981558333818243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7201811972654372222545495 10802717958981558333818243)
    ·
      refine ⟨16204076938472337500727365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802717958981558333818243 16204076938472337500727365)
      ·
        refine ⟨3038264425963563281386381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16204076938472337500727365 3038264425963563281386381)
        ·
          refine ⟨1139349159736336230519893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3038264425963563281386381 1139349159736336230519893)
          ·
            refine ⟨13351747965660190201405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1139349159736336230519893 13351747965660190201405)
            ·
              rfl

theorem cell19_394912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_394912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394912 prefixEnd_394912 := by exact prefixLift 394912
  have htrace : WordTrace (prefixWord ++ tailWord_394912) baseStart_394912 baseEnd_394912 := by
    simpa [prefixWord, tailWord_394912, baseEnd_394912] using wordTrace_append hprefix tailTrace_394912
  have hstable : (prefixWord ++ tailWord_394912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394912).length < 2 ^ (prefixWord ++ tailWord_394912).sum := by decide
  have hdescent : baseEnd_394912 < baseStart_394912 := by decide
  rcases family_descends (prefixWord ++ tailWord_394912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394969 : List Nat := [1, 2, 1, 2, 3, 4, 6]
def baseStart_394969 : Nat := 118140960795 + 394969 * 2 ^ 59
def prefixEnd_394969 : Nat := 4983230072969 + 3 ^ 40 * 394969 * 2
def baseEnd_394969 : Nat := 40061025308794156181941

theorem tailTrace_394969 : CollatzResearch.WordTrace tailWord_394969 prefixEnd_394969 40061025308794156181941 := by
  unfold tailWord_394969
  simp only [CollatzResearch.WordTrace]
  refine ⟨14405702906102243179915961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9603801937401495453277307 14405702906102243179915961)
  ·
    refine ⟨10804277179576682384936971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14405702906102243179915961 10804277179576682384936971)
    ·
      refine ⟨16206415769365023577405457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10804277179576682384936971 16206415769365023577405457)
      ·
        refine ⟨12154811827023767683054093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16206415769365023577405457 12154811827023767683054093)
        ·
          refine ⟨4558054435133912881145285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12154811827023767683054093 4558054435133912881145285)
          ·
            refine ⟨854635206587608665214741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4558054435133912881145285 854635206587608665214741)
            ·
              refine ⟨40061025308794156181941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 854635206587608665214741 40061025308794156181941)
              ·
                rfl

theorem cell19_394969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_394969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_394969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_394969 prefixEnd_394969 := by exact prefixLift 394969
  have htrace : WordTrace (prefixWord ++ tailWord_394969) baseStart_394969 baseEnd_394969 := by
    simpa [prefixWord, tailWord_394969, baseEnd_394969] using wordTrace_append hprefix tailTrace_394969
  have hstable : (prefixWord ++ tailWord_394969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394969).length < 2 ^ (prefixWord ++ tailWord_394969).sum := by decide
  have hdescent : baseEnd_394969 < baseStart_394969 := by decide
  rcases family_descends (prefixWord ++ tailWord_394969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395014 : List Nat := [6, 2, 2, 1, 2, 1, 5]
def baseStart_395014 : Nat := 118140960795 + 395014 * 2 ^ 59
def prefixEnd_395014 : Nat := 4983230072969 + 3 ^ 40 * 395014 * 2
def baseEnd_395014 : Nat := 40065589581278565848567

theorem tailTrace_395014 : CollatzResearch.WordTrace tailWord_395014 prefixEnd_395014 40065589581278565848567 := by
  unfold tailWord_395014
  simp only [CollatzResearch.WordTrace]
  refine ⟨450229505966850495790753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9604896127292810576869397 450229505966850495790753)
  ·
    refine ⟨337672129475137871843065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 450229505966850495790753 337672129475137871843065)
    ·
      refine ⟨253254097106353403882299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337672129475137871843065 253254097106353403882299)
      ·
        refine ⟨379881145659530105823449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253254097106353403882299 379881145659530105823449)
        ·
          refine ⟨284910859244647579367587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379881145659530105823449 284910859244647579367587)
          ·
            refine ⟨427366288866971369051381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284910859244647579367587 427366288866971369051381)
            ·
              refine ⟨40065589581278565848567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 427366288866971369051381 40065589581278565848567)
              ·
                rfl

theorem cell19_395014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_395014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395014 prefixEnd_395014 := by exact prefixLift 395014
  have htrace : WordTrace (prefixWord ++ tailWord_395014) baseStart_395014 baseEnd_395014 := by
    simpa [prefixWord, tailWord_395014, baseEnd_395014] using wordTrace_append hprefix tailTrace_395014
  have hstable : (prefixWord ++ tailWord_395014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395014).length < 2 ^ (prefixWord ++ tailWord_395014).sum := by decide
  have hdescent : baseEnd_395014 < baseStart_395014 := by decide
  rcases family_descends (prefixWord ++ tailWord_395014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395045 : List Nat := [1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_395045 : Nat := 118140960795 + 395045 * 2 ^ 59
def prefixEnd_395045 : Nat := 4983230072969 + 3 ^ 40 * 395045 * 2
def baseEnd_395045 : Nat := 120206201573636810856727

theorem tailTrace_395045 : CollatzResearch.WordTrace tailWord_395045 prefixEnd_395045 120206201573636810856727 := by
  unfold tailWord_395045
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408474853826908159682589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9605649902551272106455059 14408474853826908159682589)
  ·
    refine ⟨5403178070185090559880971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14408474853826908159682589 5403178070185090559880971)
    ·
      refine ⟨8104767105277635839821457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5403178070185090559880971 8104767105277635839821457)
      ·
        refine ⟨6078575328958226879866093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8104767105277635839821457 6078575328958226879866093)
        ·
          refine ⟨2279465748359335079949785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6078575328958226879866093 2279465748359335079949785)
          ·
            refine ⟨1709599311269501309962339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2279465748359335079949785 1709599311269501309962339)
            ·
              refine ⟨2564398966904251964943509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709599311269501309962339 2564398966904251964943509)
              ·
                refine ⟨120206201573636810856727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2564398966904251964943509 120206201573636810856727)
                ·
                  rfl

theorem cell19_395045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_395045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395045 prefixEnd_395045 := by exact prefixLift 395045
  have htrace : WordTrace (prefixWord ++ tailWord_395045) baseStart_395045 baseEnd_395045 := by
    simpa [prefixWord, tailWord_395045, baseEnd_395045] using wordTrace_append hprefix tailTrace_395045
  have hstable : (prefixWord ++ tailWord_395045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395045).length < 2 ^ (prefixWord ++ tailWord_395045).sum := by decide
  have hdescent : baseEnd_395045 < baseStart_395045 := by decide
  rcases family_descends (prefixWord ++ tailWord_395045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395064 : List Nat := [2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_395064 : Nat := 118140960795 + 395064 * 2 ^ 59
def prefixEnd_395064 : Nat := 4983230072969 + 3 ^ 40 * 395064 * 2
def baseEnd_395064 : Nat := 120211982985450396434453

theorem tailTrace_395064 : CollatzResearch.WordTrace tailWord_395064 prefixEnd_395064 120211982985450396434453 := by
  unfold tailWord_395064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204583920379037202312123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9606111893838716269749497 7204583920379037202312123)
  ·
    refine ⟨10806875880568555803468185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7204583920379037202312123 10806875880568555803468185)
    ·
      refine ⟨8105156910426416852601139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10806875880568555803468185 8105156910426416852601139)
      ·
        refine ⟨12157735365639625278901709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8105156910426416852601139 12157735365639625278901709)
        ·
          refine ⟨4559150762114859479588141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12157735365639625278901709 4559150762114859479588141)
          ·
            refine ⟨1709681535793072304845553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4559150762114859479588141 1709681535793072304845553)
            ·
              refine ⟨1282261151844804228634165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709681535793072304845553 1282261151844804228634165)
              ·
                refine ⟨120211982985450396434453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1282261151844804228634165 120211982985450396434453)
                ·
                  rfl

theorem cell19_395064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_395064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395064 prefixEnd_395064 := by exact prefixLift 395064
  have htrace : WordTrace (prefixWord ++ tailWord_395064) baseStart_395064 baseEnd_395064 := by
    simpa [prefixWord, tailWord_395064, baseEnd_395064] using wordTrace_append hprefix tailTrace_395064
  have hstable : (prefixWord ++ tailWord_395064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395064).length < 2 ^ (prefixWord ++ tailWord_395064).sum := by decide
  have hdescent : baseEnd_395064 < baseStart_395064 := by decide
  rcases family_descends (prefixWord ++ tailWord_395064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395197 : List Nat := [1, 4, 1, 2, 3, 1, 7]
def baseStart_395197 : Nat := 118140960795 + 395197 * 2 ^ 59
def prefixEnd_395197 : Nat := 4983230072969 + 3 ^ 40 * 395197 * 2
def baseEnd_395197 : Nat := 40084150956048498492845

theorem tailTrace_395197 : CollatzResearch.WordTrace tailWord_395197 prefixEnd_395197 40084150956048498492845 := by
  unfold tailWord_395197
  simp only [CollatzResearch.WordTrace]
  refine ⟨14414018749276238119215845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9609345832850825412810563 14414018749276238119215845)
  ·
    refine ⟨2702628515489294647352971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14414018749276238119215845 2702628515489294647352971)
    ·
      refine ⟨4053942773233941971029457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2702628515489294647352971 4053942773233941971029457)
      ·
        refine ⟨3040457079925456478272093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4053942773233941971029457 3040457079925456478272093)
        ·
          refine ⟨1140171404972046179352035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3040457079925456478272093 1140171404972046179352035)
          ·
            refine ⟨1710257107458069269028053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140171404972046179352035 1710257107458069269028053)
            ·
              refine ⟨40084150956048498492845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1710257107458069269028053 40084150956048498492845)
              ·
                rfl

theorem cell19_395197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_395197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395197 prefixEnd_395197 := by exact prefixLift 395197
  have htrace : WordTrace (prefixWord ++ tailWord_395197) baseStart_395197 baseEnd_395197 := by
    simpa [prefixWord, tailWord_395197, baseEnd_395197] using wordTrace_append hprefix tailTrace_395197
  have hstable : (prefixWord ++ tailWord_395197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395197).length < 2 ^ (prefixWord ++ tailWord_395197).sum := by decide
  have hdescent : baseEnd_395197 < baseStart_395197 := by decide
  rcases family_descends (prefixWord ++ tailWord_395197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395235 : List Nat := [1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_395235 : Nat := 118140960795 + 395235 * 2 ^ 59
def prefixEnd_395235 : Nat := 4983230072969 + 3 ^ 40 * 395235 * 2
def baseEnd_395235 : Nat := 120264015691772666633987

theorem tailTrace_395235 : CollatzResearch.WordTrace tailWord_395235 prefixEnd_395235 120264015691772666633987 := by
  unfold tailWord_395235
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415404723138570609099159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9610269815425713739399439 14415404723138570609099159)
  ·
    refine ⟨21623107084707855913648739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14415404723138570609099159 21623107084707855913648739)
    ·
      refine ⟨32434660627061783870473109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21623107084707855913648739 32434660627061783870473109)
      ·
        refine ⟨1520374716893521118928427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32434660627061783870473109 1520374716893521118928427)
        ·
          refine ⟨2280562075340281678392641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520374716893521118928427 2280562075340281678392641)
          ·
            refine ⟨1710421556505211258794481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280562075340281678392641 1710421556505211258794481)
            ·
              refine ⟨1282816167378908444095861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710421556505211258794481 1282816167378908444095861)
              ·
                refine ⟨120264015691772666633987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1282816167378908444095861 120264015691772666633987)
                ·
                  rfl

theorem cell19_395235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_395235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395235 prefixEnd_395235 := by exact prefixLift 395235
  have htrace : WordTrace (prefixWord ++ tailWord_395235) baseStart_395235 baseEnd_395235 := by
    simpa [prefixWord, tailWord_395235, baseEnd_395235] using wordTrace_append hprefix tailTrace_395235
  have hstable : (prefixWord ++ tailWord_395235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395235).length < 2 ^ (prefixWord ++ tailWord_395235).sum := by decide
  have hdescent : baseEnd_395235 < baseStart_395235 := by decide
  rcases family_descends (prefixWord ++ tailWord_395235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395254 : List Nat := [5, 1, 1, 1, 11]
def baseStart_395254 : Nat := 118140960795 + 395254 * 2 ^ 59
def prefixEnd_395254 : Nat := 4983230072969 + 3 ^ 40 * 395254 * 2
def baseEnd_395254 : Nat := 4454436929762453785619

theorem tailTrace_395254 : CollatzResearch.WordTrace tailWord_395254 prefixEnd_395254 4454436929762453785619 := by
  unfold tailWord_395254
  simp only [CollatzResearch.WordTrace]
  refine ⟨901006106879358553377551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9610731806713157902693877 901006106879358553377551)
  ·
    refine ⟨1351509160319037830066327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 901006106879358553377551 1351509160319037830066327)
    ·
      refine ⟨2027263740478556745099491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351509160319037830066327 2027263740478556745099491)
      ·
        refine ⟨3040895610717835117649237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027263740478556745099491 3040895610717835117649237)
        ·
          refine ⟨4454436929762453785619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3040895610717835117649237 4454436929762453785619)
          ·
            rfl

theorem cell19_395254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 11].length) (baseStart_395254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395254 prefixEnd_395254 := by exact prefixLift 395254
  have htrace : WordTrace (prefixWord ++ tailWord_395254) baseStart_395254 baseEnd_395254 := by
    simpa [prefixWord, tailWord_395254, baseEnd_395254] using wordTrace_append hprefix tailTrace_395254
  have hstable : (prefixWord ++ tailWord_395254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395254).length < 2 ^ (prefixWord ++ tailWord_395254).sum := by decide
  have hdescent : baseEnd_395254 < baseStart_395254 := by decide
  rcases family_descends (prefixWord ++ tailWord_395254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395271 : List Nat := [1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_395271 : Nat := 118140960795 + 395271 * 2 ^ 59
def prefixEnd_395271 : Nat := 4983230072969 + 3 ^ 40 * 395271 * 2
def baseEnd_395271 : Nat := 120274969945735249833889

theorem tailTrace_395271 : CollatzResearch.WordTrace tailWord_395271 prefixEnd_395271 120274969945735249833889 := by
  unfold tailWord_395271
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416717751008148757409667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9611145167338765838273111 14416717751008148757409667)
  ·
    refine ⟨21625076626512223136114501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14416717751008148757409667 21625076626512223136114501)
    ·
      refine ⟨4054701867471041838021469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21625076626512223136114501 4054701867471041838021469)
      ·
        refine ⟨1520513200301640689258051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4054701867471041838021469 1520513200301640689258051)
        ·
          refine ⟨2280769800452461033887077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520513200301640689258051 2280769800452461033887077)
          ·
            refine ⟨427644337584836443853827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2280769800452461033887077 427644337584836443853827)
            ·
              refine ⟨641466506377254665780741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427644337584836443853827 641466506377254665780741)
              ·
                refine ⟨120274969945735249833889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 641466506377254665780741 120274969945735249833889)
                ·
                  rfl

theorem cell19_395271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_395271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395271 prefixEnd_395271 := by exact prefixLift 395271
  have htrace : WordTrace (prefixWord ++ tailWord_395271) baseStart_395271 baseEnd_395271 := by
    simpa [prefixWord, tailWord_395271, baseEnd_395271] using wordTrace_append hprefix tailTrace_395271
  have hstable : (prefixWord ++ tailWord_395271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395271).length < 2 ^ (prefixWord ++ tailWord_395271).sum := by decide
  have hdescent : baseEnd_395271 < baseStart_395271 := by decide
  rcases family_descends (prefixWord ++ tailWord_395271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395290 : List Nat := [3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_395290 : Nat := 118140960795 + 395290 * 2 ^ 59
def prefixEnd_395290 : Nat := 4983230072969 + 3 ^ 40 * 395290 * 2
def baseEnd_395290 : Nat := 120280751357548835411615

theorem tailTrace_395290 : CollatzResearch.WordTrace tailWord_395290 prefixEnd_395290 120280751357548835411615 := by
  unfold tailWord_395290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604352684484828750587831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9611607158626210001567549 3604352684484828750587831)
  ·
    refine ⟨5406529026727243125881747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3604352684484828750587831 5406529026727243125881747)
    ·
      refine ⟨8109793540090864688822621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406529026727243125881747 8109793540090864688822621)
      ·
        refine ⟨3041172577534074258308483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8109793540090864688822621 3041172577534074258308483)
        ·
          refine ⟨4561758866301111387462725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041172577534074258308483 4561758866301111387462725)
          ·
            refine ⟨855329787431458385149261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4561758866301111387462725 855329787431458385149261)
            ·
              refine ⟨320748670286796894430973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855329787431458385149261 320748670286796894430973)
              ·
                refine ⟨120280751357548835411615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320748670286796894430973 120280751357548835411615)
                ·
                  rfl

theorem cell19_395290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_395290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395290 prefixEnd_395290 := by exact prefixLift 395290
  have htrace : WordTrace (prefixWord ++ tailWord_395290) baseStart_395290 baseEnd_395290 := by
    simpa [prefixWord, tailWord_395290, baseEnd_395290] using wordTrace_append hprefix tailTrace_395290
  have hstable : (prefixWord ++ tailWord_395290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395290).length < 2 ^ (prefixWord ++ tailWord_395290).sum := by decide
  have hdescent : baseEnd_395290 < baseStart_395290 := by decide
  rcases family_descends (prefixWord ++ tailWord_395290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395349 : List Nat := [1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_395349 : Nat := 118140960795 + 395349 * 2 ^ 59
def prefixEnd_395349 : Nat := 4983230072969 + 3 ^ 40 * 395349 * 2
def baseEnd_395349 : Nat := 120298704162654180100343

theorem tailTrace_395349 : CollatzResearch.WordTrace tailWord_395349 prefixEnd_395349 120298704162654180100343 := by
  unfold tailWord_395349
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419562644725568078749101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9613041763150378719166067 14419562644725568078749101)
  ·
    refine ⟨5407335991772088029530913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14419562644725568078749101 5407335991772088029530913)
    ·
      refine ⟨4055501993829066022148185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5407335991772088029530913 4055501993829066022148185)
      ·
        refine ⟨3041626495371799516611139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4055501993829066022148185 3041626495371799516611139)
        ·
          refine ⟨4562439743057699274916709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041626495371799516611139 4562439743057699274916709)
          ·
            refine ⟨855457451823318614046883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4562439743057699274916709 855457451823318614046883)
            ·
              refine ⟨1283186177734977921070325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855457451823318614046883 1283186177734977921070325)
              ·
                refine ⟨120298704162654180100343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1283186177734977921070325 120298704162654180100343)
                ·
                  rfl

theorem cell19_395349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_395349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395349 prefixEnd_395349 := by exact prefixLift 395349
  have htrace : WordTrace (prefixWord ++ tailWord_395349) baseStart_395349 baseEnd_395349 := by
    simpa [prefixWord, tailWord_395349, baseEnd_395349] using wordTrace_append hprefix tailTrace_395349
  have hstable : (prefixWord ++ tailWord_395349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395349).length < 2 ^ (prefixWord ++ tailWord_395349).sum := by decide
  have hdescent : baseEnd_395349 < baseStart_395349 := by decide
  rcases family_descends (prefixWord ++ tailWord_395349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395408 : List Nat := [2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_395408 : Nat := 118140960795 + 395408 * 2 ^ 59
def prefixEnd_395408 : Nat := 4983230072969 + 3 ^ 40 * 395408 * 2
def baseEnd_395408 : Nat := 120316656967759524789071

theorem tailTrace_395408 : CollatzResearch.WordTrace tailWord_395408 prefixEnd_395408 120316656967759524789071 := by
  unfold tailWord_395408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7210857275755910577573439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9614476367674547436764585 7210857275755910577573439)
  ·
    refine ⟨10816285913633865866360159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7210857275755910577573439 10816285913633865866360159)
    ·
      refine ⟨16224428870450798799540239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10816285913633865866360159 16224428870450798799540239)
      ·
        refine ⟨24336643305676198199310359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16224428870450798799540239 24336643305676198199310359)
        ·
          refine ⟨36504964958514297298965539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24336643305676198199310359 36504964958514297298965539)
          ·
            refine ⟨54757447437771445948448309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36504964958514297298965539 54757447437771445948448309)
            ·
              refine ⟨5133510697291073057667029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54757447437771445948448309 5133510697291073057667029)
              ·
                refine ⟨120316656967759524789071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5133510697291073057667029 120316656967759524789071)
                ·
                  rfl

theorem cell19_395408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_395408 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395408 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395408 prefixEnd_395408 := by exact prefixLift 395408
  have htrace : WordTrace (prefixWord ++ tailWord_395408) baseStart_395408 baseEnd_395408 := by
    simpa [prefixWord, tailWord_395408, baseEnd_395408] using wordTrace_append hprefix tailTrace_395408
  have hstable : (prefixWord ++ tailWord_395408).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395408).length < 2 ^ (prefixWord ++ tailWord_395408).sum := by decide
  have hdescent : baseEnd_395408 < baseStart_395408 := by decide
  rcases family_descends (prefixWord ++ tailWord_395408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395438 : List Nat := [4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_395438 : Nat := 118140960795 + 395438 * 2 ^ 59
def prefixEnd_395438 : Nat := 4983230072969 + 3 ^ 40 * 395438 * 2
def baseEnd_395438 : Nat := 120325785512728344122323

theorem tailTrace_395438 : CollatzResearch.WordTrace tailWord_395438 prefixEnd_395438 120325785512728344122323 := by
  unfold tailWord_395438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802851092675392034842371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9615205827602090852492645 1802851092675392034842371)
  ·
    refine ⟨2704276639013088052263557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802851092675392034842371 2704276639013088052263557)
    ·
      refine ⟨507051869814954009799417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2704276639013088052263557 507051869814954009799417)
      ·
        refine ⟨380288902361215507349563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507051869814954009799417 380288902361215507349563)
        ·
          refine ⟨570433353541823261024345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380288902361215507349563 570433353541823261024345)
          ·
            refine ⟨427825015156367445768259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570433353541823261024345 427825015156367445768259)
            ·
              refine ⟨641737522734551168652389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427825015156367445768259 641737522734551168652389)
              ·
                refine ⟨120325785512728344122323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 641737522734551168652389 120325785512728344122323)
                ·
                  rfl

theorem cell19_395438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_395438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395438 prefixEnd_395438 := by exact prefixLift 395438
  have htrace : WordTrace (prefixWord ++ tailWord_395438) baseStart_395438 baseEnd_395438 := by
    simpa [prefixWord, tailWord_395438, baseEnd_395438] using wordTrace_append hprefix tailTrace_395438
  have hstable : (prefixWord ++ tailWord_395438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395438).length < 2 ^ (prefixWord ++ tailWord_395438).sum := by decide
  have hdescent : baseEnd_395438 < baseStart_395438 := by decide
  rcases family_descends (prefixWord ++ tailWord_395438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395520 : List Nat := [2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_395520 : Nat := 118140960795 + 395520 * 2 ^ 59
def prefixEnd_395520 : Nat := 4983230072969 + 3 ^ 40 * 395520 * 2
def baseEnd_395520 : Nat := 120350736868976450299877

theorem tailTrace_395520 : CollatzResearch.WordTrace tailWord_395520 prefixEnd_395520 120350736868976450299877 := by
  unfold tailWord_395520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212899763553032141612007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9617199684737376188816009 7212899763553032141612007)
  ·
    refine ⟨10819349645329548212418011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7212899763553032141612007 10819349645329548212418011)
    ·
      refine ⟨16229024467994322318627017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10819349645329548212418011 16229024467994322318627017)
      ·
        refine ⟨12171768350995741738970263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16229024467994322318627017 12171768350995741738970263)
        ·
          refine ⟨18257652526493612608455395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12171768350995741738970263 18257652526493612608455395)
          ·
            refine ⟨27386478789740418912683093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18257652526493612608455395 27386478789740418912683093)
            ·
              refine ⟨320935298317270534133005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 27386478789740418912683093 320935298317270534133005)
              ·
                refine ⟨120350736868976450299877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320935298317270534133005 120350736868976450299877)
                ·
                  rfl

theorem cell19_395520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_395520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395520 prefixEnd_395520 := by exact prefixLift 395520
  have htrace : WordTrace (prefixWord ++ tailWord_395520) baseStart_395520 baseEnd_395520 := by
    simpa [prefixWord, tailWord_395520, baseEnd_395520] using wordTrace_append hprefix tailTrace_395520
  have hstable : (prefixWord ++ tailWord_395520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395520).length < 2 ^ (prefixWord ++ tailWord_395520).sum := by decide
  have hdescent : baseEnd_395520 < baseStart_395520 := by decide
  rcases family_descends (prefixWord ++ tailWord_395520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395541 : List Nat := [1, 3, 2, 1, 2, 1, 9]
def baseStart_395541 : Nat := 118140960795 + 395541 * 2 ^ 59
def prefixEnd_395541 : Nat := 4983230072969 + 3 ^ 40 * 395541 * 2
def baseEnd_395541 : Nat := 40119042283484874611051

theorem tailTrace_395541 : CollatzResearch.WordTrace tailWord_395541 prefixEnd_395541 40119042283484874611051 := by
  unfold tailWord_395541
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426565460029984869738477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9617710306686656579825651 14426565460029984869738477)
  ·
    refine ⟨5409962047511244326151929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14426565460029984869738477 5409962047511244326151929)
    ·
      refine ⟨4057471535633433244613947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409962047511244326151929 4057471535633433244613947)
      ·
        refine ⟨6086207303450149866920921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057471535633433244613947 6086207303450149866920921)
        ·
          refine ⟨4564655477587612400190691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6086207303450149866920921 4564655477587612400190691)
          ·
            refine ⟨6846983216381418600286037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564655477587612400190691 6846983216381418600286037)
            ·
              refine ⟨40119042283484874611051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6846983216381418600286037 40119042283484874611051)
              ·
                rfl

theorem cell19_395541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_395541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395541 prefixEnd_395541 := by exact prefixLift 395541
  have htrace : WordTrace (prefixWord ++ tailWord_395541) baseStart_395541 baseEnd_395541 := by
    simpa [prefixWord, tailWord_395541, baseEnd_395541] using wordTrace_append hprefix tailTrace_395541
  have hstable : (prefixWord ++ tailWord_395541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395541).length < 2 ^ (prefixWord ++ tailWord_395541).sum := by decide
  have hdescent : baseEnd_395541 < baseStart_395541 := by decide
  rcases family_descends (prefixWord ++ tailWord_395541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395577 : List Nat := [1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_395577 : Nat := 118140960795 + 395577 * 2 ^ 59
def prefixEnd_395577 : Nat := 4983230072969 + 3 ^ 40 * 395577 * 2
def baseEnd_395577 : Nat := 120368081104417207033055

theorem tailTrace_395577 : CollatzResearch.WordTrace tailWord_395577 prefixEnd_395577 120368081104417207033055 := by
  unfold tailWord_395577
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427878487899563018048985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9618585658599708678699323 14427878487899563018048985)
  ·
    refine ⟨10820908865924672263536739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14427878487899563018048985 10820908865924672263536739)
    ·
      refine ⟨16231363298887008395305109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10820908865924672263536739 16231363298887008395305109)
      ·
        refine ⟨760845154635328518529927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16231363298887008395305109 760845154635328518529927)
        ·
          refine ⟨1141267731952992777794891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760845154635328518529927 1141267731952992777794891)
          ·
            refine ⟨1711901597929489166692337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141267731952992777794891 1711901597929489166692337)
            ·
              refine ⟨1283926198447116875019253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711901597929489166692337 1283926198447116875019253)
              ·
                refine ⟨120368081104417207033055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1283926198447116875019253 120368081104417207033055)
                ·
                  rfl

theorem cell19_395577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_395577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395577 prefixEnd_395577 := by exact prefixLift 395577
  have htrace : WordTrace (prefixWord ++ tailWord_395577) baseStart_395577 baseEnd_395577 := by
    simpa [prefixWord, tailWord_395577, baseEnd_395577] using wordTrace_append hprefix tailTrace_395577
  have hstable : (prefixWord ++ tailWord_395577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395577).length < 2 ^ (prefixWord ++ tailWord_395577).sum := by decide
  have hdescent : baseEnd_395577 < baseStart_395577 := by decide
  rcases family_descends (prefixWord ++ tailWord_395577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395655 : List Nat := [1, 1, 4, 2, 2, 1, 8]
def baseStart_395655 : Nat := 118140960795 + 395655 * 2 ^ 59
def prefixEnd_395655 : Nat := 4983230072969 + 3 ^ 40 * 395655 * 2
def baseEnd_395655 : Nat := 40130605107112045766503

theorem tailTrace_395655 : CollatzResearch.WordTrace tailWord_395655 prefixEnd_395655 40130605107112045766503 := by
  unfold tailWord_395655
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430723381616982339388419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9620482254411321559592279 14430723381616982339388419)
  ·
    refine ⟨21646085072425473509082629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14430723381616982339388419 21646085072425473509082629)
    ·
      refine ⟨4058640951079776282952993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21646085072425473509082629 4058640951079776282952993)
      ·
        refine ⟨3043980713309832212214745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4058640951079776282952993 3043980713309832212214745)
        ·
          refine ⟨2282985534982374159161059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043980713309832212214745 2282985534982374159161059)
          ·
            refine ⟨3424478302473561238741589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282985534982374159161059 3424478302473561238741589)
            ·
              refine ⟨40130605107112045766503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3424478302473561238741589 40130605107112045766503)
              ·
                rfl

theorem cell19_395655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_395655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395655 prefixEnd_395655 := by exact prefixLift 395655
  have htrace : WordTrace (prefixWord ++ tailWord_395655) baseStart_395655 baseEnd_395655 := by
    simpa [prefixWord, tailWord_395655, baseEnd_395655] using wordTrace_append hprefix tailTrace_395655
  have hstable : (prefixWord ++ tailWord_395655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395655).length < 2 ^ (prefixWord ++ tailWord_395655).sum := by decide
  have hdescent : baseEnd_395655 < baseStart_395655 := by decide
  rcases family_descends (prefixWord ++ tailWord_395655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395765 : List Nat := [1, 3, 5, 1, 3, 6]
def baseStart_395765 : Nat := 118140960795 + 395765 * 2 ^ 59
def prefixEnd_395765 : Nat := 4983230072969 + 3 ^ 40 * 395765 * 2
def baseEnd_395765 : Nat := 13380587405876497206085

theorem tailTrace_395765 : CollatzResearch.WordTrace tailWord_395765 prefixEnd_395765 13380587405876497206085 := by
  unfold tailWord_395765
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434735411218471125892749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9623156940812314083928499 14434735411218471125892749)
  ·
    refine ⟨5413025779206926672209781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14434735411218471125892749 5413025779206926672209781)
    ·
      refine ⟨507471166800649375519667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5413025779206926672209781 507471166800649375519667)
      ·
        refine ⟨761206750200974063279501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507471166800649375519667 761206750200974063279501)
        ·
          refine ⟨285452531325365273729813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 761206750200974063279501 285452531325365273729813)
          ·
            refine ⟨13380587405876497206085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285452531325365273729813 13380587405876497206085)
            ·
              rfl

theorem cell19_395765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_395765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395765 prefixEnd_395765 := by exact prefixLift 395765
  have htrace : WordTrace (prefixWord ++ tailWord_395765) baseStart_395765 baseEnd_395765 := by
    simpa [prefixWord, tailWord_395765, baseEnd_395765] using wordTrace_append hprefix tailTrace_395765
  have hstable : (prefixWord ++ tailWord_395765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395765).length < 2 ^ (prefixWord ++ tailWord_395765).sum := by decide
  have hdescent : baseEnd_395765 < baseStart_395765 := by decide
  rcases family_descends (prefixWord ++ tailWord_395765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395860 : List Nat := [2, 4, 1, 1, 1, 5, 2, 3]
def baseStart_395860 : Nat := 118140960795 + 395860 * 2 ^ 59
def prefixEnd_395860 : Nat := 4983230072969 + 3 ^ 40 * 395860 * 2
def baseEnd_395860 : Nat := 120454193711956402743395

theorem tailTrace_395860 : CollatzResearch.WordTrace tailWord_395860 prefixEnd_395860 120454193711956402743395 := by
  unfold tailWord_395860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219100172937151175300517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9625466897249534900400689 7219100172937151175300517)
  ·
    refine ⟨1353581282425715845368847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7219100172937151175300517 1353581282425715845368847)
    ·
      refine ⟨2030371923638573768053271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1353581282425715845368847 2030371923638573768053271)
      ·
        refine ⟨3045557885457860652079907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030371923638573768053271 3045557885457860652079907)
        ·
          refine ⟨4568336828186790978119861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045557885457860652079907 4568336828186790978119861)
          ·
            refine ⟨428281577642511654198737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4568336828186790978119861 428281577642511654198737)
            ·
              refine ⟨321211183231883740649053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428281577642511654198737 321211183231883740649053)
              ·
                refine ⟨120454193711956402743395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321211183231883740649053 120454193711956402743395)
                ·
                  rfl

theorem cell19_395860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_395860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395860 prefixEnd_395860 := by exact prefixLift 395860
  have htrace : WordTrace (prefixWord ++ tailWord_395860) baseStart_395860 baseEnd_395860 := by
    simpa [prefixWord, tailWord_395860, baseEnd_395860] using wordTrace_append hprefix tailTrace_395860
  have hstable : (prefixWord ++ tailWord_395860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395860).length < 2 ^ (prefixWord ++ tailWord_395860).sum := by decide
  have hdescent : baseEnd_395860 < baseStart_395860 := by decide
  rcases family_descends (prefixWord ++ tailWord_395860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395953 : List Nat := [1, 2, 2, 6, 2, 1, 1, 4]
def baseStart_395953 : Nat := 118140960795 + 395953 * 2 ^ 59
def prefixEnd_395953 : Nat := 4983230072969 + 3 ^ 40 * 395953 * 2
def baseEnd_395953 : Nat := 120482492201359742676475

theorem tailTrace_395953 : CollatzResearch.WordTrace tailWord_395953 prefixEnd_395953 120482492201359742676475 := by
  unfold tailWord_395953
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441592334537379233736513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9627728223024919489157675 14441592334537379233736513)
  ·
    refine ⟨10831194250903034425302385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14441592334537379233736513 10831194250903034425302385)
    ·
      refine ⟨8123395688177275818976789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10831194250903034425302385 8123395688177275818976789)
      ·
        refine ⟨380784172883309804014537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8123395688177275818976789 380784172883309804014537)
        ·
          refine ⟨285588129662482353010903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380784172883309804014537 285588129662482353010903)
          ·
            refine ⟨428382194493723529516355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285588129662482353010903 428382194493723529516355)
            ·
              refine ⟨642573291740585294274533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428382194493723529516355 642573291740585294274533)
              ·
                refine ⟨120482492201359742676475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642573291740585294274533 120482492201359742676475)
                ·
                  rfl

theorem cell19_395953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_395953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395953 prefixEnd_395953 := by exact prefixLift 395953
  have htrace : WordTrace (prefixWord ++ tailWord_395953) baseStart_395953 baseEnd_395953 := by
    simpa [prefixWord, tailWord_395953, baseEnd_395953] using wordTrace_append hprefix tailTrace_395953
  have hstable : (prefixWord ++ tailWord_395953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395953).length < 2 ^ (prefixWord ++ tailWord_395953).sum := by decide
  have hdescent : baseEnd_395953 < baseStart_395953 := by decide
  rcases family_descends (prefixWord ++ tailWord_395953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395957 : List Nat := [1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_395957 : Nat := 118140960795 + 395957 * 2 ^ 59
def prefixEnd_395957 : Nat := 4983230072969 + 3 ^ 40 * 395957 * 2
def baseEnd_395957 : Nat := 120483709340688918587575

theorem tailTrace_395957 : CollatzResearch.WordTrace tailWord_395957 prefixEnd_395957 120483709340688918587575 := by
  unfold tailWord_395957
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441738226522887916882125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9627825484348591944588083 14441738226522887916882125)
  ·
    refine ⟨5415651834946082968830797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14441738226522887916882125 5415651834946082968830797)
    ·
      refine ⟨2030869438104781113311549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5415651834946082968830797 2030869438104781113311549)
      ·
        refine ⟨761576039289292917491831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2030869438104781113311549 761576039289292917491831)
        ·
          refine ⟨1142364058933939376237747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761576039289292917491831 1142364058933939376237747)
          ·
            refine ⟨1713546088400909064356621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142364058933939376237747 1713546088400909064356621)
            ·
              refine ⟨642579783150340899133733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1713546088400909064356621 642579783150340899133733)
              ·
                refine ⟨120483709340688918587575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642579783150340899133733 120483709340688918587575)
                ·
                  rfl

theorem cell19_395957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_395957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395957 prefixEnd_395957 := by exact prefixLift 395957
  have htrace : WordTrace (prefixWord ++ tailWord_395957) baseStart_395957 baseEnd_395957 := by
    simpa [prefixWord, tailWord_395957, baseEnd_395957] using wordTrace_append hprefix tailTrace_395957
  have hstable : (prefixWord ++ tailWord_395957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395957).length < 2 ^ (prefixWord ++ tailWord_395957).sum := by decide
  have hdescent : baseEnd_395957 < baseStart_395957 := by decide
  rcases family_descends (prefixWord ++ tailWord_395957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395976 : List Nat := [2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_395976 : Nat := 118140960795 + 395976 * 2 ^ 59
def prefixEnd_395976 : Nat := 4983230072969 + 3 ^ 40 * 395976 * 2
def baseEnd_395976 : Nat := 120489490752502504165301

theorem tailTrace_395976 : CollatzResearch.WordTrace tailWord_395976 prefixEnd_395976 120489490752502504165301 := by
  unfold tailWord_395976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7221215606727027080911891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9628287475636036107882521 7221215606727027080911891)
  ·
    refine ⟨10831823410090540621367837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7221215606727027080911891 10831823410090540621367837)
    ·
      refine ⟨4061933778783952733012939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10831823410090540621367837 4061933778783952733012939)
      ·
        refine ⟨6092900668175929099519409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061933778783952733012939 6092900668175929099519409)
        ·
          refine ⟨4569675501131946824639557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6092900668175929099519409 4569675501131946824639557)
          ·
            refine ⟨856814156462240029619917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4569675501131946824639557 856814156462240029619917)
            ·
              refine ⟨321305308673340011107469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856814156462240029619917 321305308673340011107469)
              ·
                refine ⟨120489490752502504165301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321305308673340011107469 120489490752502504165301)
                ·
                  rfl

theorem cell19_395976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_395976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_395976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_395976 prefixEnd_395976 := by exact prefixLift 395976
  have htrace : WordTrace (prefixWord ++ tailWord_395976) baseStart_395976 baseEnd_395976 := by
    simpa [prefixWord, tailWord_395976, baseEnd_395976] using wordTrace_append hprefix tailTrace_395976
  have hstable : (prefixWord ++ tailWord_395976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395976).length < 2 ^ (prefixWord ++ tailWord_395976).sum := by decide
  have hdescent : baseEnd_395976 < baseStart_395976 := by decide
  rcases family_descends (prefixWord ++ tailWord_395976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396050 : List Nat := [3, 2, 4, 1, 2, 2, 5]
def baseStart_396050 : Nat := 118140960795 + 396050 * 2 ^ 59
def prefixEnd_396050 : Nat := 4983230072969 + 3 ^ 40 * 396050 * 2
def baseEnd_396050 : Nat := 40170669276697419506885

theorem tailTrace_396050 : CollatzResearch.WordTrace tailWord_396050 prefixEnd_396050 40170669276697419506885 := by
  unfold tailWord_396050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611282553796491200004401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9630086810123976533345069 3611282553796491200004401)
  ·
    refine ⟨2708461915347368400003301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3611282553796491200004401 2708461915347368400003301)
    ·
      refine ⟨507836609127631575000619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2708461915347368400003301 507836609127631575000619)
      ·
        refine ⟨761754913691447362500929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507836609127631575000619 761754913691447362500929)
        ·
          refine ⟨571316185268585521875697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761754913691447362500929 571316185268585521875697)
          ·
            refine ⟨428487138951439141406773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571316185268585521875697 428487138951439141406773)
            ·
              refine ⟨40170669276697419506885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 428487138951439141406773 40170669276697419506885)
              ·
                rfl

theorem cell19_396050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_396050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396050 prefixEnd_396050 := by exact prefixLift 396050
  have htrace : WordTrace (prefixWord ++ tailWord_396050) baseStart_396050 baseEnd_396050 := by
    simpa [prefixWord, tailWord_396050, baseEnd_396050] using wordTrace_append hprefix tailTrace_396050
  have hstable : (prefixWord ++ tailWord_396050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396050).length < 2 ^ (prefixWord ++ tailWord_396050).sum := by decide
  have hdescent : baseEnd_396050 < baseStart_396050 := by decide
  rcases family_descends (prefixWord ++ tailWord_396050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396075 : List Nat := [1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_396075 : Nat := 118140960795 + 396075 * 2 ^ 59
def prefixEnd_396075 : Nat := 4983230072969 + 3 ^ 40 * 396075 * 2
def baseEnd_396075 : Nat := 120519614950899607965031

theorem tailTrace_396075 : CollatzResearch.WordTrace tailWord_396075 prefixEnd_396075 120519614950899607965031 := by
  unfold tailWord_396075
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446042040095394069677679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9630694693396929379785119 14446042040095394069677679)
  ·
    refine ⟨21669063060143091104516519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14446042040095394069677679 21669063060143091104516519)
    ·
      refine ⟨32503594590214636656774779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21669063060143091104516519 32503594590214636656774779)
      ·
        refine ⟨48755391885321954985162169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32503594590214636656774779 48755391885321954985162169)
        ·
          refine ⟨36566543913991466238871627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48755391885321954985162169 36566543913991466238871627)
          ·
            refine ⟨54849815870987199358307441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36566543913991466238871627 54849815870987199358307441)
            ·
              refine ⟨41137361903240399518730581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54849815870987199358307441 41137361903240399518730581)
              ·
                refine ⟨120519614950899607965031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41137361903240399518730581 120519614950899607965031)
                ·
                  rfl

theorem cell19_396075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_396075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396075 prefixEnd_396075 := by exact prefixLift 396075
  have htrace : WordTrace (prefixWord ++ tailWord_396075) baseStart_396075 baseEnd_396075 := by
    simpa [prefixWord, tailWord_396075, baseEnd_396075] using wordTrace_append hprefix tailTrace_396075
  have hstable : (prefixWord ++ tailWord_396075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396075).length < 2 ^ (prefixWord ++ tailWord_396075).sum := by decide
  have hdescent : baseEnd_396075 < baseStart_396075 := by decide
  rcases family_descends (prefixWord ++ tailWord_396075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396109 : List Nat := [1, 6, 1, 2, 2, 7]
def baseStart_396109 : Nat := 118140960795 + 396109 * 2 ^ 59
def prefixEnd_396109 : Nat := 4983230072969 + 3 ^ 40 * 396109 * 2
def baseEnd_396109 : Nat := 13392217848355289245487

theorem tailTrace_396109 : CollatzResearch.WordTrace tailWord_396109 prefixEnd_396109 13392217848355289245487 := by
  unfold tailWord_396109
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447282121972217876415381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9631521414648145250943587 14447282121972217876415381)
  ·
    refine ⟨677216349467447712956971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14447282121972217876415381 677216349467447712956971)
    ·
      refine ⟨1015824524201171569435457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677216349467447712956971 1015824524201171569435457)
      ·
        refine ⟨761868393150878677076593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1015824524201171569435457 761868393150878677076593)
        ·
          refine ⟨571401294863159007807445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761868393150878677076593 571401294863159007807445)
          ·
            refine ⟨13392217848355289245487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 571401294863159007807445 13392217848355289245487)
            ·
              rfl

theorem cell19_396109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_396109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396109 prefixEnd_396109 := by exact prefixLift 396109
  have htrace : WordTrace (prefixWord ++ tailWord_396109) baseStart_396109 baseEnd_396109 := by
    simpa [prefixWord, tailWord_396109, baseEnd_396109] using wordTrace_append hprefix tailTrace_396109
  have hstable : (prefixWord ++ tailWord_396109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396109).length < 2 ^ (prefixWord ++ tailWord_396109).sum := by decide
  have hdescent : baseEnd_396109 < baseStart_396109 := by decide
  rcases family_descends (prefixWord ++ tailWord_396109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396113 : List Nat := [1, 2, 2, 1, 13]
def baseStart_396113 : Nat := 118140960795 + 396113 * 2 ^ 59
def prefixEnd_396113 : Nat := 4983230072969 + 3 ^ 40 * 396113 * 2
def baseEnd_396113 : Nat := 4464117695352843671129

theorem tailTrace_396113 : CollatzResearch.WordTrace tailWord_396113 prefixEnd_396113 4464117695352843671129 := by
  unfold tailWord_396113
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447428013957726559560993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9631618675971817706373995 14447428013957726559560993)
  ·
    refine ⟨10835571010468294919670745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14447428013957726559560993 10835571010468294919670745)
    ·
      refine ⟨8126678257851221189753059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10835571010468294919670745 8126678257851221189753059)
      ·
        refine ⟨12190017386776831784629589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126678257851221189753059 12190017386776831784629589)
        ·
          refine ⟨4464117695352843671129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12190017386776831784629589 4464117695352843671129)
          ·
            rfl

theorem cell19_396113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 13].length) (baseStart_396113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396113 prefixEnd_396113 := by exact prefixLift 396113
  have htrace : WordTrace (prefixWord ++ tailWord_396113) baseStart_396113 baseEnd_396113 := by
    simpa [prefixWord, tailWord_396113, baseEnd_396113] using wordTrace_append hprefix tailTrace_396113
  have hstable : (prefixWord ++ tailWord_396113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396113).length < 2 ^ (prefixWord ++ tailWord_396113).sum := by decide
  have hdescent : baseEnd_396113 < baseStart_396113 := by decide
  rcases family_descends (prefixWord ++ tailWord_396113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396151 : List Nat := [1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_396151 : Nat := 118140960795 + 396151 * 2 ^ 59
def prefixEnd_396151 : Nat := 4983230072969 + 3 ^ 40 * 396151 * 2
def baseEnd_396151 : Nat := 120542740598153950275935

theorem tailTrace_396151 : CollatzResearch.WordTrace tailWord_396151 prefixEnd_396151 120542740598153950275935 := by
  unfold tailWord_396151
  simp only [CollatzResearch.WordTrace]
  refine ⟨14448813987820059049444307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9632542658546706032962871 14448813987820059049444307)
  ·
    refine ⟨21673220981730088574166461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14448813987820059049444307 21673220981730088574166461)
    ·
      refine ⟨8127457868148783215312423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21673220981730088574166461 8127457868148783215312423)
      ·
        refine ⟨12191186802223174822968635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8127457868148783215312423 12191186802223174822968635)
        ·
          refine ⟨18286780203334762234452953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12191186802223174822968635 18286780203334762234452953)
          ·
            refine ⟨13715085152501071675839715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18286780203334762234452953 13715085152501071675839715)
            ·
              refine ⟨20572627728751607513759573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13715085152501071675839715 20572627728751607513759573)
              ·
                refine ⟨120542740598153950275935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20572627728751607513759573 120542740598153950275935)
                ·
                  rfl

theorem cell19_396151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_396151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396151 prefixEnd_396151 := by exact prefixLift 396151
  have htrace : WordTrace (prefixWord ++ tailWord_396151) baseStart_396151 baseEnd_396151 := by
    simpa [prefixWord, tailWord_396151, baseEnd_396151] using wordTrace_append hprefix tailTrace_396151
  have hstable : (prefixWord ++ tailWord_396151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396151).length < 2 ^ (prefixWord ++ tailWord_396151).sum := by decide
  have hdescent : baseEnd_396151 < baseStart_396151 := by decide
  rcases family_descends (prefixWord ++ tailWord_396151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396168 : List Nat := [2, 1, 3, 3, 2, 2, 6]
def baseStart_396168 : Nat := 118140960795 + 396168 * 2 ^ 59
def prefixEnd_396168 : Nat := 4983230072969 + 3 ^ 40 * 396168 * 2
def baseEnd_396168 : Nat := 40182637813434315966037

theorem tailTrace_396168 : CollatzResearch.WordTrace tailWord_396168 prefixEnd_396168 40182637813434315966037 := by
  unfold tailWord_396168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224717014379235476406579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9632956019172313968542105 7224717014379235476406579)
  ·
    refine ⟨10837075521568853214609869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7224717014379235476406579 10837075521568853214609869)
    ·
      refine ⟨4063903320588319955478701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10837075521568853214609869 4063903320588319955478701)
      ·
        refine ⟨1523963745220619983304513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4063903320588319955478701 1523963745220619983304513)
        ·
          refine ⟨1142972808915464987478385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523963745220619983304513 1142972808915464987478385)
          ·
            refine ⟨857229606686598740608789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142972808915464987478385 857229606686598740608789)
            ·
              refine ⟨40182637813434315966037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 857229606686598740608789 40182637813434315966037)
              ·
                rfl

theorem cell19_396168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_396168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396168 prefixEnd_396168 := by exact prefixLift 396168
  have htrace : WordTrace (prefixWord ++ tailWord_396168) baseStart_396168 baseEnd_396168 := by
    simpa [prefixWord, tailWord_396168, baseEnd_396168] using wordTrace_append hprefix tailTrace_396168
  have hstable : (prefixWord ++ tailWord_396168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396168).length < 2 ^ (prefixWord ++ tailWord_396168).sum := by decide
  have hdescent : baseEnd_396168 < baseStart_396168 := by decide
  rcases family_descends (prefixWord ++ tailWord_396168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396242 : List Nat := [3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_396242 : Nat := 118140960795 + 396242 * 2 ^ 59
def prefixEnd_396242 : Nat := 4983230072969 + 3 ^ 40 * 396242 * 2
def baseEnd_396242 : Nat := 120570430517892702253465

theorem tailTrace_396242 : CollatzResearch.WordTrace tailWord_396242 prefixEnd_396242 120570430517892702253465 := by
  unfold tailWord_396242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613033257622595397751745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9634755353660254394004653 3613033257622595397751745)
  ·
    refine ⟨2709774943216946548313809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3613033257622595397751745 2709774943216946548313809)
    ·
      refine ⟨2032331207412709911235357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2709774943216946548313809 2032331207412709911235357)
      ·
        refine ⟨762124202779766216713259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2032331207412709911235357 762124202779766216713259)
        ·
          refine ⟨1143186304169649325069889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762124202779766216713259 1143186304169649325069889)
          ·
            refine ⟨857389728127236993802417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143186304169649325069889 857389728127236993802417)
            ·
              refine ⟨643042296095427745351813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857389728127236993802417 643042296095427745351813)
              ·
                refine ⟨120570430517892702253465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643042296095427745351813 120570430517892702253465)
                ·
                  rfl

theorem cell19_396242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_396242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396242 prefixEnd_396242 := by exact prefixLift 396242
  have htrace : WordTrace (prefixWord ++ tailWord_396242) baseStart_396242 baseEnd_396242 := by
    simpa [prefixWord, tailWord_396242, baseEnd_396242] using wordTrace_append hprefix tailTrace_396242
  have hstable : (prefixWord ++ tailWord_396242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396242).length < 2 ^ (prefixWord ++ tailWord_396242).sum := by decide
  have hdescent : baseEnd_396242 < baseStart_396242 := by decide
  rcases family_descends (prefixWord ++ tailWord_396242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396244 : List Nat := [2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_396244 : Nat := 118140960795 + 396244 * 2 ^ 59
def prefixEnd_396244 : Nat := 4983230072969 + 3 ^ 40 * 396244 * 2
def baseEnd_396244 : Nat := 120571039087557290209015

theorem tailTrace_396244 : CollatzResearch.WordTrace tailWord_396244 prefixEnd_396244 120571039087557290209015 := by
  unfold tailWord_396244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226102988241567966289893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9634803984322090621719857 7226102988241567966289893)
  ·
    refine ⟨1354894310295293993679355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7226102988241567966289893 1354894310295293993679355)
    ·
      refine ⟨2032341465442940990519033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354894310295293993679355 2032341465442940990519033)
      ·
        refine ⟨1524256099082205742889275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032341465442940990519033 1524256099082205742889275)
        ·
          refine ⟨2286384148623308614333913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524256099082205742889275 2286384148623308614333913)
          ·
            refine ⟨1714788111467481460750435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286384148623308614333913 1714788111467481460750435)
            ·
              refine ⟨2572182167201222191125653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714788111467481460750435 2572182167201222191125653)
              ·
                refine ⟨120571039087557290209015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2572182167201222191125653 120571039087557290209015)
                ·
                  rfl

theorem cell19_396244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_396244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396244 prefixEnd_396244 := by exact prefixLift 396244
  have htrace : WordTrace (prefixWord ++ tailWord_396244) baseStart_396244 baseEnd_396244 := by
    simpa [prefixWord, tailWord_396244, baseEnd_396244] using wordTrace_append hprefix tailTrace_396244
  have hstable : (prefixWord ++ tailWord_396244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396244).length < 2 ^ (prefixWord ++ tailWord_396244).sum := by decide
  have hdescent : baseEnd_396244 < baseStart_396244 := by decide
  rcases family_descends (prefixWord ++ tailWord_396244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396263 : List Nat := [1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_396263 : Nat := 118140960795 + 396263 * 2 ^ 59
def prefixEnd_396263 : Nat := 4983230072969 + 3 ^ 40 * 396263 * 2
def baseEnd_396263 : Nat := 120576820499370875786741

theorem tailTrace_396263 : CollatzResearch.WordTrace tailWord_396263 prefixEnd_396263 120576820499370875786741 := by
  unfold tailWord_396263
  simp only [CollatzResearch.WordTrace]
  refine ⟨14452898963414302177521443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9635265975609534785014295 14452898963414302177521443)
  ·
    refine ⟨21679348445121453266282165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14452898963414302177521443 21679348445121453266282165)
    ·
      refine ⟨2032438916730136243713953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21679348445121453266282165 2032438916730136243713953)
      ·
        refine ⟨1524329187547602182785465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032438916730136243713953 1524329187547602182785465)
        ·
          refine ⟨1143246890660701637089099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1524329187547602182785465 1143246890660701637089099)
          ·
            refine ⟨1714870335991052455633649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143246890660701637089099 1714870335991052455633649)
            ·
              refine ⟨1286152751993289341725237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714870335991052455633649 1286152751993289341725237)
              ·
                refine ⟨120576820499370875786741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1286152751993289341725237 120576820499370875786741)
                ·
                  rfl

theorem cell19_396263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_396263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396263 prefixEnd_396263 := by exact prefixLift 396263
  have htrace : WordTrace (prefixWord ++ tailWord_396263) baseStart_396263 baseEnd_396263 := by
    simpa [prefixWord, tailWord_396263, baseEnd_396263] using wordTrace_append hprefix tailTrace_396263
  have hstable : (prefixWord ++ tailWord_396263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396263).length < 2 ^ (prefixWord ++ tailWord_396263).sum := by decide
  have hdescent : baseEnd_396263 < baseStart_396263 := by decide
  rcases family_descends (prefixWord ++ tailWord_396263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396276 : List Nat := [2, 6, 2, 1, 1, 7]
def baseStart_396276 : Nat := 118140960795 + 396276 * 2 ^ 59
def prefixEnd_396276 : Nat := 4983230072969 + 3 ^ 40 * 396276 * 2
def baseEnd_396276 : Nat := 13397864022465633055313

theorem tailTrace_396276 : CollatzResearch.WordTrace tailWord_396276 prefixEnd_396276 13397864022465633055313 := by
  unfold tailWord_396276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226686556183602698872341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9635582074911470265163121 7226686556183602698872341)
  ·
    refine ⟨338750932321106376509641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7226686556183602698872341 338750932321106376509641)
    ·
      refine ⟨254063199240829782382231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338750932321106376509641 254063199240829782382231)
      ·
        refine ⟨381094798861244673573347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254063199240829782382231 381094798861244673573347)
        ·
          refine ⟨571642198291867010360021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381094798861244673573347 571642198291867010360021)
          ·
            refine ⟨13397864022465633055313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 571642198291867010360021 13397864022465633055313)
            ·
              rfl

theorem cell19_396276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_396276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396276 prefixEnd_396276 := by exact prefixLift 396276
  have htrace : WordTrace (prefixWord ++ tailWord_396276) baseStart_396276 baseEnd_396276 := by
    simpa [prefixWord, tailWord_396276, baseEnd_396276] using wordTrace_append hprefix tailTrace_396276
  have hstable : (prefixWord ++ tailWord_396276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396276).length < 2 ^ (prefixWord ++ tailWord_396276).sum := by decide
  have hdescent : baseEnd_396276 < baseStart_396276 := by decide
  rcases family_descends (prefixWord ++ tailWord_396276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396284 : List Nat := [2, 2, 2, 1, 2, 10]
def baseStart_396284 : Nat := 118140960795 + 396284 * 2 ^ 59
def prefixEnd_396284 : Nat := 4983230072969 + 3 ^ 40 * 396284 * 2
def baseEnd_396284 : Nat := 13398134497872116591113

theorem tailTrace_396284 : CollatzResearch.WordTrace tailWord_396284 prefixEnd_396284 13398134497872116591113 := by
  unfold tailWord_396284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226832448169111382017953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9635776597558815176023937 7226832448169111382017953)
  ·
    refine ⟨5420124336126833536513465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7226832448169111382017953 5420124336126833536513465)
    ·
      refine ⟨4065093252095125152385099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5420124336126833536513465 4065093252095125152385099)
      ·
        refine ⟨6097639878142687728577649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065093252095125152385099 6097639878142687728577649)
        ·
          refine ⟨4573229908607015796433237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097639878142687728577649 4573229908607015796433237)
          ·
            refine ⟨13398134497872116591113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4573229908607015796433237 13398134497872116591113)
            ·
              rfl

theorem cell19_396284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_396284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396284 prefixEnd_396284 := by exact prefixLift 396284
  have htrace : WordTrace (prefixWord ++ tailWord_396284) baseStart_396284 baseEnd_396284 := by
    simpa [prefixWord, tailWord_396284, baseEnd_396284] using wordTrace_append hprefix tailTrace_396284
  have hstable : (prefixWord ++ tailWord_396284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396284).length < 2 ^ (prefixWord ++ tailWord_396284).sum := by decide
  have hdescent : baseEnd_396284 < baseStart_396284 := by decide
  rcases family_descends (prefixWord ++ tailWord_396284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396360 : List Nat := [2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_396360 : Nat := 118140960795 + 396360 * 2 ^ 59
def prefixEnd_396360 : Nat := 4983230072969 + 3 ^ 40 * 396360 * 2
def baseEnd_396360 : Nat := 120606336128103391630921

theorem tailTrace_396360 : CollatzResearch.WordTrace tailWord_396360 prefixEnd_396360 120606336128103391630921 := by
  unfold tailWord_396360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228218422031443871901267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9637624562708591829201689 7228218422031443871901267)
  ·
    refine ⟨10842327633047165807851901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7228218422031443871901267 10842327633047165807851901)
    ·
      refine ⟨4065872862392687177944463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10842327633047165807851901 4065872862392687177944463)
      ·
        refine ⟨6098809293589030766916695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065872862392687177944463 6098809293589030766916695)
        ·
          refine ⟨9148213940383546150375043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098809293589030766916695 9148213940383546150375043)
          ·
            refine ⟨13722320910575319225562565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148213940383546150375043 13722320910575319225562565)
            ·
              refine ⟨2572935170732872354792981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13722320910575319225562565 2572935170732872354792981)
              ·
                refine ⟨120606336128103391630921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2572935170732872354792981 120606336128103391630921)
                ·
                  rfl

theorem cell19_396360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_396360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396360 prefixEnd_396360 := by exact prefixLift 396360
  have htrace : WordTrace (prefixWord ++ tailWord_396360) baseStart_396360 baseEnd_396360 := by
    simpa [prefixWord, tailWord_396360, baseEnd_396360] using wordTrace_append hprefix tailTrace_396360
  have hstable : (prefixWord ++ tailWord_396360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396360).length < 2 ^ (prefixWord ++ tailWord_396360).sum := by decide
  have hdescent : baseEnd_396360 < baseStart_396360 := by decide
  rcases family_descends (prefixWord ++ tailWord_396360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396392 : List Nat := [2, 1, 4, 4, 2, 1, 5]
def baseStart_396392 : Nat := 118140960795 + 396392 * 2 ^ 59
def prefixEnd_396392 : Nat := 4983230072969 + 3 ^ 40 * 396392 * 2
def baseEnd_396392 : Nat := 40205357747578932973241

theorem tailTrace_396392 : CollatzResearch.WordTrace tailWord_396392 prefixEnd_396392 40205357747578932973241 := by
  unfold tailWord_396392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228801989973478604483715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9638402653297971472644953 7228801989973478604483715)
  ·
    refine ⟨10843202984960217906725573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7228801989973478604483715 10843202984960217906725573)
    ·
      refine ⟨2033100559680040857511045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10843202984960217906725573 2033100559680040857511045)
      ·
        refine ⟨381206354940007660783321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2033100559680040857511045 381206354940007660783321)
        ·
          refine ⟨285904766205005745587491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381206354940007660783321 285904766205005745587491)
          ·
            refine ⟨428857149307508618381237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285904766205005745587491 428857149307508618381237)
            ·
              refine ⟨40205357747578932973241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 428857149307508618381237 40205357747578932973241)
              ·
                rfl

theorem cell19_396392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_396392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396392 prefixEnd_396392 := by exact prefixLift 396392
  have htrace : WordTrace (prefixWord ++ tailWord_396392) baseStart_396392 baseEnd_396392 := by
    simpa [prefixWord, tailWord_396392, baseEnd_396392] using wordTrace_append hprefix tailTrace_396392
  have hstable : (prefixWord ++ tailWord_396392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396392).length < 2 ^ (prefixWord ++ tailWord_396392).sum := by decide
  have hdescent : baseEnd_396392 < baseStart_396392 := by decide
  rcases family_descends (prefixWord ++ tailWord_396392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396434 : List Nat := [3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_396434 : Nat := 118140960795 + 396434 * 2 ^ 59
def prefixEnd_396434 : Nat := 4983230072969 + 3 ^ 40 * 396434 * 2
def baseEnd_396434 : Nat := 120628853205693145986275

theorem tailTrace_396434 : CollatzResearch.WordTrace tailWord_396434 prefixEnd_396434 120628853205693145986275 := by
  unfold tailWord_396434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3614783961448699595499089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9639423897196532254664237 3614783961448699595499089)
  ·
    refine ⟨2711087971086524696624317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3614783961448699595499089 2711087971086524696624317)
    ·
      refine ⟨1016657989157446761234119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2711087971086524696624317 1016657989157446761234119)
      ·
        refine ⟨1524986983736170141851179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016657989157446761234119 1524986983736170141851179)
        ·
          refine ⟨2287480475604255212776769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524986983736170141851179 2287480475604255212776769)
          ·
            refine ⟨1715610356703191409582577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287480475604255212776769 1715610356703191409582577)
            ·
              refine ⟨1286707767527393557186933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715610356703191409582577 1286707767527393557186933)
              ·
                refine ⟨120628853205693145986275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1286707767527393557186933 120628853205693145986275)
                ·
                  rfl

theorem cell19_396434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_396434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396434 prefixEnd_396434 := by exact prefixLift 396434
  have htrace : WordTrace (prefixWord ++ tailWord_396434) baseStart_396434 baseEnd_396434 := by
    simpa [prefixWord, tailWord_396434, baseEnd_396434] using wordTrace_append hprefix tailTrace_396434
  have hstable : (prefixWord ++ tailWord_396434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396434).length < 2 ^ (prefixWord ++ tailWord_396434).sum := by decide
  have hdescent : baseEnd_396434 < baseStart_396434 := by decide
  rcases family_descends (prefixWord ++ tailWord_396434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396512 : List Nat := [2, 1, 1, 3, 1, 5, 6]
def baseStart_396512 : Nat := 118140960795 + 396512 * 2 ^ 59
def prefixEnd_396512 : Nat := 4983230072969 + 3 ^ 40 * 396512 * 2
def baseEnd_396512 : Nat := 40217529140870692084243

theorem tailTrace_396512 : CollatzResearch.WordTrace tailWord_396512 prefixEnd_396512 40217529140870692084243 := by
  unfold tailWord_396512
  simp only [CollatzResearch.WordTrace]
  refine ⟨7230990369756108851667895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9641320493008145135557193 7230990369756108851667895)
  ·
    refine ⟨10846485554634163277501843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7230990369756108851667895 10846485554634163277501843)
    ·
      refine ⟨16269728331951244916252765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10846485554634163277501843 16269728331951244916252765)
      ·
        refine ⟨6101148124481716843594787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16269728331951244916252765 6101148124481716843594787)
        ·
          refine ⟨9151722186722575265392181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6101148124481716843594787 9151722186722575265392181)
          ·
            refine ⟨857973955005241431130517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9151722186722575265392181 857973955005241431130517)
            ·
              refine ⟨40217529140870692084243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 857973955005241431130517 40217529140870692084243)
              ·
                rfl

theorem cell19_396512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_396512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396512 prefixEnd_396512 := by exact prefixLift 396512
  have htrace : WordTrace (prefixWord ++ tailWord_396512) baseStart_396512 baseEnd_396512 := by
    simpa [prefixWord, tailWord_396512, baseEnd_396512] using wordTrace_append hprefix tailTrace_396512
  have hstable : (prefixWord ++ tailWord_396512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396512).length < 2 ^ (prefixWord ++ tailWord_396512).sum := by decide
  have hdescent : baseEnd_396512 < baseStart_396512 := by decide
  rcases family_descends (prefixWord ++ tailWord_396512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396546 : List Nat := [3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_396546 : Nat := 118140960795 + 396546 * 2 ^ 59
def prefixEnd_396546 : Nat := 4983230072969 + 3 ^ 40 * 396546 * 2
def baseEnd_396546 : Nat := 120662933106910071497081

theorem tailTrace_396546 : CollatzResearch.WordTrace tailWord_396546 prefixEnd_396546 120662933106910071497081 := by
  unfold tailWord_396546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615805205347260377518373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9642147214259361006715661 3615805205347260377518373)
  ·
    refine ⟨677963476002611320784695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3615805205347260377518373 677963476002611320784695)
    ·
      refine ⟨1016945214003916981177043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677963476002611320784695 1016945214003916981177043)
      ·
        refine ⟨1525417821005875471765565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016945214003916981177043 1525417821005875471765565)
        ·
          refine ⟨572031682877203301912087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1525417821005875471765565 572031682877203301912087)
          ·
            refine ⟨858047524315804952868131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572031682877203301912087 858047524315804952868131)
            ·
              refine ⟨1287071286473707429302197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858047524315804952868131 1287071286473707429302197)
              ·
                refine ⟨120662933106910071497081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1287071286473707429302197 120662933106910071497081)
                ·
                  rfl

theorem cell19_396546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_396546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396546 prefixEnd_396546 := by exact prefixLift 396546
  have htrace : WordTrace (prefixWord ++ tailWord_396546) baseStart_396546 baseEnd_396546 := by
    simpa [prefixWord, tailWord_396546, baseEnd_396546] using wordTrace_append hprefix tailTrace_396546
  have hstable : (prefixWord ++ tailWord_396546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396546).length < 2 ^ (prefixWord ++ tailWord_396546).sum := by decide
  have hdescent : baseEnd_396546 < baseStart_396546 := by decide
  rcases family_descends (prefixWord ++ tailWord_396546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396548 : List Nat := [2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_396548 : Nat := 118140960795 + 396548 * 2 ^ 59
def prefixEnd_396548 : Nat := 4983230072969 + 3 ^ 40 * 396548 * 2
def baseEnd_396548 : Nat := 120663541676574659452631

theorem tailTrace_396548 : CollatzResearch.WordTrace tailWord_396548 prefixEnd_396548 120663541676574659452631 := by
  unfold tailWord_396548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231646883690897925823149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9642195844921197234430865 7231646883690897925823149)
  ·
    refine ⟨2711867581384086722183681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7231646883690897925823149 2711867581384086722183681)
    ·
      refine ⟨2033900686038065041637761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2711867581384086722183681 2033900686038065041637761)
      ·
        refine ⟨1525425514528548781228321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033900686038065041637761 1525425514528548781228321)
        ·
          refine ⟨1144069135896411585921241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525425514528548781228321 1144069135896411585921241)
          ·
            refine ⟨858051851922308689440931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144069135896411585921241 858051851922308689440931)
            ·
              refine ⟨1287077777883463034161397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858051851922308689440931 1287077777883463034161397)
              ·
                refine ⟨120663541676574659452631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1287077777883463034161397 120663541676574659452631)
                ·
                  rfl

theorem cell19_396548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_396548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396548 prefixEnd_396548 := by exact prefixLift 396548
  have htrace : WordTrace (prefixWord ++ tailWord_396548) baseStart_396548 baseEnd_396548 := by
    simpa [prefixWord, tailWord_396548, baseEnd_396548] using wordTrace_append hprefix tailTrace_396548
  have hstable : (prefixWord ++ tailWord_396548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396548).length < 2 ^ (prefixWord ++ tailWord_396548).sum := by decide
  have hdescent : baseEnd_396548 < baseStart_396548 := by decide
  rcases family_descends (prefixWord ++ tailWord_396548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396586 : List Nat := [3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_396586 : Nat := 118140960795 + 396586 * 2 ^ 59
def prefixEnd_396586 : Nat := 4983230072969 + 3 ^ 40 * 396586 * 2
def baseEnd_396586 : Nat := 120675104500201830608083

theorem tailTrace_396586 : CollatzResearch.WordTrace tailWord_396586 prefixEnd_396586 120675104500201830608083 := by
  unfold tailWord_396586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616169935311032085382403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9643119827496085561019741 3616169935311032085382403)
  ·
    refine ⟨5424254902966548128073605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3616169935311032085382403 5424254902966548128073605)
    ·
      refine ⟨1017047794306227774013801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5424254902966548128073605 1017047794306227774013801)
      ·
        refine ⟨762785845729670830510351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017047794306227774013801 762785845729670830510351)
        ·
          refine ⟨1144178768594506245765527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762785845729670830510351 1144178768594506245765527)
          ·
            refine ⟨1716268152891759368648291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144178768594506245765527 1716268152891759368648291)
            ·
              refine ⟨2574402229337639052972437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716268152891759368648291 2574402229337639052972437)
              ·
                refine ⟨120675104500201830608083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2574402229337639052972437 120675104500201830608083)
                ·
                  rfl

theorem cell19_396586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_396586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396586 prefixEnd_396586 := by exact prefixLift 396586
  have htrace : WordTrace (prefixWord ++ tailWord_396586) baseStart_396586 baseEnd_396586 := by
    simpa [prefixWord, tailWord_396586, baseEnd_396586] using wordTrace_append hprefix tailTrace_396586
  have hstable : (prefixWord ++ tailWord_396586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396586).length < 2 ^ (prefixWord ++ tailWord_396586).sum := by decide
  have hdescent : baseEnd_396586 < baseStart_396586 := by decide
  rcases family_descends (prefixWord ++ tailWord_396586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396607 : List Nat := [1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_396607 : Nat := 118140960795 + 396607 * 2 ^ 59
def prefixEnd_396607 : Nat := 4983230072969 + 3 ^ 40 * 396607 * 2
def baseEnd_396607 : Nat := 120681494481680004141359

theorem tailTrace_396607 : CollatzResearch.WordTrace tailWord_396607 prefixEnd_396607 120681494481680004141359 := by
  unfold tailWord_396607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465445674168048928044075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9643630449445365952029383 14465445674168048928044075)
  ·
    refine ⟨21698168511252073392066113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14465445674168048928044075 21698168511252073392066113)
    ·
      refine ⟨16273626383439055044049585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21698168511252073392066113 16273626383439055044049585)
      ·
        refine ⟨12205219787579291283037189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16273626383439055044049585 12205219787579291283037189)
        ·
          refine ⟨2288478710171117115569473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12205219787579291283037189 2288478710171117115569473)
          ·
            refine ⟨1716359032628337836677105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2288478710171117115569473 1716359032628337836677105)
            ·
              refine ⟨1287269274471253377507829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716359032628337836677105 1287269274471253377507829)
              ·
                refine ⟨120681494481680004141359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1287269274471253377507829 120681494481680004141359)
                ·
                  rfl

theorem cell19_396607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_396607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396607 prefixEnd_396607 := by exact prefixLift 396607
  have htrace : WordTrace (prefixWord ++ tailWord_396607) baseStart_396607 baseEnd_396607 := by
    simpa [prefixWord, tailWord_396607, baseEnd_396607] using wordTrace_append hprefix tailTrace_396607
  have hstable : (prefixWord ++ tailWord_396607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396607).length < 2 ^ (prefixWord ++ tailWord_396607).sum := by decide
  have hdescent : baseEnd_396607 < baseStart_396607 := by decide
  rcases family_descends (prefixWord ++ tailWord_396607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396637 : List Nat := [1, 4, 5, 1, 1, 2, 1, 4]
def baseStart_396637 : Nat := 118140960795 + 396637 * 2 ^ 59
def prefixEnd_396637 : Nat := 4983230072969 + 3 ^ 40 * 396637 * 2
def baseEnd_396637 : Nat := 120690623026648823474611

theorem tailTrace_396637 : CollatzResearch.WordTrace tailWord_396637 prefixEnd_396637 120690623026648823474611 := by
  unfold tailWord_396637
  simp only [CollatzResearch.WordTrace]
  refine ⟨14466539864059364051636165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9644359909372909367757443 14466539864059364051636165)
  ·
    refine ⟨2712476224511130759681781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14466539864059364051636165 2712476224511130759681781)
    ·
      refine ⟨254294646047918508720167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2712476224511130759681781 254294646047918508720167)
      ·
        refine ⟨381441969071877763080251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254294646047918508720167 381441969071877763080251)
        ·
          refine ⟨572162953607816644620377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381441969071877763080251 572162953607816644620377)
          ·
            refine ⟨429122215205862483465283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572162953607816644620377 429122215205862483465283)
            ·
              refine ⟨643683322808793725197925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429122215205862483465283 643683322808793725197925)
              ·
                refine ⟨120690623026648823474611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643683322808793725197925 120690623026648823474611)
                ·
                  rfl

theorem cell19_396637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_396637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396637 prefixEnd_396637 := by exact prefixLift 396637
  have htrace : WordTrace (prefixWord ++ tailWord_396637) baseStart_396637 baseEnd_396637 := by
    simpa [prefixWord, tailWord_396637, baseEnd_396637] using wordTrace_append hprefix tailTrace_396637
  have hstable : (prefixWord ++ tailWord_396637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396637).length < 2 ^ (prefixWord ++ tailWord_396637).sum := by decide
  have hdescent : baseEnd_396637 < baseStart_396637 := by decide
  rcases family_descends (prefixWord ++ tailWord_396637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396643 : List Nat := [1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_396643 : Nat := 118140960795 + 396643 * 2 ^ 59
def prefixEnd_396643 : Nat := 4983230072969 + 3 ^ 40 * 396643 * 2
def baseEnd_396643 : Nat := 120692448735642587341261

theorem tailTrace_396643 : CollatzResearch.WordTrace tailWord_396643 prefixEnd_396643 120692448735642587341261 := by
  unfold tailWord_396643
  simp only [CollatzResearch.WordTrace]
  refine ⟨14466758702037627076354583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9644505801358418050903055 14466758702037627076354583)
  ·
    refine ⟨21700138053056440614531875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14466758702037627076354583 21700138053056440614531875)
    ·
      refine ⟨32550207079584660921797813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21700138053056440614531875 32550207079584660921797813)
      ·
        refine ⟨3051581913711061961418545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32550207079584660921797813 3051581913711061961418545)
        ·
          refine ⟨2288686435283296471063909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051581913711061961418545 2288686435283296471063909)
          ·
            refine ⟨429128706615618088324483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2288686435283296471063909 429128706615618088324483)
            ·
              refine ⟨643693059923427132486725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429128706615618088324483 643693059923427132486725)
              ·
                refine ⟨120692448735642587341261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643693059923427132486725 120692448735642587341261)
                ·
                  rfl

theorem cell19_396643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_396643 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396643 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396643 prefixEnd_396643 := by exact prefixLift 396643
  have htrace : WordTrace (prefixWord ++ tailWord_396643) baseStart_396643 baseEnd_396643 := by
    simpa [prefixWord, tailWord_396643, baseEnd_396643] using wordTrace_append hprefix tailTrace_396643
  have hstable : (prefixWord ++ tailWord_396643).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396643).length < 2 ^ (prefixWord ++ tailWord_396643).sum := by decide
  have hdescent : baseEnd_396643 < baseStart_396643 := by decide
  rcases family_descends (prefixWord ++ tailWord_396643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396717 : List Nat := [1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_396717 : Nat := 118140960795 + 396717 * 2 ^ 59
def prefixEnd_396717 : Nat := 4983230072969 + 3 ^ 40 * 396717 * 2
def baseEnd_396717 : Nat := 120714965813232341696615

theorem tailTrace_396717 : CollatzResearch.WordTrace tailWord_396717 prefixEnd_396717 120714965813232341696615 := by
  unfold tailWord_396717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14469457703769537714548405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9646305135846358476365603 14469457703769537714548405)
  ·
    refine ⟨1356511659728394160738913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14469457703769537714548405 1356511659728394160738913)
    ·
      refine ⟨1017383744796295620554185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1356511659728394160738913 1017383744796295620554185)
      ·
        refine ⟨763037808597221715415639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017383744796295620554185 763037808597221715415639)
        ·
          refine ⟨1144556712895832573123459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763037808597221715415639 1144556712895832573123459)
          ·
            refine ⟨1716835069343748859685189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144556712895832573123459 1716835069343748859685189)
            ·
              refine ⟨321906575501952911190973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1716835069343748859685189 321906575501952911190973)
              ·
                refine ⟨120714965813232341696615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321906575501952911190973 120714965813232341696615)
                ·
                  rfl

theorem cell19_396717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_396717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396717 prefixEnd_396717 := by exact prefixLift 396717
  have htrace : WordTrace (prefixWord ++ tailWord_396717) baseStart_396717 baseEnd_396717 := by
    simpa [prefixWord, tailWord_396717, baseEnd_396717] using wordTrace_append hprefix tailTrace_396717
  have hstable : (prefixWord ++ tailWord_396717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396717).length < 2 ^ (prefixWord ++ tailWord_396717).sum := by decide
  have hdescent : baseEnd_396717 < baseStart_396717 := by decide
  rcases family_descends (prefixWord ++ tailWord_396717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396721 : List Nat := [1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_396721 : Nat := 118140960795 + 396721 * 2 ^ 59
def prefixEnd_396721 : Nat := 4983230072969 + 3 ^ 40 * 396721 * 2
def baseEnd_396721 : Nat := 120716182952561517607715

theorem tailTrace_396721 : CollatzResearch.WordTrace tailWord_396721 prefixEnd_396721 120716182952561517607715 := by
  unfold tailWord_396721
  simp only [CollatzResearch.WordTrace]
  refine ⟨14469603595755046397694017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9646402397170030931796011 14469603595755046397694017)
  ·
    refine ⟨10852202696816284798270513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14469603595755046397694017 10852202696816284798270513)
    ·
      refine ⟨8139152022612213598702885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10852202696816284798270513 8139152022612213598702885)
      ·
        refine ⟨1526091004239790049756791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8139152022612213598702885 1526091004239790049756791)
        ·
          refine ⟨2289136506359685074635187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526091004239790049756791 2289136506359685074635187)
          ·
            refine ⟨3433704759539527611952781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289136506359685074635187 3433704759539527611952781)
            ·
              refine ⟨1287639284827322854482293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3433704759539527611952781 1287639284827322854482293)
              ·
                refine ⟨120716182952561517607715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1287639284827322854482293 120716182952561517607715)
                ·
                  rfl

theorem cell19_396721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_396721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396721 prefixEnd_396721 := by exact prefixLift 396721
  have htrace : WordTrace (prefixWord ++ tailWord_396721) baseStart_396721 baseEnd_396721 := by
    simpa [prefixWord, tailWord_396721, baseEnd_396721] using wordTrace_append hprefix tailTrace_396721
  have hstable : (prefixWord ++ tailWord_396721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396721).length < 2 ^ (prefixWord ++ tailWord_396721).sum := by decide
  have hdescent : baseEnd_396721 < baseStart_396721 := by decide
  rcases family_descends (prefixWord ++ tailWord_396721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396806 : List Nat := [6, 2, 1, 1, 3, 1, 1, 4]
def baseStart_396806 : Nat := 118140960795 + 396806 * 2 ^ 59
def prefixEnd_396806 : Nat := 4983230072969 + 3 ^ 40 * 396806 * 2
def baseEnd_396806 : Nat := 120742047163306505718595

theorem tailTrace_396806 : CollatzResearch.WordTrace tailWord_396806 prefixEnd_396806 120742047163306505718595 := by
  unfold tailWord_396806
  simp only [CollatzResearch.WordTrace]
  refine ⟨452271993763972059829321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9648469200298070609692181 452271993763972059829321)
  ·
    refine ⟨339203995322979044871991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 452271993763972059829321 339203995322979044871991)
    ·
      refine ⟨508805992984468567307987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339203995322979044871991 508805992984468567307987)
      ·
        refine ⟨763208989476702850961981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508805992984468567307987 763208989476702850961981)
        ·
          refine ⟨286203371053763569110743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 763208989476702850961981 286203371053763569110743)
          ·
            refine ⟨429305056580645353666115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286203371053763569110743 429305056580645353666115)
            ·
              refine ⟨643957584870968030499173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429305056580645353666115 643957584870968030499173)
              ·
                refine ⟨120742047163306505718595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643957584870968030499173 120742047163306505718595)
                ·
                  rfl

theorem cell19_396806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_396806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396806 prefixEnd_396806 := by exact prefixLift 396806
  have htrace : WordTrace (prefixWord ++ tailWord_396806) baseStart_396806 baseEnd_396806 := by
    simpa [prefixWord, tailWord_396806, baseEnd_396806] using wordTrace_append hprefix tailTrace_396806
  have hstable : (prefixWord ++ tailWord_396806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396806).length < 2 ^ (prefixWord ++ tailWord_396806).sum := by decide
  have hdescent : baseEnd_396806 < baseStart_396806 := by decide
  rcases family_descends (prefixWord ++ tailWord_396806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396812 : List Nat := [2, 2, 1, 2, 6, 1, 1, 4]
def baseStart_396812 : Nat := 118140960795 + 396812 * 2 ^ 59
def prefixEnd_396812 : Nat := 4983230072969 + 3 ^ 40 * 396812 * 2
def baseEnd_396812 : Nat := 120743872872300269585245

theorem tailTrace_396812 : CollatzResearch.WordTrace tailWord_396812 prefixEnd_396812 120743872872300269585245 := by
  unfold tailWord_396812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236461319212684469628345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9648615092283579292837793 7236461319212684469628345)
  ·
    refine ⟨5427345989409513352221259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7236461319212684469628345 5427345989409513352221259)
    ·
      refine ⟨8141018984114270028331889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5427345989409513352221259 8141018984114270028331889)
      ·
        refine ⟨6105764238085702521248917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8141018984114270028331889 6105764238085702521248917)
        ·
          refine ⟨286207698660267305683543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6105764238085702521248917 286207698660267305683543)
          ·
            refine ⟨429311547990400958525315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286207698660267305683543 429311547990400958525315)
            ·
              refine ⟨643967321985601437787973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429311547990400958525315 643967321985601437787973)
              ·
                refine ⟨120743872872300269585245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643967321985601437787973 120743872872300269585245)
                ·
                  rfl

theorem cell19_396812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_396812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396812 prefixEnd_396812 := by exact prefixLift 396812
  have htrace : WordTrace (prefixWord ++ tailWord_396812) baseStart_396812 baseEnd_396812 := by
    simpa [prefixWord, tailWord_396812, baseEnd_396812] using wordTrace_append hprefix tailTrace_396812
  have hstable : (prefixWord ++ tailWord_396812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396812).length < 2 ^ (prefixWord ++ tailWord_396812).sum := by decide
  have hdescent : baseEnd_396812 < baseStart_396812 := by decide
  rcases family_descends (prefixWord ++ tailWord_396812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396833 : List Nat := [1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_396833 : Nat := 118140960795 + 396833 * 2 ^ 59
def prefixEnd_396833 : Nat := 4983230072969 + 3 ^ 40 * 396833 * 2
def baseEnd_396833 : Nat := 120750262853778443118521

theorem tailTrace_396833 : CollatzResearch.WordTrace tailWord_396833 prefixEnd_396833 120750262853778443118521 := by
  unfold tailWord_396833
  simp only [CollatzResearch.WordTrace]
  refine ⟨14473688571349289525771153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9649125714232859683847435 14473688571349289525771153)
  ·
    refine ⟨10855266428511967144328365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14473688571349289525771153 10855266428511967144328365)
    ·
      refine ⟨4070724910691987679123137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10855266428511967144328365 4070724910691987679123137)
      ·
        refine ⟨3053043683018990759342353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4070724910691987679123137 3053043683018990759342353)
        ·
          refine ⟨2289782762264243069506765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3053043683018990759342353 2289782762264243069506765)
          ·
            refine ⟨858668535849091151065037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2289782762264243069506765 858668535849091151065037)
            ·
              refine ⟨322000700943409181649389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858668535849091151065037 322000700943409181649389)
              ·
                refine ⟨120750262853778443118521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322000700943409181649389 120750262853778443118521)
                ·
                  rfl

theorem cell19_396833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_396833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396833 prefixEnd_396833 := by exact prefixLift 396833
  have htrace : WordTrace (prefixWord ++ tailWord_396833) baseStart_396833 baseEnd_396833 := by
    simpa [prefixWord, tailWord_396833, baseEnd_396833] using wordTrace_append hprefix tailTrace_396833
  have hstable : (prefixWord ++ tailWord_396833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396833).length < 2 ^ (prefixWord ++ tailWord_396833).sum := by decide
  have hdescent : baseEnd_396833 < baseStart_396833 := by decide
  rcases family_descends (prefixWord ++ tailWord_396833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396875 : List Nat := [1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_396875 : Nat := 118140960795 + 396875 * 2 ^ 59
def prefixEnd_396875 : Nat := 4983230072969 + 3 ^ 40 * 396875 * 2
def baseEnd_396875 : Nat := 120763042816734790185073

theorem tailTrace_396875 : CollatzResearch.WordTrace tailWord_396875 prefixEnd_396875 120763042816734790185073 := by
  unfold tailWord_396875
  simp only [CollatzResearch.WordTrace]
  refine ⟨14475220437197130698800079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9650146958131420465866719 14475220437197130698800079)
  ·
    refine ⟨21712830655795696048200119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14475220437197130698800079 21712830655795696048200119)
    ·
      refine ⟨32569245983693544072300179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21712830655795696048200119 32569245983693544072300179)
      ·
        refine ⟨48853868975540316108450269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32569245983693544072300179 48853868975540316108450269)
        ·
          refine ⟨18320200865827618540668851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48853868975540316108450269 18320200865827618540668851)
          ·
            refine ⟨27480301298741427811003277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18320200865827618540668851 27480301298741427811003277)
            ·
              refine ⟨10305112987028035429126229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27480301298741427811003277 10305112987028035429126229)
              ·
                refine ⟨120763042816734790185073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10305112987028035429126229 120763042816734790185073)
                ·
                  rfl

theorem cell19_396875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_396875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396875 prefixEnd_396875 := by exact prefixLift 396875
  have htrace : WordTrace (prefixWord ++ tailWord_396875) baseStart_396875 baseEnd_396875 := by
    simpa [prefixWord, tailWord_396875, baseEnd_396875] using wordTrace_append hprefix tailTrace_396875
  have hstable : (prefixWord ++ tailWord_396875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396875).length < 2 ^ (prefixWord ++ tailWord_396875).sum := by decide
  have hdescent : baseEnd_396875 < baseStart_396875 := by decide
  rcases family_descends (prefixWord ++ tailWord_396875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396886 : List Nat := [5, 2, 2, 2, 1, 1, 1, 5]
def baseStart_396886 : Nat := 118140960795 + 396886 * 2 ^ 59
def prefixEnd_396886 : Nat := 4983230072969 + 3 ^ 40 * 396886 * 2
def baseEnd_396886 : Nat := 120766389949890023940599

theorem tailTrace_396886 : CollatzResearch.WordTrace tailWord_396886 prefixEnd_396886 120766389949890023940599 := by
  unfold tailWord_396886
  simp only [CollatzResearch.WordTrace]
  refine ⟨904726352509829973590657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9650414426771519718300341 904726352509829973590657)
  ·
    refine ⟨678544764382372480192993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 904726352509829973590657 678544764382372480192993)
    ·
      refine ⟨508908573286779360144745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678544764382372480192993 508908573286779360144745)
      ·
        refine ⟨381681429965084520108559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508908573286779360144745 381681429965084520108559)
        ·
          refine ⟨572522144947626780162839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381681429965084520108559 572522144947626780162839)
          ·
            refine ⟨858783217421440170244259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572522144947626780162839 858783217421440170244259)
            ·
              refine ⟨1288174826132160255366389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858783217421440170244259 1288174826132160255366389)
              ·
                refine ⟨120766389949890023940599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1288174826132160255366389 120766389949890023940599)
                ·
                  rfl

theorem cell19_396886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_396886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396886 prefixEnd_396886 := by exact prefixLift 396886
  have htrace : WordTrace (prefixWord ++ tailWord_396886) baseStart_396886 baseEnd_396886 := by
    simpa [prefixWord, tailWord_396886, baseEnd_396886] using wordTrace_append hprefix tailTrace_396886
  have hstable : (prefixWord ++ tailWord_396886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396886).length < 2 ^ (prefixWord ++ tailWord_396886).sum := by decide
  have hdescent : baseEnd_396886 < baseStart_396886 := by decide
  rcases family_descends (prefixWord ++ tailWord_396886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396909 : List Nat := [1, 5, 1, 1, 4, 2, 5]
def baseStart_396909 : Nat := 118140960795 + 396909 * 2 ^ 59
def prefixEnd_396909 : Nat := 4983230072969 + 3 ^ 40 * 396909 * 2
def baseEnd_396909 : Nat := 40257796167010928476475

theorem tailTrace_396909 : CollatzResearch.WordTrace tailWord_396909 prefixEnd_396909 40257796167010928476475 := by
  unfold tailWord_396909
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476460519073954505537781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9650973679382636337025187 14476460519073954505537781)
  ·
    refine ⟨1357168173663183234894167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14476460519073954505537781 1357168173663183234894167)
    ·
      refine ⟨2035752260494774852341251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357168173663183234894167 2035752260494774852341251)
      ·
        refine ⟨3053628390742162278511877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035752260494774852341251 3053628390742162278511877)
        ·
          refine ⟨572555323264155427220977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3053628390742162278511877 572555323264155427220977)
          ·
            refine ⟨429416492448116570415733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572555323264155427220977 429416492448116570415733)
            ·
              refine ⟨40257796167010928476475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 429416492448116570415733 40257796167010928476475)
              ·
                rfl

theorem cell19_396909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_396909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_396909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_396909 prefixEnd_396909 := by exact prefixLift 396909
  have htrace : WordTrace (prefixWord ++ tailWord_396909) baseStart_396909 baseEnd_396909 := by
    simpa [prefixWord, tailWord_396909, baseEnd_396909] using wordTrace_append hprefix tailTrace_396909
  have hstable : (prefixWord ++ tailWord_396909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396909).length < 2 ^ (prefixWord ++ tailWord_396909).sum := by decide
  have hdescent : baseEnd_396909 < baseStart_396909 := by decide
  rcases family_descends (prefixWord ++ tailWord_396909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397025 : List Nat := [1, 2, 3, 1, 5, 1, 6]
def baseStart_397025 : Nat := 118140960795 + 397025 * 2 ^ 59
def prefixEnd_397025 : Nat := 4983230072969 + 3 ^ 40 * 397025 * 2
def baseEnd_397025 : Nat := 40269561847192962283777

theorem tailTrace_397025 : CollatzResearch.WordTrace tailWord_397025 prefixEnd_397025 40269561847192962283777 := by
  unfold tailWord_397025
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480691386653706316760529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9653794257769137544507019 14480691386653706316760529)
  ·
    refine ⟨10860518539990279737570397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14480691386653706316760529 10860518539990279737570397)
    ·
      refine ⟨4072694452496354901588899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10860518539990279737570397 4072694452496354901588899)
      ·
        refine ⟨6109041678744532352383349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072694452496354901588899 6109041678744532352383349)
        ·
          refine ⟨572722657382299908035939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6109041678744532352383349 572722657382299908035939)
          ·
            refine ⟨859083986073449862053909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572722657382299908035939 859083986073449862053909)
            ·
              refine ⟨40269561847192962283777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 859083986073449862053909 40269561847192962283777)
              ·
                rfl

theorem cell19_397025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_397025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397025 prefixEnd_397025 := by exact prefixLift 397025
  have htrace : WordTrace (prefixWord ++ tailWord_397025) baseStart_397025 baseEnd_397025 := by
    simpa [prefixWord, tailWord_397025, baseEnd_397025] using wordTrace_append hprefix tailTrace_397025
  have hstable : (prefixWord ++ tailWord_397025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397025).length < 2 ^ (prefixWord ++ tailWord_397025).sum := by decide
  have hdescent : baseEnd_397025 < baseStart_397025 := by decide
  rcases family_descends (prefixWord ++ tailWord_397025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397076 : List Nat := [2, 4, 4, 1, 1, 2, 5]
def baseStart_397076 : Nat := 118140960795 + 397076 * 2 ^ 59
def prefixEnd_397076 : Nat := 4983230072969 + 3 ^ 40 * 397076 * 2
def baseEnd_397076 : Nat := 40274734689341959905953

theorem tailTrace_397076 : CollatzResearch.WordTrace tailWord_397076 prefixEnd_397076 40274734689341959905953 := by
  unfold tailWord_397076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241275754734471013433541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9655034339645961351244721 7241275754734471013433541)
  ·
    refine ⟨1357739204012713315018789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7241275754734471013433541 1357739204012713315018789)
    ·
      refine ⟨254576100752383746566023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1357739204012713315018789 254576100752383746566023)
      ·
        refine ⟨381864151128575619849035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254576100752383746566023 381864151128575619849035)
        ·
          refine ⟨572796226692863429773553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381864151128575619849035 572796226692863429773553)
          ·
            refine ⟨429597170019647572330165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572796226692863429773553 429597170019647572330165)
            ·
              refine ⟨40274734689341959905953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 429597170019647572330165 40274734689341959905953)
              ·
                rfl

theorem cell19_397076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_397076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397076 prefixEnd_397076 := by exact prefixLift 397076
  have htrace : WordTrace (prefixWord ++ tailWord_397076) baseStart_397076 baseEnd_397076 := by
    simpa [prefixWord, tailWord_397076, baseEnd_397076] using wordTrace_append hprefix tailTrace_397076
  have hstable : (prefixWord ++ tailWord_397076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397076).length < 2 ^ (prefixWord ++ tailWord_397076).sum := by decide
  have hdescent : baseEnd_397076 < baseStart_397076 := by decide
  rcases family_descends (prefixWord ++ tailWord_397076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397082 : List Nat := [3, 1, 1, 3, 2, 4, 5]
def baseStart_397082 : Nat := 118140960795 + 397082 * 2 ^ 59
def prefixEnd_397082 : Nat := 4983230072969 + 3 ^ 40 * 397082 * 2
def baseEnd_397082 : Nat := 40275343259006547861503

theorem tailTrace_397082 : CollatzResearch.WordTrace tailWord_397082 prefixEnd_397082 40275343259006547861503 := by
  unfold tailWord_397082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620692586861801262896375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9655180231631470034390333 3620692586861801262896375)
  ·
    refine ⟨5431038880292701894344563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3620692586861801262896375 5431038880292701894344563)
    ·
      refine ⟨8146558320439052841516845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5431038880292701894344563 8146558320439052841516845)
      ·
        refine ⟨3054959370164644815568817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8146558320439052841516845 3054959370164644815568817)
        ·
          refine ⟨2291219527623483611676613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054959370164644815568817 2291219527623483611676613)
          ·
            refine ⟨429603661429403177189365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2291219527623483611676613 429603661429403177189365)
            ·
              refine ⟨40275343259006547861503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 429603661429403177189365 40275343259006547861503)
              ·
                rfl

theorem cell19_397082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_397082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397082 prefixEnd_397082 := by exact prefixLift 397082
  have htrace : WordTrace (prefixWord ++ tailWord_397082) baseStart_397082 baseEnd_397082 := by
    simpa [prefixWord, tailWord_397082, baseEnd_397082] using wordTrace_append hprefix tailTrace_397082
  have hstable : (prefixWord ++ tailWord_397082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397082).length < 2 ^ (prefixWord ++ tailWord_397082).sum := by decide
  have hdescent : baseEnd_397082 < baseStart_397082 := by decide
  rcases family_descends (prefixWord ++ tailWord_397082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397141 : List Nat := [1, 3, 2, 2, 2, 9]
def baseStart_397141 : Nat := 118140960795 + 397141 * 2 ^ 59
def prefixEnd_397141 : Nat := 4983230072969 + 3 ^ 40 * 397141 * 2
def baseEnd_397141 : Nat := 13427109175791665363693

theorem tailTrace_397141 : CollatzResearch.WordTrace tailWord_397141 prefixEnd_397141 13427109175791665363693 := by
  unfold tailWord_397141
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484922254233458127983277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656614836155638751988851 14484922254233458127983277)
  ·
    refine ⟨5431845845337546797993729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14484922254233458127983277 5431845845337546797993729)
    ·
      refine ⟨4073884384003160098495297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5431845845337546797993729 4073884384003160098495297)
      ·
        refine ⟨3055413288002370073871473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073884384003160098495297 3055413288002370073871473)
        ·
          refine ⟨2291559966001777555403605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055413288002370073871473 2291559966001777555403605)
          ·
            refine ⟨13427109175791665363693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2291559966001777555403605 13427109175791665363693)
            ·
              rfl

theorem cell19_397141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_397141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397141 prefixEnd_397141 := by exact prefixLift 397141
  have htrace : WordTrace (prefixWord ++ tailWord_397141) baseStart_397141 baseEnd_397141 := by
    simpa [prefixWord, tailWord_397141, baseEnd_397141] using wordTrace_append hprefix tailTrace_397141
  have hstable : (prefixWord ++ tailWord_397141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397141).length < 2 ^ (prefixWord ++ tailWord_397141).sum := by decide
  have hdescent : baseEnd_397141 < baseStart_397141 := by decide
  rcases family_descends (prefixWord ++ tailWord_397141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397156 : List Nat := [2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_397156 : Nat := 118140960795 + 397156 * 2 ^ 59
def prefixEnd_397156 : Nat := 4983230072969 + 3 ^ 40 * 397156 * 2
def baseEnd_397156 : Nat := 120848546854609397939863

theorem tailTrace_397156 : CollatzResearch.WordTrace tailWord_397156 prefixEnd_397156 120848546854609397939863 := by
  unfold tailWord_397156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242734674589557844889661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9656979566119410459852881 7242734674589557844889661)
  ·
    refine ⟨2716025502971084191833623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7242734674589557844889661 2716025502971084191833623)
    ·
      refine ⟨4074038254456626287750435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716025502971084191833623 4074038254456626287750435)
      ·
        refine ⟨6111057381684939431625653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074038254456626287750435 6111057381684939431625653)
        ·
          refine ⟨572911629532963071714905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6111057381684939431625653 572911629532963071714905)
          ·
            refine ⟨429683722149722303786179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572911629532963071714905 429683722149722303786179)
            ·
              refine ⟨644525583224583455679269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429683722149722303786179 644525583224583455679269)
              ·
                refine ⟨120848546854609397939863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644525583224583455679269 120848546854609397939863)
                ·
                  rfl

theorem cell19_397156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_397156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397156 prefixEnd_397156 := by exact prefixLift 397156
  have htrace : WordTrace (prefixWord ++ tailWord_397156) baseStart_397156 baseEnd_397156 := by
    simpa [prefixWord, tailWord_397156, baseEnd_397156] using wordTrace_append hprefix tailTrace_397156
  have hstable : (prefixWord ++ tailWord_397156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397156).length < 2 ^ (prefixWord ++ tailWord_397156).sum := by decide
  have hdescent : baseEnd_397156 < baseStart_397156 := by decide
  rcases family_descends (prefixWord ++ tailWord_397156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397177 : List Nat := [1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_397177 : Nat := 118140960795 + 397177 * 2 ^ 59
def prefixEnd_397177 : Nat := 4983230072969 + 3 ^ 40 * 397177 * 2
def baseEnd_397177 : Nat := 120854936836087571473139

theorem tailTrace_397177 : CollatzResearch.WordTrace tailWord_397177 prefixEnd_397177 120854936836087571473139 := by
  unfold tailWord_397177
  simp only [CollatzResearch.WordTrace]
  refine ⟨14486235282103036276293785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9657490188068690850862523 14486235282103036276293785)
  ·
    refine ⟨10864676461577277207220339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14486235282103036276293785 10864676461577277207220339)
    ·
      refine ⟨16297014692365915810830509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10864676461577277207220339 16297014692365915810830509)
      ·
        refine ⟨6111380509637218429061441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16297014692365915810830509 6111380509637218429061441)
        ·
          refine ⟨4583535382227913821796081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111380509637218429061441 4583535382227913821796081)
          ·
            refine ⟨3437651536670935366347061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583535382227913821796081 3437651536670935366347061)
            ·
              refine ⟨322279831562900190595037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3437651536670935366347061 322279831562900190595037)
              ·
                refine ⟨120854936836087571473139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322279831562900190595037 120854936836087571473139)
                ·
                  rfl

theorem cell19_397177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_397177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397177 prefixEnd_397177 := by exact prefixLift 397177
  have htrace : WordTrace (prefixWord ++ tailWord_397177) baseStart_397177 baseEnd_397177 := by
    simpa [prefixWord, tailWord_397177, baseEnd_397177] using wordTrace_append hprefix tailTrace_397177
  have hstable : (prefixWord ++ tailWord_397177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397177).length < 2 ^ (prefixWord ++ tailWord_397177).sum := by decide
  have hdescent : baseEnd_397177 < baseStart_397177 := by decide
  rcases family_descends (prefixWord ++ tailWord_397177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397310 : List Nat := [4, 2, 2, 2, 1, 8]
def baseStart_397310 : Nat := 118140960795 + 397310 * 2 ^ 59
def prefixEnd_397310 : Nat := 4983230072969 + 3 ^ 40 * 397310 * 2
def baseEnd_397310 : Nat := 13432822968753630057469

theorem tailTrace_397310 : CollatzResearch.WordTrace tailWord_397310 prefixEnd_397310 13432822968753630057469 := by
  unfold tailWord_397310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811385773827649998860673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9660724127080799993923589 1811385773827649998860673)
  ·
    refine ⟨1358539330370737499145505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1811385773827649998860673 1358539330370737499145505)
    ·
      refine ⟨1018904497778053124359129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358539330370737499145505 1018904497778053124359129)
      ·
        refine ⟨764178373333539843269347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1018904497778053124359129 764178373333539843269347)
        ·
          refine ⟨1146267560000309764904021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764178373333539843269347 1146267560000309764904021)
          ·
            refine ⟨13432822968753630057469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1146267560000309764904021 13432822968753630057469)
            ·
              rfl

theorem cell19_397310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_397310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397310 prefixEnd_397310 := by exact prefixLift 397310
  have htrace : WordTrace (prefixWord ++ tailWord_397310) baseStart_397310 baseEnd_397310 := by
    simpa [prefixWord, tailWord_397310, baseEnd_397310] using wordTrace_append hprefix tailTrace_397310
  have hstable : (prefixWord ++ tailWord_397310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397310).length < 2 ^ (prefixWord ++ tailWord_397310).sum := by decide
  have hdescent : baseEnd_397310 < baseStart_397310 := by decide
  rcases family_descends (prefixWord ++ tailWord_397310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397331 : List Nat := [1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_397331 : Nat := 118140960795 + 397331 * 2 ^ 59
def prefixEnd_397331 : Nat := 4983230072969 + 3 ^ 40 * 397331 * 2
def baseEnd_397331 : Nat := 120901796700260844050497

theorem tailTrace_397331 : CollatzResearch.WordTrace tailWord_397331 prefixEnd_397331 120901796700260844050497 := by
  unfold tailWord_397331
  simp only [CollatzResearch.WordTrace]
  refine ⟨14491852123545120577399847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9661234749030080384933231 14491852123545120577399847)
  ·
    refine ⟨21737778185317680866099771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14491852123545120577399847 21737778185317680866099771)
    ·
      refine ⟨32606667277976521299149657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21737778185317680866099771 32606667277976521299149657)
      ·
        refine ⟨24455000458482390974362243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32606667277976521299149657 24455000458482390974362243)
        ·
          refine ⟨36682500687723586461543365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24455000458482390974362243 36682500687723586461543365)
          ·
            refine ⟨6877968878948172461539381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36682500687723586461543365 6877968878948172461539381)
            ·
              refine ⟨644809582401391168269317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6877968878948172461539381 644809582401391168269317)
              ·
                refine ⟨120901796700260844050497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644809582401391168269317 120901796700260844050497)
                ·
                  rfl

theorem cell19_397331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_397331 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397331 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397331 prefixEnd_397331 := by exact prefixLift 397331
  have htrace : WordTrace (prefixWord ++ tailWord_397331) baseStart_397331 baseEnd_397331 := by
    simpa [prefixWord, tailWord_397331, baseEnd_397331] using wordTrace_append hprefix tailTrace_397331
  have hstable : (prefixWord ++ tailWord_397331).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397331).length < 2 ^ (prefixWord ++ tailWord_397331).sum := by decide
  have hdescent : baseEnd_397331 < baseStart_397331 := by decide
  rcases family_descends (prefixWord ++ tailWord_397331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397426 : List Nat := [3, 2, 1, 2, 2, 2, 7]
def baseStart_397426 : Nat := 118140960795 + 397426 * 2 ^ 59
def prefixEnd_397426 : Nat := 4983230072969 + 3 ^ 40 * 397426 * 2
def baseEnd_397426 : Nat := 40310234586442923979709

theorem tailTrace_397426 : CollatzResearch.WordTrace tailWord_397426 prefixEnd_397426 40310234586442923979709 := by
  unfold tailWord_397426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623829264550237950527033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9663544705467301201405421 3623829264550237950527033)
  ·
    refine ⟨2717871948412678462895275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3623829264550237950527033 2717871948412678462895275)
    ·
      refine ⟨4076807922619017694342913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717871948412678462895275 4076807922619017694342913)
      ·
        refine ⟨3057605941964263270757185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4076807922619017694342913 3057605941964263270757185)
        ·
          refine ⟨2293204456473197453067889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3057605941964263270757185 2293204456473197453067889)
          ·
            refine ⟨1719903342354898089800917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293204456473197453067889 1719903342354898089800917)
            ·
              refine ⟨40310234586442923979709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1719903342354898089800917 40310234586442923979709)
              ·
                rfl

theorem cell19_397426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_397426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397426 prefixEnd_397426 := by exact prefixLift 397426
  have htrace : WordTrace (prefixWord ++ tailWord_397426) baseStart_397426 baseEnd_397426 := by
    simpa [prefixWord, tailWord_397426, baseEnd_397426] using wordTrace_append hprefix tailTrace_397426
  have hstable : (prefixWord ++ tailWord_397426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397426).length < 2 ^ (prefixWord ++ tailWord_397426).sum := by decide
  have hdescent : baseEnd_397426 < baseStart_397426 := by decide
  rcases family_descends (prefixWord ++ tailWord_397426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397445 : List Nat := [1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_397445 : Nat := 118140960795 + 397445 * 2 ^ 59
def prefixEnd_397445 : Nat := 4983230072969 + 3 ^ 40 * 397445 * 2
def baseEnd_397445 : Nat := 120936485171142357516853

theorem tailTrace_397445 : CollatzResearch.WordTrace tailWord_397445 prefixEnd_397445 120936485171142357516853 := by
  unfold tailWord_397445
  simp only [CollatzResearch.WordTrace]
  refine ⟨14496010045132118047049789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9664006696754745364699859 14496010045132118047049789)
  ·
    refine ⟨5436003766924544267643671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14496010045132118047049789 5436003766924544267643671)
    ·
      refine ⟨8154005650386816401465507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5436003766924544267643671 8154005650386816401465507)
      ·
        refine ⟨12231008475580224602198261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8154005650386816401465507 12231008475580224602198261)
        ·
          refine ⟨1146657044585646056456087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12231008475580224602198261 1146657044585646056456087)
          ·
            refine ⟨1719985566878469084684131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146657044585646056456087 1719985566878469084684131)
            ·
              refine ⟨2579978350317703627026197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719985566878469084684131 2579978350317703627026197)
              ·
                refine ⟨120936485171142357516853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2579978350317703627026197 120936485171142357516853)
                ·
                  rfl

theorem cell19_397445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_397445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397445 prefixEnd_397445 := by exact prefixLift 397445
  have htrace : WordTrace (prefixWord ++ tailWord_397445) baseStart_397445 baseEnd_397445 := by
    simpa [prefixWord, tailWord_397445, baseEnd_397445] using wordTrace_append hprefix tailTrace_397445
  have hstable : (prefixWord ++ tailWord_397445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397445).length < 2 ^ (prefixWord ++ tailWord_397445).sum := by decide
  have hdescent : baseEnd_397445 < baseStart_397445 := by decide
  rcases family_descends (prefixWord ++ tailWord_397445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397492 : List Nat := [2, 5, 3, 1, 2, 1, 1, 4]
def baseStart_397492 : Nat := 118140960795 + 397492 * 2 ^ 59
def prefixEnd_397492 : Nat := 4983230072969 + 3 ^ 40 * 397492 * 2
def baseEnd_397492 : Nat := 120950786558260174472281

theorem tailTrace_397492 : CollatzResearch.WordTrace tailWord_397492 prefixEnd_397492 120950786558260174472281 := by
  unfold tailWord_397492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7248862137980922537005365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9665149517307896716007153 7248862137980922537005365)
  ·
    refine ⟨679580825435711487844253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7248862137980922537005365 679580825435711487844253)
    ·
      refine ⟨254842809538391807941595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 679580825435711487844253 254842809538391807941595)
      ·
        refine ⟨382264214307587711912393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254842809538391807941595 382264214307587711912393)
        ·
          refine ⟨286698160730690783934295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382264214307587711912393 286698160730690783934295)
          ·
            refine ⟨430047241096036175901443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286698160730690783934295 430047241096036175901443)
            ·
              refine ⟨645070861644054263852165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430047241096036175901443 645070861644054263852165)
              ·
                refine ⟨120950786558260174472281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645070861644054263852165 120950786558260174472281)
                ·
                  rfl

theorem cell19_397492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_397492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397492 prefixEnd_397492 := by exact prefixLift 397492
  have htrace : WordTrace (prefixWord ++ tailWord_397492) baseStart_397492 baseEnd_397492 := by
    simpa [prefixWord, tailWord_397492, baseEnd_397492] using wordTrace_append hprefix tailTrace_397492
  have hstable : (prefixWord ++ tailWord_397492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397492).length < 2 ^ (prefixWord ++ tailWord_397492).sum := by decide
  have hdescent : baseEnd_397492 < baseStart_397492 := by decide
  rcases family_descends (prefixWord ++ tailWord_397492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397572 : List Nat := [2, 3, 2, 2, 4, 1, 2, 3]
def baseStart_397572 : Nat := 118140960795 + 397572 * 2 ^ 59
def prefixEnd_397572 : Nat := 4983230072969 + 3 ^ 40 * 397572 * 2
def baseEnd_397572 : Nat := 120975129344843692694285

theorem tailTrace_397572 : CollatzResearch.WordTrace tailWord_397572 prefixEnd_397572 120975129344843692694285 := by
  unfold tailWord_397572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250321057836009368461485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9667094743781345824615313 7250321057836009368461485)
  ·
    refine ⟨2718870396688503513173057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7250321057836009368461485 2718870396688503513173057)
    ·
      refine ⟨2039152797516377634879793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2718870396688503513173057 2039152797516377634879793)
      ·
        refine ⟨1529364598137283226159845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2039152797516377634879793 1529364598137283226159845)
        ·
          refine ⟨286755862150740604904971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1529364598137283226159845 286755862150740604904971)
          ·
            refine ⟨430133793226110907357457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286755862150740604904971 430133793226110907357457)
            ·
              refine ⟨322600344919583180518093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430133793226110907357457 322600344919583180518093)
              ·
                refine ⟨120975129344843692694285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322600344919583180518093 120975129344843692694285)
                ·
                  rfl

theorem cell19_397572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_397572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397572 prefixEnd_397572 := by exact prefixLift 397572
  have htrace : WordTrace (prefixWord ++ tailWord_397572) baseStart_397572 baseEnd_397572 := by
    simpa [prefixWord, tailWord_397572, baseEnd_397572] using wordTrace_append hprefix tailTrace_397572
  have hstable : (prefixWord ++ tailWord_397572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397572).length < 2 ^ (prefixWord ++ tailWord_397572).sum := by decide
  have hdescent : baseEnd_397572 < baseStart_397572 := by decide
  rcases family_descends (prefixWord ++ tailWord_397572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397576 : List Nat := [2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_397576 : Nat := 118140960795 + 397576 * 2 ^ 59
def prefixEnd_397576 : Nat := 4983230072969 + 3 ^ 40 * 397576 * 2
def baseEnd_397576 : Nat := 120976346484172868605385

theorem tailTrace_397576 : CollatzResearch.WordTrace tailWord_397576 prefixEnd_397576 120976346484172868605385 := by
  unfold tailWord_397576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250394003828763710034291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9667192005105018280045721 7250394003828763710034291)
  ·
    refine ⟨10875591005743145565051437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7250394003828763710034291 10875591005743145565051437)
    ·
      refine ⟨4078346627153679586894289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10875591005743145565051437 4078346627153679586894289)
      ·
        refine ⟨3058759970365259690170717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4078346627153679586894289 3058759970365259690170717)
        ·
          refine ⟨1147034988886972383814019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3058759970365259690170717 1147034988886972383814019)
          ·
            refine ⟨1720552483330458575721029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147034988886972383814019 1720552483330458575721029)
            ·
              refine ⟨322603590624460982947693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1720552483330458575721029 322603590624460982947693)
              ·
                refine ⟨120976346484172868605385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322603590624460982947693 120976346484172868605385)
                ·
                  rfl

theorem cell19_397576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_397576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397576 prefixEnd_397576 := by exact prefixLift 397576
  have htrace : WordTrace (prefixWord ++ tailWord_397576) baseStart_397576 baseEnd_397576 := by
    simpa [prefixWord, tailWord_397576, baseEnd_397576] using wordTrace_append hprefix tailTrace_397576
  have hstable : (prefixWord ++ tailWord_397576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397576).length < 2 ^ (prefixWord ++ tailWord_397576).sum := by decide
  have hdescent : baseEnd_397576 < baseStart_397576 := by decide
  rcases family_descends (prefixWord ++ tailWord_397576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397671 : List Nat := [1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_397671 : Nat := 118140960795 + 397671 * 2 ^ 59
def prefixEnd_397671 : Nat := 4983230072969 + 3 ^ 40 * 397671 * 2
def baseEnd_397671 : Nat := 121005253543240796494015

theorem tailTrace_397671 : CollatzResearch.WordTrace tailWord_397671 prefixEnd_397671 121005253543240796494015 := by
  unfold tailWord_397671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14504252942313358644776867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9669501961542239096517911 14504252942313358644776867)
  ·
    refine ⟨21756379413470037967165301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14504252942313358644776867 21756379413470037967165301)
    ·
      refine ⟨2039660570012816059421747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21756379413470037967165301 2039660570012816059421747)
      ·
        refine ⟨3059490855019224089132621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039660570012816059421747 3059490855019224089132621)
        ·
          refine ⟨1147309070632209033424733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3059490855019224089132621 1147309070632209033424733)
          ·
            refine ⟨430240901487078387534275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1147309070632209033424733 430240901487078387534275)
            ·
              refine ⟨645361352230617581301413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430240901487078387534275 645361352230617581301413)
              ·
                refine ⟨121005253543240796494015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645361352230617581301413 121005253543240796494015)
                ·
                  rfl

theorem cell19_397671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_397671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397671 prefixEnd_397671 := by exact prefixLift 397671
  have htrace : WordTrace (prefixWord ++ tailWord_397671) baseStart_397671 baseEnd_397671 := by
    simpa [prefixWord, tailWord_397671, baseEnd_397671] using wordTrace_append hprefix tailTrace_397671
  have hstable : (prefixWord ++ tailWord_397671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397671).length < 2 ^ (prefixWord ++ tailWord_397671).sum := by decide
  have hdescent : baseEnd_397671 < baseStart_397671 := by decide
  rcases family_descends (prefixWord ++ tailWord_397671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397686 : List Nat := [5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_397686 : Nat := 118140960795 + 397686 * 2 ^ 59
def prefixEnd_397686 : Nat := 4983230072969 + 3 ^ 40 * 397686 * 2
def baseEnd_397686 : Nat := 121009817815725206160641

theorem tailTrace_397686 : CollatzResearch.WordTrace tailWord_397686 prefixEnd_397686 121009817815725206160641 := by
  unfold tailWord_397686
  simp only [CollatzResearch.WordTrace]
  refine ⟨906550002328688512910807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9669866691506010804381941 906550002328688512910807)
  ·
    refine ⟨1359825003493032769366211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 906550002328688512910807 1359825003493032769366211)
    ·
      refine ⟨2039737505239549154049317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359825003493032769366211 2039737505239549154049317)
      ·
        refine ⟨382450782232415466384247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2039737505239549154049317 382450782232415466384247)
        ·
          refine ⟨573676173348623199576371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382450782232415466384247 573676173348623199576371)
          ·
            refine ⟨860514260022934799364557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573676173348623199576371 860514260022934799364557)
            ·
              refine ⟨322692847508600549761709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860514260022934799364557 322692847508600549761709)
              ·
                refine ⟨121009817815725206160641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322692847508600549761709 121009817815725206160641)
                ·
                  rfl

theorem cell19_397686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_397686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397686 prefixEnd_397686 := by exact prefixLift 397686
  have htrace : WordTrace (prefixWord ++ tailWord_397686) baseStart_397686 baseEnd_397686 := by
    simpa [prefixWord, tailWord_397686, baseEnd_397686] using wordTrace_append hprefix tailTrace_397686
  have hstable : (prefixWord ++ tailWord_397686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397686).length < 2 ^ (prefixWord ++ tailWord_397686).sum := by decide
  have hdescent : baseEnd_397686 < baseStart_397686 := by decide
  rcases family_descends (prefixWord ++ tailWord_397686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397730 : List Nat := [3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_397730 : Nat := 118140960795 + 397730 * 2 ^ 59
def prefixEnd_397730 : Nat := 4983230072969 + 3 ^ 40 * 397730 * 2
def baseEnd_397730 : Nat := 121023206348346141182743

theorem tailTrace_397730 : CollatzResearch.WordTrace tailWord_397730 prefixEnd_397730 121023206348346141182743 := by
  unfold tailWord_397730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626601212274902930293661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9670936566066407814116429 3626601212274902930293661)
  ·
    refine ⟨1359975454603088598860123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3626601212274902930293661 1359975454603088598860123)
    ·
      refine ⟨2039963181904632898290185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359975454603088598860123 2039963181904632898290185)
      ·
        refine ⟨1529972386428474673717639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2039963181904632898290185 1529972386428474673717639)
        ·
          refine ⟨2294958579642712010576459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529972386428474673717639 2294958579642712010576459)
          ·
            refine ⟨3442437869464068015864689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294958579642712010576459 3442437869464068015864689)
            ·
              refine ⟨2581828402098051011898517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442437869464068015864689 2581828402098051011898517)
              ·
                refine ⟨121023206348346141182743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2581828402098051011898517 121023206348346141182743)
                ·
                  rfl

theorem cell19_397730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_397730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397730 prefixEnd_397730 := by exact prefixLift 397730
  have htrace : WordTrace (prefixWord ++ tailWord_397730) baseStart_397730 baseEnd_397730 := by
    simpa [prefixWord, tailWord_397730, baseEnd_397730] using wordTrace_append hprefix tailTrace_397730
  have hstable : (prefixWord ++ tailWord_397730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397730).length < 2 ^ (prefixWord ++ tailWord_397730).sum := by decide
  have hdescent : baseEnd_397730 < baseStart_397730 := by decide
  rcases family_descends (prefixWord ++ tailWord_397730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397764 : List Nat := [2, 3, 3, 2, 3, 1, 5]
def baseStart_397764 : Nat := 118140960795 + 397764 * 2 ^ 59
def prefixEnd_397764 : Nat := 4983230072969 + 3 ^ 40 * 397764 * 2
def baseEnd_397764 : Nat := 40344517344214712142365

theorem tailTrace_397764 : CollatzResearch.WordTrace tailWord_397764 prefixEnd_397764 40344517344214712142365 := by
  unfold tailWord_397764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253822465488217763956173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9671763287317623685274897 7253822465488217763956173)
  ·
    refine ⟨2720183424558081661483565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7253822465488217763956173 2720183424558081661483565)
    ·
      refine ⟨1020068784209280623056337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2720183424558081661483565 1020068784209280623056337)
      ·
        refine ⟨765051588156960467292253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1020068784209280623056337 765051588156960467292253)
        ·
          refine ⟨286894345558860175234595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 765051588156960467292253 286894345558860175234595)
          ·
            refine ⟨430341518338290262851893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286894345558860175234595 430341518338290262851893)
            ·
              refine ⟨40344517344214712142365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 430341518338290262851893 40344517344214712142365)
              ·
                rfl

theorem cell19_397764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_397764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397764 prefixEnd_397764 := by exact prefixLift 397764
  have htrace : WordTrace (prefixWord ++ tailWord_397764) baseStart_397764 baseEnd_397764 := by
    simpa [prefixWord, tailWord_397764, baseEnd_397764] using wordTrace_append hprefix tailTrace_397764
  have hstable : (prefixWord ++ tailWord_397764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397764).length < 2 ^ (prefixWord ++ tailWord_397764).sum := by decide
  have hdescent : baseEnd_397764 < baseStart_397764 := by decide
  rcases family_descends (prefixWord ++ tailWord_397764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397768 : List Nat := [2, 1, 3, 1, 3, 4, 5]
def baseStart_397768 : Nat := 118140960795 + 397768 * 2 ^ 59
def prefixEnd_397768 : Nat := 4983230072969 + 3 ^ 40 * 397768 * 2
def baseEnd_397768 : Nat := 40344923057324437446065

theorem tailTrace_397768 : CollatzResearch.WordTrace tailWord_397768 prefixEnd_397768 40344923057324437446065 := by
  unfold tailWord_397768
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253895411480972105528979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9671860548641296140705305 7253895411480972105528979)
  ·
    refine ⟨10880843117221458158293469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7253895411480972105528979 10880843117221458158293469)
    ·
      refine ⟨4080316168958046809360051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10880843117221458158293469 4080316168958046809360051)
      ·
        refine ⟨6120474253437070214040077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080316168958046809360051 6120474253437070214040077)
        ·
          refine ⟨2295177845038901330265029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6120474253437070214040077 2295177845038901330265029)
          ·
            refine ⟨430345845944793999424693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2295177845038901330265029 430345845944793999424693)
            ·
              refine ⟨40344923057324437446065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 430345845944793999424693 40344923057324437446065)
              ·
                rfl

theorem cell19_397768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_397768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397768 prefixEnd_397768 := by exact prefixLift 397768
  have htrace : WordTrace (prefixWord ++ tailWord_397768) baseStart_397768 baseEnd_397768 := by
    simpa [prefixWord, tailWord_397768, baseEnd_397768] using wordTrace_append hprefix tailTrace_397768
  have hstable : (prefixWord ++ tailWord_397768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397768).length < 2 ^ (prefixWord ++ tailWord_397768).sum := by decide
  have hdescent : baseEnd_397768 < baseStart_397768 := by decide
  rcases family_descends (prefixWord ++ tailWord_397768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397806 : List Nat := [4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_397806 : Nat := 118140960795 + 397806 * 2 ^ 59
def prefixEnd_397806 : Nat := 4983230072969 + 3 ^ 40 * 397806 * 2
def baseEnd_397806 : Nat := 121046331995600483493647

theorem tailTrace_397806 : CollatzResearch.WordTrace tailWord_397806 prefixEnd_397806 121046331995600483493647 := by
  unfold tailWord_397806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813647099603034587617659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9672784531216184467294181 1813647099603034587617659)
  ·
    refine ⟨2720470649404551881426489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813647099603034587617659 2720470649404551881426489)
    ·
      refine ⟨2040352987053413911069867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2720470649404551881426489 2040352987053413911069867)
      ·
        refine ⟨3060529480580120866604801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040352987053413911069867 3060529480580120866604801)
        ·
          refine ⟨2295397110435090649953601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060529480580120866604801 2295397110435090649953601)
          ·
            refine ⟨1721547832826317987465201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295397110435090649953601 1721547832826317987465201)
            ·
              refine ⟨1291160874619738490598901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721547832826317987465201 1291160874619738490598901)
              ·
                refine ⟨121046331995600483493647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1291160874619738490598901 121046331995600483493647)
                ·
                  rfl

theorem cell19_397806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_397806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397806 prefixEnd_397806 := by exact prefixLift 397806
  have htrace : WordTrace (prefixWord ++ tailWord_397806) baseStart_397806 baseEnd_397806 := by
    simpa [prefixWord, tailWord_397806, baseEnd_397806] using wordTrace_append hprefix tailTrace_397806
  have hstable : (prefixWord ++ tailWord_397806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397806).length < 2 ^ (prefixWord ++ tailWord_397806).sum := by decide
  have hdescent : baseEnd_397806 < baseStart_397806 := by decide
  rcases family_descends (prefixWord ++ tailWord_397806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397808 : List Nat := [2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_397808 : Nat := 118140960795 + 397808 * 2 ^ 59
def prefixEnd_397808 : Nat := 4983230072969 + 3 ^ 40 * 397808 * 2
def baseEnd_397808 : Nat := 121046940565265071449197

theorem tailTrace_397808 : CollatzResearch.WordTrace tailWord_397808 prefixEnd_397808 121046940565265071449197 := by
  unfold tailWord_397808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254624871408515521257039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9672833161878020695009385 7254624871408515521257039)
  ·
    refine ⟨10881937307112773281885559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254624871408515521257039 10881937307112773281885559)
    ·
      refine ⟨16322905960669159922828339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10881937307112773281885559 16322905960669159922828339)
      ·
        refine ⟨24484358941003739884242509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16322905960669159922828339 24484358941003739884242509)
        ·
          refine ⟨9181634602876402456590941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24484358941003739884242509 9181634602876402456590941)
          ·
            refine ⟨3443112976078650921221603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9181634602876402456590941 3443112976078650921221603)
            ·
              refine ⟨5164669464117976381832405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443112976078650921221603 5164669464117976381832405)
              ·
                refine ⟨121046940565265071449197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5164669464117976381832405 121046940565265071449197)
                ·
                  rfl

theorem cell19_397808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_397808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397808 prefixEnd_397808 := by exact prefixLift 397808
  have htrace : WordTrace (prefixWord ++ tailWord_397808) baseStart_397808 baseEnd_397808 := by
    simpa [prefixWord, tailWord_397808, baseEnd_397808] using wordTrace_append hprefix tailTrace_397808
  have hstable : (prefixWord ++ tailWord_397808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397808).length < 2 ^ (prefixWord ++ tailWord_397808).sum := by decide
  have hdescent : baseEnd_397808 < baseStart_397808 := by decide
  rcases family_descends (prefixWord ++ tailWord_397808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397916 : List Nat := [2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_397916 : Nat := 118140960795 + 397916 * 2 ^ 59
def prefixEnd_397916 : Nat := 4983230072969 + 3 ^ 40 * 397916 * 2
def baseEnd_397916 : Nat := 121079803327152821048903

theorem tailTrace_397916 : CollatzResearch.WordTrace tailWord_397916 prefixEnd_397916 121079803327152821048903 := by
  unfold tailWord_397916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256594413212882743722801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9675459217617176991630401 7256594413212882743722801)
  ·
    refine ⟨5442445809909662057792101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7256594413212882743722801 5442445809909662057792101)
    ·
      refine ⟨1020458589358061635836019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5442445809909662057792101 1020458589358061635836019)
      ·
        refine ⟨1530687884037092453754029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020458589358061635836019 1530687884037092453754029)
        ·
          refine ⟨574007956513909670157761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1530687884037092453754029 574007956513909670157761)
          ·
            refine ⟨430505967385432252618321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574007956513909670157761 430505967385432252618321)
            ·
              refine ⟨322879475539074189463741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430505967385432252618321 322879475539074189463741)
              ·
                refine ⟨121079803327152821048903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322879475539074189463741 121079803327152821048903)
                ·
                  rfl

theorem cell19_397916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_397916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397916 prefixEnd_397916 := by exact prefixLift 397916
  have htrace : WordTrace (prefixWord ++ tailWord_397916) baseStart_397916 baseEnd_397916 := by
    simpa [prefixWord, tailWord_397916, baseEnd_397916] using wordTrace_append hprefix tailTrace_397916
  have hstable : (prefixWord ++ tailWord_397916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397916).length < 2 ^ (prefixWord ++ tailWord_397916).sum := by decide
  have hdescent : baseEnd_397916 < baseStart_397916 := by decide
  rcases family_descends (prefixWord ++ tailWord_397916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397920 : List Nat := [2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_397920 : Nat := 118140960795 + 397920 * 2 ^ 59
def prefixEnd_397920 : Nat := 4983230072969 + 3 ^ 40 * 397920 * 2
def baseEnd_397920 : Nat := 121081020466481996960003

theorem tailTrace_397920 : CollatzResearch.WordTrace tailWord_397920 prefixEnd_397920 121081020466481996960003 := by
  unfold tailWord_397920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256667359205637085295607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9675556478940849447060809 7256667359205637085295607)
  ·
    refine ⟨10885001038808455627943411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7256667359205637085295607 10885001038808455627943411)
    ·
      refine ⟨16327501558212683441915117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10885001038808455627943411 16327501558212683441915117)
      ·
        refine ⟨6122813084329756290718169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16327501558212683441915117 6122813084329756290718169)
        ·
          refine ⟨4592109813247317218038627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122813084329756290718169 4592109813247317218038627)
          ·
            refine ⟨6888164719870975827057941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592109813247317218038627 6888164719870975827057941)
            ·
              refine ⟨322882721243951991893341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6888164719870975827057941 322882721243951991893341)
              ·
                refine ⟨121081020466481996960003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322882721243951991893341 121081020466481996960003)
                ·
                  rfl

theorem cell19_397920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_397920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397920 prefixEnd_397920 := by exact prefixLift 397920
  have htrace : WordTrace (prefixWord ++ tailWord_397920) baseStart_397920 baseEnd_397920 := by
    simpa [prefixWord, tailWord_397920, baseEnd_397920] using wordTrace_append hprefix tailTrace_397920
  have hstable : (prefixWord ++ tailWord_397920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397920).length < 2 ^ (prefixWord ++ tailWord_397920).sum := by decide
  have hdescent : baseEnd_397920 < baseStart_397920 := by decide
  rcases family_descends (prefixWord ++ tailWord_397920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397994 : List Nat := [3, 1, 5, 2, 1, 7]
def baseStart_397994 : Nat := 118140960795 + 397994 * 2 ^ 59
def prefixEnd_397994 : Nat := 4983230072969 + 3 ^ 40 * 397994 * 2
def baseEnd_397994 : Nat := 13455948616007972368373

theorem tailTrace_397994 : CollatzResearch.WordTrace tailWord_397994 prefixEnd_397994 13455948616007972368373 := by
  unfold tailWord_397994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629008430035796202196259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9677355813428789872523357 3629008430035796202196259)
  ·
    refine ⟨5443512645053694303294389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629008430035796202196259 5443512645053694303294389)
    ·
      refine ⟨510329310473783840933849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5443512645053694303294389 510329310473783840933849)
      ·
        refine ⟨382746982855337880700387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510329310473783840933849 382746982855337880700387)
        ·
          refine ⟨574120474283006821050581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382746982855337880700387 574120474283006821050581)
          ·
            refine ⟨13455948616007972368373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 574120474283006821050581 13455948616007972368373)
            ·
              rfl

theorem cell19_397994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_397994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_397994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_397994 prefixEnd_397994 := by exact prefixLift 397994
  have htrace : WordTrace (prefixWord ++ tailWord_397994) baseStart_397994 baseEnd_397994 := by
    simpa [prefixWord, tailWord_397994, baseEnd_397994] using wordTrace_append hprefix tailTrace_397994
  have hstable : (prefixWord ++ tailWord_397994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397994).length < 2 ^ (prefixWord ++ tailWord_397994).sum := by decide
  have hdescent : baseEnd_397994 < baseStart_397994 := by decide
  rcases family_descends (prefixWord ++ tailWord_397994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398015 : List Nat := [1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_398015 : Nat := 118140960795 + 398015 * 2 ^ 59
def prefixEnd_398015 : Nat := 4983230072969 + 3 ^ 40 * 398015 * 2
def baseEnd_398015 : Nat := 121109927525549924848633

theorem tailTrace_398015 : CollatzResearch.WordTrace tailWord_398015 prefixEnd_398015 121109927525549924848633 := by
  unfold tailWord_398015
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516799653067105395299499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9677866435378070263532999 14516799653067105395299499)
  ·
    refine ⟨21775199479600658092949249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14516799653067105395299499 21775199479600658092949249)
    ·
      refine ⟨16331399609700493569711937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21775199479600658092949249 16331399609700493569711937)
      ·
        refine ⟨12248549707275370177283953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16331399609700493569711937 12248549707275370177283953)
        ·
          refine ⟨9186412280456527632962965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12248549707275370177283953 9186412280456527632962965)
          ·
            refine ⟨430613075646399732795139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9186412280456527632962965 430613075646399732795139)
            ·
              refine ⟨645919613469599599192709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430613075646399732795139 645919613469599599192709)
              ·
                refine ⟨121109927525549924848633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645919613469599599192709 121109927525549924848633)
                ·
                  rfl

theorem cell19_398015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_398015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398015 prefixEnd_398015 := by exact prefixLift 398015
  have htrace : WordTrace (prefixWord ++ tailWord_398015) baseStart_398015 baseEnd_398015 := by
    simpa [prefixWord, tailWord_398015, baseEnd_398015] using wordTrace_append hprefix tailTrace_398015
  have hstable : (prefixWord ++ tailWord_398015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398015).length < 2 ^ (prefixWord ++ tailWord_398015).sum := by decide
  have hdescent : baseEnd_398015 < baseStart_398015 := by decide
  rcases family_descends (prefixWord ++ tailWord_398015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398112 : List Nat := [2, 1, 1, 5, 1, 2, 7]
def baseStart_398112 : Nat := 118140960795 + 398112 * 2 ^ 59
def prefixEnd_398112 : Nat := 4983230072969 + 3 ^ 40 * 398112 * 2
def baseEnd_398112 : Nat := 40379814384760813564271

theorem tailTrace_398112 : CollatzResearch.WordTrace tailWord_398112 prefixEnd_398112 40379814384760813564271 := by
  unfold tailWord_398112
  simp only [CollatzResearch.WordTrace]
  refine ⟨7260168766857845480790295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9680225022477127307720393 7260168766857845480790295)
  ·
    refine ⟨10890253150286768221185443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7260168766857845480790295 10890253150286768221185443)
    ·
      refine ⟨16335379725430152331778165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10890253150286768221185443 16335379725430152331778165)
      ·
        refine ⟨1531441849259076781104203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16335379725430152331778165 1531441849259076781104203)
        ·
          refine ⟨2297162773888615171656305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531441849259076781104203 2297162773888615171656305)
          ·
            refine ⟨1722872080416461378742229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297162773888615171656305 1722872080416461378742229)
            ·
              refine ⟨40379814384760813564271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1722872080416461378742229 40379814384760813564271)
              ·
                rfl

theorem cell19_398112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_398112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398112 prefixEnd_398112 := by exact prefixLift 398112
  have htrace : WordTrace (prefixWord ++ tailWord_398112) baseStart_398112 baseEnd_398112 := by
    simpa [prefixWord, tailWord_398112, baseEnd_398112] using wordTrace_append hprefix tailTrace_398112
  have hstable : (prefixWord ++ tailWord_398112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398112).length < 2 ^ (prefixWord ++ tailWord_398112).sum := by decide
  have hdescent : baseEnd_398112 < baseStart_398112 := by decide
  rcases family_descends (prefixWord ++ tailWord_398112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398125 : List Nat := [1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_398125 : Nat := 118140960795 + 398125 * 2 ^ 59
def prefixEnd_398125 : Nat := 4983230072969 + 3 ^ 40 * 398125 * 2
def baseEnd_398125 : Nat := 121143398857102262403889

theorem tailTrace_398125 : CollatzResearch.WordTrace tailWord_398125 prefixEnd_398125 121143398857102262403889 := by
  unfold tailWord_398125
  simp only [CollatzResearch.WordTrace]
  refine ⟨14520811682668594181803829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9680541121779062787869219 14520811682668594181803829)
  ·
    refine ⟨1361326095250180704544109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14520811682668594181803829 1361326095250180704544109)
    ·
      refine ⟨510497285718817764204041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1361326095250180704544109 510497285718817764204041)
      ·
        refine ⟨382872964289113323153031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510497285718817764204041 382872964289113323153031)
        ·
          refine ⟨574309446433669984729547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382872964289113323153031 574309446433669984729547)
          ·
            refine ⟨861464169650504977094321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574309446433669984729547 861464169650504977094321)
            ·
              refine ⟨646098127237878732820741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861464169650504977094321 646098127237878732820741)
              ·
                refine ⟨121143398857102262403889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 646098127237878732820741 121143398857102262403889)
                ·
                  rfl

theorem cell19_398125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_398125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398125 prefixEnd_398125 := by exact prefixLift 398125
  have htrace : WordTrace (prefixWord ++ tailWord_398125) baseStart_398125 baseEnd_398125 := by
    simpa [prefixWord, tailWord_398125, baseEnd_398125] using wordTrace_append hprefix tailTrace_398125
  have hstable : (prefixWord ++ tailWord_398125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398125).length < 2 ^ (prefixWord ++ tailWord_398125).sum := by decide
  have hdescent : baseEnd_398125 < baseStart_398125 := by decide
  rcases family_descends (prefixWord ++ tailWord_398125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398131 : List Nat := [1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_398131 : Nat := 118140960795 + 398131 * 2 ^ 59
def prefixEnd_398131 : Nat := 4983230072969 + 3 ^ 40 * 398131 * 2
def baseEnd_398131 : Nat := 121145224566096026270539

theorem tailTrace_398131 : CollatzResearch.WordTrace tailWord_398131 prefixEnd_398131 121145224566096026270539 := by
  unfold tailWord_398131
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521030520646857206522247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9680687013764571471014831 14521030520646857206522247)
  ·
    refine ⟨21781545780970285809783371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14521030520646857206522247 21781545780970285809783371)
    ·
      refine ⟨32672318671455428714675057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21781545780970285809783371 32672318671455428714675057)
      ·
        refine ⟨24504239003591571536006293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32672318671455428714675057 24504239003591571536006293)
        ·
          refine ⟨1148636203293354915750295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24504239003591571536006293 1148636203293354915750295)
          ·
            refine ⟨1722954304940032373625443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148636203293354915750295 1722954304940032373625443)
            ·
              refine ⟨2584431457410048560438165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722954304940032373625443 2584431457410048560438165)
              ·
                refine ⟨121145224566096026270539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2584431457410048560438165 121145224566096026270539)
                ·
                  rfl

theorem cell19_398131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_398131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398131 prefixEnd_398131 := by exact prefixLift 398131
  have htrace : WordTrace (prefixWord ++ tailWord_398131) baseStart_398131 baseEnd_398131 := by
    simpa [prefixWord, tailWord_398131, baseEnd_398131] using wordTrace_append hprefix tailTrace_398131
  have hstable : (prefixWord ++ tailWord_398131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398131).length < 2 ^ (prefixWord ++ tailWord_398131).sum := by decide
  have hdescent : baseEnd_398131 < baseStart_398131 := by decide
  rcases family_descends (prefixWord ++ tailWord_398131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398260 : List Nat := [2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_398260 : Nat := 118140960795 + 398260 * 2 ^ 59
def prefixEnd_398260 : Nat := 4983230072969 + 3 ^ 40 * 398260 * 2
def baseEnd_398260 : Nat := 121184477309461949403521

theorem tailTrace_398260 : CollatzResearch.WordTrace tailWord_398260 prefixEnd_398260 121184477309461949403521 := by
  unfold tailWord_398260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262867768589756118984117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9683823691453008158645489 7262867768589756118984117)
  ·
    refine ⟨680893853305289636154761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7262867768589756118984117 680893853305289636154761)
    ·
      refine ⟨510670389978967227116071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680893853305289636154761 510670389978967227116071)
      ·
        refine ⟨766005584968450840674107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510670389978967227116071 766005584968450840674107)
        ·
          refine ⟨1149008377452676261011161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766005584968450840674107 1149008377452676261011161)
          ·
            refine ⟨861756283089507195758371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149008377452676261011161 861756283089507195758371)
            ·
              refine ⟨1292634424634260793637557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861756283089507195758371 1292634424634260793637557)
              ·
                refine ⟨121184477309461949403521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1292634424634260793637557 121184477309461949403521)
                ·
                  rfl

theorem cell19_398260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_398260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398260 prefixEnd_398260 := by exact prefixLift 398260
  have htrace : WordTrace (prefixWord ++ tailWord_398260) baseStart_398260 baseEnd_398260 := by
    simpa [prefixWord, tailWord_398260, baseEnd_398260] using wordTrace_append hprefix tailTrace_398260
  have hstable : (prefixWord ++ tailWord_398260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398260).length < 2 ^ (prefixWord ++ tailWord_398260).sum := by decide
  have hdescent : baseEnd_398260 < baseStart_398260 := by decide
  rcases family_descends (prefixWord ++ tailWord_398260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398264 : List Nat := [2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_398264 : Nat := 118140960795 + 398264 * 2 ^ 59
def prefixEnd_398264 : Nat := 4983230072969 + 3 ^ 40 * 398264 * 2
def baseEnd_398264 : Nat := 121185694448791125314621

theorem tailTrace_398264 : CollatzResearch.WordTrace tailWord_398264 prefixEnd_398264 121185694448791125314621 := by
  unfold tailWord_398264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262940714582510460556923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9683920952776680614075897 7262940714582510460556923)
  ·
    refine ⟨10894411071873765690835385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7262940714582510460556923 10894411071873765690835385)
    ·
      refine ⟨8170808303905324268126539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10894411071873765690835385 8170808303905324268126539)
      ·
        refine ⟨12256212455857986402189809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8170808303905324268126539 12256212455857986402189809)
        ·
          refine ⟨9192159341893489801642357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12256212455857986402189809 9192159341893489801642357)
          ·
            refine ⟨861764938302514668903971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9192159341893489801642357 861764938302514668903971)
            ·
              refine ⟨1292647407453772003355957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861764938302514668903971 1292647407453772003355957)
              ·
                refine ⟨121185694448791125314621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1292647407453772003355957 121185694448791125314621)
                ·
                  rfl

theorem cell19_398264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_398264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398264 prefixEnd_398264 := by exact prefixLift 398264
  have htrace : WordTrace (prefixWord ++ tailWord_398264) baseStart_398264 baseEnd_398264 := by
    simpa [prefixWord, tailWord_398264, baseEnd_398264] using wordTrace_append hprefix tailTrace_398264
  have hstable : (prefixWord ++ tailWord_398264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398264).length < 2 ^ (prefixWord ++ tailWord_398264).sum := by decide
  have hdescent : baseEnd_398264 < baseStart_398264 := by decide
  rcases family_descends (prefixWord ++ tailWord_398264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398283 : List Nat := [1, 1, 1, 1, 3, 7, 5]
def baseStart_398283 : Nat := 118140960795 + 398283 * 2 ^ 59
def prefixEnd_398283 : Nat := 4983230072969 + 3 ^ 40 * 398283 * 2
def baseEnd_398283 : Nat := 40397158620201570297449

theorem tailTrace_398283 : CollatzResearch.WordTrace tailWord_398283 prefixEnd_398283 40397158620201570297449 := by
  unfold tailWord_398283
  simp only [CollatzResearch.WordTrace]
  refine ⟨14526574416096187166055503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9684382944064124777370335 14526574416096187166055503)
  ·
    refine ⟨21789861624144280749083255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14526574416096187166055503 21789861624144280749083255)
    ·
      refine ⟨32684792436216421123624883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21789861624144280749083255 32684792436216421123624883)
      ·
        refine ⟨49027188654324631685437325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32684792436216421123624883 49027188654324631685437325)
        ·
          refine ⟨18385195745371736882038997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49027188654324631685437325 18385195745371736882038997)
          ·
            refine ⟨430903025282150083172789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18385195745371736882038997 430903025282150083172789)
            ·
              refine ⟨40397158620201570297449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 430903025282150083172789 40397158620201570297449)
              ·
                rfl

theorem cell19_398283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_398283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398283 prefixEnd_398283 := by exact prefixLift 398283
  have htrace : WordTrace (prefixWord ++ tailWord_398283) baseStart_398283 baseEnd_398283 := by
    simpa [prefixWord, tailWord_398283, baseEnd_398283] using wordTrace_append hprefix tailTrace_398283
  have hstable : (prefixWord ++ tailWord_398283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398283).length < 2 ^ (prefixWord ++ tailWord_398283).sum := by decide
  have hdescent : baseEnd_398283 < baseStart_398283 := by decide
  rcases family_descends (prefixWord ++ tailWord_398283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398321 : List Nat := [1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_398321 : Nat := 118140960795 + 398321 * 2 ^ 59
def prefixEnd_398321 : Nat := 4983230072969 + 3 ^ 40 * 398321 * 2
def baseEnd_398321 : Nat := 121203038684231882047799

theorem tailTrace_398321 : CollatzResearch.WordTrace tailWord_398321 prefixEnd_398321 121203038684231882047799 := by
  unfold tailWord_398321
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527960389958519655938817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9685306926639013103959211 14527960389958519655938817)
  ·
    refine ⟨10895970292468889741954113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14527960389958519655938817 10895970292468889741954113)
    ·
      refine ⟨8171977719351667306465585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10895970292468889741954113 8171977719351667306465585)
      ·
        refine ⟨6128983289513750479849189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8171977719351667306465585 6128983289513750479849189)
        ·
          refine ⟨1149184366783828214971723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6128983289513750479849189 1149184366783828214971723)
          ·
            refine ⟨1723776550175742322457585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149184366783828214971723 1723776550175742322457585)
            ·
              refine ⟨1292832412631806741843189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723776550175742322457585 1292832412631806741843189)
              ·
                refine ⟨121203038684231882047799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1292832412631806741843189 121203038684231882047799)
                ·
                  rfl

theorem cell19_398321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_398321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398321 prefixEnd_398321 := by exact prefixLift 398321
  have htrace : WordTrace (prefixWord ++ tailWord_398321) baseStart_398321 baseEnd_398321 := by
    simpa [prefixWord, tailWord_398321, baseEnd_398321] using wordTrace_append hprefix tailTrace_398321
  have hstable : (prefixWord ++ tailWord_398321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398321).length < 2 ^ (prefixWord ++ tailWord_398321).sum := by decide
  have hdescent : baseEnd_398321 < baseStart_398321 := by decide
  rcases family_descends (prefixWord ++ tailWord_398321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398338 : List Nat := [3, 4, 1, 3, 8]
def baseStart_398338 : Nat := 118140960795 + 398338 * 2 ^ 59
def prefixEnd_398338 : Nat := 4983230072969 + 3 ^ 40 * 398338 * 2
def baseEnd_398338 : Nat := 4489193019495588135925

theorem tailTrace_398338 : CollatzResearch.WordTrace tailWord_398338 prefixEnd_398338 4489193019495588135925 := by
  unfold tailWord_398338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632145107724232889826917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9685720287264621039538445 3632145107724232889826917)
  ·
    refine ⟨681027207698293666842547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3632145107724232889826917 681027207698293666842547)
    ·
      refine ⟨1021540811547440500263821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681027207698293666842547 1021540811547440500263821)
      ·
        refine ⟨383077804330290187598933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1021540811547440500263821 383077804330290187598933)
        ·
          refine ⟨4489193019495588135925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 383077804330290187598933 4489193019495588135925)
          ·
            rfl

theorem cell19_398338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 8].length) (baseStart_398338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398338 prefixEnd_398338 := by exact prefixLift 398338
  have htrace : WordTrace (prefixWord ++ tailWord_398338) baseStart_398338 baseEnd_398338 := by
    simpa [prefixWord, tailWord_398338, baseEnd_398338] using wordTrace_append hprefix tailTrace_398338
  have hstable : (prefixWord ++ tailWord_398338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398338).length < 2 ^ (prefixWord ++ tailWord_398338).sum := by decide
  have hdescent : baseEnd_398338 < baseStart_398338 := by decide
  rcases family_descends (prefixWord ++ tailWord_398338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398357 : List Nat := [1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_398357 : Nat := 118140960795 + 398357 * 2 ^ 59
def prefixEnd_398357 : Nat := 4983230072969 + 3 ^ 40 * 398357 * 2
def baseEnd_398357 : Nat := 121213992938194465247701

theorem tailTrace_398357 : CollatzResearch.WordTrace tailWord_398357 prefixEnd_398357 121213992938194465247701 := by
  unfold tailWord_398357
  simp only [CollatzResearch.WordTrace]
  refine ⟨14529273417828097804249325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9686182278552065202832883 14529273417828097804249325)
  ·
    refine ⟨5448477531685536676593497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14529273417828097804249325 5448477531685536676593497)
    ·
      refine ⟨4086358148764152507445123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5448477531685536676593497 4086358148764152507445123)
      ·
        refine ⟨6129537223146228761167685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086358148764152507445123 6129537223146228761167685)
        ·
          refine ⟨1149288229339917892718941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6129537223146228761167685 1149288229339917892718941)
          ·
            refine ⟨430983086002469209769603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1149288229339917892718941 430983086002469209769603)
            ·
              refine ⟨646474629003703814654405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430983086002469209769603 646474629003703814654405)
              ·
                refine ⟨121213992938194465247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 646474629003703814654405 121213992938194465247701)
                ·
                  rfl

theorem cell19_398357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_398357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398357 prefixEnd_398357 := by exact prefixLift 398357
  have htrace : WordTrace (prefixWord ++ tailWord_398357) baseStart_398357 baseEnd_398357 := by
    simpa [prefixWord, tailWord_398357, baseEnd_398357] using wordTrace_append hprefix tailTrace_398357
  have hstable : (prefixWord ++ tailWord_398357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398357).length < 2 ^ (prefixWord ++ tailWord_398357).sum := by decide
  have hdescent : baseEnd_398357 < baseStart_398357 := by decide
  rcases family_descends (prefixWord ++ tailWord_398357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398397 : List Nat := [1, 4, 1, 3, 1, 3, 6]
def baseStart_398397 : Nat := 118140960795 + 398397 * 2 ^ 59
def prefixEnd_398397 : Nat := 4983230072969 + 3 ^ 40 * 398397 * 2
def baseEnd_398397 : Nat := 40408721443828741452901

theorem tailTrace_398397 : CollatzResearch.WordTrace tailWord_398397 prefixEnd_398397 40408721443828741452901 := by
  unfold tailWord_398397
  simp only [CollatzResearch.WordTrace]
  refine ⟨14530732337683184635705445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9687154891788789757136963 14530732337683184635705445)
  ·
    refine ⟨2724512313315597119194771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14530732337683184635705445 2724512313315597119194771)
    ·
      refine ⟨4086768469973395678792157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724512313315597119194771 4086768469973395678792157)
      ·
        refine ⟨1532538176240023379547059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4086768469973395678792157 1532538176240023379547059)
        ·
          refine ⟨2298807264360035069320589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532538176240023379547059 2298807264360035069320589)
          ·
            refine ⟨862052724135013150995221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2298807264360035069320589 862052724135013150995221)
            ·
              refine ⟨40408721443828741452901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 862052724135013150995221 40408721443828741452901)
              ·
                rfl

theorem cell19_398397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_398397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398397 prefixEnd_398397 := by exact prefixLift 398397
  have htrace : WordTrace (prefixWord ++ tailWord_398397) baseStart_398397 baseEnd_398397 := by
    simpa [prefixWord, tailWord_398397, baseEnd_398397] using wordTrace_append hprefix tailTrace_398397
  have hstable : (prefixWord ++ tailWord_398397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398397).length < 2 ^ (prefixWord ++ tailWord_398397).sum := by decide
  have hdescent : baseEnd_398397 < baseStart_398397 := by decide
  rcases family_descends (prefixWord ++ tailWord_398397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398429 : List Nat := [1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_398429 : Nat := 118140960795 + 398429 * 2 ^ 59
def prefixEnd_398429 : Nat := 4983230072969 + 3 ^ 40 * 398429 * 2
def baseEnd_398429 : Nat := 121235901446119631647505

theorem tailTrace_398429 : CollatzResearch.WordTrace tailWord_398429 prefixEnd_398429 121235901446119631647505 := by
  unfold tailWord_398429
  simp only [CollatzResearch.WordTrace]
  refine ⟨14531899473567254100870341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9687932982378169400580227 14531899473567254100870341)
  ·
    refine ⟨2724731151293860143913189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14531899473567254100870341 2724731151293860143913189)
    ·
      refine ⟨510887090867598776983723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2724731151293860143913189 510887090867598776983723)
      ·
        refine ⟨766330636301398165475585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510887090867598776983723 766330636301398165475585)
        ·
          refine ⟨574747977226048624106689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766330636301398165475585 574747977226048624106689)
          ·
            refine ⟨431060982919536468080017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574747977226048624106689 431060982919536468080017)
            ·
              refine ⟨323295737189652351060013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431060982919536468080017 323295737189652351060013)
              ·
                refine ⟨121235901446119631647505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323295737189652351060013 121235901446119631647505)
                ·
                  rfl

theorem cell19_398429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_398429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398429 prefixEnd_398429 := by exact prefixLift 398429
  have htrace : WordTrace (prefixWord ++ tailWord_398429) baseStart_398429 baseEnd_398429 := by
    simpa [prefixWord, tailWord_398429, baseEnd_398429] using wordTrace_append hprefix tailTrace_398429
  have hstable : (prefixWord ++ tailWord_398429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398429).length < 2 ^ (prefixWord ++ tailWord_398429).sum := by decide
  have hdescent : baseEnd_398429 < baseStart_398429 := by decide
  rcases family_descends (prefixWord ++ tailWord_398429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398456 : List Nat := [2, 1, 2, 1, 1, 1, 11]
def baseStart_398456 : Nat := 118140960795 + 398456 * 2 ^ 59
def prefixEnd_398456 : Nat := 4983230072969 + 3 ^ 40 * 398456 * 2
def baseEnd_398456 : Nat := 40414705712197189682477

theorem tailTrace_398456 : CollatzResearch.WordTrace tailWord_398456 prefixEnd_398456 40414705712197189682477 := by
  unfold tailWord_398456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266442122234718856051611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9688589496312958474735481 7266442122234718856051611)
  ·
    refine ⟨10899663183352078284077417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7266442122234718856051611 10899663183352078284077417)
    ·
      refine ⟨8174747387514058713058063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10899663183352078284077417 8174747387514058713058063)
      ·
        refine ⟨12262121081271088069587095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8174747387514058713058063 12262121081271088069587095)
        ·
          refine ⟨18393181621906632104380643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12262121081271088069587095 18393181621906632104380643)
          ·
            refine ⟨27589772432859948156570965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18393181621906632104380643 27589772432859948156570965)
            ·
              refine ⟨40414705712197189682477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27589772432859948156570965 40414705712197189682477)
              ·
                rfl

theorem cell19_398456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_398456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398456 prefixEnd_398456 := by exact prefixLift 398456
  have htrace : WordTrace (prefixWord ++ tailWord_398456) baseStart_398456 baseEnd_398456 := by
    simpa [prefixWord, tailWord_398456, baseEnd_398456] using wordTrace_append hprefix tailTrace_398456
  have hstable : (prefixWord ++ tailWord_398456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398456).length < 2 ^ (prefixWord ++ tailWord_398456).sum := by decide
  have hdescent : baseEnd_398456 < baseStart_398456 := by decide
  rcases family_descends (prefixWord ++ tailWord_398456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398473 : List Nat := [1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_398473 : Nat := 118140960795 + 398473 * 2 ^ 59
def prefixEnd_398473 : Nat := 4983230072969 + 3 ^ 40 * 398473 * 2
def baseEnd_398473 : Nat := 121249289978740566669607

theorem tailTrace_398473 : CollatzResearch.WordTrace tailWord_398473 prefixEnd_398473 121249289978740566669607 := by
  unfold tailWord_398473
  simp only [CollatzResearch.WordTrace]
  refine ⟨14533504285407849615472073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9689002856938566410314715 14533504285407849615472073)
  ·
    refine ⟨10900128214055887211604055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14533504285407849615472073 10900128214055887211604055)
    ·
      refine ⟨16350192321083830817406083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900128214055887211604055 16350192321083830817406083)
      ·
        refine ⟨24525288481625746226109125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16350192321083830817406083 24525288481625746226109125)
        ·
          refine ⟨4598491590304827417395461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24525288481625746226109125 4598491590304827417395461)
          ·
            refine ⟨862217173182155140761649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4598491590304827417395461 862217173182155140761649)
            ·
              refine ⟨646662879886616355571237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862217173182155140761649 646662879886616355571237)
              ·
                refine ⟨121249289978740566669607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 646662879886616355571237 121249289978740566669607)
                ·
                  rfl

theorem cell19_398473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_398473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398473 prefixEnd_398473 := by exact prefixLift 398473
  have htrace : WordTrace (prefixWord ++ tailWord_398473) baseStart_398473 baseEnd_398473 := by
    simpa [prefixWord, tailWord_398473, baseEnd_398473] using wordTrace_append hprefix tailTrace_398473
  have hstable : (prefixWord ++ tailWord_398473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398473).length < 2 ^ (prefixWord ++ tailWord_398473).sum := by decide
  have hdescent : baseEnd_398473 < baseStart_398473 := by decide
  rcases family_descends (prefixWord ++ tailWord_398473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398492 : List Nat := [2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_398492 : Nat := 118140960795 + 398492 * 2 ^ 59
def prefixEnd_398492 : Nat := 4983230072969 + 3 ^ 40 * 398492 * 2
def baseEnd_398492 : Nat := 121255071390554152247333

theorem tailTrace_398492 : CollatzResearch.WordTrace tailWord_398492 prefixEnd_398492 121255071390554152247333 := by
  unfold tailWord_398492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7267098636169507930206865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9689464848226010573609153 7267098636169507930206865)
  ·
    refine ⟨5450323977127130947655149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7267098636169507930206865 5450323977127130947655149)
    ·
      refine ⟨2043871491422674105370681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5450323977127130947655149 2043871491422674105370681)
      ·
        refine ⟨1532903618567005579028011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043871491422674105370681 1532903618567005579028011)
        ·
          refine ⟨2299355427850508368542017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532903618567005579028011 2299355427850508368542017)
          ·
            refine ⟨1724516570887881276406513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299355427850508368542017 1724516570887881276406513)
            ·
              refine ⟨1293387428165910957304885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724516570887881276406513 1293387428165910957304885)
              ·
                refine ⟨121255071390554152247333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1293387428165910957304885 121255071390554152247333)
                ·
                  rfl

theorem cell19_398492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_398492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398492 prefixEnd_398492 := by exact prefixLift 398492
  have htrace : WordTrace (prefixWord ++ tailWord_398492) baseStart_398492 baseEnd_398492 := by
    simpa [prefixWord, tailWord_398492, baseEnd_398492] using wordTrace_append hprefix tailTrace_398492
  have hstable : (prefixWord ++ tailWord_398492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398492).length < 2 ^ (prefixWord ++ tailWord_398492).sum := by decide
  have hdescent : baseEnd_398492 < baseStart_398492 := by decide
  rcases family_descends (prefixWord ++ tailWord_398492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398509 : List Nat := [1, 5, 2, 1, 4, 6]
def baseStart_398509 : Nat := 118140960795 + 398509 * 2 ^ 59
def prefixEnd_398509 : Nat := 4983230072969 + 3 ^ 40 * 398509 * 2
def baseEnd_398509 : Nat := 13473360470300349985501

theorem tailTrace_398509 : CollatzResearch.WordTrace tailWord_398509 prefixEnd_398509 13473360470300349985501 := by
  unfold tailWord_398509
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534817313277427763782581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9689878208851618509188387 14534817313277427763782581)
  ·
    refine ⟨1362639123119758852854617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14534817313277427763782581 1362639123119758852854617)
    ·
      refine ⟨1021979342339819139640963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1362639123119758852854617 1021979342339819139640963)
      ·
        refine ⟨1532969013509728709461445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021979342339819139640963 1532969013509728709461445)
        ·
          refine ⟨287431690033074133024021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1532969013509728709461445 287431690033074133024021)
          ·
            refine ⟨13473360470300349985501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287431690033074133024021 13473360470300349985501)
            ·
              rfl

theorem cell19_398509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_398509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398509 prefixEnd_398509 := by exact prefixLift 398509
  have htrace : WordTrace (prefixWord ++ tailWord_398509) baseStart_398509 baseEnd_398509 := by
    simpa [prefixWord, tailWord_398509, baseEnd_398509] using wordTrace_append hprefix tailTrace_398509
  have hstable : (prefixWord ++ tailWord_398509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398509).length < 2 ^ (prefixWord ++ tailWord_398509).sum := by decide
  have hdescent : baseEnd_398509 < baseStart_398509 := by decide
  rcases family_descends (prefixWord ++ tailWord_398509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398528 : List Nat := [2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_398528 : Nat := 118140960795 + 398528 * 2 ^ 59
def prefixEnd_398528 : Nat := 4983230072969 + 3 ^ 40 * 398528 * 2
def baseEnd_398528 : Nat := 121266025644516735447235

theorem tailTrace_398528 : CollatzResearch.WordTrace tailWord_398528 prefixEnd_398528 121266025644516735447235 := by
  unfold tailWord_398528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7267755150104297004362119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9690340200139062672482825 7267755150104297004362119)
  ·
    refine ⟨10901632725156445506543179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7267755150104297004362119 10901632725156445506543179)
    ·
      refine ⟨16352449087734668259814769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10901632725156445506543179 16352449087734668259814769)
      ·
        refine ⟨12264336815801001194861077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16352449087734668259814769 12264336815801001194861077)
        ·
          refine ⟨574890788240671931009113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12264336815801001194861077 574890788240671931009113)
          ·
            refine ⟨431168091180503948256835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574890788240671931009113 431168091180503948256835)
            ·
              refine ⟨646752136770755922385253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431168091180503948256835 646752136770755922385253)
              ·
                refine ⟨121266025644516735447235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 646752136770755922385253 121266025644516735447235)
                ·
                  rfl

theorem cell19_398528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_398528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398528 prefixEnd_398528 := by exact prefixLift 398528
  have htrace : WordTrace (prefixWord ++ tailWord_398528) baseStart_398528 baseEnd_398528 := by
    simpa [prefixWord, tailWord_398528, baseEnd_398528] using wordTrace_append hprefix tailTrace_398528
  have hstable : (prefixWord ++ tailWord_398528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398528).length < 2 ^ (prefixWord ++ tailWord_398528).sum := by decide
  have hdescent : baseEnd_398528 < baseStart_398528 := by decide
  rcases family_descends (prefixWord ++ tailWord_398528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398551 : List Nat := [1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_398551 : Nat := 118140960795 + 398551 * 2 ^ 59
def prefixEnd_398551 : Nat := 4983230072969 + 3 ^ 40 * 398551 * 2
def baseEnd_398551 : Nat := 121273024195659496936061

theorem tailTrace_398551 : CollatzResearch.WordTrace tailWord_398551 prefixEnd_398551 121273024195659496936061 := by
  unfold tailWord_398551
  simp only [CollatzResearch.WordTrace]
  refine ⟨14536349179125268936811507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9690899452750179291207671 14536349179125268936811507)
  ·
    refine ⟨21804523768687903405217261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14536349179125268936811507 21804523768687903405217261)
    ·
      refine ⟨8176696413257963776956473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21804523768687903405217261 8176696413257963776956473)
      ·
        refine ⟨6132522309943472832717355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8176696413257963776956473 6132522309943472832717355)
        ·
          refine ⟨9198783464915209249076033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6132522309943472832717355 9198783464915209249076033)
          ·
            refine ⟨6899087598686406936807025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9198783464915209249076033 6899087598686406936807025)
            ·
              refine ⟨5174315699014805202605269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899087598686406936807025 5174315699014805202605269)
              ·
                refine ⟨121273024195659496936061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5174315699014805202605269 121273024195659496936061)
                ·
                  rfl

theorem cell19_398551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_398551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398551 prefixEnd_398551 := by exact prefixLift 398551
  have htrace : WordTrace (prefixWord ++ tailWord_398551) baseStart_398551 baseEnd_398551 := by
    simpa [prefixWord, tailWord_398551, baseEnd_398551] using wordTrace_append hprefix tailTrace_398551
  have hstable : (prefixWord ++ tailWord_398551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398551).length < 2 ^ (prefixWord ++ tailWord_398551).sum := by decide
  have hdescent : baseEnd_398551 < baseStart_398551 := by decide
  rcases family_descends (prefixWord ++ tailWord_398551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398604 : List Nat := [2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_398604 : Nat := 118140960795 + 398604 * 2 ^ 59
def prefixEnd_398604 : Nat := 4983230072969 + 3 ^ 40 * 398604 * 2
def baseEnd_398604 : Nat := 121289151291771077758139

theorem tailTrace_398604 : CollatzResearch.WordTrace tailWord_398604 prefixEnd_398604 121289151291771077758139 := by
  unfold tailWord_398604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269141123966629494245433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9692188165288839325660577 7269141123966629494245433)
  ·
    refine ⟨5451855842974972120684075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7269141123966629494245433 5451855842974972120684075)
    ·
      refine ⟨8177783764462458181026113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5451855842974972120684075 8177783764462458181026113)
      ·
        refine ⟨6133337823346843635769585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8177783764462458181026113 6133337823346843635769585)
        ·
          refine ⟨4600003367510132726827189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6133337823346843635769585 4600003367510132726827189)
          ·
            refine ⟨431250315704074943140049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4600003367510132726827189 431250315704074943140049)
            ·
              refine ⟨323437736778056207355037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431250315704074943140049 323437736778056207355037)
              ·
                refine ⟨121289151291771077758139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323437736778056207355037 121289151291771077758139)
                ·
                  rfl

theorem cell19_398604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_398604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398604 prefixEnd_398604 := by exact prefixLift 398604
  have htrace : WordTrace (prefixWord ++ tailWord_398604) baseStart_398604 baseEnd_398604 := by
    simpa [prefixWord, tailWord_398604, baseEnd_398604] using wordTrace_append hprefix tailTrace_398604
  have hstable : (prefixWord ++ tailWord_398604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398604).length < 2 ^ (prefixWord ++ tailWord_398604).sum := by decide
  have hdescent : baseEnd_398604 < baseStart_398604 := by decide
  rcases family_descends (prefixWord ++ tailWord_398604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398606 : List Nat := [4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_398606 : Nat := 118140960795 + 398606 * 2 ^ 59
def prefixEnd_398606 : Nat := 4983230072969 + 3 ^ 40 * 398606 * 2
def baseEnd_398606 : Nat := 121289759861435665713689

theorem tailTrace_398606 : CollatzResearch.WordTrace tailWord_398606 prefixEnd_398606 121289759861435665713689 := by
  unfold tailWord_398606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817294399240751666257959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9692236795950675553375781 1817294399240751666257959)
  ·
    refine ⟨2725941598861127499386939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1817294399240751666257959 2725941598861127499386939)
    ·
      refine ⟨4088912398291691249080409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2725941598861127499386939 4088912398291691249080409)
      ·
        refine ⟨3066684298718768436810307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4088912398291691249080409 3066684298718768436810307)
        ·
          refine ⟨4600026448078152655215461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066684298718768436810307 4600026448078152655215461)
          ·
            refine ⟨862504959014653622852899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4600026448078152655215461 862504959014653622852899)
            ·
              refine ⟨1293757438521980434279349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862504959014653622852899 1293757438521980434279349)
              ·
                refine ⟨121289759861435665713689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1293757438521980434279349 121289759861435665713689)
                ·
                  rfl

theorem cell19_398606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_398606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398606 prefixEnd_398606 := by exact prefixLift 398606
  have htrace : WordTrace (prefixWord ++ tailWord_398606) baseStart_398606 baseEnd_398606 := by
    simpa [prefixWord, tailWord_398606, baseEnd_398606] using wordTrace_append hprefix tailTrace_398606
  have hstable : (prefixWord ++ tailWord_398606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398606).length < 2 ^ (prefixWord ++ tailWord_398606).sum := by decide
  have hdescent : baseEnd_398606 < baseStart_398606 := by decide
  rcases family_descends (prefixWord ++ tailWord_398606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398623 : List Nat := [1, 1, 2, 4, 5, 1, 5]
def baseStart_398623 : Nat := 118140960795 + 398623 * 2 ^ 59
def prefixEnd_398623 : Nat := 4983230072969 + 3 ^ 40 * 398623 * 2
def baseEnd_398623 : Nat := 40431644234528221111955

theorem tailTrace_398623 : CollatzResearch.WordTrace tailWord_398623 prefixEnd_398623 40431644234528221111955 := by
  unfold tailWord_398623
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538975234864425233432523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9692650156576283488955015 14538975234864425233432523)
  ·
    refine ⟨21808462852296637850148785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14538975234864425233432523 21808462852296637850148785)
    ·
      refine ⟨16356347139222478387611589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21808462852296637850148785 16356347139222478387611589)
      ·
        refine ⟨3066815088604214697677173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16356347139222478387611589 3066815088604214697677173)
        ·
          refine ⟨287513914556645127907235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3066815088604214697677173 287513914556645127907235)
          ·
            refine ⟨431270871834967691860853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287513914556645127907235 431270871834967691860853)
            ·
              refine ⟨40431644234528221111955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 431270871834967691860853 40431644234528221111955)
              ·
                rfl

theorem cell19_398623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_398623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398623 prefixEnd_398623 := by exact prefixLift 398623
  have htrace : WordTrace (prefixWord ++ tailWord_398623) baseStart_398623 baseEnd_398623 := by
    simpa [prefixWord, tailWord_398623, baseEnd_398623] using wordTrace_append hprefix tailTrace_398623
  have hstable : (prefixWord ++ tailWord_398623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398623).length < 2 ^ (prefixWord ++ tailWord_398623).sum := by decide
  have hdescent : baseEnd_398623 < baseStart_398623 := by decide
  rcases family_descends (prefixWord ++ tailWord_398623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398627 : List Nat := [1, 1, 1, 4, 2, 3, 7]
def baseStart_398627 : Nat := 118140960795 + 398627 * 2 ^ 59
def prefixEnd_398627 : Nat := 4983230072969 + 3 ^ 40 * 398627 * 2
def baseEnd_398627 : Nat := 40432049947637946415655

theorem tailTrace_398627 : CollatzResearch.WordTrace tailWord_398627 prefixEnd_398627 40432049947637946415655 := by
  unfold tailWord_398627
  simp only [CollatzResearch.WordTrace]
  refine ⟨14539121126849933916578135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9692747417899955944385423 14539121126849933916578135)
  ·
    refine ⟨21808681690274900874867203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14539121126849933916578135 21808681690274900874867203)
    ·
      refine ⟨32713022535412351312300805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21808681690274900874867203 32713022535412351312300805)
      ·
        refine ⟨6133691725389815871056401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32713022535412351312300805 6133691725389815871056401)
        ·
          refine ⟨4600268794042361903292301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6133691725389815871056401 4600268794042361903292301)
          ·
            refine ⟨1725100797765885713734613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4600268794042361903292301 1725100797765885713734613)
            ·
              refine ⟨40432049947637946415655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1725100797765885713734613 40432049947637946415655)
              ·
                rfl

theorem cell19_398627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_398627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398627 prefixEnd_398627 := by exact prefixLift 398627
  have htrace : WordTrace (prefixWord ++ tailWord_398627) baseStart_398627 baseEnd_398627 := by
    simpa [prefixWord, tailWord_398627, baseEnd_398627] using wordTrace_append hprefix tailTrace_398627
  have hstable : (prefixWord ++ tailWord_398627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398627).length < 2 ^ (prefixWord ++ tailWord_398627).sum := by decide
  have hdescent : baseEnd_398627 < baseStart_398627 := by decide
  rcases family_descends (prefixWord ++ tailWord_398627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398665 : List Nat := [1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_398665 : Nat := 118140960795 + 398665 * 2 ^ 59
def prefixEnd_398665 : Nat := 4983230072969 + 3 ^ 40 * 398665 * 2
def baseEnd_398665 : Nat := 121307712666541010402417

theorem tailTrace_398665 : CollatzResearch.WordTrace tailWord_398665 prefixEnd_398665 121307712666541010402417 := by
  unfold tailWord_398665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540507100712266406461449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9693671400474844270974299 14540507100712266406461449)
  ·
    refine ⟨10905380325534199804846087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14540507100712266406461449 10905380325534199804846087)
    ·
      refine ⟨16358070488301299707269131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10905380325534199804846087 16358070488301299707269131)
      ·
        refine ⟨24537105732451949560903697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16358070488301299707269131 24537105732451949560903697)
        ·
          refine ⟨18402829299338962170677773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24537105732451949560903697 18402829299338962170677773)
          ·
            refine ⟨6901060987252110814004165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18402829299338962170677773 6901060987252110814004165)
            ·
              refine ⟨1293948935109770777625781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6901060987252110814004165 1293948935109770777625781)
              ·
                refine ⟨121307712666541010402417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1293948935109770777625781 121307712666541010402417)
                ·
                  rfl

theorem cell19_398665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_398665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398665 prefixEnd_398665 := by exact prefixLift 398665
  have htrace : WordTrace (prefixWord ++ tailWord_398665) baseStart_398665 baseEnd_398665 := by
    simpa [prefixWord, tailWord_398665, baseEnd_398665] using wordTrace_append hprefix tailTrace_398665
  have hstable : (prefixWord ++ tailWord_398665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398665).length < 2 ^ (prefixWord ++ tailWord_398665).sum := by decide
  have hdescent : baseEnd_398665 < baseStart_398665 := by decide
  rcases family_descends (prefixWord ++ tailWord_398665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398678 : List Nat := [5, 2, 3, 1, 8]
def baseStart_398678 : Nat := 118140960795 + 398678 * 2 ^ 59
def prefixEnd_398678 : Nat := 4983230072969 + 3 ^ 40 * 398678 * 2
def baseEnd_398678 : Nat := 4493024754420771559759

theorem tailTrace_398678 : CollatzResearch.WordTrace tailWord_398678 prefixEnd_398678 4493024754420771559759 := by
  unfold tailWord_398678
  simp only [CollatzResearch.WordTrace]
  refine ⟨908811328104073101667793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9693987499776779751123125 908811328104073101667793)
  ·
    refine ⟨681608496078054826250845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 908811328104073101667793 681608496078054826250845)
    ·
      refine ⟨255603186029270559844067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 681608496078054826250845 255603186029270559844067)
      ·
        refine ⟨383404779043905839766101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255603186029270559844067 383404779043905839766101)
        ·
          refine ⟨4493024754420771559759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 383404779043905839766101 4493024754420771559759)
          ·
            rfl

theorem cell19_398678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 8].length) (baseStart_398678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398678 prefixEnd_398678 := by exact prefixLift 398678
  have htrace : WordTrace (prefixWord ++ tailWord_398678) baseStart_398678 baseEnd_398678 := by
    simpa [prefixWord, tailWord_398678, baseEnd_398678] using wordTrace_append hprefix tailTrace_398678
  have hstable : (prefixWord ++ tailWord_398678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398678).length < 2 ^ (prefixWord ++ tailWord_398678).sum := by decide
  have hdescent : baseEnd_398678 < baseStart_398678 := by decide
  rcases family_descends (prefixWord ++ tailWord_398678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398684 : List Nat := [2, 2, 4, 11]
def baseStart_398684 : Nat := 118140960795 + 398684 * 2 ^ 59
def prefixEnd_398684 : Nat := 4983230072969 + 3 ^ 40 * 398684 * 2
def baseEnd_398684 : Nat := 1497697457757464147903

theorem tailTrace_398684 : CollatzResearch.WordTrace tailWord_398684 prefixEnd_398684 1497697457757464147903 := by
  unfold tailWord_398684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270600043821716325701553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9694133391762288434268737 7270600043821716325701553)
  ·
    refine ⟨5452950032866287244276165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7270600043821716325701553 5452950032866287244276165)
    ·
      refine ⟨1022428131162428858301781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5452950032866287244276165 1022428131162428858301781)
      ·
        refine ⟨1497697457757464147903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1022428131162428858301781 1497697457757464147903)
        ·
          rfl

theorem cell19_398684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 11].length) (baseStart_398684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398684 prefixEnd_398684 := by exact prefixLift 398684
  have htrace : WordTrace (prefixWord ++ tailWord_398684) baseStart_398684 baseEnd_398684 := by
    simpa [prefixWord, tailWord_398684, baseEnd_398684] using wordTrace_append hprefix tailTrace_398684
  have hstable : (prefixWord ++ tailWord_398684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398684).length < 2 ^ (prefixWord ++ tailWord_398684).sum := by decide
  have hdescent : baseEnd_398684 < baseStart_398684 := by decide
  rcases family_descends (prefixWord ++ tailWord_398684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398701 : List Nat := [1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_398701 : Nat := 118140960795 + 398701 * 2 ^ 59
def prefixEnd_398701 : Nat := 4983230072969 + 3 ^ 40 * 398701 * 2
def baseEnd_398701 : Nat := 121318666920503593602319

theorem tailTrace_398701 : CollatzResearch.WordTrace tailWord_398701 prefixEnd_398701 121318666920503593602319 := by
  unfold tailWord_398701
  simp only [CollatzResearch.WordTrace]
  refine ⟨14541820128581844554771957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9694546752387896369847971 14541820128581844554771957)
  ·
    refine ⟨1363295637054547927009871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14541820128581844554771957 1363295637054547927009871)
    ·
      refine ⟨2044943455581821890514807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363295637054547927009871 2044943455581821890514807)
      ·
        refine ⟨3067415183372732835772211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044943455581821890514807 3067415183372732835772211)
        ·
          refine ⟨4601122775059099253658317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067415183372732835772211 4601122775059099253658317)
          ·
            refine ⟨1725421040647162220121869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4601122775059099253658317 1725421040647162220121869)
            ·
              refine ⟨647032890242685832545701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1725421040647162220121869 647032890242685832545701)
              ·
                refine ⟨121318666920503593602319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647032890242685832545701 121318666920503593602319)
                ·
                  rfl

theorem cell19_398701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_398701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398701 prefixEnd_398701 := by exact prefixLift 398701
  have htrace : WordTrace (prefixWord ++ tailWord_398701) baseStart_398701 baseEnd_398701 := by
    simpa [prefixWord, tailWord_398701, baseEnd_398701] using wordTrace_append hprefix tailTrace_398701
  have hstable : (prefixWord ++ tailWord_398701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398701).length < 2 ^ (prefixWord ++ tailWord_398701).sum := by decide
  have hdescent : baseEnd_398701 < baseStart_398701 := by decide
  rcases family_descends (prefixWord ++ tailWord_398701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398777 : List Nat := [1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_398777 : Nat := 118140960795 + 398777 * 2 ^ 59
def prefixEnd_398777 : Nat := 4983230072969 + 3 ^ 40 * 398777 * 2
def baseEnd_398777 : Nat := 121341792567757935913223

theorem tailTrace_398777 : CollatzResearch.WordTrace tailWord_398777 prefixEnd_398777 121341792567757935913223 := by
  unfold tailWord_398777
  simp only [CollatzResearch.WordTrace]
  refine ⟨14544592076306509534538585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9696394717537673023025723 14544592076306509534538585)
  ·
    refine ⟨10908444057229882150903939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14544592076306509534538585 10908444057229882150903939)
    ·
      refine ⟨16362666085844823226355909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10908444057229882150903939 16362666085844823226355909)
      ·
        refine ⟨3067999891095904354941733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16362666085844823226355909 3067999891095904354941733)
        ·
          refine ⟨575249979580482066551575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3067999891095904354941733 575249979580482066551575)
          ·
            refine ⟨862874969370723099827363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575249979580482066551575 862874969370723099827363)
            ·
              refine ⟨1294312454056084649741045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862874969370723099827363 1294312454056084649741045)
              ·
                refine ⟨121341792567757935913223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1294312454056084649741045 121341792567757935913223)
                ·
                  rfl

theorem cell19_398777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_398777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398777 prefixEnd_398777 := by exact prefixLift 398777
  have htrace : WordTrace (prefixWord ++ tailWord_398777) baseStart_398777 baseEnd_398777 := by
    simpa [prefixWord, tailWord_398777, baseEnd_398777] using wordTrace_append hprefix tailTrace_398777
  have hstable : (prefixWord ++ tailWord_398777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398777).length < 2 ^ (prefixWord ++ tailWord_398777).sum := by decide
  have hdescent : baseEnd_398777 < baseStart_398777 := by decide
  rcases family_descends (prefixWord ++ tailWord_398777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398796 : List Nat := [2, 2, 1, 4, 2, 3, 5]
def baseStart_398796 : Nat := 118140960795 + 398796 * 2 ^ 59
def prefixEnd_398796 : Nat := 4983230072969 + 3 ^ 40 * 398796 * 2
def baseEnd_398796 : Nat := 40449191326523840496983

theorem tailTrace_398796 : CollatzResearch.WordTrace tailWord_398796 prefixEnd_398796 40449191326523840496983 := by
  unfold tailWord_398796
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272642531618837889740121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9696856708825117186320161 7272642531618837889740121)
  ·
    refine ⟨5454481898714128417305091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7272642531618837889740121 5454481898714128417305091)
    ·
      refine ⟨8181722848071192625957637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454481898714128417305091 8181722848071192625957637)
      ·
        refine ⟨1534073034013348617367057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8181722848071192625957637 1534073034013348617367057)
        ·
          refine ⟨1150554775510011463025293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534073034013348617367057 1150554775510011463025293)
          ·
            refine ⟨431458040816254298634485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1150554775510011463025293 431458040816254298634485)
            ·
              refine ⟨40449191326523840496983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 431458040816254298634485 40449191326523840496983)
              ·
                rfl

theorem cell19_398796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_398796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398796 prefixEnd_398796 := by exact prefixLift 398796
  have htrace : WordTrace (prefixWord ++ tailWord_398796) baseStart_398796 baseEnd_398796 := by
    simpa [prefixWord, tailWord_398796, baseEnd_398796] using wordTrace_append hprefix tailTrace_398796
  have hstable : (prefixWord ++ tailWord_398796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398796).length < 2 ^ (prefixWord ++ tailWord_398796).sum := by decide
  have hdescent : baseEnd_398796 < baseStart_398796 := by decide
  rcases family_descends (prefixWord ++ tailWord_398796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398798 : List Nat := [4, 1, 1, 1, 2, 1, 9]
def baseStart_398798 : Nat := 118140960795 + 398798 * 2 ^ 59
def prefixEnd_398798 : Nat := 4983230072969 + 3 ^ 40 * 398798 * 2
def baseEnd_398798 : Nat := 40449394183078703148833

theorem tailTrace_398798 : CollatzResearch.WordTrace tailWord_398798 prefixEnd_398798 40449394183078703148833 := by
  unfold tailWord_398798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818169751153803765131631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9696905339486953414035365 1818169751153803765131631)
  ·
    refine ⟨2727254626730705647697447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1818169751153803765131631 2727254626730705647697447)
    ·
      refine ⟨4090881940096058471546171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727254626730705647697447 4090881940096058471546171)
      ·
        refine ⟨6136322910144087707319257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090881940096058471546171 6136322910144087707319257)
        ·
          refine ⟨4602242182608065780489443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6136322910144087707319257 4602242182608065780489443)
          ·
            refine ⟨6903363273912098670734165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602242182608065780489443 6903363273912098670734165)
            ·
              refine ⟨40449394183078703148833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6903363273912098670734165 40449394183078703148833)
              ·
                rfl

theorem cell19_398798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_398798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398798 prefixEnd_398798 := by exact prefixLift 398798
  have htrace : WordTrace (prefixWord ++ tailWord_398798) baseStart_398798 baseEnd_398798 := by
    simpa [prefixWord, tailWord_398798, baseEnd_398798] using wordTrace_append hprefix tailTrace_398798
  have hstable : (prefixWord ++ tailWord_398798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398798).length < 2 ^ (prefixWord ++ tailWord_398798).sum := by decide
  have hdescent : baseEnd_398798 < baseStart_398798 := by decide
  rcases family_descends (prefixWord ++ tailWord_398798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398817 : List Nat := [1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_398817 : Nat := 118140960795 + 398817 * 2 ^ 59
def prefixEnd_398817 : Nat := 4983230072969 + 3 ^ 40 * 398817 * 2
def baseEnd_398817 : Nat := 121353963961049695024225

theorem tailTrace_398817 : CollatzResearch.WordTrace tailWord_398817 prefixEnd_398817 121353963961049695024225 := by
  unfold tailWord_398817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14546050996161596365994705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9697367330774397577329803 14546050996161596365994705)
  ·
    refine ⟨10909538247121197274496029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14546050996161596365994705 10909538247121197274496029)
    ·
      refine ⟨4091076842670448977936011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10909538247121197274496029 4091076842670448977936011)
      ·
        refine ⟨6136615264005673466904017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091076842670448977936011 6136615264005673466904017)
        ·
          refine ⟨4602461448004255100178013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6136615264005673466904017 4602461448004255100178013)
          ·
            refine ⟨1725923043001595662566755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4602461448004255100178013 1725923043001595662566755)
            ·
              refine ⟨2588884564502393493850133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725923043001595662566755 2588884564502393493850133)
              ·
                refine ⟨121353963961049695024225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2588884564502393493850133 121353963961049695024225)
                ·
                  rfl

theorem cell19_398817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_398817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398817 prefixEnd_398817 := by exact prefixLift 398817
  have htrace : WordTrace (prefixWord ++ tailWord_398817) baseStart_398817 baseEnd_398817 := by
    simpa [prefixWord, tailWord_398817, baseEnd_398817] using wordTrace_append hprefix tailTrace_398817
  have hstable : (prefixWord ++ tailWord_398817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398817).length < 2 ^ (prefixWord ++ tailWord_398817).sum := by decide
  have hdescent : baseEnd_398817 < baseStart_398817 := by decide
  rcases family_descends (prefixWord ++ tailWord_398817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398834 : List Nat := [3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_398834 : Nat := 118140960795 + 398834 * 2 ^ 59
def prefixEnd_398834 : Nat := 4983230072969 + 3 ^ 40 * 398834 * 2
def baseEnd_398834 : Nat := 121359136803198692646401

theorem tailTrace_398834 : CollatzResearch.WordTrace tailWord_398834 prefixEnd_398834 121359136803198692646401 := by
  unfold tailWord_398834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636667759275002067340889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9697780691400005512909037 3636667759275002067340889)
  ·
    refine ⟨2727500819456251550505667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3636667759275002067340889 2727500819456251550505667)
    ·
      refine ⟨4091251229184377325758501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727500819456251550505667 4091251229184377325758501)
      ·
        refine ⟨767109605472070748579719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4091251229184377325758501 767109605472070748579719)
        ·
          refine ⟨1150664408208106122869579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767109605472070748579719 1150664408208106122869579)
          ·
            refine ⟨1725996612312159184304369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150664408208106122869579 1725996612312159184304369)
            ·
              refine ⟨1294497459234119388228277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725996612312159184304369 1294497459234119388228277)
              ·
                refine ⟨121359136803198692646401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1294497459234119388228277 121359136803198692646401)
                ·
                  rfl

theorem cell19_398834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_398834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398834 prefixEnd_398834 := by exact prefixLift 398834
  have htrace : WordTrace (prefixWord ++ tailWord_398834) baseStart_398834 baseEnd_398834 := by
    simpa [prefixWord, tailWord_398834, baseEnd_398834] using wordTrace_append hprefix tailTrace_398834
  have hstable : (prefixWord ++ tailWord_398834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398834).length < 2 ^ (prefixWord ++ tailWord_398834).sum := by decide
  have hdescent : baseEnd_398834 < baseStart_398834 := by decide
  rcases family_descends (prefixWord ++ tailWord_398834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398855 : List Nat := [1, 1, 4, 3, 2, 8]
def baseStart_398855 : Nat := 118140960795 + 398855 * 2 ^ 59
def prefixEnd_398855 : Nat := 4983230072969 + 3 ^ 40 * 398855 * 2
def baseEnd_398855 : Nat := 13485058531630762908853

theorem tailTrace_398855 : CollatzResearch.WordTrace tailWord_398855 prefixEnd_398855 13485058531630762908853 := by
  unfold tailWord_398855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14547436970023928855878019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9698291313349285903918679 14547436970023928855878019)
  ·
    refine ⟨21821155455035893283817029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14547436970023928855878019 21821155455035893283817029)
    ·
      refine ⟨4091466647819229990715693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21821155455035893283817029 4091466647819229990715693)
      ·
        refine ⟨1534299992932211246518385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4091466647819229990715693 1534299992932211246518385)
        ·
          refine ⟨1150724994699158434888789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534299992932211246518385 1150724994699158434888789)
          ·
            refine ⟨13485058531630762908853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1150724994699158434888789 13485058531630762908853)
            ·
              rfl

theorem cell19_398855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_398855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398855 prefixEnd_398855 := by exact prefixLift 398855
  have htrace : WordTrace (prefixWord ++ tailWord_398855) baseStart_398855 baseEnd_398855 := by
    simpa [prefixWord, tailWord_398855, baseEnd_398855] using wordTrace_append hprefix tailTrace_398855
  have hstable : (prefixWord ++ tailWord_398855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398855).length < 2 ^ (prefixWord ++ tailWord_398855).sum := by decide
  have hdescent : baseEnd_398855 < baseStart_398855 := by decide
  rcases family_descends (prefixWord ++ tailWord_398855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398868 : List Nat := [2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_398868 : Nat := 118140960795 + 398868 * 2 ^ 59
def prefixEnd_398868 : Nat := 4983230072969 + 3 ^ 40 * 398868 * 2
def baseEnd_398868 : Nat := 121369482487496687890753

theorem tailTrace_398868 : CollatzResearch.WordTrace tailWord_398868 prefixEnd_398868 121369482487496687890753 := by
  unfold tailWord_398868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273955559488416038050629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9698607412651221384067505 7273955559488416038050629)
  ·
    refine ⟨1363866667404078007134493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7273955559488416038050629 1363866667404078007134493)
    ·
      refine ⟨511450000276529252675435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1363866667404078007134493 511450000276529252675435)
      ·
        refine ⟨767175000414793879013153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511450000276529252675435 767175000414793879013153)
        ·
          refine ⟨575381250311095409259865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767175000414793879013153 575381250311095409259865)
          ·
            refine ⟨431535937733321556944899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575381250311095409259865 431535937733321556944899)
            ·
              refine ⟨647303906599982335417349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431535937733321556944899 647303906599982335417349)
              ·
                refine ⟨121369482487496687890753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647303906599982335417349 121369482487496687890753)
                ·
                  rfl

theorem cell19_398868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_398868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398868 prefixEnd_398868 := by exact prefixLift 398868
  have htrace : WordTrace (prefixWord ++ tailWord_398868) baseStart_398868 baseEnd_398868 := by
    simpa [prefixWord, tailWord_398868, baseEnd_398868] using wordTrace_append hprefix tailTrace_398868
  have hstable : (prefixWord ++ tailWord_398868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398868).length < 2 ^ (prefixWord ++ tailWord_398868).sum := by decide
  have hdescent : baseEnd_398868 < baseStart_398868 := by decide
  rcases family_descends (prefixWord ++ tailWord_398868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398948 : List Nat := [2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_398948 : Nat := 118140960795 + 398948 * 2 ^ 59
def prefixEnd_398948 : Nat := 4983230072969 + 3 ^ 40 * 398948 * 2
def baseEnd_398948 : Nat := 121393825274080206112757

theorem tailTrace_398948 : CollatzResearch.WordTrace tailWord_398948 prefixEnd_398948 121393825274080206112757 := by
  unfold tailWord_398948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7275414479343502869506749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9700552639124670492675665 7275414479343502869506749)
  ·
    refine ⟨2728280429753813576065031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7275414479343502869506749 2728280429753813576065031)
    ·
      refine ⟨4092420644630720364097547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728280429753813576065031 4092420644630720364097547)
      ·
        refine ⟨6138630966946080546146321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092420644630720364097547 6138630966946080546146321)
        ·
          refine ⟨4603973225209560409609741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6138630966946080546146321 4603973225209560409609741)
          ·
            refine ⟨1726489959453585153603653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4603973225209560409609741 1726489959453585153603653)
            ·
              refine ⟨323716867397547216300685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1726489959453585153603653 323716867397547216300685)
              ·
                refine ⟨121393825274080206112757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323716867397547216300685 121393825274080206112757)
                ·
                  rfl

theorem cell19_398948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_398948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398948 prefixEnd_398948 := by exact prefixLift 398948
  have htrace : WordTrace (prefixWord ++ tailWord_398948) baseStart_398948 baseEnd_398948 := by
    simpa [prefixWord, tailWord_398948, baseEnd_398948] using wordTrace_append hprefix tailTrace_398948
  have hstable : (prefixWord ++ tailWord_398948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398948).length < 2 ^ (prefixWord ++ tailWord_398948).sum := by decide
  have hdescent : baseEnd_398948 < baseStart_398948 := by decide
  rcases family_descends (prefixWord ++ tailWord_398948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398984 : List Nat := [2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_398984 : Nat := 118140960795 + 398984 * 2 ^ 59
def prefixEnd_398984 : Nat := 4983230072969 + 3 ^ 40 * 398984 * 2
def baseEnd_398984 : Nat := 121404779528042789312659

theorem tailTrace_398984 : CollatzResearch.WordTrace tailWord_398984 prefixEnd_398984 121404779528042789312659 := by
  unfold tailWord_398984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276070993278291943662003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9701427991037722591549337 7276070993278291943662003)
  ·
    refine ⟨10914106489917437915493005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7276070993278291943662003 10914106489917437915493005)
    ·
      refine ⟨4092789933719039218309877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10914106489917437915493005 4092789933719039218309877)
      ·
        refine ⟨383699056286159926716551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4092789933719039218309877 383699056286159926716551)
        ·
          refine ⟨575548584429239890074827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383699056286159926716551 575548584429239890074827)
          ·
            refine ⟨863322876643859835112241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575548584429239890074827 863322876643859835112241)
            ·
              refine ⟨647492157482894876334181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863322876643859835112241 647492157482894876334181)
              ·
                refine ⟨121404779528042789312659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647492157482894876334181 121404779528042789312659)
                ·
                  rfl

theorem cell19_398984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_398984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398984 prefixEnd_398984 := by exact prefixLift 398984
  have htrace : WordTrace (prefixWord ++ tailWord_398984) baseStart_398984 baseEnd_398984 := by
    simpa [prefixWord, tailWord_398984, baseEnd_398984] using wordTrace_append hprefix tailTrace_398984
  have hstable : (prefixWord ++ tailWord_398984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398984).length < 2 ^ (prefixWord ++ tailWord_398984).sum := by decide
  have hdescent : baseEnd_398984 < baseStart_398984 := by decide
  rcases family_descends (prefixWord ++ tailWord_398984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398986 : List Nat := [3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_398986 : Nat := 118140960795 + 398986 * 2 ^ 59
def prefixEnd_398986 : Nat := 4983230072969 + 3 ^ 40 * 398986 * 2
def baseEnd_398986 : Nat := 121405388097707377268209

theorem tailTrace_398986 : CollatzResearch.WordTrace tailWord_398986 prefixEnd_398986 121405388097707377268209 := by
  unfold tailWord_398986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638053733137334557224203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9701476621699558819264541 3638053733137334557224203)
  ·
    refine ⟨5457080599706001835836305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3638053733137334557224203 5457080599706001835836305)
    ·
      refine ⟨4092810449779501376877229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5457080599706001835836305 4092810449779501376877229)
      ·
        refine ⟨1534803918667313016328961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4092810449779501376877229 1534803918667313016328961)
        ·
          refine ⟨1151102939000484762246721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534803918667313016328961 1151102939000484762246721)
          ·
            refine ⟨863327204250363571685041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151102939000484762246721 863327204250363571685041)
            ·
              refine ⟨647495403187772678763781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863327204250363571685041 647495403187772678763781)
              ·
                refine ⟨121405388097707377268209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647495403187772678763781 121405388097707377268209)
                ·
                  rfl

theorem cell19_398986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_398986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398986 prefixEnd_398986 := by exact prefixLift 398986
  have htrace : WordTrace (prefixWord ++ tailWord_398986) baseStart_398986 baseEnd_398986 := by
    simpa [prefixWord, tailWord_398986, baseEnd_398986] using wordTrace_append hprefix tailTrace_398986
  have hstable : (prefixWord ++ tailWord_398986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398986).length < 2 ^ (prefixWord ++ tailWord_398986).sum := by decide
  have hdescent : baseEnd_398986 < baseStart_398986 := by decide
  rcases family_descends (prefixWord ++ tailWord_398986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398988 : List Nat := [2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_398988 : Nat := 118140960795 + 398988 * 2 ^ 59
def prefixEnd_398988 : Nat := 4983230072969 + 3 ^ 40 * 398988 * 2
def baseEnd_398988 : Nat := 121405996667371965223759

theorem tailTrace_398988 : CollatzResearch.WordTrace tailWord_398988 prefixEnd_398988 121405996667371965223759 := by
  unfold tailWord_398988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276143939271046285234809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9701525252361395046979745 7276143939271046285234809)
  ·
    refine ⟨5457107954453284713926107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7276143939271046285234809 5457107954453284713926107)
    ·
      refine ⟨8185661931679927070889161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457107954453284713926107 8185661931679927070889161)
      ·
        refine ⟨6139246448759945303166871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8185661931679927070889161 6139246448759945303166871)
        ·
          refine ⟨9208869673139917954750307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139246448759945303166871 9208869673139917954750307)
          ·
            refine ⟨13813304509709876932125461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208869673139917954750307 13813304509709876932125461)
            ·
              refine ⟨647498648892650481193381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13813304509709876932125461 647498648892650481193381)
              ·
                refine ⟨121405996667371965223759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647498648892650481193381 121405996667371965223759)
                ·
                  rfl

theorem cell19_398988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_398988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_398988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_398988 prefixEnd_398988 := by exact prefixLift 398988
  have htrace : WordTrace (prefixWord ++ tailWord_398988) baseStart_398988 baseEnd_398988 := by
    simpa [prefixWord, tailWord_398988, baseEnd_398988] using wordTrace_append hprefix tailTrace_398988
  have hstable : (prefixWord ++ tailWord_398988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398988).length < 2 ^ (prefixWord ++ tailWord_398988).sum := by decide
  have hdescent : baseEnd_398988 < baseStart_398988 := by decide
  rcases family_descends (prefixWord ++ tailWord_398988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399022 : List Nat := [4, 1, 4, 1, 3, 6]
def baseStart_399022 : Nat := 118140960795 + 399022 * 2 ^ 59
def prefixEnd_399022 : Nat := 4983230072969 + 3 ^ 40 * 399022 * 2
def baseEnd_399022 : Nat := 13490704705741106718679

theorem tailTrace_399022 : CollatzResearch.WordTrace tailWord_399022 prefixEnd_399022 13490704705741106718679 := by
  unfold tailWord_399022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819190995052364547150915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9702351973612610918138213 1819190995052364547150915)
  ·
    refine ⟨2728786492578546820726373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1819190995052364547150915 2728786492578546820726373)
    ·
      refine ⟨511647467358477528886195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2728786492578546820726373 511647467358477528886195)
      ·
        refine ⟨767471201037716293329293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511647467358477528886195 767471201037716293329293)
        ·
          refine ⟨287801700389143609998485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767471201037716293329293 287801700389143609998485)
          ·
            refine ⟨13490704705741106718679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287801700389143609998485 13490704705741106718679)
            ·
              rfl

theorem cell19_399022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_399022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399022 prefixEnd_399022 := by exact prefixLift 399022
  have htrace : WordTrace (prefixWord ++ tailWord_399022) baseStart_399022 baseEnd_399022 := by
    simpa [prefixWord, tailWord_399022, baseEnd_399022] using wordTrace_append hprefix tailTrace_399022
  have hstable : (prefixWord ++ tailWord_399022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399022).length < 2 ^ (prefixWord ++ tailWord_399022).sum := by decide
  have hdescent : baseEnd_399022 < baseStart_399022 := by decide
  rcases family_descends (prefixWord ++ tailWord_399022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399060 : List Nat := [2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_399060 : Nat := 118140960795 + 399060 * 2 ^ 59
def prefixEnd_399060 : Nat := 4983230072969 + 3 ^ 40 * 399060 * 2
def baseEnd_399060 : Nat := 121427905175297131623563

theorem tailTrace_399060 : CollatzResearch.WordTrace tailWord_399060 prefixEnd_399060 121427905175297131623563 := by
  unfold tailWord_399060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277456967140624433545317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9703275956187499244727089 7277456967140624433545317)
  ·
    refine ⟨1364523181338867081289747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7277456967140624433545317 1364523181338867081289747)
    ·
      refine ⟨2046784772008300621934621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1364523181338867081289747 2046784772008300621934621)
      ·
        refine ⟨767544289503112733225483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2046784772008300621934621 767544289503112733225483)
        ·
          refine ⟨1151316434254669099838225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767544289503112733225483 1151316434254669099838225)
          ·
            refine ⟨863487325691001824878669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151316434254669099838225 863487325691001824878669)
            ·
              refine ⟨323807747134125684329501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 863487325691001824878669 323807747134125684329501)
              ·
                refine ⟨121427905175297131623563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323807747134125684329501 121427905175297131623563)
                ·
                  rfl

theorem cell19_399060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_399060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399060 prefixEnd_399060 := by exact prefixLift 399060
  have htrace : WordTrace (prefixWord ++ tailWord_399060) baseStart_399060 baseEnd_399060 := by
    simpa [prefixWord, tailWord_399060, baseEnd_399060] using wordTrace_append hprefix tailTrace_399060
  have hstable : (prefixWord ++ tailWord_399060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399060).length < 2 ^ (prefixWord ++ tailWord_399060).sum := by decide
  have hdescent : baseEnd_399060 < baseStart_399060 := by decide
  rcases family_descends (prefixWord ++ tailWord_399060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399134 : List Nat := [4, 3, 2, 2, 1, 2, 5]
def baseStart_399134 : Nat := 118140960795 + 399134 * 2 ^ 59
def prefixEnd_399134 : Nat := 4983230072969 + 3 ^ 40 * 399134 * 2
def baseEnd_399134 : Nat := 40483474084295628659639

theorem tailTrace_399134 : CollatzResearch.WordTrace tailWord_399134 prefixEnd_399134 40483474084295628659639 := by
  unfold tailWord_399134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819701617001644938160557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9705075290675439670189637 1819701617001644938160557)
  ·
    refine ⟨682388106375616851810209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1819701617001644938160557 682388106375616851810209)
    ·
      refine ⟨511791079781712638857657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 682388106375616851810209 511791079781712638857657)
      ·
        refine ⟨383843309836284479143243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511791079781712638857657 383843309836284479143243)
        ·
          refine ⟨575764964754426718714865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383843309836284479143243 575764964754426718714865)
          ·
            refine ⟨431823723565820039036149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575764964754426718714865 431823723565820039036149)
            ·
              refine ⟨40483474084295628659639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 431823723565820039036149 40483474084295628659639)
              ·
                rfl

theorem cell19_399134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_399134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399134 prefixEnd_399134 := by exact prefixLift 399134
  have htrace : WordTrace (prefixWord ++ tailWord_399134) baseStart_399134 baseEnd_399134 := by
    simpa [prefixWord, tailWord_399134, baseEnd_399134] using wordTrace_append hprefix tailTrace_399134
  have hstable : (prefixWord ++ tailWord_399134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399134).length < 2 ^ (prefixWord ++ tailWord_399134).sum := by decide
  have hdescent : baseEnd_399134 < baseStart_399134 := by decide
  rcases family_descends (prefixWord ++ tailWord_399134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399140 : List Nat := [2, 3, 1, 3, 2, 1, 7]
def baseStart_399140 : Nat := 118140960795 + 399140 * 2 ^ 59
def prefixEnd_399140 : Nat := 4983230072969 + 3 ^ 40 * 399140 * 2
def baseEnd_399140 : Nat := 40484082653960216615189

theorem tailTrace_399140 : CollatzResearch.WordTrace tailWord_399140 prefixEnd_399140 40484082653960216615189 := by
  unfold tailWord_399140
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278915886995711265001437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9705221182660948353335249 7278915886995711265001437)
  ·
    refine ⟨2729593457623391724375539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7278915886995711265001437 2729593457623391724375539)
    ·
      refine ⟨4094390186435087586563309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2729593457623391724375539 4094390186435087586563309)
      ·
        refine ⟨1535396319913157844961241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4094390186435087586563309 1535396319913157844961241)
        ·
          refine ⟨1151547239934868383720931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535396319913157844961241 1151547239934868383720931)
          ·
            refine ⟨1727320859902302575581397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151547239934868383720931 1727320859902302575581397)
            ·
              refine ⟨40484082653960216615189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1727320859902302575581397 40484082653960216615189)
              ·
                rfl

theorem cell19_399140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_399140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399140 prefixEnd_399140 := by exact prefixLift 399140
  have htrace : WordTrace (prefixWord ++ tailWord_399140) baseStart_399140 baseEnd_399140 := by
    simpa [prefixWord, tailWord_399140, baseEnd_399140] using wordTrace_append hprefix tailTrace_399140
  have hstable : (prefixWord ++ tailWord_399140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399140).length < 2 ^ (prefixWord ++ tailWord_399140).sum := by decide
  have hdescent : baseEnd_399140 < baseStart_399140 := by decide
  rcases family_descends (prefixWord ++ tailWord_399140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399157 : List Nat := [1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_399157 : Nat := 118140960795 + 399157 * 2 ^ 59
def prefixEnd_399157 : Nat := 4983230072969 + 3 ^ 40 * 399157 * 2
def baseEnd_399157 : Nat := 121457420804029647467743

theorem tailTrace_399157 : CollatzResearch.WordTrace tailWord_399157 prefixEnd_399157 121457420804029647467743 := by
  unfold tailWord_399157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14558451814929834433371725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9705634543286556288914483 14558451814929834433371725)
  ·
    refine ⟨5459419430598687912514397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14558451814929834433371725 5459419430598687912514397)
    ·
      refine ⟨2047282286474507967192899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5459419430598687912514397 2047282286474507967192899)
      ·
        refine ⟨3070923429711761950789349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047282286474507967192899 3070923429711761950789349)
        ·
          refine ⟨575798143070955365773003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3070923429711761950789349 575798143070955365773003)
          ·
            refine ⟨863697214606433048659505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575798143070955365773003 863697214606433048659505)
            ·
              refine ⟨647772910954824786494629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863697214606433048659505 647772910954824786494629)
              ·
                refine ⟨121457420804029647467743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647772910954824786494629 121457420804029647467743)
                ·
                  rfl

theorem cell19_399157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_399157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399157 prefixEnd_399157 := by exact prefixLift 399157
  have htrace : WordTrace (prefixWord ++ tailWord_399157) baseStart_399157 baseEnd_399157 := by
    simpa [prefixWord, tailWord_399157, baseEnd_399157] using wordTrace_append hprefix tailTrace_399157
  have hstable : (prefixWord ++ tailWord_399157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399157).length < 2 ^ (prefixWord ++ tailWord_399157).sum := by decide
  have hdescent : baseEnd_399157 < baseStart_399157 := by decide
  rcases family_descends (prefixWord ++ tailWord_399157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399174 : List Nat := [6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_399174 : Nat := 118140960795 + 399174 * 2 ^ 59
def prefixEnd_399174 : Nat := 4983230072969 + 3 ^ 40 * 399174 * 2
def baseEnd_399174 : Nat := 121462593646178645089919

theorem tailTrace_399174 : CollatzResearch.WordTrace tailWord_399174 prefixEnd_399174 121462593646178645089919 := by
  unfold tailWord_399174
  simp only [CollatzResearch.WordTrace]
  refine ⟨454970995495882698023143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9706047903912164224493717 454970995495882698023143)
  ·
    refine ⟨682456493243824047034715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454970995495882698023143 682456493243824047034715)
    ·
      refine ⟨1023684739865736070552073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682456493243824047034715 1023684739865736070552073)
      ·
        refine ⟨767763554899302052914055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023684739865736070552073 767763554899302052914055)
        ·
          refine ⟨1151645332348953079371083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767763554899302052914055 1151645332348953079371083)
          ·
            refine ⟨1727467998523429619056625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151645332348953079371083 1727467998523429619056625)
            ·
              refine ⟨1295600998892572214292469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727467998523429619056625 1295600998892572214292469)
              ·
                refine ⟨121462593646178645089919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1295600998892572214292469 121462593646178645089919)
                ·
                  rfl

theorem cell19_399174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_399174 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399174 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399174 prefixEnd_399174 := by exact prefixLift 399174
  have htrace : WordTrace (prefixWord ++ tailWord_399174) baseStart_399174 baseEnd_399174 := by
    simpa [prefixWord, tailWord_399174, baseEnd_399174] using wordTrace_append hprefix tailTrace_399174
  have hstable : (prefixWord ++ tailWord_399174).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399174).length < 2 ^ (prefixWord ++ tailWord_399174).sum := by decide
  have hdescent : baseEnd_399174 < baseStart_399174 := by decide
  rcases family_descends (prefixWord ++ tailWord_399174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399199 : List Nat := [1, 1, 2, 3, 1, 11]
def baseStart_399199 : Nat := 118140960795 + 399199 * 2 ^ 59
def prefixEnd_399199 : Nat := 4983230072969 + 3 ^ 40 * 399199 * 2
def baseEnd_399199 : Nat := 13496688974109554948255

theorem tailTrace_399199 : CollatzResearch.WordTrace tailWord_399199 prefixEnd_399199 13496688974109554948255 := by
  unfold tailWord_399199
  simp only [CollatzResearch.WordTrace]
  refine ⟨14559983680777675606400651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9706655787185117070933767 14559983680777675606400651)
  ·
    refine ⟨21839975521166513409600977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14559983680777675606400651 21839975521166513409600977)
    ·
      refine ⟨16379981640874885057200733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21839975521166513409600977 16379981640874885057200733)
      ·
        refine ⟨6142493115328081896450275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16379981640874885057200733 6142493115328081896450275)
        ·
          refine ⟨9213739672992122844675413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6142493115328081896450275 9213739672992122844675413)
          ·
            refine ⟨13496688974109554948255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9213739672992122844675413 13496688974109554948255)
            ·
              rfl

theorem cell19_399199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_399199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399199 prefixEnd_399199 := by exact prefixLift 399199
  have htrace : WordTrace (prefixWord ++ tailWord_399199) baseStart_399199 baseEnd_399199 := by
    simpa [prefixWord, tailWord_399199, baseEnd_399199] using wordTrace_append hprefix tailTrace_399199
  have hstable : (prefixWord ++ tailWord_399199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399199).length < 2 ^ (prefixWord ++ tailWord_399199).sum := by decide
  have hdescent : baseEnd_399199 < baseStart_399199 := by decide
  rcases family_descends (prefixWord ++ tailWord_399199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399210 : List Nat := [3, 1, 3, 4, 2, 1, 1, 4]
def baseStart_399210 : Nat := 118140960795 + 399210 * 2 ^ 59
def prefixEnd_399210 : Nat := 4983230072969 + 3 ^ 40 * 399210 * 2
def baseEnd_399210 : Nat := 121473547900141228289821

theorem tailTrace_399210 : CollatzResearch.WordTrace tailWord_399210 prefixEnd_399210 121473547900141228289821 := by
  unfold tailWord_399210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640096220934456121262771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9706923255825216323367389 3640096220934456121262771)
  ·
    refine ⟨5460144331401684181894157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640096220934456121262771 5460144331401684181894157)
    ·
      refine ⟨2047554124275631568210309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5460144331401684181894157 2047554124275631568210309)
      ·
        refine ⟨383916398301680919039433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2047554124275631568210309 383916398301680919039433)
        ·
          refine ⟨287937298726260689279575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383916398301680919039433 287937298726260689279575)
          ·
            refine ⟨431905948089391033919363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287937298726260689279575 431905948089391033919363)
            ·
              refine ⟨647858922134086550879045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431905948089391033919363 647858922134086550879045)
              ·
                refine ⟨121473547900141228289821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647858922134086550879045 121473547900141228289821)
                ·
                  rfl

theorem cell19_399210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_399210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399210 prefixEnd_399210 := by exact prefixLift 399210
  have htrace : WordTrace (prefixWord ++ tailWord_399210) baseStart_399210 baseEnd_399210 := by
    simpa [prefixWord, tailWord_399210, baseEnd_399210] using wordTrace_append hprefix tailTrace_399210
  have hstable : (prefixWord ++ tailWord_399210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399210).length < 2 ^ (prefixWord ++ tailWord_399210).sum := by decide
  have hdescent : baseEnd_399210 < baseStart_399210 := by decide
  rcases family_descends (prefixWord ++ tailWord_399210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399214 : List Nat := [4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_399214 : Nat := 118140960795 + 399214 * 2 ^ 59
def prefixEnd_399214 : Nat := 4983230072969 + 3 ^ 40 * 399214 * 2
def baseEnd_399214 : Nat := 121474765039470404200921

theorem tailTrace_399214 : CollatzResearch.WordTrace tailWord_399214 prefixEnd_399214 121474765039470404200921 := by
  unfold tailWord_399214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820066346965416646024587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9707020517148888778797797 1820066346965416646024587)
  ·
    refine ⟨2730099520448124969036881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1820066346965416646024587 2730099520448124969036881)
    ·
      refine ⟨2047574640336093726777661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2730099520448124969036881 2047574640336093726777661)
      ·
        refine ⟨767840490126035147541623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2047574640336093726777661 767840490126035147541623)
        ·
          refine ⟨1151760735189052721312435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767840490126035147541623 1151760735189052721312435)
          ·
            refine ⟨1727641102783579081968653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151760735189052721312435 1727641102783579081968653)
            ·
              refine ⟨647865413543842155738245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1727641102783579081968653 647865413543842155738245)
              ·
                refine ⟨121474765039470404200921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 647865413543842155738245 121474765039470404200921)
                ·
                  rfl

theorem cell19_399214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_399214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399214 prefixEnd_399214 := by exact prefixLift 399214
  have htrace : WordTrace (prefixWord ++ tailWord_399214) baseStart_399214 baseEnd_399214 := by
    simpa [prefixWord, tailWord_399214, baseEnd_399214] using wordTrace_append hprefix tailTrace_399214
  have hstable : (prefixWord ++ tailWord_399214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399214).length < 2 ^ (prefixWord ++ tailWord_399214).sum := by decide
  have hdescent : baseEnd_399214 < baseStart_399214 := by decide
  rcases family_descends (prefixWord ++ tailWord_399214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399284 : List Nat := [2, 5, 2, 1, 3, 1, 2, 3]
def baseStart_399284 : Nat := 118140960795 + 399284 * 2 ^ 59
def prefixEnd_399284 : Nat := 4983230072969 + 3 ^ 40 * 399284 * 2
def baseEnd_399284 : Nat := 121496064977730982645175

theorem tailTrace_399284 : CollatzResearch.WordTrace tailWord_399284 prefixEnd_399284 121496064977730982645175 := by
  unfold tailWord_399284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7281541942734867561622453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9708722590313156748829937 7281541942734867561622453)
  ·
    refine ⟨682644557131393833902105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7281541942734867561622453 682644557131393833902105)
    ·
      refine ⟨511983417848545375426579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 682644557131393833902105 511983417848545375426579)
      ·
        refine ⟨767975126772818063139869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511983417848545375426579 767975126772818063139869)
        ·
          refine ⟨287990672539806773677451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767975126772818063139869 287990672539806773677451)
          ·
            refine ⟨431986008809710160516177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287990672539806773677451 431986008809710160516177)
            ·
              refine ⟨323989506607282620387133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431986008809710160516177 323989506607282620387133)
              ·
                refine ⟨121496064977730982645175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323989506607282620387133 121496064977730982645175)
                ·
                  rfl

theorem cell19_399284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_399284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399284 prefixEnd_399284 := by exact prefixLift 399284
  have htrace : WordTrace (prefixWord ++ tailWord_399284) baseStart_399284 baseEnd_399284 := by
    simpa [prefixWord, tailWord_399284, baseEnd_399284] using wordTrace_append hprefix tailTrace_399284
  have hstable : (prefixWord ++ tailWord_399284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399284).length < 2 ^ (prefixWord ++ tailWord_399284).sum := by decide
  have hdescent : baseEnd_399284 < baseStart_399284 := by decide
  rcases family_descends (prefixWord ++ tailWord_399284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399324 : List Nat := [2, 2, 6, 1, 1, 1, 2, 4]
def baseStart_399324 : Nat := 118140960795 + 399324 * 2 ^ 59
def prefixEnd_399324 : Nat := 4983230072969 + 3 ^ 40 * 399324 * 2
def baseEnd_399324 : Nat := 121508236371022741756177

theorem tailTrace_399324 : CollatzResearch.WordTrace tailWord_399324 prefixEnd_399324 121508236371022741756177 := by
  unfold tailWord_399324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282271402662410977350513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9709695203549881303134017 7282271402662410977350513)
  ·
    refine ⟨5461703551996808233012885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7282271402662410977350513 5461703551996808233012885)
    ·
      refine ⟨256017353999850385922479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5461703551996808233012885 256017353999850385922479)
      ·
        refine ⟨384026030999775578883719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256017353999850385922479 384026030999775578883719)
        ·
          refine ⟨576039046499663368325579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384026030999775578883719 576039046499663368325579)
          ·
            refine ⟨864058569749495052488369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576039046499663368325579 864058569749495052488369)
            ·
              refine ⟨648043927312121289366277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864058569749495052488369 648043927312121289366277)
              ·
                refine ⟨121508236371022741756177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648043927312121289366277 121508236371022741756177)
                ·
                  rfl

theorem cell19_399324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_399324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399324 prefixEnd_399324 := by exact prefixLift 399324
  have htrace : WordTrace (prefixWord ++ tailWord_399324) baseStart_399324 baseEnd_399324 := by
    simpa [prefixWord, tailWord_399324, baseEnd_399324] using wordTrace_append hprefix tailTrace_399324
  have hstable : (prefixWord ++ tailWord_399324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399324).length < 2 ^ (prefixWord ++ tailWord_399324).sum := by decide
  have hdescent : baseEnd_399324 < baseStart_399324 := by decide
  rcases family_descends (prefixWord ++ tailWord_399324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399370 : List Nat := [3, 1, 2, 2, 11]
def baseStart_399370 : Nat := 118140960795 + 399370 * 2 ^ 59
def prefixEnd_399370 : Nat := 4983230072969 + 3 ^ 40 * 399370 * 2
def baseEnd_399370 : Nat := 4500823461974380175327

theorem tailTrace_399370 : CollatzResearch.WordTrace tailWord_399370 prefixEnd_399370 4500823461974380175327 := by
  unfold tailWord_399370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641555140789542952718891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9710813708772114540583709 3641555140789542952718891)
  ·
    refine ⟨5462332711184314429078337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3641555140789542952718891 5462332711184314429078337)
    ·
      refine ⟨4096749533388235821808753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5462332711184314429078337 4096749533388235821808753)
      ·
        refine ⟨3072562150041176866356565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4096749533388235821808753 3072562150041176866356565)
        ·
          refine ⟨4500823461974380175327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3072562150041176866356565 4500823461974380175327)
          ·
            rfl

theorem cell19_399370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 11].length) (baseStart_399370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399370 prefixEnd_399370 := by exact prefixLift 399370
  have htrace : WordTrace (prefixWord ++ tailWord_399370) baseStart_399370 baseEnd_399370 := by
    simpa [prefixWord, tailWord_399370, baseEnd_399370] using wordTrace_append hprefix tailTrace_399370
  have hstable : (prefixWord ++ tailWord_399370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399370).length < 2 ^ (prefixWord ++ tailWord_399370).sum := by decide
  have hdescent : baseEnd_399370 < baseStart_399370 := by decide
  rcases family_descends (prefixWord ++ tailWord_399370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399383 : List Nat := [1, 1, 3, 5, 3, 1, 1, 4]
def baseStart_399383 : Nat := 118140960795 + 399383 * 2 ^ 59
def prefixEnd_399383 : Nat := 4983230072969 + 3 ^ 40 * 399383 * 2
def baseEnd_399383 : Nat := 121526189176128086444905

theorem tailTrace_399383 : CollatzResearch.WordTrace tailWord_399383 prefixEnd_399383 121526189176128086444905 := by
  unfold tailWord_399383
  simp only [CollatzResearch.WordTrace]
  refine ⟨14566694712111075031098803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9711129808074050020732535 14566694712111075031098803)
  ·
    refine ⟨21850042068166612546648205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14566694712111075031098803 21850042068166612546648205)
    ·
      refine ⟨8193765775562479704993077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21850042068166612546648205 8193765775562479704993077)
      ·
        refine ⟨768165541458982472343101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8193765775562479704993077 768165541458982472343101)
        ·
          refine ⟨288062078047118427128663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768165541458982472343101 288062078047118427128663)
          ·
            refine ⟨432093117070677640692995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288062078047118427128663 432093117070677640692995)
            ·
              refine ⟨648139675606016461039493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432093117070677640692995 648139675606016461039493)
              ·
                refine ⟨121526189176128086444905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648139675606016461039493 121526189176128086444905)
                ·
                  rfl

theorem cell19_399383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_399383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399383 prefixEnd_399383 := by exact prefixLift 399383
  have htrace : WordTrace (prefixWord ++ tailWord_399383) baseStart_399383 baseEnd_399383 := by
    simpa [prefixWord, tailWord_399383, baseEnd_399383] using wordTrace_append hprefix tailTrace_399383
  have hstable : (prefixWord ++ tailWord_399383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399383).length < 2 ^ (prefixWord ++ tailWord_399383).sum := by decide
  have hdescent : baseEnd_399383 < baseStart_399383 := by decide
  rcases family_descends (prefixWord ++ tailWord_399383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399425 : List Nat := [1, 2, 5, 1, 2, 2, 6]
def baseStart_399425 : Nat := 118140960795 + 399425 * 2 ^ 59
def prefixEnd_399425 : Nat := 4983230072969 + 3 ^ 40 * 399425 * 2
def baseEnd_399425 : Nat := 40512989713028144503819

theorem tailTrace_399425 : CollatzResearch.WordTrace tailWord_399425 prefixEnd_399425 40512989713028144503819 := by
  unfold tailWord_399425
  simp only [CollatzResearch.WordTrace]
  refine ⟨14568226577958916204127729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9712151051972610802751819 14568226577958916204127729)
  ·
    refine ⟨10926169933469187153095797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14568226577958916204127729 10926169933469187153095797)
    ·
      refine ⟨1024328431262736295602731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10926169933469187153095797 1024328431262736295602731)
      ·
        refine ⟨1536492646894104443404097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024328431262736295602731 1536492646894104443404097)
        ·
          refine ⟨1152369485170578332553073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536492646894104443404097 1152369485170578332553073)
          ·
            refine ⟨864277113877933749414805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152369485170578332553073 864277113877933749414805)
            ·
              refine ⟨40512989713028144503819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 864277113877933749414805 40512989713028144503819)
              ·
                rfl

theorem cell19_399425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_399425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399425 prefixEnd_399425 := by exact prefixLift 399425
  have htrace : WordTrace (prefixWord ++ tailWord_399425) baseStart_399425 baseEnd_399425 := by
    simpa [prefixWord, tailWord_399425, baseEnd_399425] using wordTrace_append hprefix tailTrace_399425
  have hstable : (prefixWord ++ tailWord_399425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399425).length < 2 ^ (prefixWord ++ tailWord_399425).sum := by decide
  have hdescent : baseEnd_399425 < baseStart_399425 := by decide
  rcases family_descends (prefixWord ++ tailWord_399425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399461 : List Nat := [1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_399461 : Nat := 118140960795 + 399461 * 2 ^ 59
def prefixEnd_399461 : Nat := 4983230072969 + 3 ^ 40 * 399461 * 2
def baseEnd_399461 : Nat := 121549923393047016711359

theorem tailTrace_399461 : CollatzResearch.WordTrace tailWord_399461 prefixEnd_399461 121549923393047016711359 := by
  unfold tailWord_399461
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569539605828494352438237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9713026403885662901625491 14569539605828494352438237)
  ·
    refine ⟨5463577352185685382164339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14569539605828494352438237 5463577352185685382164339)
    ·
      refine ⟨8195366028278528073246509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5463577352185685382164339 8195366028278528073246509)
      ·
        refine ⟨3073262260604448027467441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8195366028278528073246509 3073262260604448027467441)
        ·
          refine ⟨2304946695453336020600581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3073262260604448027467441 2304946695453336020600581)
          ·
            refine ⟨432177505397500503862609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2304946695453336020600581 432177505397500503862609)
            ·
              refine ⟨324133129048125377896957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432177505397500503862609 324133129048125377896957)
              ·
                refine ⟨121549923393047016711359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324133129048125377896957 121549923393047016711359)
                ·
                  rfl

theorem cell19_399461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_399461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399461 prefixEnd_399461 := by exact prefixLift 399461
  have htrace : WordTrace (prefixWord ++ tailWord_399461) baseStart_399461 baseEnd_399461 := by
    simpa [prefixWord, tailWord_399461, baseEnd_399461] using wordTrace_append hprefix tailTrace_399461
  have hstable : (prefixWord ++ tailWord_399461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399461).length < 2 ^ (prefixWord ++ tailWord_399461).sum := by decide
  have hdescent : baseEnd_399461 < baseStart_399461 := by decide
  rcases family_descends (prefixWord ++ tailWord_399461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399465 : List Nat := [1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_399465 : Nat := 118140960795 + 399465 * 2 ^ 59
def prefixEnd_399465 : Nat := 4983230072969 + 3 ^ 40 * 399465 * 2
def baseEnd_399465 : Nat := 121551140532376192622459

theorem tailTrace_399465 : CollatzResearch.WordTrace tailWord_399465 prefixEnd_399465 121551140532376192622459 := by
  unfold tailWord_399465
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569685497814003035583849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9713123665209335357055899 14569685497814003035583849)
  ·
    refine ⟨10927264123360502276687887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14569685497814003035583849 10927264123360502276687887)
    ·
      refine ⟨16390896185040753415031831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10927264123360502276687887 16390896185040753415031831)
      ·
        refine ⟨24586344277561130122547747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16390896185040753415031831 24586344277561130122547747)
        ·
          refine ⟨36879516416341695183821621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24586344277561130122547747 36879516416341695183821621)
          ·
            refine ⟨3457454664032033923483277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36879516416341695183821621 3457454664032033923483277)
            ·
              refine ⟨1296545499012012721306229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3457454664032033923483277 1296545499012012721306229)
              ·
                refine ⟨121551140532376192622459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1296545499012012721306229 121551140532376192622459)
                ·
                  rfl

theorem cell19_399465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_399465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399465 prefixEnd_399465 := by exact prefixLift 399465
  have htrace : WordTrace (prefixWord ++ tailWord_399465) baseStart_399465 baseEnd_399465 := by
    simpa [prefixWord, tailWord_399465, baseEnd_399465] using wordTrace_append hprefix tailTrace_399465
  have hstable : (prefixWord ++ tailWord_399465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399465).length < 2 ^ (prefixWord ++ tailWord_399465).sum := by decide
  have hdescent : baseEnd_399465 < baseStart_399465 := by decide
  rcases family_descends (prefixWord ++ tailWord_399465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399484 : List Nat := [2, 2, 2, 1, 1, 4, 7]
def baseStart_399484 : Nat := 118140960795 + 399484 * 2 ^ 59
def prefixEnd_399484 : Nat := 4983230072969 + 3 ^ 40 * 399484 * 2
def baseEnd_399484 : Nat := 40518973981396592733395

theorem tailTrace_399484 : CollatzResearch.WordTrace tailWord_399484 prefixEnd_399484 40518973981396592733395 := by
  unfold tailWord_399484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285189242372584640262753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9713585656496779520350337 7285189242372584640262753)
  ·
    refine ⟨5463891931779438480197065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7285189242372584640262753 5463891931779438480197065)
    ·
      refine ⟨4097918948834578860147799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5463891931779438480197065 4097918948834578860147799)
      ·
        refine ⟨6146878423251868290221699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097918948834578860147799 6146878423251868290221699)
        ·
          refine ⟨9220317634877802435332549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146878423251868290221699 9220317634877802435332549)
          ·
            refine ⟨1728809556539587956624853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9220317634877802435332549 1728809556539587956624853)
            ·
              refine ⟨40518973981396592733395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1728809556539587956624853 40518973981396592733395)
              ·
                rfl

theorem cell19_399484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_399484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399484 prefixEnd_399484 := by exact prefixLift 399484
  have htrace : WordTrace (prefixWord ++ tailWord_399484) baseStart_399484 baseEnd_399484 := by
    simpa [prefixWord, tailWord_399484, baseEnd_399484] using wordTrace_append hprefix tailTrace_399484
  have hstable : (prefixWord ++ tailWord_399484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399484).length < 2 ^ (prefixWord ++ tailWord_399484).sum := by decide
  have hdescent : baseEnd_399484 < baseStart_399484 := by decide
  rcases family_descends (prefixWord ++ tailWord_399484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399554 : List Nat := [3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_399554 : Nat := 118140960795 + 399554 * 2 ^ 59
def prefixEnd_399554 : Nat := 4983230072969 + 3 ^ 40 * 399554 * 2
def baseEnd_399554 : Nat := 121578221882450356644439

theorem tailTrace_399554 : CollatzResearch.WordTrace tailWord_399554 prefixEnd_399554 121578221882450356644439 := by
  unfold tailWord_399554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3643232898622892808893429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9715287729661047490382477 3643232898622892808893429)
  ·
    refine ⟨341553084245896200833759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3643232898622892808893429 341553084245896200833759)
    ·
      refine ⟨512329626368844301250639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341553084245896200833759 512329626368844301250639)
      ·
        refine ⟨768494439553266451875959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512329626368844301250639 768494439553266451875959)
        ·
          refine ⟨1152741659329899677813939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768494439553266451875959 1152741659329899677813939)
          ·
            refine ⟨1729112488994849516720909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152741659329899677813939 1729112488994849516720909)
            ·
              refine ⟨648417183373068568770341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1729112488994849516720909 648417183373068568770341)
              ·
                refine ⟨121578221882450356644439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648417183373068568770341 121578221882450356644439)
                ·
                  rfl

theorem cell19_399554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_399554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399554 prefixEnd_399554 := by exact prefixLift 399554
  have htrace : WordTrace (prefixWord ++ tailWord_399554) baseStart_399554 baseEnd_399554 := by
    simpa [prefixWord, tailWord_399554, baseEnd_399554] using wordTrace_append hprefix tailTrace_399554
  have hstable : (prefixWord ++ tailWord_399554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399554).length < 2 ^ (prefixWord ++ tailWord_399554).sum := by decide
  have hdescent : baseEnd_399554 < baseStart_399554 := by decide
  rcases family_descends (prefixWord ++ tailWord_399554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399556 : List Nat := [2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_399556 : Nat := 118140960795 + 399556 * 2 ^ 59
def prefixEnd_399556 : Nat := 4983230072969 + 3 ^ 40 * 399556 * 2
def baseEnd_399556 : Nat := 121578830452114944599989

theorem tailTrace_399556 : CollatzResearch.WordTrace tailWord_399556 prefixEnd_399556 121578830452114944599989 := by
  unfold tailWord_399556
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286502270242162788573261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9715336360322883718097681 7286502270242162788573261)
  ·
    refine ⟨2732438351340811045714973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7286502270242162788573261 2732438351340811045714973)
    ·
      refine ⟨1024664381752804142143115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2732438351340811045714973 1024664381752804142143115)
      ·
        refine ⟨1536996572629206213214673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024664381752804142143115 1536996572629206213214673)
        ·
          refine ⟨1152747429471904659911005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536996572629206213214673 1152747429471904659911005)
          ·
            refine ⟨432280286051964247466627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1152747429471904659911005 432280286051964247466627)
            ·
              refine ⟨648420429077946371199941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432280286051964247466627 648420429077946371199941)
              ·
                refine ⟨121578830452114944599989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648420429077946371199941 121578830452114944599989)
                ·
                  rfl

theorem cell19_399556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_399556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399556 prefixEnd_399556 := by exact prefixLift 399556
  have htrace : WordTrace (prefixWord ++ tailWord_399556) baseStart_399556 baseEnd_399556 := by
    simpa [prefixWord, tailWord_399556, baseEnd_399556] using wordTrace_append hprefix tailTrace_399556
  have hstable : (prefixWord ++ tailWord_399556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399556).length < 2 ^ (prefixWord ++ tailWord_399556).sum := by decide
  have hdescent : baseEnd_399556 < baseStart_399556 := by decide
  rcases family_descends (prefixWord ++ tailWord_399556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399617 : List Nat := [1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_399617 : Nat := 118140960795 + 399617 * 2 ^ 59
def prefixEnd_399617 : Nat := 4983230072969 + 3 ^ 40 * 399617 * 2
def baseEnd_399617 : Nat := 121597391826884877244267

theorem tailTrace_399617 : CollatzResearch.WordTrace tailWord_399617 prefixEnd_399617 121597391826884877244267 := by
  unfold tailWord_399617
  simp only [CollatzResearch.WordTrace]
  refine ⟨14575229393263332995117105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9716819595508888663411403 14575229393263332995117105)
  ·
    refine ⟨10931422044947499746337829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14575229393263332995117105 10931422044947499746337829)
    ·
      refine ⟨2049641633427656202438343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10931422044947499746337829 2049641633427656202438343)
      ·
        refine ⟨3074462450141484303657515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049641633427656202438343 3074462450141484303657515)
        ·
          refine ⟨4611693675212226455486273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074462450141484303657515 4611693675212226455486273)
          ·
            refine ⟨3458770256409169841614705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4611693675212226455486273 3458770256409169841614705)
            ·
              refine ⟨2594077692306877381211029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458770256409169841614705 2594077692306877381211029)
              ·
                refine ⟨121597391826884877244267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2594077692306877381211029 121597391826884877244267)
                ·
                  rfl

theorem cell19_399617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_399617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399617 prefixEnd_399617 := by exact prefixLift 399617
  have htrace : WordTrace (prefixWord ++ tailWord_399617) baseStart_399617 baseEnd_399617 := by
    simpa [prefixWord, tailWord_399617, baseEnd_399617] using wordTrace_append hprefix tailTrace_399617
  have hstable : (prefixWord ++ tailWord_399617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399617).length < 2 ^ (prefixWord ++ tailWord_399617).sum := by decide
  have hdescent : baseEnd_399617 < baseStart_399617 := by decide
  rcases family_descends (prefixWord ++ tailWord_399617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399653 : List Nat := [1, 3, 1, 2, 5, 2, 5]
def baseStart_399653 : Nat := 118140960795 + 399653 * 2 ^ 59
def prefixEnd_399653 : Nat := 4983230072969 + 3 ^ 40 * 399653 * 2
def baseEnd_399653 : Nat := 40536115360282486814723

theorem tailTrace_399653 : CollatzResearch.WordTrace tailWord_399653 prefixEnd_399653 40536115360282486814723 := by
  unfold tailWord_399653
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576542421132911143427613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9717694947421940762285075 14576542421132911143427613)
  ·
    refine ⟨5466203407924841678785355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14576542421132911143427613 5466203407924841678785355)
    ·
      refine ⟨8199305111887262518178033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5466203407924841678785355 8199305111887262518178033)
      ·
        refine ⟨6149478833915446888633525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8199305111887262518178033 6149478833915446888633525)
        ·
          refine ⟨576513640679573145809393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6149478833915446888633525 576513640679573145809393)
          ·
            refine ⟨432385230509679859357045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576513640679573145809393 432385230509679859357045)
            ·
              refine ⟨40536115360282486814723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 432385230509679859357045 40536115360282486814723)
              ·
                rfl

theorem cell19_399653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_399653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399653 prefixEnd_399653 := by exact prefixLift 399653
  have htrace : WordTrace (prefixWord ++ tailWord_399653) baseStart_399653 baseEnd_399653 := by
    simpa [prefixWord, tailWord_399653, baseEnd_399653] using wordTrace_append hprefix tailTrace_399653
  have hstable : (prefixWord ++ tailWord_399653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399653).length < 2 ^ (prefixWord ++ tailWord_399653).sum := by decide
  have hdescent : baseEnd_399653 < baseStart_399653 := by decide
  rcases family_descends (prefixWord ++ tailWord_399653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399674 : List Nat := [3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_399674 : Nat := 118140960795 + 399674 * 2 ^ 59
def prefixEnd_399674 : Nat := 4983230072969 + 3 ^ 40 * 399674 * 2
def baseEnd_399674 : Nat := 121614736062325633977445

theorem tailTrace_399674 : CollatzResearch.WordTrace tailWord_399674 prefixEnd_399674 121614736062325633977445 := by
  unfold tailWord_399674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644327088514207932485519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9718205569371221153294717 3644327088514207932485519)
  ·
    refine ⟨5466490632771311898728279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3644327088514207932485519 5466490632771311898728279)
    ·
      refine ⟨8199735949156967848092419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5466490632771311898728279 8199735949156967848092419)
      ·
        refine ⟨12299603923735451772138629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199735949156967848092419 12299603923735451772138629)
        ·
          refine ⟨2306175735700397207275993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12299603923735451772138629 2306175735700397207275993)
          ·
            refine ⟨1729631801775297905456995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306175735700397207275993 1729631801775297905456995)
            ·
              refine ⟨2594447702662946858185493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729631801775297905456995 2594447702662946858185493)
              ·
                refine ⟨121614736062325633977445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2594447702662946858185493 121614736062325633977445)
                ·
                  rfl

theorem cell19_399674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_399674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399674 prefixEnd_399674 := by exact prefixLift 399674
  have htrace : WordTrace (prefixWord ++ tailWord_399674) baseStart_399674 baseEnd_399674 := by
    simpa [prefixWord, tailWord_399674, baseEnd_399674] using wordTrace_append hprefix tailTrace_399674
  have hstable : (prefixWord ++ tailWord_399674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399674).length < 2 ^ (prefixWord ++ tailWord_399674).sum := by decide
  have hdescent : baseEnd_399674 < baseStart_399674 := by decide
  rcases family_descends (prefixWord ++ tailWord_399674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399708 : List Nat := [2, 2, 4, 3, 2, 6]
def baseStart_399708 : Nat := 118140960795 + 399708 * 2 ^ 59
def prefixEnd_399708 : Nat := 4983230072969 + 3 ^ 40 * 399708 * 2
def baseEnd_399708 : Nat := 13513897971847069913533

theorem tailTrace_399708 : CollatzResearch.WordTrace tailWord_399708 prefixEnd_399708 13513897971847069913533 := by
  unfold tailWord_399708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289274217966827768339889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9719032290622437024453185 7289274217966827768339889)
  ·
    refine ⟨5466955663475120826254917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7289274217966827768339889 5466955663475120826254917)
    ·
      refine ⟨1025054186901585154922797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5466955663475120826254917 1025054186901585154922797)
      ·
        refine ⟨384395320088094433096049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1025054186901585154922797 384395320088094433096049)
        ·
          refine ⟨288296490066070824822037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384395320088094433096049 288296490066070824822037)
          ·
            refine ⟨13513897971847069913533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 288296490066070824822037 13513897971847069913533)
            ·
              rfl

theorem cell19_399708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_399708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399708 prefixEnd_399708 := by exact prefixLift 399708
  have htrace : WordTrace (prefixWord ++ tailWord_399708) baseStart_399708 baseEnd_399708 := by
    simpa [prefixWord, tailWord_399708, baseEnd_399708] using wordTrace_append hprefix tailTrace_399708
  have hstable : (prefixWord ++ tailWord_399708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399708).length < 2 ^ (prefixWord ++ tailWord_399708).sum := by decide
  have hdescent : baseEnd_399708 < baseStart_399708 := by decide
  rcases family_descends (prefixWord ++ tailWord_399708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399712 : List Nat := [2, 1, 1, 3, 5, 7]
def baseStart_399712 : Nat := 118140960795 + 399712 * 2 ^ 59
def prefixEnd_399712 : Nat := 4983230072969 + 3 ^ 40 * 399712 * 2
def baseEnd_399712 : Nat := 13514033209550311681433

theorem tailTrace_399712 : CollatzResearch.WordTrace tailWord_399712 prefixEnd_399712 13514033209550311681433 := by
  unfold tailWord_399712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289347163959582109912695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9719129551946109479883593 7289347163959582109912695)
  ·
    refine ⟨10934020745939373164869043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7289347163959582109912695 10934020745939373164869043)
    ·
      refine ⟨16401031118909059747303565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10934020745939373164869043 16401031118909059747303565)
      ·
        refine ⟨6150386669590897405238837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16401031118909059747303565 6150386669590897405238837)
        ·
          refine ⟨576598750274146631741141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6150386669590897405238837 576598750274146631741141)
          ·
            refine ⟨13514033209550311681433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 576598750274146631741141 13514033209550311681433)
            ·
              rfl

theorem cell19_399712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_399712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399712 prefixEnd_399712 := by exact prefixLift 399712
  have htrace : WordTrace (prefixWord ++ tailWord_399712) baseStart_399712 baseEnd_399712 := by
    simpa [prefixWord, tailWord_399712, baseEnd_399712] using wordTrace_append hprefix tailTrace_399712
  have hstable : (prefixWord ++ tailWord_399712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399712).length < 2 ^ (prefixWord ++ tailWord_399712).sum := by decide
  have hdescent : baseEnd_399712 < baseStart_399712 := by decide
  rcases family_descends (prefixWord ++ tailWord_399712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399748 : List Nat := [2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_399748 : Nat := 118140960795 + 399748 * 2 ^ 59
def prefixEnd_399748 : Nat := 4983230072969 + 3 ^ 40 * 399748 * 2
def baseEnd_399748 : Nat := 121637253139915388332799

theorem tailTrace_399748 : CollatzResearch.WordTrace tailWord_399748 prefixEnd_399748 121637253139915388332799 := by
  unfold tailWord_399748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290003677894371184067949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9720004903859161578757265 7290003677894371184067949)
  ·
    refine ⟨2733751379210389194025481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7290003677894371184067949 2733751379210389194025481)
    ·
      refine ⟨2050313534407791895519111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2733751379210389194025481 2050313534407791895519111)
      ·
        refine ⟨3075470301611687843278667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050313534407791895519111 3075470301611687843278667)
        ·
          refine ⟨4613205452417531764918001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075470301611687843278667 4613205452417531764918001)
          ·
            refine ⟨3459904089313148823688501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613205452417531764918001 3459904089313148823688501)
            ·
              refine ⟨324366008373107702220797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3459904089313148823688501 324366008373107702220797)
              ·
                refine ⟨121637253139915388332799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324366008373107702220797 121637253139915388332799)
                ·
                  rfl

theorem cell19_399748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_399748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399748 prefixEnd_399748 := by exact prefixLift 399748
  have htrace : WordTrace (prefixWord ++ tailWord_399748) baseStart_399748 baseEnd_399748 := by
    simpa [prefixWord, tailWord_399748, baseEnd_399748] using wordTrace_append hprefix tailTrace_399748
  have hstable : (prefixWord ++ tailWord_399748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399748).length < 2 ^ (prefixWord ++ tailWord_399748).sum := by decide
  have hdescent : baseEnd_399748 < baseStart_399748 := by decide
  rcases family_descends (prefixWord ++ tailWord_399748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399805 : List Nat := [1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_399805 : Nat := 118140960795 + 399805 * 2 ^ 59
def prefixEnd_399805 : Nat := 4983230072969 + 3 ^ 40 * 399805 * 2
def baseEnd_399805 : Nat := 121654597375356145065977

theorem tailTrace_399805 : CollatzResearch.WordTrace tailWord_399805 prefixEnd_399805 121654597375356145065977 := by
  unfold tailWord_399805
  simp only [CollatzResearch.WordTrace]
  refine ⟨14582086316582241102960869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9721390877721494068640579 14582086316582241102960869)
  ·
    refine ⟨2734141184359170206805163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14582086316582241102960869 2734141184359170206805163)
    ·
      refine ⟨4101211776538755310207745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734141184359170206805163 4101211776538755310207745)
      ·
        refine ⟨3075908832404066482655809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4101211776538755310207745 3075908832404066482655809)
        ·
          refine ⟨2306931624303049861991857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3075908832404066482655809 2306931624303049861991857)
          ·
            refine ⟨1730198718227287396493893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306931624303049861991857 1730198718227287396493893)
            ·
              refine ⟨324412259667616386842605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1730198718227287396493893 324412259667616386842605)
              ·
                refine ⟨121654597375356145065977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324412259667616386842605 121654597375356145065977)
                ·
                  rfl

theorem cell19_399805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_399805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399805 prefixEnd_399805 := by exact prefixLift 399805
  have htrace : WordTrace (prefixWord ++ tailWord_399805) baseStart_399805 baseEnd_399805 := by
    simpa [prefixWord, tailWord_399805, baseEnd_399805] using wordTrace_append hprefix tailTrace_399805
  have hstable : (prefixWord ++ tailWord_399805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399805).length < 2 ^ (prefixWord ++ tailWord_399805).sum := by decide
  have hdescent : baseEnd_399805 < baseStart_399805 := by decide
  rcases family_descends (prefixWord ++ tailWord_399805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399843 : List Nat := [1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_399843 : Nat := 118140960795 + 399843 * 2 ^ 59
def prefixEnd_399843 : Nat := 4983230072969 + 3 ^ 40 * 399843 * 2
def baseEnd_399843 : Nat := 121666160198983316221429

theorem tailTrace_399843 : CollatzResearch.WordTrace tailWord_399843 prefixEnd_399843 121666160198983316221429 := by
  unfold tailWord_399843
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583472290444573592844183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9722314860296382395229455 14583472290444573592844183)
  ·
    refine ⟨21875208435666860389266275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14583472290444573592844183 21875208435666860389266275)
    ·
      refine ⟨32812812653500290583899413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21875208435666860389266275 32812812653500290583899413)
      ·
        refine ⟨1538100593132826121120285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32812812653500290583899413 1538100593132826121120285)
        ·
          refine ⟨576787722424809795420107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1538100593132826121120285 576787722424809795420107)
          ·
            refine ⟨865181583637214693130161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576787722424809795420107 865181583637214693130161)
            ·
              refine ⟨648886187727911019847621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865181583637214693130161 648886187727911019847621)
              ·
                refine ⟨121666160198983316221429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648886187727911019847621 121666160198983316221429)
                ·
                  rfl

theorem cell19_399843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_399843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399843 prefixEnd_399843 := by exact prefixLift 399843
  have htrace : WordTrace (prefixWord ++ tailWord_399843) baseStart_399843 baseEnd_399843 := by
    simpa [prefixWord, tailWord_399843, baseEnd_399843] using wordTrace_append hprefix tailTrace_399843
  have hstable : (prefixWord ++ tailWord_399843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399843).length < 2 ^ (prefixWord ++ tailWord_399843).sum := by decide
  have hdescent : baseEnd_399843 < baseStart_399843 := by decide
  rcases family_descends (prefixWord ++ tailWord_399843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399900 : List Nat := [2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_399900 : Nat := 118140960795 + 399900 * 2 ^ 59
def prefixEnd_399900 : Nat := 4983230072969 + 3 ^ 40 * 399900 * 2
def baseEnd_399900 : Nat := 121683504434424072954607

theorem tailTrace_399900 : CollatzResearch.WordTrace tailWord_399900 prefixEnd_399900 121683504434424072954607 := by
  unfold tailWord_399900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292775625619036163834577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9723700834158714885112769 7292775625619036163834577)
  ·
    refine ⟨5469581719214277122875933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7292775625619036163834577 5469581719214277122875933)
    ·
      refine ⟨2051093144705353921078475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5469581719214277122875933 2051093144705353921078475)
      ·
        refine ⟨3076639717058030881617713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051093144705353921078475 3076639717058030881617713)
        ·
          refine ⟨2307479787793523161213285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3076639717058030881617713 2307479787793523161213285)
          ·
            refine ⟨432652460211285592727491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2307479787793523161213285 432652460211285592727491)
            ·
              refine ⟨648978690316928389091237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432652460211285592727491 648978690316928389091237)
              ·
                refine ⟨121683504434424072954607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 648978690316928389091237 121683504434424072954607)
                ·
                  rfl

theorem cell19_399900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_399900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399900 prefixEnd_399900 := by exact prefixLift 399900
  have htrace : WordTrace (prefixWord ++ tailWord_399900) baseStart_399900 baseEnd_399900 := by
    simpa [prefixWord, tailWord_399900, baseEnd_399900] using wordTrace_append hprefix tailTrace_399900
  have hstable : (prefixWord ++ tailWord_399900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399900).length < 2 ^ (prefixWord ++ tailWord_399900).sum := by decide
  have hdescent : baseEnd_399900 < baseStart_399900 := by decide
  rcases family_descends (prefixWord ++ tailWord_399900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399970 : List Nat := [3, 3, 2, 3, 2, 1, 2, 3]
def baseStart_399970 : Nat := 118140960795 + 399970 * 2 ^ 59
def prefixEnd_399970 : Nat := 4983230072969 + 3 ^ 40 * 399970 * 2
def baseEnd_399970 : Nat := 121704804372684651398861

theorem tailTrace_399970 : CollatzResearch.WordTrace tailWord_399970 prefixEnd_399970 121704804372684651398861 := by
  unfold tailWord_399970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647026090246118570679341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9725402907322982855144909 3647026090246118570679341)
  ·
    refine ⟨1367634783842294464004753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3647026090246118570679341 1367634783842294464004753)
    ·
      refine ⟨1025726087881720848003565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1367634783842294464004753 1025726087881720848003565)
      ·
        refine ⟨384647282955645318001337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1025726087881720848003565 384647282955645318001337)
        ·
          refine ⟨288485462216733988501003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384647282955645318001337 288485462216733988501003)
          ·
            refine ⟨432728193325100982751505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288485462216733988501003 432728193325100982751505)
            ·
              refine ⟨324546144993825737063629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432728193325100982751505 324546144993825737063629)
              ·
                refine ⟨121704804372684651398861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324546144993825737063629 121704804372684651398861)
                ·
                  rfl

theorem cell19_399970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_399970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399970 prefixEnd_399970 := by exact prefixLift 399970
  have htrace : WordTrace (prefixWord ++ tailWord_399970) baseStart_399970 baseEnd_399970 := by
    simpa [prefixWord, tailWord_399970, baseEnd_399970] using wordTrace_append hprefix tailTrace_399970
  have hstable : (prefixWord ++ tailWord_399970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399970).length < 2 ^ (prefixWord ++ tailWord_399970).sum := by decide
  have hdescent : baseEnd_399970 < baseStart_399970 := by decide
  rcases family_descends (prefixWord ++ tailWord_399970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399976 : List Nat := [2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_399976 : Nat := 118140960795 + 399976 * 2 ^ 59
def prefixEnd_399976 : Nat := 4983230072969 + 3 ^ 40 * 399976 * 2
def baseEnd_399976 : Nat := 121706630081678415265511

theorem tailTrace_399976 : CollatzResearch.WordTrace tailWord_399976 prefixEnd_399976 121706630081678415265511 := by
  unfold tailWord_399976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294161599481368653717891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9725548799308491538290521 7294161599481368653717891)
  ·
    refine ⟨10941242399222052980576837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7294161599481368653717891 10941242399222052980576837)
    ·
      refine ⟨2051482949854134933858157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10941242399222052980576837 2051482949854134933858157)
      ·
        refine ⟨769306106195300600196809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2051482949854134933858157 769306106195300600196809)
        ·
          refine ⟨576979579646475450147607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769306106195300600196809 576979579646475450147607)
          ·
            refine ⟨865469369469713175221411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576979579646475450147607 865469369469713175221411)
            ·
              refine ⟨1298204054204569762832117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865469369469713175221411 1298204054204569762832117)
              ·
                refine ⟨121706630081678415265511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1298204054204569762832117 121706630081678415265511)
                ·
                  rfl

theorem cell19_399976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_399976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399976 prefixEnd_399976 := by exact prefixLift 399976
  have htrace : WordTrace (prefixWord ++ tailWord_399976) baseStart_399976 baseEnd_399976 := by
    simpa [prefixWord, tailWord_399976, baseEnd_399976] using wordTrace_append hprefix tailTrace_399976
  have hstable : (prefixWord ++ tailWord_399976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399976).length < 2 ^ (prefixWord ++ tailWord_399976).sum := by decide
  have hdescent : baseEnd_399976 < baseStart_399976 := by decide
  rcases family_descends (prefixWord ++ tailWord_399976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399978 : List Nat := [3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_399978 : Nat := 118140960795 + 399978 * 2 ^ 59
def prefixEnd_399978 : Nat := 4983230072969 + 3 ^ 40 * 399978 * 2
def baseEnd_399978 : Nat := 121707238651343003221061

theorem tailTrace_399978 : CollatzResearch.WordTrace tailWord_399978 prefixEnd_399978 121707238651343003221061 := by
  unfold tailWord_399978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647099036238872912252147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9725597429970327766005725 3647099036238872912252147)
  ·
    refine ⟨5470648554358309368378221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3647099036238872912252147 5470648554358309368378221)
    ·
      refine ⟨2051493207884366013141833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5470648554358309368378221 2051493207884366013141833)
      ·
        refine ⟨1538619905913274509856375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051493207884366013141833 1538619905913274509856375)
        ·
          refine ⟨2307929858869911764784563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538619905913274509856375 2307929858869911764784563)
          ·
            refine ⟨3461894788304867647176845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307929858869911764784563 3461894788304867647176845)
            ·
              refine ⟨1298210545614325367691317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3461894788304867647176845 1298210545614325367691317)
              ·
                refine ⟨121707238651343003221061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1298210545614325367691317 121707238651343003221061)
                ·
                  rfl

theorem cell19_399978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_399978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_399978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_399978 prefixEnd_399978 := by exact prefixLift 399978
  have htrace : WordTrace (prefixWord ++ tailWord_399978) baseStart_399978 baseEnd_399978 := by
    simpa [prefixWord, tailWord_399978, baseEnd_399978] using wordTrace_append hprefix tailTrace_399978
  have hstable : (prefixWord ++ tailWord_399978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399978).length < 2 ^ (prefixWord ++ tailWord_399978).sum := by decide
  have hdescent : baseEnd_399978 < baseStart_399978 := by decide
  rcases family_descends (prefixWord ++ tailWord_399978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400113 : List Nat := [1, 2, 2, 2, 2, 2, 8]
def baseStart_400113 : Nat := 118140960795 + 400113 * 2 ^ 59
def prefixEnd_400113 : Nat := 4983230072969 + 3 ^ 40 * 400113 * 2
def baseEnd_400113 : Nat := 40582772367900896740231

theorem tailTrace_400113 : CollatzResearch.WordTrace tailWord_400113 prefixEnd_400113 40582772367900896740231 := by
  unfold tailWord_400113
  simp only [CollatzResearch.WordTrace]
  refine ⟨14593319999466409705172993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9728879999644273136781995 14593319999466409705172993)
  ·
    refine ⟨10944989999599807278879745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14593319999466409705172993 10944989999599807278879745)
    ·
      refine ⟨8208742499699855459159809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10944989999599807278879745 8208742499699855459159809)
      ·
        refine ⟨6156556874774891594369857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8208742499699855459159809 6156556874774891594369857)
        ·
          refine ⟨4617417656081168695777393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6156556874774891594369857 4617417656081168695777393)
          ·
            refine ⟨3463063242060876521833045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4617417656081168695777393 3463063242060876521833045)
            ·
              refine ⟨40582772367900896740231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3463063242060876521833045 40582772367900896740231)
              ·
                rfl

theorem cell19_400113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_400113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400113 prefixEnd_400113 := by exact prefixLift 400113
  have htrace : WordTrace (prefixWord ++ tailWord_400113) baseStart_400113 baseEnd_400113 := by
    simpa [prefixWord, tailWord_400113, baseEnd_400113] using wordTrace_append hprefix tailTrace_400113
  have hstable : (prefixWord ++ tailWord_400113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400113).length < 2 ^ (prefixWord ++ tailWord_400113).sum := by decide
  have hdescent : baseEnd_400113 < baseStart_400113 := by decide
  rcases family_descends (prefixWord ++ tailWord_400113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400208 : List Nat := [2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_400208 : Nat := 118140960795 + 400208 * 2 ^ 59
def prefixEnd_400208 : Nat := 4983230072969 + 3 ^ 40 * 400208 * 2
def baseEnd_400208 : Nat := 121777224162770618109323

theorem tailTrace_400208 : CollatzResearch.WordTrace tailWord_400208 prefixEnd_400208 121777224162770618109323 := by
  unfold tailWord_400208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298392467061120464940639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9731189956081493953254185 7298392467061120464940639)
  ·
    refine ⟨10947588700591680697410959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7298392467061120464940639 10947588700591680697410959)
    ·
      refine ⟨16421383050887521046116439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10947588700591680697410959 16421383050887521046116439)
      ·
        refine ⟨24632074576331281569174659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16421383050887521046116439 24632074576331281569174659)
        ·
          refine ⟨36948111864496922353761989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24632074576331281569174659 36948111864496922353761989)
          ·
            refine ⟨6927770974593172941330373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36948111864496922353761989 6927770974593172941330373)
            ·
              refine ⟨1298957057736219926499445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6927770974593172941330373 1298957057736219926499445)
              ·
                refine ⟨121777224162770618109323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1298957057736219926499445 121777224162770618109323)
                ·
                  rfl

theorem cell19_400208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_400208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400208 prefixEnd_400208 := by exact prefixLift 400208
  have htrace : WordTrace (prefixWord ++ tailWord_400208) baseStart_400208 baseEnd_400208 := by
    simpa [prefixWord, tailWord_400208, baseEnd_400208] using wordTrace_append hprefix tailTrace_400208
  have hstable : (prefixWord ++ tailWord_400208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400208).length < 2 ^ (prefixWord ++ tailWord_400208).sum := by decide
  have hdescent : baseEnd_400208 < baseStart_400208 := by decide
  rcases family_descends (prefixWord ++ tailWord_400208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400227 : List Nat := [1, 1, 1, 5, 3, 8]
def baseStart_400227 : Nat := 118140960795 + 400227 * 2 ^ 59
def prefixEnd_400227 : Nat := 4983230072969 + 3 ^ 40 * 400227 * 2
def baseEnd_400227 : Nat := 13531445063842689298561

theorem tailTrace_400227 : CollatzResearch.WordTrace tailWord_400227 prefixEnd_400227 13531445063842689298561 := by
  unfold tailWord_400227
  simp only [CollatzResearch.WordTrace]
  refine ⟨14597477921053407174822935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9731651947368938116548623 14597477921053407174822935)
  ·
    refine ⟨21896216881580110762234403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14597477921053407174822935 21896216881580110762234403)
    ·
      refine ⟨32844325322370166143351605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21896216881580110762234403 32844325322370166143351605)
      ·
        refine ⟨3079155498972203075939213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32844325322370166143351605 3079155498972203075939213)
        ·
          refine ⟨1154683312114576153477205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3079155498972203075939213 1154683312114576153477205)
          ·
            refine ⟨13531445063842689298561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1154683312114576153477205 13531445063842689298561)
            ·
              rfl

theorem cell19_400227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_400227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400227 prefixEnd_400227 := by exact prefixLift 400227
  have htrace : WordTrace (prefixWord ++ tailWord_400227) baseStart_400227 baseEnd_400227 := by
    simpa [prefixWord, tailWord_400227, baseEnd_400227] using wordTrace_append hprefix tailTrace_400227
  have hstable : (prefixWord ++ tailWord_400227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400227).length < 2 ^ (prefixWord ++ tailWord_400227).sum := by decide
  have hdescent : baseEnd_400227 < baseStart_400227 := by decide
  rcases family_descends (prefixWord ++ tailWord_400227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400278 : List Nat := [5, 3, 1, 1, 1, 2, 6]
def baseStart_400278 : Nat := 118140960795 + 400278 * 2 ^ 59
def prefixEnd_400278 : Nat := 4983230072969 + 3 ^ 40 * 400278 * 2
def baseEnd_400278 : Nat := 40599508033677065517859

theorem tailTrace_400278 : CollatzResearch.WordTrace tailWord_400278 prefixEnd_400278 40599508033677065517859 := by
  unfold tailWord_400278
  simp only [CollatzResearch.WordTrace]
  refine ⟨912458627741790180308093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9732892029245761923286325 912458627741790180308093)
  ·
    refine ⟨342171985403171317615535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 912458627741790180308093 342171985403171317615535)
    ·
      refine ⟨513257978104756976423303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342171985403171317615535 513257978104756976423303)
      ·
        refine ⟨769886967157135464634955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513257978104756976423303 769886967157135464634955)
        ·
          refine ⟨1154830450735703196952433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769886967157135464634955 1154830450735703196952433)
          ·
            refine ⟨866122838051777397714325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154830450735703196952433 866122838051777397714325)
            ·
              refine ⟨40599508033677065517859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 866122838051777397714325 40599508033677065517859)
              ·
                rfl

theorem cell19_400278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_400278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400278 prefixEnd_400278 := by exact prefixLift 400278
  have htrace : WordTrace (prefixWord ++ tailWord_400278) baseStart_400278 baseEnd_400278 := by
    simpa [prefixWord, tailWord_400278, baseEnd_400278] using wordTrace_append hprefix tailTrace_400278
  have hstable : (prefixWord ++ tailWord_400278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400278).length < 2 ^ (prefixWord ++ tailWord_400278).sum := by decide
  have hdescent : baseEnd_400278 < baseStart_400278 := by decide
  rcases family_descends (prefixWord ++ tailWord_400278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400282 : List Nat := [3, 1, 1, 4, 3, 1, 6]
def baseStart_400282 : Nat := 118140960795 + 400282 * 2 ^ 59
def prefixEnd_400282 : Nat := 4983230072969 + 3 ^ 40 * 400282 * 2
def baseEnd_400282 : Nat := 40599913746786790821559

theorem tailTrace_400282 : CollatzResearch.WordTrace tailWord_400282 prefixEnd_400282 40599913746786790821559 := by
  unfold tailWord_400282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649870983963537892018775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9732989290569434378716733 3649870983963537892018775)
  ·
    refine ⟨5474806475945306838028163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3649870983963537892018775 5474806475945306838028163)
    ·
      refine ⟨8212209713917960257042245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474806475945306838028163 8212209713917960257042245)
      ·
        refine ⟨1539789321359617548195421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8212209713917960257042245 1539789321359617548195421)
        ·
          refine ⟨577420995509856580573283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1539789321359617548195421 577420995509856580573283)
          ·
            refine ⟨866131493264784870859925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577420995509856580573283 866131493264784870859925)
            ·
              refine ⟨40599913746786790821559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 866131493264784870859925 40599913746786790821559)
              ·
                rfl

theorem cell19_400282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_400282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400282 prefixEnd_400282 := by exact prefixLift 400282
  have htrace : WordTrace (prefixWord ++ tailWord_400282) baseStart_400282 baseEnd_400282 := by
    simpa [prefixWord, tailWord_400282, baseEnd_400282] using wordTrace_append hprefix tailTrace_400282
  have hstable : (prefixWord ++ tailWord_400282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400282).length < 2 ^ (prefixWord ++ tailWord_400282).sum := by decide
  have hdescent : baseEnd_400282 < baseStart_400282 := by decide
  rcases family_descends (prefixWord ++ tailWord_400282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400310 : List Nat := [5, 1, 4, 1, 2, 1, 2, 3]
def baseStart_400310 : Nat := 118140960795 + 400310 * 2 ^ 59
def prefixEnd_400310 : Nat := 4983230072969 + 3 ^ 40 * 400310 * 2
def baseEnd_400310 : Nat := 121808261215664603842379

theorem tailTrace_400310 : CollatzResearch.WordTrace tailWord_400310 prefixEnd_400310 121808261215664603842379 := by
  unfold tailWord_400310
  simp only [CollatzResearch.WordTrace]
  refine ⟨912531573734544521880899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9733670119835141566729589 912531573734544521880899)
  ·
    refine ⟨1368797360601816782821349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912531573734544521880899 1368797360601816782821349)
    ·
      refine ⟨256649505112840646779003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1368797360601816782821349 256649505112840646779003)
      ·
        refine ⟨384974257669260970168505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256649505112840646779003 384974257669260970168505)
        ·
          refine ⟨288730693251945727626379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384974257669260970168505 288730693251945727626379)
          ·
            refine ⟨433096039877918591439569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288730693251945727626379 433096039877918591439569)
            ·
              refine ⟨324822029908438943579677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433096039877918591439569 324822029908438943579677)
              ·
                refine ⟨121808261215664603842379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324822029908438943579677 121808261215664603842379)
                ·
                  rfl

theorem cell19_400310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_400310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400310 prefixEnd_400310 := by exact prefixLift 400310
  have htrace : WordTrace (prefixWord ++ tailWord_400310) baseStart_400310 baseEnd_400310 := by
    simpa [prefixWord, tailWord_400310, baseEnd_400310] using wordTrace_append hprefix tailTrace_400310
  have hstable : (prefixWord ++ tailWord_400310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400310).length < 2 ^ (prefixWord ++ tailWord_400310).sum := by decide
  have hdescent : baseEnd_400310 < baseStart_400310 := by decide
  rcases family_descends (prefixWord ++ tailWord_400310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400320 : List Nat := [2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_400320 : Nat := 118140960795 + 400320 * 2 ^ 59
def prefixEnd_400320 : Nat := 4983230072969 + 3 ^ 40 * 400320 * 2
def baseEnd_400320 : Nat := 121811304063987543620129

theorem tailTrace_400320 : CollatzResearch.WordTrace tailWord_400320 prefixEnd_400320 121811304063987543620129 := by
  unfold tailWord_400320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300434954858242028979207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9733913273144322705305609 7300434954858242028979207)
  ·
    refine ⟨10950652432287363043468811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300434954858242028979207 10950652432287363043468811)
    ·
      refine ⟨16425978648431044565203217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10950652432287363043468811 16425978648431044565203217)
      ·
        refine ⟨12319483986323283423902413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16425978648431044565203217 12319483986323283423902413)
        ·
          refine ⟨4619806494871231283963405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12319483986323283423902413 4619806494871231283963405)
          ·
            refine ⟨1732427435576711731486277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4619806494871231283963405 1732427435576711731486277)
            ·
              refine ⟨324830144170633449653677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1732427435576711731486277 324830144170633449653677)
              ·
                refine ⟨121811304063987543620129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324830144170633449653677 121811304063987543620129)
                ·
                  rfl

theorem cell19_400320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_400320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400320 prefixEnd_400320 := by exact prefixLift 400320
  have htrace : WordTrace (prefixWord ++ tailWord_400320) baseStart_400320 baseEnd_400320 := by
    simpa [prefixWord, tailWord_400320, baseEnd_400320] using wordTrace_append hprefix tailTrace_400320
  have hstable : (prefixWord ++ tailWord_400320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400320).length < 2 ^ (prefixWord ++ tailWord_400320).sum := by decide
  have hdescent : baseEnd_400320 < baseStart_400320 := by decide
  rcases family_descends (prefixWord ++ tailWord_400320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400333 : List Nat := [1, 6, 3, 1, 1, 2, 5]
def baseStart_400333 : Nat := 118140960795 + 400333 * 2 ^ 59
def prefixEnd_400333 : Nat := 4983230072969 + 3 ^ 40 * 400333 * 2
def baseEnd_400333 : Nat := 40605086588935788443735

theorem tailTrace_400333 : CollatzResearch.WordTrace tailWord_400333 prefixEnd_400333 40605086588935788443735 := by
  unfold tailWord_400333
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601344058669387278181653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9734229372446258185454435 14601344058669387278181653)
  ·
    refine ⟨684438002750127528664765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14601344058669387278181653 684438002750127528664765)
    ·
      refine ⟨256664251031297823249287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 684438002750127528664765 256664251031297823249287)
      ·
        refine ⟨384996376546946734873931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256664251031297823249287 384996376546946734873931)
        ·
          refine ⟨577494564820420102310897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384996376546946734873931 577494564820420102310897)
          ·
            refine ⟨433120923615315076733173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577494564820420102310897 433120923615315076733173)
            ·
              refine ⟨40605086588935788443735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433120923615315076733173 40605086588935788443735)
              ·
                rfl

theorem cell19_400333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_400333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400333 prefixEnd_400333 := by exact prefixLift 400333
  have htrace : WordTrace (prefixWord ++ tailWord_400333) baseStart_400333 baseEnd_400333 := by
    simpa [prefixWord, tailWord_400333, baseEnd_400333] using wordTrace_append hprefix tailTrace_400333
  have hstable : (prefixWord ++ tailWord_400333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400333).length < 2 ^ (prefixWord ++ tailWord_400333).sum := by decide
  have hdescent : baseEnd_400333 < baseStart_400333 := by decide
  rcases family_descends (prefixWord ++ tailWord_400333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400360 : List Nat := [2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_400360 : Nat := 118140960795 + 400360 * 2 ^ 59
def prefixEnd_400360 : Nat := 4983230072969 + 3 ^ 40 * 400360 * 2
def baseEnd_400360 : Nat := 121823475457279302731131

theorem tailTrace_400360 : CollatzResearch.WordTrace tailWord_400360 prefixEnd_400360 121823475457279302731131 := by
  unfold tailWord_400360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7301164414785785444707267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9734885886381047259609689 7301164414785785444707267)
  ·
    refine ⟨10951746622178678167060901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7301164414785785444707267 10951746622178678167060901)
    ·
      refine ⟨2053452491658502156323919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10951746622178678167060901 2053452491658502156323919)
      ·
        refine ⟨3080178737487753234485879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053452491658502156323919 3080178737487753234485879)
        ·
          refine ⟨4620268106231629851728819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080178737487753234485879 4620268106231629851728819)
          ·
            refine ⟨6930402159347444777593229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4620268106231629851728819 6930402159347444777593229)
            ·
              refine ⟨2598900809755291791597461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6930402159347444777593229 2598900809755291791597461)
              ·
                refine ⟨121823475457279302731131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2598900809755291791597461 121823475457279302731131)
                ·
                  rfl

theorem cell19_400360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_400360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400360 prefixEnd_400360 := by exact prefixLift 400360
  have htrace : WordTrace (prefixWord ++ tailWord_400360) baseStart_400360 baseEnd_400360 := by
    simpa [prefixWord, tailWord_400360, baseEnd_400360] using wordTrace_append hprefix tailTrace_400360
  have hstable : (prefixWord ++ tailWord_400360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400360).length < 2 ^ (prefixWord ++ tailWord_400360).sum := by decide
  have hdescent : baseEnd_400360 < baseStart_400360 := by decide
  rcases family_descends (prefixWord ++ tailWord_400360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400398 : List Nat := [4, 1, 1, 2, 2, 9]
def baseStart_400398 : Nat := 118140960795 + 400398 * 2 ^ 59
def prefixEnd_400398 : Nat := 4983230072969 + 3 ^ 40 * 400398 * 2
def baseEnd_400398 : Nat := 13537226475656274876287

theorem tailTrace_400398 : CollatzResearch.WordTrace tailWord_400398 prefixEnd_400398 13537226475656274876287 := by
  unfold tailWord_400398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825464350429237922412231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9735809868955935586198565 1825464350429237922412231)
  ·
    refine ⟨2738196525643856883618347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1825464350429237922412231 2738196525643856883618347)
    ·
      refine ⟨4107294788465785325427521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738196525643856883618347 4107294788465785325427521)
      ·
        refine ⟨3080471091349338994070641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4107294788465785325427521 3080471091349338994070641)
        ·
          refine ⟨2310353318512004245552981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3080471091349338994070641 2310353318512004245552981)
          ·
            refine ⟨13537226475656274876287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2310353318512004245552981 13537226475656274876287)
            ·
              rfl

theorem cell19_400398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_400398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400398 prefixEnd_400398 := by exact prefixLift 400398
  have htrace : WordTrace (prefixWord ++ tailWord_400398) baseStart_400398 baseEnd_400398 := by
    simpa [prefixWord, tailWord_400398, baseEnd_400398] using wordTrace_append hprefix tailTrace_400398
  have hstable : (prefixWord ++ tailWord_400398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400398).length < 2 ^ (prefixWord ++ tailWord_400398).sum := by decide
  have hdescent : baseEnd_400398 < baseStart_400398 := by decide
  rcases family_descends (prefixWord ++ tailWord_400398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400413 : List Nat := [1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_400413 : Nat := 118140960795 + 400413 * 2 ^ 59
def prefixEnd_400413 : Nat := 4983230072969 + 3 ^ 40 * 400413 * 2
def baseEnd_400413 : Nat := 121839602553390883553209

theorem tailTrace_400413 : CollatzResearch.WordTrace tailWord_400413 prefixEnd_400413 121839602553390883553209 := by
  unfold tailWord_400413
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604261898379560941093893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9736174598919707294062595 14604261898379560941093893)
  ·
    refine ⟨2738299105946167676455105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14604261898379560941093893 2738299105946167676455105)
    ·
      refine ⟨2053724329459625757341329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2738299105946167676455105 2053724329459625757341329)
      ·
        refine ⟨1540293247094719318005997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053724329459625757341329 1540293247094719318005997)
        ·
          refine ⟨577609967660519744252249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1540293247094719318005997 577609967660519744252249)
          ·
            refine ⟨433207475745389808189187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577609967660519744252249 433207475745389808189187)
            ·
              refine ⟨649811213618084712283781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433207475745389808189187 649811213618084712283781)
              ·
                refine ⟨121839602553390883553209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649811213618084712283781 121839602553390883553209)
                ·
                  rfl

theorem cell19_400413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_400413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400413 prefixEnd_400413 := by exact prefixLift 400413
  have htrace : WordTrace (prefixWord ++ tailWord_400413) baseStart_400413 baseEnd_400413 := by
    simpa [prefixWord, tailWord_400413, baseEnd_400413] using wordTrace_append hprefix tailTrace_400413
  have hstable : (prefixWord ++ tailWord_400413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400413).length < 2 ^ (prefixWord ++ tailWord_400413).sum := by decide
  have hdescent : baseEnd_400413 < baseStart_400413 := by decide
  rcases family_descends (prefixWord ++ tailWord_400413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400415 : List Nat := [1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_400415 : Nat := 118140960795 + 400415 * 2 ^ 59
def prefixEnd_400415 : Nat := 4983230072969 + 3 ^ 40 * 400415 * 2
def baseEnd_400415 : Nat := 121840211123055471508759

theorem tailTrace_400415 : CollatzResearch.WordTrace tailWord_400415 prefixEnd_400415 121840211123055471508759 := by
  unfold tailWord_400415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604334844372315282666699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9736223229581543521777799 14604334844372315282666699)
  ·
    refine ⟨21906502266558472924000049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14604334844372315282666699 21906502266558472924000049)
    ·
      refine ⟨16429876699918854693000037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21906502266558472924000049 16429876699918854693000037)
      ·
        refine ⟨3080601881234785254937507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16429876699918854693000037 3080601881234785254937507)
        ·
          refine ⟨4620902821852177882406261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080601881234785254937507 4620902821852177882406261)
          ·
            refine ⟨433209639548641676475587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4620902821852177882406261 433209639548641676475587)
            ·
              refine ⟨649814459322962514713381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433209639548641676475587 649814459322962514713381)
              ·
                refine ⟨121840211123055471508759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 649814459322962514713381 121840211123055471508759)
                ·
                  rfl

theorem cell19_400415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_400415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400415 prefixEnd_400415 := by exact prefixLift 400415
  have htrace : WordTrace (prefixWord ++ tailWord_400415) baseStart_400415 baseEnd_400415 := by
    simpa [prefixWord, tailWord_400415, baseEnd_400415] using wordTrace_append hprefix tailTrace_400415
  have hstable : (prefixWord ++ tailWord_400415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400415).length < 2 ^ (prefixWord ++ tailWord_400415).sum := by decide
  have hdescent : baseEnd_400415 < baseStart_400415 := by decide
  rcases family_descends (prefixWord ++ tailWord_400415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400434 : List Nat := [3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_400434 : Nat := 118140960795 + 400434 * 2 ^ 59
def prefixEnd_400434 : Nat := 4983230072969 + 3 ^ 40 * 400434 * 2
def baseEnd_400434 : Nat := 121845992534869057086485

theorem tailTrace_400434 : CollatzResearch.WordTrace tailWord_400434 prefixEnd_400434 121845992534869057086485 := by
  unfold tailWord_400434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651256957825870381902089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9736685220868987685072237 3651256957825870381902089)
  ·
    refine ⟨2738442718369402786426567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3651256957825870381902089 2738442718369402786426567)
    ·
      refine ⟨4107664077554104179639851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738442718369402786426567 4107664077554104179639851)
      ·
        refine ⟨6161496116331156269459777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107664077554104179639851 6161496116331156269459777)
        ·
          refine ⟨4621122087248367202094833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161496116331156269459777 4621122087248367202094833)
          ·
            refine ⟨3465841565436275401571125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621122087248367202094833 3465841565436275401571125)
            ·
              refine ⟨324922646759650818897293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3465841565436275401571125 324922646759650818897293)
              ·
                refine ⟨121845992534869057086485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324922646759650818897293 121845992534869057086485)
                ·
                  rfl

theorem cell19_400434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_400434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400434 prefixEnd_400434 := by exact prefixLift 400434
  have htrace : WordTrace (prefixWord ++ tailWord_400434) baseStart_400434 baseEnd_400434 := by
    simpa [prefixWord, tailWord_400434, baseEnd_400434] using wordTrace_append hprefix tailTrace_400434
  have hstable : (prefixWord ++ tailWord_400434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400434).length < 2 ^ (prefixWord ++ tailWord_400434).sum := by decide
  have hdescent : baseEnd_400434 < baseStart_400434 := by decide
  rcases family_descends (prefixWord ++ tailWord_400434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400455 : List Nat := [1, 1, 4, 1, 3, 3, 6]
def baseStart_400455 : Nat := 118140960795 + 400455 * 2 ^ 59
def prefixEnd_400455 : Nat := 4983230072969 + 3 ^ 40 * 400455 * 2
def baseEnd_400455 : Nat := 40617460838782410206587

theorem tailTrace_400455 : CollatzResearch.WordTrace tailWord_400455 prefixEnd_400455 40617460838782410206587 := by
  unfold tailWord_400455
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605793764227402114122819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9737195842818268076081879 14605793764227402114122819)
  ·
    refine ⟨21908690646341103171184229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14605793764227402114122819 21908690646341103171184229)
    ·
      refine ⟨4107879496188956844597043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21908690646341103171184229 4107879496188956844597043)
      ·
        refine ⟨6161819244283435266895565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107879496188956844597043 6161819244283435266895565)
        ·
          refine ⟨2310682216606288225085837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6161819244283435266895565 2310682216606288225085837)
          ·
            refine ⟨866505831227358084407189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2310682216606288225085837 866505831227358084407189)
            ·
              refine ⟨40617460838782410206587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 866505831227358084407189 40617460838782410206587)
              ·
                rfl

theorem cell19_400455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_400455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400455 prefixEnd_400455 := by exact prefixLift 400455
  have htrace : WordTrace (prefixWord ++ tailWord_400455) baseStart_400455 baseEnd_400455 := by
    simpa [prefixWord, tailWord_400455, baseEnd_400455] using wordTrace_append hprefix tailTrace_400455
  have hstable : (prefixWord ++ tailWord_400455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400455).length < 2 ^ (prefixWord ++ tailWord_400455).sum := by decide
  have hdescent : baseEnd_400455 < baseStart_400455 := by decide
  rcases family_descends (prefixWord ++ tailWord_400455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400586 : List Nat := [3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_400586 : Nat := 118140960795 + 400586 * 2 ^ 59
def prefixEnd_400586 : Nat := 4983230072969 + 3 ^ 40 * 400586 * 2
def baseEnd_400586 : Nat := 121892243829377741708293

theorem tailTrace_400586 : CollatzResearch.WordTrace tailWord_400586 prefixEnd_400586 121892243829377741708293 := by
  unfold tailWord_400586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652642931688202871785403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9740381151168540991427741 3652642931688202871785403)
  ·
    refine ⟨5478964397532304307678105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3652642931688202871785403 5478964397532304307678105)
    ·
      refine ⟨4109223298149228230758579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5478964397532304307678105 4109223298149228230758579)
      ·
        refine ⟨6163834947223842346137869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4109223298149228230758579 6163834947223842346137869)
        ·
          refine ⟨2311438105208940879801701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6163834947223842346137869 2311438105208940879801701)
          ·
            refine ⟨433394644726676414962819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2311438105208940879801701 433394644726676414962819)
            ·
              refine ⟨650091967090014622444229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433394644726676414962819 650091967090014622444229)
              ·
                refine ⟨121892243829377741708293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650091967090014622444229 121892243829377741708293)
                ·
                  rfl

theorem cell19_400586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_400586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400586 prefixEnd_400586 := by exact prefixLift 400586
  have htrace : WordTrace (prefixWord ++ tailWord_400586) baseStart_400586 baseEnd_400586 := by
    simpa [prefixWord, tailWord_400586, baseEnd_400586] using wordTrace_append hprefix tailTrace_400586
  have hstable : (prefixWord ++ tailWord_400586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400586).length < 2 ^ (prefixWord ++ tailWord_400586).sum := by decide
  have hdescent : baseEnd_400586 < baseStart_400586 := by decide
  rcases family_descends (prefixWord ++ tailWord_400586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400664 : List Nat := [2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_400664 : Nat := 118140960795 + 400664 * 2 ^ 59
def prefixEnd_400664 : Nat := 4983230072969 + 3 ^ 40 * 400664 * 2
def baseEnd_400664 : Nat := 121915978046296671974747

theorem tailTrace_400664 : CollatzResearch.WordTrace tailWord_400664 prefixEnd_400664 121915978046296671974747 := by
  unfold tailWord_400664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306708310235115404240523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9742277746980153872320697 7306708310235115404240523)
  ·
    refine ⟨10960062465352673106360785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7306708310235115404240523 10960062465352673106360785)
    ·
      refine ⟨8220046849014504829770589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10960062465352673106360785 8220046849014504829770589)
      ·
        refine ⟨3082517568380439311163971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8220046849014504829770589 3082517568380439311163971)
        ·
          refine ⟨4623776352570658966745957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082517568380439311163971 4623776352570658966745957)
          ·
            refine ⟨866958066106998556264867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4623776352570658966745957 866958066106998556264867)
            ·
              refine ⟨1300437099160497834397301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866958066106998556264867 1300437099160497834397301)
              ·
                refine ⟨121915978046296671974747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1300437099160497834397301 121915978046296671974747)
                ·
                  rfl

theorem cell19_400664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_400664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400664 prefixEnd_400664 := by exact prefixLift 400664
  have htrace : WordTrace (prefixWord ++ tailWord_400664) baseStart_400664 baseEnd_400664 := by
    simpa [prefixWord, tailWord_400664, baseEnd_400664] using wordTrace_append hprefix tailTrace_400664
  have hstable : (prefixWord ++ tailWord_400664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400664).length < 2 ^ (prefixWord ++ tailWord_400664).sum := by decide
  have hdescent : baseEnd_400664 < baseStart_400664 := by decide
  rcases family_descends (prefixWord ++ tailWord_400664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400723 : List Nat := [1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_400723 : Nat := 118140960795 + 400723 * 2 ^ 59
def prefixEnd_400723 : Nat := 4983230072969 + 3 ^ 40 * 400723 * 2
def baseEnd_400723 : Nat := 121933930851402016663475

theorem tailTrace_400723 : CollatzResearch.WordTrace tailWord_400723 prefixEnd_400723 121933930851402016663475 := by
  unfold tailWord_400723
  simp only [CollatzResearch.WordTrace]
  refine ⟨14615568527256483884878823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9743712351504322589919215 14615568527256483884878823)
  ·
    refine ⟨21923352790884725827318235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14615568527256483884878823 21923352790884725827318235)
    ·
      refine ⟨32885029186327088740977353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21923352790884725827318235 32885029186327088740977353)
      ·
        refine ⟨24663771889745316555733015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32885029186327088740977353 24663771889745316555733015)
        ·
          refine ⟨36995657834617974833599523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24663771889745316555733015 36995657834617974833599523)
          ·
            refine ⟨55493486751926962250399285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36995657834617974833599523 55493486751926962250399285)
            ·
              refine ⟨5202514382993152710974933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55493486751926962250399285 5202514382993152710974933)
              ·
                refine ⟨121933930851402016663475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5202514382993152710974933 121933930851402016663475)
                ·
                  rfl

theorem cell19_400723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_400723 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400723 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400723 prefixEnd_400723 := by exact prefixLift 400723
  have htrace : WordTrace (prefixWord ++ tailWord_400723) baseStart_400723 baseEnd_400723 := by
    simpa [prefixWord, tailWord_400723, baseEnd_400723] using wordTrace_append hprefix tailTrace_400723
  have hstable : (prefixWord ++ tailWord_400723).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400723).length < 2 ^ (prefixWord ++ tailWord_400723).sum := by decide
  have hdescent : baseEnd_400723 < baseStart_400723 := by decide
  rcases family_descends (prefixWord ++ tailWord_400723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400776 : List Nat := [2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_400776 : Nat := 118140960795 + 400776 * 2 ^ 59
def prefixEnd_400776 : Nat := 4983230072969 + 3 ^ 40 * 400776 * 2
def baseEnd_400776 : Nat := 121950057947513597485553

theorem tailTrace_400776 : CollatzResearch.WordTrace tailWord_400776 prefixEnd_400776 121950057947513597485553 := by
  unfold tailWord_400776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308750798032236968279091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9745001064042982624372121 7308750798032236968279091)
  ·
    refine ⟨10963126197048355452418637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7308750798032236968279091 10963126197048355452418637)
    ·
      refine ⟨4111172323893133294656989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10963126197048355452418637 4111172323893133294656989)
      ·
        refine ⟨1541689621459924985496371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4111172323893133294656989 1541689621459924985496371)
        ·
          refine ⟨2312534432189887478244557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541689621459924985496371 2312534432189887478244557)
          ·
            refine ⟨867200412071207804341709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2312534432189887478244557 867200412071207804341709)
            ·
              refine ⟨325200154526702926628141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 867200412071207804341709 325200154526702926628141)
              ·
                refine ⟨121950057947513597485553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325200154526702926628141 121950057947513597485553)
                ·
                  rfl

theorem cell19_400776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_400776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400776 prefixEnd_400776 := by exact prefixLift 400776
  have htrace : WordTrace (prefixWord ++ tailWord_400776) baseStart_400776 baseEnd_400776 := by
    simpa [prefixWord, tailWord_400776, baseEnd_400776] using wordTrace_append hprefix tailTrace_400776
  have hstable : (prefixWord ++ tailWord_400776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400776).length < 2 ^ (prefixWord ++ tailWord_400776).sum := by decide
  have hdescent : baseEnd_400776 < baseStart_400776 := by decide
  rcases family_descends (prefixWord ++ tailWord_400776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400797 : List Nat := [1, 4, 2, 1, 3, 2, 6]
def baseStart_400797 : Nat := 118140960795 + 400797 * 2 ^ 59
def prefixEnd_400797 : Nat := 4983230072969 + 3 ^ 40 * 400797 * 2
def baseEnd_400797 : Nat := 40652149309663923672943

theorem tailTrace_400797 : CollatzResearch.WordTrace tailWord_400797 prefixEnd_400797 40652149309663923672943 := by
  unfold tailWord_400797
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618267528988394523072645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9745511685992263015381763 14618267528988394523072645)
  ·
    refine ⟨2740925161685323973076121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14618267528988394523072645 2740925161685323973076121)
    ·
      refine ⟨2055693871263992979807091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740925161685323973076121 2055693871263992979807091)
      ·
        refine ⟨3083540806895989469710637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055693871263992979807091 3083540806895989469710637)
        ·
          refine ⟨1156327802585996051141489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3083540806895989469710637 1156327802585996051141489)
          ·
            refine ⟨867245851939497038356117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156327802585996051141489 867245851939497038356117)
            ·
              refine ⟨40652149309663923672943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 867245851939497038356117 40652149309663923672943)
              ·
                rfl

theorem cell19_400797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_400797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400797 prefixEnd_400797 := by exact prefixLift 400797
  have htrace : WordTrace (prefixWord ++ tailWord_400797) baseStart_400797 baseEnd_400797 := by
    simpa [prefixWord, tailWord_400797, baseEnd_400797] using wordTrace_append hprefix tailTrace_400797
  have hstable : (prefixWord ++ tailWord_400797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400797).length < 2 ^ (prefixWord ++ tailWord_400797).sum := by decide
  have hdescent : baseEnd_400797 < baseStart_400797 := by decide
  rcases family_descends (prefixWord ++ tailWord_400797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400835 : List Nat := [1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_400835 : Nat := 118140960795 + 400835 * 2 ^ 59
def prefixEnd_400835 : Nat := 4983230072969 + 3 ^ 40 * 400835 * 2
def baseEnd_400835 : Nat := 121968010752618942174281

theorem tailTrace_400835 : CollatzResearch.WordTrace tailWord_400835 prefixEnd_400835 121968010752618942174281 := by
  unfold tailWord_400835
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619653502850727012955959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9746435668567151341970639 14619653502850727012955959)
  ·
    refine ⟨21929480254276090519433939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14619653502850727012955959 21929480254276090519433939)
    ·
      refine ⟨32894220381414135779150909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21929480254276090519433939 32894220381414135779150909)
      ·
        refine ⟨12335332643030300917181591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32894220381414135779150909 12335332643030300917181591)
        ·
          refine ⟨18502998964545451375772387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335332643030300917181591 18502998964545451375772387)
          ·
            refine ⟨27754498446818177063658581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18502998964545451375772387 27754498446818177063658581)
            ·
              refine ⟨325248028673650512464749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 27754498446818177063658581 325248028673650512464749)
              ·
                refine ⟨121968010752618942174281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325248028673650512464749 121968010752618942174281)
                ·
                  rfl

theorem cell19_400835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_400835 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400835 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400835 prefixEnd_400835 := by exact prefixLift 400835
  have htrace : WordTrace (prefixWord ++ tailWord_400835) baseStart_400835 baseEnd_400835 := by
    simpa [prefixWord, tailWord_400835, baseEnd_400835] using wordTrace_append hprefix tailTrace_400835
  have hstable : (prefixWord ++ tailWord_400835).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400835).length < 2 ^ (prefixWord ++ tailWord_400835).sum := by decide
  have hdescent : baseEnd_400835 < baseStart_400835 := by decide
  rcases family_descends (prefixWord ++ tailWord_400835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400852 : List Nat := [2, 4, 1, 2, 3, 2, 5]
def baseStart_400852 : Nat := 118140960795 + 400852 * 2 ^ 59
def prefixEnd_400852 : Nat := 4983230072969 + 3 ^ 40 * 400852 * 2
def baseEnd_400852 : Nat := 40657727864922646598819

theorem tailTrace_400852 : CollatzResearch.WordTrace tailWord_400852 prefixEnd_400852 40657727864922646598819 := by
  unfold tailWord_400852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310136771894569458162405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9746849029192759277549873 7310136771894569458162405)
  ·
    refine ⟨1370650644730231773405451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7310136771894569458162405 1370650644730231773405451)
    ·
      refine ⟨2055975967095347660108177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370650644730231773405451 2055975967095347660108177)
      ·
        refine ⟨1541981975321510745081133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2055975967095347660108177 1541981975321510745081133)
        ·
          refine ⟨578243240745566529405425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1541981975321510745081133 578243240745566529405425)
          ·
            refine ⟨433682430559174897054069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578243240745566529405425 433682430559174897054069)
            ·
              refine ⟨40657727864922646598819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433682430559174897054069 40657727864922646598819)
              ·
                rfl

theorem cell19_400852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_400852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400852 prefixEnd_400852 := by exact prefixLift 400852
  have htrace : WordTrace (prefixWord ++ tailWord_400852) baseStart_400852 baseEnd_400852 := by
    simpa [prefixWord, tailWord_400852, baseEnd_400852] using wordTrace_append hprefix tailTrace_400852
  have hstable : (prefixWord ++ tailWord_400852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400852).length < 2 ^ (prefixWord ++ tailWord_400852).sum := by decide
  have hdescent : baseEnd_400852 < baseStart_400852 := by decide
  rcases family_descends (prefixWord ++ tailWord_400852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400856 : List Nat := [2, 1, 2, 2, 2, 1, 9]
def baseStart_400856 : Nat := 118140960795 + 400856 * 2 ^ 59
def prefixEnd_400856 : Nat := 4983230072969 + 3 ^ 40 * 400856 * 2
def baseEnd_400856 : Nat := 40658133578032371902519

theorem tailTrace_400856 : CollatzResearch.WordTrace tailWord_400856 prefixEnd_400856 40658133578032371902519 := by
  unfold tailWord_400856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310209717887323799735211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9746946290516431732980281 7310209717887323799735211)
  ·
    refine ⟨10965314576830985699602817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7310209717887323799735211 10965314576830985699602817)
    ·
      refine ⟨8223985932623239274702113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10965314576830985699602817 8223985932623239274702113)
      ·
        refine ⟨6167989449467429456026585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8223985932623239274702113 6167989449467429456026585)
        ·
          refine ⟨4625992087100572092019939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6167989449467429456026585 4625992087100572092019939)
          ·
            refine ⟨6938988130650858138029909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625992087100572092019939 6938988130650858138029909)
            ·
              refine ⟨40658133578032371902519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6938988130650858138029909 40658133578032371902519)
              ·
                rfl

theorem cell19_400856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_400856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400856 prefixEnd_400856 := by exact prefixLift 400856
  have htrace : WordTrace (prefixWord ++ tailWord_400856) baseStart_400856 baseEnd_400856 := by
    simpa [prefixWord, tailWord_400856, baseEnd_400856] using wordTrace_append hprefix tailTrace_400856
  have hstable : (prefixWord ++ tailWord_400856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400856).length < 2 ^ (prefixWord ++ tailWord_400856).sum := by decide
  have hdescent : baseEnd_400856 < baseStart_400856 := by decide
  rcases family_descends (prefixWord ++ tailWord_400856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400909 : List Nat := [1, 7, 1, 1, 9]
def baseStart_400909 : Nat := 118140960795 + 400909 * 2 ^ 59
def prefixEnd_400909 : Nat := 4983230072969 + 3 ^ 40 * 400909 * 2
def baseEnd_400909 : Nat := 4518167697415136908505

theorem tailTrace_400909 : CollatzResearch.WordTrace tailWord_400909 prefixEnd_400909 4518167697415136908505 := by
  unfold tailWord_400909
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622352504582637651149781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9748235003055091767433187 14622352504582637651149781)
  ·
    refine ⟨342711386826155569948823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14622352504582637651149781 342711386826155569948823)
    ·
      refine ⟨514067080239233354923235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342711386826155569948823 514067080239233354923235)
      ·
        refine ⟨771100620358850032384853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514067080239233354923235 771100620358850032384853)
        ·
          refine ⟨4518167697415136908505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 771100620358850032384853 4518167697415136908505)
          ·
            rfl

theorem cell19_400909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 9].length) (baseStart_400909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400909 prefixEnd_400909 := by exact prefixLift 400909
  have htrace : WordTrace (prefixWord ++ tailWord_400909) baseStart_400909 baseEnd_400909 := by
    simpa [prefixWord, tailWord_400909, baseEnd_400909] using wordTrace_append hprefix tailTrace_400909
  have hstable : (prefixWord ++ tailWord_400909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400909).length < 2 ^ (prefixWord ++ tailWord_400909).sum := by decide
  have hdescent : baseEnd_400909 < baseStart_400909 := by decide
  rcases family_descends (prefixWord ++ tailWord_400909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400928 : List Nat := [2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_400928 : Nat := 118140960795 + 400928 * 2 ^ 59
def prefixEnd_400928 : Nat := 4983230072969 + 3 ^ 40 * 400928 * 2
def baseEnd_400928 : Nat := 121996309242022282107361

theorem tailTrace_400928 : CollatzResearch.WordTrace tailWord_400928 prefixEnd_400928 121996309242022282107361 := by
  unfold tailWord_400928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311522745756901948045719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9748696994342535930727625 7311522745756901948045719)
  ·
    refine ⟨10967284118635352922068579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7311522745756901948045719 10967284118635352922068579)
    ·
      refine ⟨16450926177953029383102869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10967284118635352922068579 16450926177953029383102869)
      ·
        refine ⟨771137164591548252332947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16450926177953029383102869 771137164591548252332947)
        ·
          refine ⟨1156705746887322378499421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771137164591548252332947 1156705746887322378499421)
          ·
            refine ⟨433764655082745891937283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1156705746887322378499421 433764655082745891937283)
            ·
              refine ⟨650646982624118837905925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433764655082745891937283 650646982624118837905925)
              ·
                refine ⟨121996309242022282107361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650646982624118837905925 121996309242022282107361)
                ·
                  rfl

theorem cell19_400928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_400928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400928 prefixEnd_400928 := by exact prefixLift 400928
  have htrace : WordTrace (prefixWord ++ tailWord_400928) baseStart_400928 baseEnd_400928 := by
    simpa [prefixWord, tailWord_400928, baseEnd_400928] using wordTrace_append hprefix tailTrace_400928
  have hstable : (prefixWord ++ tailWord_400928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400928).length < 2 ^ (prefixWord ++ tailWord_400928).sum := by decide
  have hdescent : baseEnd_400928 < baseStart_400928 := by decide
  rcases family_descends (prefixWord ++ tailWord_400928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400930 : List Nat := [3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_400930 : Nat := 118140960795 + 400930 * 2 ^ 59
def prefixEnd_400930 : Nat := 4983230072969 + 3 ^ 40 * 400930 * 2
def baseEnd_400930 : Nat := 121996917811686870062911

theorem tailTrace_400930 : CollatzResearch.WordTrace tailWord_400930 prefixEnd_400930 121996917811686870062911 := by
  unfold tailWord_400930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655779609376639559416061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9748745625004372158442829 3655779609376639559416061)
  ·
    refine ⟨1370917353516239834781023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3655779609376639559416061 1370917353516239834781023)
    ·
      refine ⟨2056376030274359752171535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370917353516239834781023 2056376030274359752171535)
      ·
        refine ⟨3084564045411539628257303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056376030274359752171535 3084564045411539628257303)
        ·
          refine ⟨4626846068117309442385955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084564045411539628257303 4626846068117309442385955)
          ·
            refine ⟨6940269102175964163578933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626846068117309442385955 6940269102175964163578933)
            ·
              refine ⟨650650228328996640335525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6940269102175964163578933 650650228328996640335525)
              ·
                refine ⟨121996917811686870062911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650650228328996640335525 121996917811686870062911)
                ·
                  rfl

theorem cell19_400930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_400930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400930 prefixEnd_400930 := by exact prefixLift 400930
  have htrace : WordTrace (prefixWord ++ tailWord_400930) baseStart_400930 baseEnd_400930 := by
    simpa [prefixWord, tailWord_400930, baseEnd_400930] using wordTrace_append hprefix tailTrace_400930
  have hstable : (prefixWord ++ tailWord_400930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400930).length < 2 ^ (prefixWord ++ tailWord_400930).sum := by decide
  have hdescent : baseEnd_400930 < baseStart_400930 := by decide
  rcases family_descends (prefixWord ++ tailWord_400930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400970 : List Nat := [3, 1, 2, 1, 1, 3, 8]
def baseStart_400970 : Nat := 118140960795 + 400970 * 2 ^ 59
def prefixEnd_400970 : Nat := 4983230072969 + 3 ^ 40 * 400970 * 2
def baseEnd_400970 : Nat := 40669696401659543057971

theorem tailTrace_400970 : CollatzResearch.WordTrace tailWord_400970 prefixEnd_400970 40669696401659543057971 := by
  unfold tailWord_400970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656144339340411267280091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9749718238241096712746909 3656144339340411267280091)
  ·
    refine ⟨5484216509010616900920137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3656144339340411267280091 5484216509010616900920137)
    ·
      refine ⟨4113162381757962675690103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5484216509010616900920137 4113162381757962675690103)
      ·
        refine ⟨6169743572636944013535155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4113162381757962675690103 6169743572636944013535155)
        ·
          refine ⟨9254615358955416020302733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169743572636944013535155 9254615358955416020302733)
          ·
            refine ⟨3470480759608281007613525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9254615358955416020302733 3470480759608281007613525)
            ·
              refine ⟨40669696401659543057971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3470480759608281007613525 40669696401659543057971)
              ·
                rfl

theorem cell19_400970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_400970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_400970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_400970 prefixEnd_400970 := by exact prefixLift 400970
  have htrace : WordTrace (prefixWord ++ tailWord_400970) baseStart_400970 baseEnd_400970 := by
    simpa [prefixWord, tailWord_400970, baseEnd_400970] using wordTrace_append hprefix tailTrace_400970
  have hstable : (prefixWord ++ tailWord_400970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400970).length < 2 ^ (prefixWord ++ tailWord_400970).sum := by decide
  have hdescent : baseEnd_400970 < baseStart_400970 := by decide
  rcases family_descends (prefixWord ++ tailWord_400970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401025 : List Nat := [1, 2, 4, 2, 1, 4, 5]
def baseStart_401025 : Nat := 118140960795 + 401025 * 2 ^ 59
def prefixEnd_401025 : Nat := 4983230072969 + 3 ^ 40 * 401025 * 2
def baseEnd_401025 : Nat := 40675274956918265983847

theorem tailTrace_401025 : CollatzResearch.WordTrace tailWord_401025 prefixEnd_401025 40675274956918265983847 := by
  unfold tailWord_401025
  simp only [CollatzResearch.WordTrace]
  refine ⟨14626583372162389462372529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9751055581441592974915019 14626583372162389462372529)
  ·
    refine ⟨10969937529121792096779397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14626583372162389462372529 10969937529121792096779397)
    ·
      refine ⟨2056863286710336018146137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10969937529121792096779397 2056863286710336018146137)
      ·
        refine ⟨1542647465032752013609603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056863286710336018146137 1542647465032752013609603)
        ·
          refine ⟨2313971197549128020414405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542647465032752013609603 2313971197549128020414405)
          ·
            refine ⟨433869599540461503827701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2313971197549128020414405 433869599540461503827701)
            ·
              refine ⟨40675274956918265983847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433869599540461503827701 40675274956918265983847)
              ·
                rfl

theorem cell19_401025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_401025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401025 prefixEnd_401025 := by exact prefixLift 401025
  have htrace : WordTrace (prefixWord ++ tailWord_401025) baseStart_401025 baseEnd_401025 := by
    simpa [prefixWord, tailWord_401025, baseEnd_401025] using wordTrace_append hprefix tailTrace_401025
  have hstable : (prefixWord ++ tailWord_401025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401025).length < 2 ^ (prefixWord ++ tailWord_401025).sum := by decide
  have hdescent : baseEnd_401025 < baseStart_401025 := by decide
  rcases family_descends (prefixWord ++ tailWord_401025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401042 : List Nat := [3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_401042 : Nat := 118140960795 + 401042 * 2 ^ 59
def prefixEnd_401042 : Nat := 4983230072969 + 3 ^ 40 * 401042 * 2
def baseEnd_401042 : Nat := 122030997712903795573717

theorem tailTrace_401042 : CollatzResearch.WordTrace tailWord_401042 prefixEnd_401042 122030997712903795573717 := by
  unfold tailWord_401042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656800853275200341435345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9751468942067200910494253 3656800853275200341435345)
  ·
    refine ⟨2742600639956400256076509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3656800853275200341435345 2742600639956400256076509)
    ·
      refine ⟨1028475239983650096028691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2742600639956400256076509 1028475239983650096028691)
      ·
        refine ⟨1542712859975475144043037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028475239983650096028691 1542712859975475144043037)
        ·
          refine ⟨578517322490803179016139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1542712859975475144043037 578517322490803179016139)
          ·
            refine ⟨867775983736204768524209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578517322490803179016139 867775983736204768524209)
            ·
              refine ⟨650831987802153576393157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867775983736204768524209 650831987802153576393157)
              ·
                refine ⟨122030997712903795573717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 650831987802153576393157 122030997712903795573717)
                ·
                  rfl

theorem cell19_401042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_401042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401042 prefixEnd_401042 := by exact prefixLift 401042
  have htrace : WordTrace (prefixWord ++ tailWord_401042) baseStart_401042 baseEnd_401042 := by
    simpa [prefixWord, tailWord_401042, baseEnd_401042] using wordTrace_append hprefix tailTrace_401042
  have hstable : (prefixWord ++ tailWord_401042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401042).length < 2 ^ (prefixWord ++ tailWord_401042).sum := by decide
  have hdescent : baseEnd_401042 < baseStart_401042 := by decide
  rcases family_descends (prefixWord ++ tailWord_401042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401084 : List Nat := [2, 2, 2, 3, 1, 9]
def baseStart_401084 : Nat := 118140960795 + 401084 * 2 ^ 59
def prefixEnd_401084 : Nat := 4983230072969 + 3 ^ 40 * 401084 * 2
def baseEnd_401084 : Nat := 13560419741762238071141

theorem tailTrace_401084 : CollatzResearch.WordTrace tailWord_401084 prefixEnd_401084 13560419741762238071141 := by
  unfold tailWord_401084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314367639474321269385153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9752490185965761692513537 7314367639474321269385153)
  ·
    refine ⟨5485775729605740952038865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7314367639474321269385153 5485775729605740952038865)
    ·
      refine ⟨4114331797204305714029149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5485775729605740952038865 4114331797204305714029149)
      ·
        refine ⟨1542874423951614642760931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4114331797204305714029149 1542874423951614642760931)
        ·
          refine ⟨2314311635927421964141397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542874423951614642760931 2314311635927421964141397)
          ·
            refine ⟨13560419741762238071141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2314311635927421964141397 13560419741762238071141)
            ·
              rfl

theorem cell19_401084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_401084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401084 prefixEnd_401084 := by exact prefixLift 401084
  have htrace : WordTrace (prefixWord ++ tailWord_401084) baseStart_401084 baseEnd_401084 := by
    simpa [prefixWord, tailWord_401084, baseEnd_401084] using wordTrace_append hprefix tailTrace_401084
  have hstable : (prefixWord ++ tailWord_401084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401084).length < 2 ^ (prefixWord ++ tailWord_401084).sum := by decide
  have hdescent : baseEnd_401084 < baseStart_401084 := by decide
  rcases family_descends (prefixWord ++ tailWord_401084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401116 : List Nat := [2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_401116 : Nat := 118140960795 + 401116 * 2 ^ 59
def prefixEnd_401116 : Nat := 4983230072969 + 3 ^ 40 * 401116 * 2
def baseEnd_401116 : Nat := 122053514790493549929071

theorem tailTrace_401116 : CollatzResearch.WordTrace tailWord_401116 prefixEnd_401116 122053514790493549929071 := by
  unfold tailWord_401116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314951207416356001967601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9753268276555141335956801 7314951207416356001967601)
  ·
    refine ⟨5486213405562267001475701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7314951207416356001967601 5486213405562267001475701)
    ·
      refine ⟨514332506771462531388347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5486213405562267001475701 514332506771462531388347)
      ·
        refine ⟨771498760157193797082521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514332506771462531388347 771498760157193797082521)
        ·
          refine ⟨578624070117895347811891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771498760157193797082521 578624070117895347811891)
          ·
            refine ⟨867936105176843021717837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578624070117895347811891 867936105176843021717837)
            ·
              refine ⟨325476039441316133144189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 867936105176843021717837 325476039441316133144189)
              ·
                refine ⟨122053514790493549929071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325476039441316133144189 122053514790493549929071)
                ·
                  rfl

theorem cell19_401116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_401116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401116 prefixEnd_401116 := by exact prefixLift 401116
  have htrace : WordTrace (prefixWord ++ tailWord_401116) baseStart_401116 baseEnd_401116 := by
    simpa [prefixWord, tailWord_401116, baseEnd_401116] using wordTrace_append hprefix tailTrace_401116
  have hstable : (prefixWord ++ tailWord_401116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401116).length < 2 ^ (prefixWord ++ tailWord_401116).sum := by decide
  have hdescent : baseEnd_401116 < baseStart_401116 := by decide
  rcases family_descends (prefixWord ++ tailWord_401116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401160 : List Nat := [2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_401160 : Nat := 118140960795 + 401160 * 2 ^ 59
def prefixEnd_401160 : Nat := 4983230072969 + 3 ^ 40 * 401160 * 2
def baseEnd_401160 : Nat := 122066903323114484951173

theorem tailTrace_401160 : CollatzResearch.WordTrace tailWord_401160 prefixEnd_401160 122066903323114484951173 := by
  unfold tailWord_401160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315753613336653759268467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9754338151115538345691289 7315753613336653759268467)
  ·
    refine ⟨10973630420004980638902701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7315753613336653759268467 10973630420004980638902701)
    ·
      refine ⟨4115111407501867739588513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10973630420004980638902701 4115111407501867739588513)
      ·
        refine ⟨3086333555626400804691385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4115111407501867739588513 3086333555626400804691385)
        ·
          refine ⟨2314750166719800603518539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086333555626400804691385 2314750166719800603518539)
          ·
            refine ⟨3472125250079700905277809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314750166719800603518539 3472125250079700905277809)
            ·
              refine ⟨2604093937559775678958357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472125250079700905277809 2604093937559775678958357)
              ·
                refine ⟨122066903323114484951173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2604093937559775678958357 122066903323114484951173)
                ·
                  rfl

theorem cell19_401160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_401160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401160 prefixEnd_401160 := by exact prefixLift 401160
  have htrace : WordTrace (prefixWord ++ tailWord_401160) baseStart_401160 baseEnd_401160 := by
    simpa [prefixWord, tailWord_401160, baseEnd_401160] using wordTrace_append hprefix tailTrace_401160
  have hstable : (prefixWord ++ tailWord_401160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401160).length < 2 ^ (prefixWord ++ tailWord_401160).sum := by decide
  have hdescent : baseEnd_401160 < baseStart_401160 := by decide
  rcases family_descends (prefixWord ++ tailWord_401160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401175 : List Nat := [1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_401175 : Nat := 118140960795 + 401175 * 2 ^ 59
def prefixEnd_401175 : Nat := 4983230072969 + 3 ^ 40 * 401175 * 2
def baseEnd_401175 : Nat := 122071467595598894617799

theorem tailTrace_401175 : CollatzResearch.WordTrace tailWord_401175 prefixEnd_401175 122071467595598894617799 := by
  unfold tailWord_401175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632054321618965080332979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754702881079310053555319 14632054321618965080332979)
  ·
    refine ⟨21948081482428447620499469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14632054321618965080332979 21948081482428447620499469)
    ·
      refine ⟨8230530555910667857687301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21948081482428447620499469 8230530555910667857687301)
      ·
        refine ⟨1543224479233250223316369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8230530555910667857687301 1543224479233250223316369)
        ·
          refine ⟨1157418359424937667487277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543224479233250223316369 1157418359424937667487277)
          ·
            refine ⟨434031884784351625307729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1157418359424937667487277 434031884784351625307729)
            ·
              refine ⟨325523913588263718980797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434031884784351625307729 325523913588263718980797)
              ·
                refine ⟨122071467595598894617799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325523913588263718980797 122071467595598894617799)
                ·
                  rfl

theorem cell19_401175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_401175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401175 prefixEnd_401175 := by exact prefixLift 401175
  have htrace : WordTrace (prefixWord ++ tailWord_401175) baseStart_401175 baseEnd_401175 := by
    simpa [prefixWord, tailWord_401175, baseEnd_401175] using wordTrace_append hprefix tailTrace_401175
  have hstable : (prefixWord ++ tailWord_401175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401175).length < 2 ^ (prefixWord ++ tailWord_401175).sum := by decide
  have hdescent : baseEnd_401175 < baseStart_401175 := by decide
  rcases family_descends (prefixWord ++ tailWord_401175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401215 : List Nat := [1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_401215 : Nat := 118140960795 + 401215 * 2 ^ 59
def prefixEnd_401215 : Nat := 4983230072969 + 3 ^ 40 * 401215 * 2
def baseEnd_401215 : Nat := 122083638988890653728801

theorem tailTrace_401215 : CollatzResearch.WordTrace tailWord_401215 prefixEnd_401215 122083638988890653728801 := by
  unfold tailWord_401215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633513241474051911789099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9755675494316034607859399 14633513241474051911789099)
  ·
    refine ⟨21950269862211077867683649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14633513241474051911789099 21950269862211077867683649)
    ·
      refine ⟨16462702396658308400762737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21950269862211077867683649 16462702396658308400762737)
      ·
        refine ⟨12347026797493731300572053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16462702396658308400762737 12347026797493731300572053)
        ·
          refine ⟨578766881132518654714315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12347026797493731300572053 578766881132518654714315)
          ·
            refine ⟨868150321698777982071473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578766881132518654714315 868150321698777982071473)
            ·
              refine ⟨651112741274083486553605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868150321698777982071473 651112741274083486553605)
              ·
                refine ⟨122083638988890653728801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651112741274083486553605 122083638988890653728801)
                ·
                  rfl

theorem cell19_401215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_401215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401215 prefixEnd_401215 := by exact prefixLift 401215
  have htrace : WordTrace (prefixWord ++ tailWord_401215) baseStart_401215 baseEnd_401215 := by
    simpa [prefixWord, tailWord_401215, baseEnd_401215] using wordTrace_append hprefix tailTrace_401215
  have hstable : (prefixWord ++ tailWord_401215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401215).length < 2 ^ (prefixWord ++ tailWord_401215).sum := by decide
  have hdescent : baseEnd_401215 < baseStart_401215 := by decide
  rcases family_descends (prefixWord ++ tailWord_401215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401274 : List Nat := [3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_401274 : Nat := 118140960795 + 401274 * 2 ^ 59
def prefixEnd_401274 : Nat := 4983230072969 + 3 ^ 40 * 401274 * 2
def baseEnd_401274 : Nat := 122101591793995998417529

theorem tailTrace_401274 : CollatzResearch.WordTrace tailWord_401274 prefixEnd_401274 122101591793995998417529 := by
  unfold tailWord_401274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3658916287065076247046719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9757110098840203325457917 3658916287065076247046719)
  ·
    refine ⟨5488374430597614370570079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3658916287065076247046719 5488374430597614370570079)
    ·
      refine ⟨8232561645896421555855119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488374430597614370570079 8232561645896421555855119)
      ·
        refine ⟨12348842468844632333782679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232561645896421555855119 12348842468844632333782679)
        ·
          refine ⟨18523263703266948500674019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12348842468844632333782679 18523263703266948500674019)
          ·
            refine ⟨27784895554900422751011029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18523263703266948500674019 27784895554900422751011029)
            ·
              refine ⟨651208489567978658226821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27784895554900422751011029 651208489567978658226821)
              ·
                refine ⟨122101591793995998417529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651208489567978658226821 122101591793995998417529)
                ·
                  rfl

theorem cell19_401274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_401274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401274 prefixEnd_401274 := by exact prefixLift 401274
  have htrace : WordTrace (prefixWord ++ tailWord_401274) baseStart_401274 baseEnd_401274 := by
    simpa [prefixWord, tailWord_401274, baseEnd_401274] using wordTrace_append hprefix tailTrace_401274
  have hstable : (prefixWord ++ tailWord_401274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401274).length < 2 ^ (prefixWord ++ tailWord_401274).sum := by decide
  have hdescent : baseEnd_401274 < baseStart_401274 := by decide
  rcases family_descends (prefixWord ++ tailWord_401274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401441 : List Nat := [1, 2, 3, 2, 5, 1, 1, 4]
def baseStart_401441 : Nat := 118140960795 + 401441 * 2 ^ 59
def prefixEnd_401441 : Nat := 4983230072969 + 3 ^ 40 * 401441 * 2
def baseEnd_401441 : Nat := 122152407360989092705963

theorem tailTrace_401441 : CollatzResearch.WordTrace tailWord_401441 prefixEnd_401441 122152407360989092705963 := by
  unfold tailWord_401441
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641756138655292509516177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9761170759103528339677451 14641756138655292509516177)
  ·
    refine ⟨10981317103991469382137133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14641756138655292509516177 10981317103991469382137133)
    ·
      refine ⟨4117993913996801018301425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10981317103991469382137133 4117993913996801018301425)
      ·
        refine ⟨3088495435497600763726069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4117993913996801018301425 3088495435497600763726069)
        ·
          refine ⟨289546447077900071599319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3088495435497600763726069 289546447077900071599319)
          ·
            refine ⟨434319670616850107398979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289546447077900071599319 434319670616850107398979)
            ·
              refine ⟨651479505925275161098469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434319670616850107398979 651479505925275161098469)
              ·
                refine ⟨122152407360989092705963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651479505925275161098469 122152407360989092705963)
                ·
                  rfl

theorem cell19_401441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_401441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401441 prefixEnd_401441 := by exact prefixLift 401441
  have htrace : WordTrace (prefixWord ++ tailWord_401441) baseStart_401441 baseEnd_401441 := by
    simpa [prefixWord, tailWord_401441, baseEnd_401441] using wordTrace_append hprefix tailTrace_401441
  have hstable : (prefixWord ++ tailWord_401441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401441).length < 2 ^ (prefixWord ++ tailWord_401441).sum := by decide
  have hdescent : baseEnd_401441 < baseStart_401441 := by decide
  rcases family_descends (prefixWord ++ tailWord_401441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401445 : List Nat := [1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_401445 : Nat := 118140960795 + 401445 * 2 ^ 59
def prefixEnd_401445 : Nat := 4983230072969 + 3 ^ 40 * 401445 * 2
def baseEnd_401445 : Nat := 122153624500318268617063

theorem tailTrace_401445 : CollatzResearch.WordTrace tailWord_401445 prefixEnd_401445 122153624500318268617063 := by
  unfold tailWord_401445
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641902030640801192661789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9761268020427200795107859 14641902030640801192661789)
  ·
    refine ⟨5490713261490300447248171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14641902030640801192661789 5490713261490300447248171)
    ·
      refine ⟨8236069892235450670872257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5490713261490300447248171 8236069892235450670872257)
      ·
        refine ⟨6177052419176588003154193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8236069892235450670872257 6177052419176588003154193)
        ·
          refine ⟨4632789314382441002365645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6177052419176588003154193 4632789314382441002365645)
          ·
            refine ⟨1737295992893415375887117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4632789314382441002365645 1737295992893415375887117)
            ·
              refine ⟨651485997335030765957669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1737295992893415375887117 651485997335030765957669)
              ·
                refine ⟨122153624500318268617063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651485997335030765957669 122153624500318268617063)
                ·
                  rfl

theorem cell19_401445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_401445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401445 prefixEnd_401445 := by exact prefixLift 401445
  have htrace : WordTrace (prefixWord ++ tailWord_401445) baseStart_401445 baseEnd_401445 := by
    simpa [prefixWord, tailWord_401445, baseEnd_401445] using wordTrace_append hprefix tailTrace_401445
  have hstable : (prefixWord ++ tailWord_401445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401445).length < 2 ^ (prefixWord ++ tailWord_401445).sum := by decide
  have hdescent : baseEnd_401445 < baseStart_401445 := by decide
  rcases family_descends (prefixWord ++ tailWord_401445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401519 : List Nat := [1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_401519 : Nat := 118140960795 + 401519 * 2 ^ 59
def prefixEnd_401519 : Nat := 4983230072969 + 3 ^ 40 * 401519 * 2
def baseEnd_401519 : Nat := 122176141577908022972417

theorem tailTrace_401519 : CollatzResearch.WordTrace tailWord_401519 prefixEnd_401519 122176141577908022972417 := by
  unfold tailWord_401519
  simp only [CollatzResearch.WordTrace]
  refine ⟨14644601032372711830855611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9763067354915141220570407 14644601032372711830855611)
  ·
    refine ⟨21966901548559067746283417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14644601032372711830855611 21966901548559067746283417)
    ·
      refine ⟨16475176161419300809712563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21966901548559067746283417 16475176161419300809712563)
      ·
        refine ⟨24712764242128951214568845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16475176161419300809712563 24712764242128951214568845)
        ·
          refine ⟨9267286590798356705463317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24712764242128951214568845 9267286590798356705463317)
          ·
            refine ⟨434404058943672970568593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9267286590798356705463317 434404058943672970568593)
            ·
              refine ⟨325803044207754727926445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434404058943672970568593 325803044207754727926445)
              ·
                refine ⟨122176141577908022972417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325803044207754727926445 122176141577908022972417)
                ·
                  rfl

theorem cell19_401519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_401519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401519 prefixEnd_401519 := by exact prefixLift 401519
  have htrace : WordTrace (prefixWord ++ tailWord_401519) baseStart_401519 baseEnd_401519 := by
    simpa [prefixWord, tailWord_401519, baseEnd_401519] using wordTrace_append hprefix tailTrace_401519
  have hstable : (prefixWord ++ tailWord_401519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401519).length < 2 ^ (prefixWord ++ tailWord_401519).sum := by decide
  have hdescent : baseEnd_401519 < baseStart_401519 := by decide
  rcases family_descends (prefixWord ++ tailWord_401519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401612 : List Nat := [2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_401612 : Nat := 118140960795 + 401612 * 2 ^ 59
def prefixEnd_401612 : Nat := 4983230072969 + 3 ^ 40 * 401612 * 2
def baseEnd_401612 : Nat := 122204440067311362905497

theorem tailTrace_401612 : CollatzResearch.WordTrace tailWord_401612 prefixEnd_401612 122204440067311362905497 := by
  unfold tailWord_401612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7323996510517894356995545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9765328680690525809327393 7323996510517894356995545)
  ·
    refine ⟨5492997382888420767746659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7323996510517894356995545 5492997382888420767746659)
    ·
      refine ⟨8239496074332631151619989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492997382888420767746659 8239496074332631151619989)
      ·
        refine ⟨386226378484342085232187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8239496074332631151619989 386226378484342085232187)
        ·
          refine ⟨579339567726513127848281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386226378484342085232187 579339567726513127848281)
          ·
            refine ⟨434504675794884845886211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579339567726513127848281 434504675794884845886211)
            ·
              refine ⟨651757013692327268829317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434504675794884845886211 651757013692327268829317)
              ·
                refine ⟨122204440067311362905497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651757013692327268829317 122204440067311362905497)
                ·
                  rfl

theorem cell19_401612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_401612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401612 prefixEnd_401612 := by exact prefixLift 401612
  have htrace : WordTrace (prefixWord ++ tailWord_401612) baseStart_401612 baseEnd_401612 := by
    simpa [prefixWord, tailWord_401612, baseEnd_401612] using wordTrace_append hprefix tailTrace_401612
  have hstable : (prefixWord ++ tailWord_401612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401612).length < 2 ^ (prefixWord ++ tailWord_401612).sum := by decide
  have hdescent : baseEnd_401612 < baseStart_401612 := by decide
  rcases family_descends (prefixWord ++ tailWord_401612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401614 : List Nat := [4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_401614 : Nat := 118140960795 + 401614 * 2 ^ 59
def prefixEnd_401614 : Nat := 4983230072969 + 3 ^ 40 * 401614 * 2
def baseEnd_401614 : Nat := 122205048636975950861047

theorem tailTrace_401614 : CollatzResearch.WordTrace tailWord_401614 prefixEnd_401614 122205048636975950861047 := by
  unfold tailWord_401614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1831008245878567881945487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9765377311352362037042597 1831008245878567881945487)
  ·
    refine ⟨2746512368817851822918231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1831008245878567881945487 2746512368817851822918231)
    ·
      refine ⟨4119768553226777734377347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746512368817851822918231 4119768553226777734377347)
      ·
        refine ⟨6179652829840166601566021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119768553226777734377347 6179652829840166601566021)
        ·
          refine ⟨1158684905595031237793629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6179652829840166601566021 1158684905595031237793629)
          ·
            refine ⟨434506839598136714172611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1158684905595031237793629 434506839598136714172611)
            ·
              refine ⟨651760259397205071258917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434506839598136714172611 651760259397205071258917)
              ·
                refine ⟨122205048636975950861047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651760259397205071258917 122205048636975950861047)
                ·
                  rfl

theorem cell19_401614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_401614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401614 prefixEnd_401614 := by exact prefixLift 401614
  have htrace : WordTrace (prefixWord ++ tailWord_401614) baseStart_401614 baseEnd_401614 := by
    simpa [prefixWord, tailWord_401614, baseEnd_401614] using wordTrace_append hprefix tailTrace_401614
  have hstable : (prefixWord ++ tailWord_401614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401614).length < 2 ^ (prefixWord ++ tailWord_401614).sum := by decide
  have hdescent : baseEnd_401614 < baseStart_401614 := by decide
  rcases family_descends (prefixWord ++ tailWord_401614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401675 : List Nat := [1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_401675 : Nat := 118140960795 + 401675 * 2 ^ 59
def prefixEnd_401675 : Nat := 4983230072969 + 3 ^ 40 * 401675 * 2
def baseEnd_401675 : Nat := 122223610011745883505325

theorem tailTrace_401675 : CollatzResearch.WordTrace tailWord_401675 prefixEnd_401675 122223610011745883505325 := by
  unfold tailWord_401675
  simp only [CollatzResearch.WordTrace]
  refine ⟨14650290819807550473534479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9766860546538366982356319 14650290819807550473534479)
  ·
    refine ⟨21975436229711325710301719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14650290819807550473534479 21975436229711325710301719)
    ·
      refine ⟨32963154344566988565452579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21975436229711325710301719 32963154344566988565452579)
      ·
        refine ⟨49444731516850482848178869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32963154344566988565452579 49444731516850482848178869)
        ·
          refine ⟨4635443579704732767016769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49444731516850482848178869 4635443579704732767016769)
          ·
            refine ⟨3476582684778549575262577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4635443579704732767016769 3476582684778549575262577)
            ·
              refine ⟨2607437013583912181446933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476582684778549575262577 2607437013583912181446933)
              ·
                refine ⟨122223610011745883505325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2607437013583912181446933 122223610011745883505325)
                ·
                  rfl

theorem cell19_401675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_401675 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401675 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401675 prefixEnd_401675 := by exact prefixLift 401675
  have htrace : WordTrace (prefixWord ++ tailWord_401675) baseStart_401675 baseEnd_401675 := by
    simpa [prefixWord, tailWord_401675, baseEnd_401675] using wordTrace_append hprefix tailTrace_401675
  have hstable : (prefixWord ++ tailWord_401675).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401675).length < 2 ^ (prefixWord ++ tailWord_401675).sum := by decide
  have hdescent : baseEnd_401675 < baseStart_401675 := by decide
  rcases family_descends (prefixWord ++ tailWord_401675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401751 : List Nat := [1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_401751 : Nat := 118140960795 + 401751 * 2 ^ 59
def prefixEnd_401751 : Nat := 4983230072969 + 3 ^ 40 * 401751 * 2
def baseEnd_401751 : Nat := 122246735659000225816229

theorem tailTrace_401751 : CollatzResearch.WordTrace tailWord_401751 prefixEnd_401751 122246735659000225816229 := by
  unfold tailWord_401751
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653062767532215453301107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9768708511688143635534071 14653062767532215453301107)
  ·
    refine ⟨21979594151298323179951661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14653062767532215453301107 21979594151298323179951661)
    ·
      refine ⟨8242347806736871192481873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21979594151298323179951661 8242347806736871192481873)
      ·
        refine ⟨6181760855052653394361405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8242347806736871192481873 6181760855052653394361405)
        ·
          refine ⟨2318160320644745022885527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6181760855052653394361405 2318160320644745022885527)
          ·
            refine ⟨3477240480967117534328291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318160320644745022885527 3477240480967117534328291)
            ·
              refine ⟨5215860721450676301492437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477240480967117534328291 5215860721450676301492437)
              ·
                refine ⟨122246735659000225816229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5215860721450676301492437 122246735659000225816229)
                ·
                  rfl

theorem cell19_401751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_401751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401751 prefixEnd_401751 := by exact prefixLift 401751
  have htrace : WordTrace (prefixWord ++ tailWord_401751) baseStart_401751 baseEnd_401751 := by
    simpa [prefixWord, tailWord_401751, baseEnd_401751] using wordTrace_append hprefix tailTrace_401751
  have hstable : (prefixWord ++ tailWord_401751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401751).length < 2 ^ (prefixWord ++ tailWord_401751).sum := by decide
  have hdescent : baseEnd_401751 < baseStart_401751 := by decide
  rcases family_descends (prefixWord ++ tailWord_401751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401787 : List Nat := [1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_401787 : Nat := 118140960795 + 401787 * 2 ^ 59
def prefixEnd_401787 : Nat := 4983230072969 + 3 ^ 40 * 401787 * 2
def baseEnd_401787 : Nat := 122257689912962809016131

theorem tailTrace_401787 : CollatzResearch.WordTrace tailWord_401787 prefixEnd_401787 122257689912962809016131 := by
  unfold tailWord_401787
  simp only [CollatzResearch.WordTrace]
  refine ⟨14654375795401793601611615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9769583863601195734407743 14654375795401793601611615)
  ·
    refine ⟨21981563693102690402417423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14654375795401793601611615 21981563693102690402417423)
    ·
      refine ⟨32972345539654035603626135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21981563693102690402417423 32972345539654035603626135)
      ·
        refine ⟨49458518309481053405439203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32972345539654035603626135 49458518309481053405439203)
        ·
          refine ⟨74187777464221580108158805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49458518309481053405439203 74187777464221580108158805)
          ·
            refine ⟨434694008579423320946243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 74187777464221580108158805 434694008579423320946243)
            ·
              refine ⟨652041012869134981419365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434694008579423320946243 652041012869134981419365)
              ·
                refine ⟨122257689912962809016131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652041012869134981419365 122257689912962809016131)
                ·
                  rfl

theorem cell19_401787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_401787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401787 prefixEnd_401787 := by exact prefixLift 401787
  have htrace : WordTrace (prefixWord ++ tailWord_401787) baseStart_401787 baseEnd_401787 := by
    simpa [prefixWord, tailWord_401787, baseEnd_401787] using wordTrace_append hprefix tailTrace_401787
  have hstable : (prefixWord ++ tailWord_401787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401787).length < 2 ^ (prefixWord ++ tailWord_401787).sum := by decide
  have hdescent : baseEnd_401787 < baseStart_401787 := by decide
  rcases family_descends (prefixWord ++ tailWord_401787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401802 : List Nat := [3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_401802 : Nat := 118140960795 + 401802 * 2 ^ 59
def prefixEnd_401802 : Nat := 4983230072969 + 3 ^ 40 * 401802 * 2
def baseEnd_401802 : Nat := 122262254185447218682757

theorem tailTrace_401802 : CollatzResearch.WordTrace tailWord_401802 prefixEnd_401802 122262254185447218682757 := by
  unfold tailWord_401802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663730722586862790851915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9769948593564967442271773 3663730722586862790851915)
  ·
    refine ⟨5495596083880294186277873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663730722586862790851915 5495596083880294186277873)
    ·
      refine ⟨4121697062910220639708405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5495596083880294186277873 4121697062910220639708405)
      ·
        refine ⟨386409099647833184972663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4121697062910220639708405 386409099647833184972663)
        ·
          refine ⟨579613649471749777458995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386409099647833184972663 579613649471749777458995)
          ·
            refine ⟨869420474207624666188493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579613649471749777458995 869420474207624666188493)
            ·
              refine ⟨326032677827859249820685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 869420474207624666188493 326032677827859249820685)
              ·
                refine ⟨122262254185447218682757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326032677827859249820685 122262254185447218682757)
                ·
                  rfl

theorem cell19_401802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_401802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401802 prefixEnd_401802 := by exact prefixLift 401802
  have htrace : WordTrace (prefixWord ++ tailWord_401802) baseStart_401802 baseEnd_401802 := by
    simpa [prefixWord, tailWord_401802, baseEnd_401802] using wordTrace_append hprefix tailTrace_401802
  have hstable : (prefixWord ++ tailWord_401802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401802).length < 2 ^ (prefixWord ++ tailWord_401802).sum := by decide
  have hdescent : baseEnd_401802 < baseStart_401802 := by decide
  rcases family_descends (prefixWord ++ tailWord_401802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401827 : List Nat := [1, 1, 1, 4, 1, 5, 6]
def baseStart_401827 : Nat := 118140960795 + 401827 * 2 ^ 59
def prefixEnd_401827 : Nat := 4983230072969 + 3 ^ 40 * 401827 * 2
def baseEnd_401827 : Nat := 40756620435418189375711

theorem tailTrace_401827 : CollatzResearch.WordTrace tailWord_401827 prefixEnd_401827 40756620435418189375711 := by
  unfold tailWord_401827
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655834715256880433067735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9770556476837920288711823 14655834715256880433067735)
  ·
    refine ⟨21983752072885320649601603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14655834715256880433067735 21983752072885320649601603)
    ·
      refine ⟨32975628109327980974402405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21983752072885320649601603 32975628109327980974402405)
      ·
        refine ⟨6182930270498996432700451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32975628109327980974402405 6182930270498996432700451)
        ·
          refine ⟨9274395405748494649050677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182930270498996432700451 9274395405748494649050677)
          ·
            refine ⟨869474569288921373348501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9274395405748494649050677 869474569288921373348501)
            ·
              refine ⟨40756620435418189375711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 869474569288921373348501 40756620435418189375711)
              ·
                rfl

theorem cell19_401827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_401827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401827 prefixEnd_401827 := by exact prefixLift 401827
  have htrace : WordTrace (prefixWord ++ tailWord_401827) baseStart_401827 baseEnd_401827 := by
    simpa [prefixWord, tailWord_401827, baseEnd_401827] using wordTrace_append hprefix tailTrace_401827
  have hstable : (prefixWord ++ tailWord_401827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401827).length < 2 ^ (prefixWord ++ tailWord_401827).sum := by decide
  have hdescent : baseEnd_401827 < baseStart_401827 := by decide
  rcases family_descends (prefixWord ++ tailWord_401827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
