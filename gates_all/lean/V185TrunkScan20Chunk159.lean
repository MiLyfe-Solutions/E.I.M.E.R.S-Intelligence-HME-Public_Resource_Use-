import V185TrunkScan20Chunk158

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_967751 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_967751 : Nat := 118140960795 + 967751 * 2 ^ 59
def prefixEnd_967751 : Nat := 4983230072969 + 3 ^ 40 * 967751 * 2
def baseEnd_967751 : Nat := 441707926106087469743911

theorem tailTrace_967751 : CollatzResearch.WordTrace tailWord_967751 prefixEnd_967751 441707926106087469743911 := by
  unfold tailWord_967751
  simp only [CollatzResearch.WordTrace]
  refine ⟨35296778717010880557399107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23531185811340587038266071 35296778717010880557399107)
  ·
    refine ⟨52945168075516320836098661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35296778717010880557399107 52945168075516320836098661)
    ·
      refine ⟨9927219014159310156768499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52945168075516320836098661 9927219014159310156768499)
      ·
        refine ⟨14890828521238965235152749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9927219014159310156768499 14890828521238965235152749)
        ·
          refine ⟨5584060695464611963182281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14890828521238965235152749 5584060695464611963182281)
          ·
            refine ⟨4188045521598458972386711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584060695464611963182281 4188045521598458972386711)
            ·
              refine ⟨6282068282397688458580067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188045521598458972386711 6282068282397688458580067)
              ·
                refine ⟨9423102423596532687870101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282068282397688458580067 9423102423596532687870101)
                ·
                  refine ⟨441707926106087469743911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9423102423596532687870101 441707926106087469743911)
                  ·
                    rfl

theorem cell20_967751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_967751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967751 prefixEnd_967751 := by exact prefixLift 967751
  have htrace : WordTrace (prefixWord ++ tailWord_967751) baseStart_967751 baseEnd_967751 := by
    simpa [prefixWord, tailWord_967751, baseEnd_967751] using wordTrace_append hprefix tailTrace_967751
  have hstable : (prefixWord ++ tailWord_967751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967751).length < 2 ^ (prefixWord ++ tailWord_967751).sum := by decide
  have hdescent : baseEnd_967751 < baseStart_967751 := by decide
  rcases family_descends (prefixWord ++ tailWord_967751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967774 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_967774 : Nat := 118140960795 + 967774 * 2 ^ 59
def prefixEnd_967774 : Nat := 4983230072969 + 3 ^ 40 * 967774 * 2
def baseEnd_967774 : Nat := 441718423932801611977151

theorem tailTrace_967774 : CollatzResearch.WordTrace tailWord_967774 prefixEnd_967774 441718423932801611977151 := by
  unfold tailWord_967774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412202199490944435685797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23531745063951703656990917 4412202199490944435685797)
  ·
    refine ⟨827287912404552081691087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4412202199490944435685797 827287912404552081691087)
    ·
      refine ⟨1240931868606828122536631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827287912404552081691087 1240931868606828122536631)
      ·
        refine ⟨1861397802910242183804947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240931868606828122536631 1861397802910242183804947)
        ·
          refine ⟨2792096704365363275707421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861397802910242183804947 2792096704365363275707421)
          ·
            refine ⟨1047036264137011228390283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2792096704365363275707421 1047036264137011228390283)
            ·
              refine ⟨1570554396205516842585425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047036264137011228390283 1570554396205516842585425)
              ·
                refine ⟨1177915797154137631939069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570554396205516842585425 1177915797154137631939069)
                ·
                  refine ⟨441718423932801611977151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177915797154137631939069 441718423932801611977151)
                  ·
                    rfl

theorem cell20_967774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_967774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967774 prefixEnd_967774 := by exact prefixLift 967774
  have htrace : WordTrace (prefixWord ++ tailWord_967774) baseStart_967774 baseEnd_967774 := by
    simpa [prefixWord, tailWord_967774, baseEnd_967774] using wordTrace_append hprefix tailTrace_967774
  have hstable : (prefixWord ++ tailWord_967774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967774).length < 2 ^ (prefixWord ++ tailWord_967774).sum := by decide
  have hdescent : baseEnd_967774 < baseStart_967774 := by decide
  rcases family_descends (prefixWord ++ tailWord_967774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967778 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_967778 : Nat := 118140960795 + 967778 * 2 ^ 59
def prefixEnd_967778 : Nat := 4983230072969 + 3 ^ 40 * 967778 * 2
def baseEnd_967778 : Nat := 441720249641795375843801

theorem tailTrace_967778 : CollatzResearch.WordTrace tailWord_967778 prefixEnd_967778 441720249641795375843801 := by
  unfold tailWord_967778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8824440871978266042157997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23531842325275376112421325 8824440871978266042157997)
  ·
    refine ⟨3309165326991849765809249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8824440871978266042157997 3309165326991849765809249)
    ·
      refine ⟨2481873995243887324356937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3309165326991849765809249 2481873995243887324356937)
      ·
        refine ⟨1861405496432915493267703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2481873995243887324356937 1861405496432915493267703)
        ·
          refine ⟨2792108244649373239901555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861405496432915493267703 2792108244649373239901555)
          ·
            refine ⟨4188162366974059859852333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792108244649373239901555 4188162366974059859852333)
            ·
              refine ⟨1570560887615272447444625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4188162366974059859852333 1570560887615272447444625)
              ·
                refine ⟨1177920665711454335583469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570560887615272447444625 1177920665711454335583469)
                ·
                  refine ⟨441720249641795375843801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177920665711454335583469 441720249641795375843801)
                  ·
                    rfl

theorem cell20_967778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_967778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967778 prefixEnd_967778 := by exact prefixLift 967778
  have htrace : WordTrace (prefixWord ++ tailWord_967778) baseStart_967778 baseEnd_967778 := by
    simpa [prefixWord, tailWord_967778, baseEnd_967778] using wordTrace_append hprefix tailTrace_967778
  have hstable : (prefixWord ++ tailWord_967778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967778).length < 2 ^ (prefixWord ++ tailWord_967778).sum := by decide
  have hdescent : baseEnd_967778 < baseStart_967778 := by decide
  rcases family_descends (prefixWord ++ tailWord_967778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967799 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 3]
def baseStart_967799 : Nat := 118140960795 + 967799 * 2 ^ 59
def prefixEnd_967799 : Nat := 4983230072969 + 3 ^ 40 * 967799 * 2
def baseEnd_967799 : Nat := 441729834614012636143715

theorem tailTrace_967799 : CollatzResearch.WordTrace tailWord_967799 prefixEnd_967799 441729834614012636143715 := by
  unfold tailWord_967799
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298529420836984755146451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23532352947224656503430967 35298529420836984755146451)
  ·
    refine ⟨52947794131255477132719677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35298529420836984755146451 52947794131255477132719677)
    ·
      refine ⟨19855422799220803924769879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52947794131255477132719677 19855422799220803924769879)
      ·
        refine ⟨29783134198831205887154819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855422799220803924769879 29783134198831205887154819)
        ·
          refine ⟨44674701298246808830732229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29783134198831205887154819 44674701298246808830732229)
          ·
            refine ⟨8376506493421276655762293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44674701298246808830732229 8376506493421276655762293)
            ·
              refine ⟨785297483758244686477715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8376506493421276655762293 785297483758244686477715)
              ·
                refine ⟨1177946225637367029716573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785297483758244686477715 1177946225637367029716573)
                ·
                  refine ⟨441729834614012636143715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177946225637367029716573 441729834614012636143715)
                  ·
                    rfl

theorem cell20_967799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_967799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967799 prefixEnd_967799 := by exact prefixLift 967799
  have htrace : WordTrace (prefixWord ++ tailWord_967799) baseStart_967799 baseEnd_967799 := by
    simpa [prefixWord, tailWord_967799, baseEnd_967799] using wordTrace_append hprefix tailTrace_967799
  have hstable : (prefixWord ++ tailWord_967799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967799).length < 2 ^ (prefixWord ++ tailWord_967799).sum := by decide
  have hdescent : baseEnd_967799 < baseStart_967799 := by decide
  rcases family_descends (prefixWord ++ tailWord_967799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967813 : List Nat := [1, 3, 1, 1, 6, 1, 1, 6]
def baseStart_967813 : Nat := 118140960795 + 967813 * 2 ^ 59
def prefixEnd_967813 : Nat := 4983230072969 + 3 ^ 40 * 967813 * 2
def baseEnd_967813 : Nat := 147245408198496936558997

theorem tailTrace_967813 : CollatzResearch.WordTrace tailWord_967813 prefixEnd_967813 147245408198496936558997 := by
  unfold tailWord_967813
  simp only [CollatzResearch.WordTrace]
  refine ⟨35299040042786265146156093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23532693361857510097437395 35299040042786265146156093)
  ·
    refine ⟨13237140016044849429808535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35299040042786265146156093 13237140016044849429808535)
    ·
      refine ⟨19855710024067274144712803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237140016044849429808535 19855710024067274144712803)
      ·
        refine ⟨29783565036100911217069205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855710024067274144712803 29783565036100911217069205)
        ·
          refine ⟨1396104611067230213300119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29783565036100911217069205 1396104611067230213300119)
          ·
            refine ⟨2094156916600845319950179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396104611067230213300119 2094156916600845319950179)
            ·
              refine ⟨3141235374901267979925269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094156916600845319950179 3141235374901267979925269)
              ·
                refine ⟨147245408198496936558997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3141235374901267979925269 147245408198496936558997)
                ·
                  rfl

theorem cell20_967813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_967813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967813 prefixEnd_967813 := by exact prefixLift 967813
  have htrace : WordTrace (prefixWord ++ tailWord_967813) baseStart_967813 baseEnd_967813 := by
    simpa [prefixWord, tailWord_967813, baseEnd_967813] using wordTrace_append hprefix tailTrace_967813
  have hstable : (prefixWord ++ tailWord_967813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967813).length < 2 ^ (prefixWord ++ tailWord_967813).sum := by decide
  have hdescent : baseEnd_967813 < baseStart_967813 := by decide
  rcases family_descends (prefixWord ++ tailWord_967813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967844 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_967844 : Nat := 118140960795 + 967844 * 2 ^ 59
def prefixEnd_967844 : Nat := 4983230072969 + 3 ^ 40 * 967844 * 2
def baseEnd_967844 : Nat := 441750373840192479643531

theorem tailTrace_967844 : CollatzResearch.WordTrace tailWord_967844 prefixEnd_967844 441750373840192479643531 := by
  unfold tailWord_967844
  simp only [CollatzResearch.WordTrace]
  refine ⟨17650085352836978720267293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23533447137115971627023057 17650085352836978720267293)
  ·
    refine ⟨6618782007313867020100235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17650085352836978720267293 6618782007313867020100235)
    ·
      refine ⟨9928173010970800530150353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6618782007313867020100235 9928173010970800530150353)
      ·
        refine ⟨7446129758228100397612765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9928173010970800530150353 7446129758228100397612765)
        ·
          refine ⟨2792298659335537649104787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7446129758228100397612765 2792298659335537649104787)
          ·
            refine ⟨4188447989003306473657181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792298659335537649104787 4188447989003306473657181)
            ·
              refine ⟨1570667995876239927621443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4188447989003306473657181 1570667995876239927621443)
              ·
                refine ⟨2356001993814359891432165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570667995876239927621443 2356001993814359891432165)
                ·
                  refine ⟨441750373840192479643531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2356001993814359891432165 441750373840192479643531)
                  ·
                    rfl

theorem cell20_967844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_967844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967844 prefixEnd_967844 := by exact prefixLift 967844
  have htrace : WordTrace (prefixWord ++ tailWord_967844) baseStart_967844 baseEnd_967844 := by
    simpa [prefixWord, tailWord_967844, baseEnd_967844] using wordTrace_append hprefix tailTrace_967844
  have hstable : (prefixWord ++ tailWord_967844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967844).length < 2 ^ (prefixWord ++ tailWord_967844).sum := by decide
  have hdescent : baseEnd_967844 < baseStart_967844 := by decide
  rcases family_descends (prefixWord ++ tailWord_967844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967879 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_967879 : Nat := 118140960795 + 967879 * 2 ^ 59
def prefixEnd_967879 : Nat := 4983230072969 + 3 ^ 40 * 967879 * 2
def baseEnd_967879 : Nat := 441766348793887913476721

theorem tailTrace_967879 : CollatzResearch.WordTrace tailWord_967879 prefixEnd_967879 441766348793887913476721 := by
  unfold tailWord_967879
  simp only [CollatzResearch.WordTrace]
  refine ⟨35301447260547158418058691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23534298173698105612039127 35301447260547158418058691)
  ·
    refine ⟨52952170890820737627088037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35301447260547158418058691 52952170890820737627088037)
    ·
      refine ⟨9928532042028888305079007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52952170890820737627088037 9928532042028888305079007)
      ·
        refine ⟨14892798063043332457618511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928532042028888305079007 14892798063043332457618511)
        ·
          refine ⟨22339197094564998686427767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14892798063043332457618511 22339197094564998686427767)
          ·
            refine ⟨33508795641847498029641651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22339197094564998686427767 33508795641847498029641651)
            ·
              refine ⟨50263193462771247044462477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33508795641847498029641651 50263193462771247044462477)
              ·
                refine ⟨18848697548539217641673429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50263193462771247044462477 18848697548539217641673429)
                ·
                  refine ⟨441766348793887913476721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18848697548539217641673429 441766348793887913476721)
                  ·
                    rfl

theorem cell20_967879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_967879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967879 prefixEnd_967879 := by exact prefixLift 967879
  have htrace : WordTrace (prefixWord ++ tailWord_967879) baseStart_967879 baseEnd_967879 := by
    simpa [prefixWord, tailWord_967879, baseEnd_967879] using wordTrace_append hprefix tailTrace_967879
  have hstable : (prefixWord ++ tailWord_967879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967879).length < 2 ^ (prefixWord ++ tailWord_967879).sum := by decide
  have hdescent : baseEnd_967879 < baseStart_967879 := by decide
  rcases family_descends (prefixWord ++ tailWord_967879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967885 : List Nat := [1, 6, 2, 2, 2, 7]
def baseStart_967885 : Nat := 118140960795 + 967885 * 2 ^ 59
def prefixEnd_967885 : Nat := 4983230072969 + 3 ^ 40 * 967885 * 2
def baseEnd_967885 : Nat := 16361818050273279973211

theorem tailTrace_967885 : CollatzResearch.WordTrace tailWord_967885 prefixEnd_967885 16361818050273279973211 := by
  unfold tailWord_967885
  simp only [CollatzResearch.WordTrace]
  refine ⟨35301666098525421442777109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23534444065683614295184739 35301666098525421442777109)
  ·
    refine ⟨1654765598368379130130177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35301666098525421442777109 1654765598368379130130177)
    ·
      refine ⟨1241074198776284347597633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1654765598368379130130177 1241074198776284347597633)
      ·
        refine ⟨930805649082213260698225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241074198776284347597633 930805649082213260698225)
        ·
          refine ⟨698104236811659945523669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930805649082213260698225 698104236811659945523669)
          ·
            refine ⟨16361818050273279973211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 698104236811659945523669 16361818050273279973211)
            ·
              rfl

theorem cell20_967885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 7].length) (baseStart_967885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967885 prefixEnd_967885 := by exact prefixLift 967885
  have htrace : WordTrace (prefixWord ++ tailWord_967885) baseStart_967885 baseEnd_967885 := by
    simpa [prefixWord, tailWord_967885, baseEnd_967885] using wordTrace_append hprefix tailTrace_967885
  have hstable : (prefixWord ++ tailWord_967885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967885).length < 2 ^ (prefixWord ++ tailWord_967885).sum := by decide
  have hdescent : baseEnd_967885 < baseStart_967885 := by decide
  rcases family_descends (prefixWord ++ tailWord_967885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967937 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 2]
def baseStart_967937 : Nat := 118140960795 + 967937 * 2 ^ 59
def prefixEnd_967937 : Nat := 4983230072969 + 3 ^ 40 * 967937 * 2
def baseEnd_967937 : Nat := 441792821574297489543151

theorem tailTrace_967937 : CollatzResearch.WordTrace tailWord_967937 prefixEnd_967937 441792821574297489543151 := by
  unfold tailWord_967937
  simp only [CollatzResearch.WordTrace]
  refine ⟨35303562694337034323670065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23535708462891356215780043 35303562694337034323670065)
  ·
    refine ⟨26477672020752775742752549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35303562694337034323670065 26477672020752775742752549)
    ·
      refine ⟨4964563503891145451766103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26477672020752775742752549 4964563503891145451766103)
      ·
        refine ⟨7446845255836718177649155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4964563503891145451766103 7446845255836718177649155)
        ·
          refine ⟨11170267883755077266473733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7446845255836718177649155 11170267883755077266473733)
          ·
            refine ⟨2094425228204076987463825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11170267883755077266473733 2094425228204076987463825)
            ·
              refine ⟨1570818921153057740597869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094425228204076987463825 1570818921153057740597869)
              ·
                refine ⟨589057095432396652724201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1570818921153057740597869 589057095432396652724201)
                ·
                  refine ⟨441792821574297489543151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589057095432396652724201 441792821574297489543151)
                  ·
                    rfl

theorem cell20_967937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_967937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967937 prefixEnd_967937 := by exact prefixLift 967937
  have htrace : WordTrace (prefixWord ++ tailWord_967937) baseStart_967937 baseEnd_967937 := by
    simpa [prefixWord, tailWord_967937, baseEnd_967937] using wordTrace_append hprefix tailTrace_967937
  have hstable : (prefixWord ++ tailWord_967937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967937).length < 2 ^ (prefixWord ++ tailWord_967937).sum := by decide
  have hdescent : baseEnd_967937 < baseStart_967937 := by decide
  rcases family_descends (prefixWord ++ tailWord_967937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967948 : List Nat := [2, 2, 1, 2, 2, 4, 7]
def baseStart_967948 : Nat := 118140960795 + 967948 * 2 ^ 59
def prefixEnd_967948 : Nat := 4983230072969 + 3 ^ 40 * 967948 * 2
def baseEnd_967948 : Nat := 49088649141558926686271

theorem tailTrace_967948 : CollatzResearch.WordTrace tailWord_967948 prefixEnd_967948 49088649141558926686271 := by
  unfold tailWord_967948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17651981948648591601160249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23535975931531455468213665 17651981948648591601160249)
  ·
    refine ⟨13238986461486443700870187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17651981948648591601160249 13238986461486443700870187)
    ·
      refine ⟨19858479692229665551305281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13238986461486443700870187 19858479692229665551305281)
      ·
        refine ⟨14893859769172249163478961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19858479692229665551305281 14893859769172249163478961)
        ·
          refine ⟨11170394826879186872609221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14893859769172249163478961 11170394826879186872609221)
          ·
            refine ⟨2094449030039847538614229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11170394826879186872609221 2094449030039847538614229)
            ·
              refine ⟨49088649141558926686271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2094449030039847538614229 49088649141558926686271)
              ·
                rfl

theorem cell20_967948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_967948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967948 prefixEnd_967948 := by exact prefixLift 967948
  have htrace : WordTrace (prefixWord ++ tailWord_967948) baseStart_967948 baseEnd_967948 := by
    simpa [prefixWord, tailWord_967948, baseEnd_967948] using wordTrace_append hprefix tailTrace_967948
  have hstable : (prefixWord ++ tailWord_967948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967948).length < 2 ^ (prefixWord ++ tailWord_967948).sum := by decide
  have hdescent : baseEnd_967948 < baseStart_967948 := by decide
  rcases family_descends (prefixWord ++ tailWord_967948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967954 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_967954 : Nat := 118140960795 + 967954 * 2 ^ 59
def prefixEnd_967954 : Nat := 4983230072969 + 3 ^ 40 * 967954 * 2
def baseEnd_967954 : Nat := 441800580837520985976415

theorem tailTrace_967954 : CollatzResearch.WordTrace tailWord_967954 prefixEnd_967954 441800580837520985976415 := by
  unfold tailWord_967954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8826045683818861556759729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23536121823516964151359277 8826045683818861556759729)
  ·
    refine ⟨6619534262864146167569797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8826045683818861556759729 6619534262864146167569797)
    ·
      refine ⟨1241162674287027406419337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6619534262864146167569797 1241162674287027406419337)
      ·
        refine ⟨930872005715270554814503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241162674287027406419337 930872005715270554814503)
        ·
          refine ⟨1396308008572905832221755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930872005715270554814503 1396308008572905832221755)
          ·
            refine ⟨2094462012859358748332633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396308008572905832221755 2094462012859358748332633)
            ·
              refine ⟨1570846509644519061249475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094462012859358748332633 1570846509644519061249475)
              ·
                refine ⟨2356269764466778591874213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570846509644519061249475 2356269764466778591874213)
                ·
                  refine ⟨441800580837520985976415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2356269764466778591874213 441800580837520985976415)
                  ·
                    rfl

theorem cell20_967954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_967954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967954 prefixEnd_967954 := by exact prefixLift 967954
  have htrace : WordTrace (prefixWord ++ tailWord_967954) baseStart_967954 baseEnd_967954 := by
    simpa [prefixWord, tailWord_967954, baseEnd_967954] using wordTrace_append hprefix tailTrace_967954
  have hstable : (prefixWord ++ tailWord_967954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967954).length < 2 ^ (prefixWord ++ tailWord_967954).sum := by decide
  have hdescent : baseEnd_967954 < baseStart_967954 := by decide
  rcases family_descends (prefixWord ++ tailWord_967954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967968 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_967968 : Nat := 118140960795 + 967968 * 2 ^ 59
def prefixEnd_967968 : Nat := 4983230072969 + 3 ^ 40 * 967968 * 2
def baseEnd_967968 : Nat := 441806970818999159509691

theorem tailTrace_967968 : CollatzResearch.WordTrace tailWord_967968 prefixEnd_967968 441806970818999159509691 := by
  unfold tailWord_967968
  simp only [CollatzResearch.WordTrace]
  refine ⟨17652346678612363309024279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23536462238149817745365705 17652346678612363309024279)
  ·
    refine ⟨26478520017918544963536419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17652346678612363309024279 26478520017918544963536419)
    ·
      refine ⟨39717780026877817445304629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26478520017918544963536419 39717780026877817445304629)
      ·
        refine ⟨3723541877519795385497309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39717780026877817445304629 3723541877519795385497309)
        ·
          refine ⟨1396328204069923269561491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3723541877519795385497309 1396328204069923269561491)
          ·
            refine ⟨2094492306104884904342237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396328204069923269561491 2094492306104884904342237)
            ·
              refine ⟨785434614789331839128339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094492306104884904342237 785434614789331839128339)
              ·
                refine ⟨1178151922183997758692509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785434614789331839128339 1178151922183997758692509)
                ·
                  refine ⟨441806970818999159509691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178151922183997758692509 441806970818999159509691)
                  ·
                    rfl

theorem cell20_967968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_967968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_967968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_967968 prefixEnd_967968 := by exact prefixLift 967968
  have htrace : WordTrace (prefixWord ++ tailWord_967968) baseStart_967968 baseEnd_967968 := by
    simpa [prefixWord, tailWord_967968, baseEnd_967968] using wordTrace_append hprefix tailTrace_967968
  have hstable : (prefixWord ++ tailWord_967968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967968).length < 2 ^ (prefixWord ++ tailWord_967968).sum := by decide
  have hdescent : baseEnd_967968 < baseStart_967968 := by decide
  rcases family_descends (prefixWord ++ tailWord_967968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968024 : List Nat := [2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_968024 : Nat := 118140960795 + 968024 * 2 ^ 59
def prefixEnd_968024 : Nat := 4983230072969 + 3 ^ 40 * 968024 * 2
def baseEnd_968024 : Nat := 147277510248303951214265

theorem tailTrace_968024 : CollatzResearch.WordTrace tailWord_968024 prefixEnd_968024 147277510248303951214265 := by
  unfold tailWord_968024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17653367922510924091043563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23537823896681232121391417 17653367922510924091043563)
  ·
    refine ⟨26480051883766386136565345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17653367922510924091043563 26480051883766386136565345)
    ·
      refine ⟨19860038912824789602424009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26480051883766386136565345 19860038912824789602424009)
      ·
        refine ⟨14895029184618592201818007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19860038912824789602424009 14895029184618592201818007)
        ·
          refine ⟨22342543776927888302727011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14895029184618592201818007 22342543776927888302727011)
          ·
            refine ⟨33513815665391832454090517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22342543776927888302727011 33513815665391832454090517)
            ·
              refine ⟨1570960109315242146285493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33513815665391832454090517 1570960109315242146285493)
              ·
                refine ⟨147277510248303951214265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1570960109315242146285493 147277510248303951214265)
                ·
                  rfl

theorem cell20_968024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_968024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968024 prefixEnd_968024 := by exact prefixLift 968024
  have htrace : WordTrace (prefixWord ++ tailWord_968024) baseStart_968024 baseEnd_968024 := by
    simpa [prefixWord, tailWord_968024, baseEnd_968024] using wordTrace_append hprefix tailTrace_968024
  have hstable : (prefixWord ++ tailWord_968024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968024).length < 2 ^ (prefixWord ++ tailWord_968024).sum := by decide
  have hdescent : baseEnd_968024 < baseStart_968024 := by decide
  rcases family_descends (prefixWord ++ tailWord_968024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968068 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 2]
def baseStart_968068 : Nat := 118140960795 + 968068 * 2 ^ 59
def prefixEnd_968068 : Nat := 4983230072969 + 3 ^ 40 * 968068 * 2
def baseEnd_968068 : Nat := 441852613543843256175949

theorem tailTrace_968068 : CollatzResearch.WordTrace tailWord_968068 prefixEnd_968068 441852613543843256175949 := by
  unfold tailWord_968068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17654170328431221848344429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23538893771241629131125905 17654170328431221848344429)
  ·
    refine ⟨6620313873161708193129161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17654170328431221848344429 6620313873161708193129161)
    ·
      refine ⟨4965235404871281144846871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6620313873161708193129161 4965235404871281144846871)
      ·
        refine ⟨7447853107306921717270307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965235404871281144846871 7447853107306921717270307)
        ·
          refine ⟨11171779660960382575905461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447853107306921717270307 11171779660960382575905461)
          ·
            refine ⟨1047354343215035866491137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11171779660960382575905461 1047354343215035866491137)
            ·
              refine ⟨785515757411276899868353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047354343215035866491137 785515757411276899868353)
              ·
                refine ⟨589136818058457674901265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785515757411276899868353 589136818058457674901265)
                ·
                  refine ⟨441852613543843256175949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589136818058457674901265 441852613543843256175949)
                  ·
                    rfl

theorem cell20_968068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_968068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968068 prefixEnd_968068 := by exact prefixLift 968068
  have htrace : WordTrace (prefixWord ++ tailWord_968068) baseStart_968068 baseEnd_968068 := by
    simpa [prefixWord, tailWord_968068, baseEnd_968068] using wordTrace_append hprefix tailTrace_968068
  have hstable : (prefixWord ++ tailWord_968068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968068).length < 2 ^ (prefixWord ++ tailWord_968068).sum := by decide
  have hdescent : baseEnd_968068 < baseStart_968068 := by decide
  rcases family_descends (prefixWord ++ tailWord_968068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968069 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_968069 : Nat := 118140960795 + 968069 * 2 ^ 59
def prefixEnd_968069 : Nat := 4983230072969 + 3 ^ 40 * 968069 * 2
def baseEnd_968069 : Nat := 441853069971091697142611

theorem tailTrace_968069 : CollatzResearch.WordTrace tailWord_968069 prefixEnd_968069 441853069971091697142611 := by
  unfold tailWord_968069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35308377129858820867475261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23538918086572547244983507 35308377129858820867475261)
  ·
    refine ⟨13240641423697057825303223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35308377129858820867475261 13240641423697057825303223)
    ·
      refine ⟨19860962135545586737954835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13240641423697057825303223 19860962135545586737954835)
      ·
        refine ⟨29791443203318380106932253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19860962135545586737954835 29791443203318380106932253)
        ·
          refine ⟨11171791201244392540099595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29791443203318380106932253 11171791201244392540099595)
          ·
            refine ⟨16757686801866588810149393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11171791201244392540099595 16757686801866588810149393)
            ·
              refine ⟨12568265101399941607612045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16757686801866588810149393 12568265101399941607612045)
              ·
                refine ⟨4713099413024978102854517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12568265101399941607612045 4713099413024978102854517)
                ·
                  refine ⟨441853069971091697142611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4713099413024978102854517 441853069971091697142611)
                  ·
                    rfl

theorem cell20_968069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_968069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968069 prefixEnd_968069 := by exact prefixLift 968069
  have htrace : WordTrace (prefixWord ++ tailWord_968069) baseStart_968069 baseEnd_968069 := by
    simpa [prefixWord, tailWord_968069, baseEnd_968069] using wordTrace_append hprefix tailTrace_968069
  have hstable : (prefixWord ++ tailWord_968069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968069).length < 2 ^ (prefixWord ++ tailWord_968069).sum := by decide
  have hdescent : baseEnd_968069 < baseStart_968069 := by decide
  rcases family_descends (prefixWord ++ tailWord_968069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968093 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_968093 : Nat := 118140960795 + 968093 * 2 ^ 59
def prefixEnd_968093 : Nat := 4983230072969 + 3 ^ 40 * 968093 * 2
def baseEnd_968093 : Nat := 441864024225054280342513

theorem tailTrace_968093 : CollatzResearch.WordTrace tailWord_968093 prefixEnd_968093 441864024225054280342513 := by
  unfold tailWord_968093
  simp only [CollatzResearch.WordTrace]
  refine ⟨35309252481771872966348933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23539501654514581977565955 35309252481771872966348933)
  ·
    refine ⟨6620484840332226181190425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35309252481771872966348933 6620484840332226181190425)
    ·
      refine ⟨4965363630249169635892819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6620484840332226181190425 4965363630249169635892819)
      ·
        refine ⟨7448045445373754453839229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965363630249169635892819 7448045445373754453839229)
        ·
          refine ⟨2793017042015157920189711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7448045445373754453839229 2793017042015157920189711)
          ·
            refine ⟨4189525563022736880284567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793017042015157920189711 4189525563022736880284567)
            ·
              refine ⟨6284288344534105320426851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189525563022736880284567 6284288344534105320426851)
              ·
                refine ⟨9426432516801157980640277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284288344534105320426851 9426432516801157980640277)
                ·
                  refine ⟨441864024225054280342513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9426432516801157980640277 441864024225054280342513)
                  ·
                    rfl

theorem cell20_968093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_968093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968093 prefixEnd_968093 := by exact prefixLift 968093
  have htrace : WordTrace (prefixWord ++ tailWord_968093) baseStart_968093 baseEnd_968093 := by
    simpa [prefixWord, tailWord_968093, baseEnd_968093] using wordTrace_append hprefix tailTrace_968093
  have hstable : (prefixWord ++ tailWord_968093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968093).length < 2 ^ (prefixWord ++ tailWord_968093).sum := by decide
  have hdescent : baseEnd_968093 < baseStart_968093 := by decide
  rcases family_descends (prefixWord ++ tailWord_968093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968165 : List Nat := [1, 3, 1, 5, 1, 1, 3, 3, 2]
def baseStart_968165 : Nat := 118140960795 + 968165 * 2 ^ 59
def prefixEnd_968165 : Nat := 4983230072969 + 3 ^ 40 * 968165 * 2
def baseEnd_968165 : Nat := 441896886986942029942219

theorem tailTrace_968165 : CollatzResearch.WordTrace tailWord_968165 prefixEnd_968165 441896886986942029942219 := by
  unfold tailWord_968165
  simp only [CollatzResearch.WordTrace]
  refine ⟨35311878537511029262969949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23541252358340686175313299 35311878537511029262969949)
  ·
    refine ⟨13241954451566635973613731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35311878537511029262969949 13241954451566635973613731)
    ·
      refine ⟨19862931677349953960420597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13241954451566635973613731 19862931677349953960420597)
      ·
        refine ⟨1862149844751558183789431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19862931677349953960420597 1862149844751558183789431)
        ·
          refine ⟨2793224767127337275684147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862149844751558183789431 2793224767127337275684147)
          ·
            refine ⟨4189837150691005913526221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793224767127337275684147 4189837150691005913526221)
            ·
              refine ⟨1571188931509127217572333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4189837150691005913526221 1571188931509127217572333)
              ·
                refine ⟨589195849315922706589625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1571188931509127217572333 589195849315922706589625)
                ·
                  refine ⟨441896886986942029942219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589195849315922706589625 441896886986942029942219)
                  ·
                    rfl

theorem cell20_968165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_968165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968165 prefixEnd_968165 := by exact prefixLift 968165
  have htrace : WordTrace (prefixWord ++ tailWord_968165) baseStart_968165 baseEnd_968165 := by
    simpa [prefixWord, tailWord_968165, baseEnd_968165] using wordTrace_append hprefix tailTrace_968165
  have hstable : (prefixWord ++ tailWord_968165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968165).length < 2 ^ (prefixWord ++ tailWord_968165).sum := by decide
  have hdescent : baseEnd_968165 < baseStart_968165 := by decide
  rcases family_descends (prefixWord ++ tailWord_968165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968176 : List Nat := [2, 1, 1, 1, 3, 6, 6]
def baseStart_968176 : Nat := 118140960795 + 968176 * 2 ^ 59
def prefixEnd_968176 : Nat := 4983230072969 + 3 ^ 40 * 968176 * 2
def baseEnd_968176 : Nat := 49100211965186097841723

theorem tailTrace_968176 : CollatzResearch.WordTrace tailWord_968176 prefixEnd_968176 49100211965186097841723 := by
  unfold tailWord_968176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656139870235589070810191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23541519826980785427746921 17656139870235589070810191)
  ·
    refine ⟨26484209805353383606215287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656139870235589070810191 26484209805353383606215287)
    ·
      refine ⟨39726314708030075409322931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26484209805353383606215287 39726314708030075409322931)
      ·
        refine ⟨59589472062045113113984397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39726314708030075409322931 59589472062045113113984397)
        ·
          refine ⟨22346052023266917417744149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59589472062045113113984397 22346052023266917417744149)
          ·
            refine ⟨1047471188590636753956757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22346052023266917417744149 1047471188590636753956757)
            ·
              refine ⟨49100211965186097841723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1047471188590636753956757 49100211965186097841723)
              ·
                rfl

theorem cell20_968176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 6].length) (baseStart_968176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968176 prefixEnd_968176 := by exact prefixLift 968176
  have htrace : WordTrace (prefixWord ++ tailWord_968176) baseStart_968176 baseEnd_968176 := by
    simpa [prefixWord, tailWord_968176, baseEnd_968176] using wordTrace_append hprefix tailTrace_968176
  have hstable : (prefixWord ++ tailWord_968176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968176).length < 2 ^ (prefixWord ++ tailWord_968176).sum := by decide
  have hdescent : baseEnd_968176 < baseStart_968176 := by decide
  rcases family_descends (prefixWord ++ tailWord_968176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968182 : List Nat := [5, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_968182 : Nat := 118140960795 + 968182 * 2 ^ 59
def prefixEnd_968182 : Nat := 4983230072969 + 3 ^ 40 * 968182 * 2
def baseEnd_968182 : Nat := 441904646250165526375483

theorem tailTrace_968182 : CollatzResearch.WordTrace tailWord_968182 prefixEnd_968182 441904646250165526375483 := by
  unfold tailWord_968182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207031161153090072896175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23541665718966294110892533 2207031161153090072896175)
  ·
    refine ⟨3310546741729635109344263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2207031161153090072896175 3310546741729635109344263)
    ·
      refine ⟨4965820112594452664016395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310546741729635109344263 4965820112594452664016395)
      ·
        refine ⟨7448730168891678996024593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965820112594452664016395 7448730168891678996024593)
        ·
          refine ⟨5586547626668759247018445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7448730168891678996024593 5586547626668759247018445)
          ·
            refine ⟨2094955360000784717631917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5586547626668759247018445 2094955360000784717631917)
            ·
              refine ⟨785608260000294269111969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094955360000784717631917 785608260000294269111969)
              ·
                refine ⟨589206195000220701833977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785608260000294269111969 589206195000220701833977)
                ·
                  refine ⟨441904646250165526375483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589206195000220701833977 441904646250165526375483)
                  ·
                    rfl

theorem cell20_968182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_968182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968182 prefixEnd_968182 := by exact prefixLift 968182
  have htrace : WordTrace (prefixWord ++ tailWord_968182) baseStart_968182 baseEnd_968182 := by
    simpa [prefixWord, tailWord_968182, baseEnd_968182] using wordTrace_append hprefix tailTrace_968182
  have hstable : (prefixWord ++ tailWord_968182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968182).length < 2 ^ (prefixWord ++ tailWord_968182).sum := by decide
  have hdescent : baseEnd_968182 < baseStart_968182 := by decide
  rcases family_descends (prefixWord ++ tailWord_968182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968193 : List Nat := [1, 2, 4, 1, 4, 1, 2, 5]
def baseStart_968193 : Nat := 118140960795 + 968193 * 2 ^ 59
def prefixEnd_968193 : Nat := 4983230072969 + 3 ^ 40 * 968193 * 2
def baseEnd_968193 : Nat := 147303222316632792336257

theorem tailTrace_968193 : CollatzResearch.WordTrace tailWord_968193 prefixEnd_968193 147303222316632792336257 := by
  unfold tailWord_968193
  simp only [CollatzResearch.WordTrace]
  refine ⟨35312899781409590044989233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23541933187606393363326155 35312899781409590044989233)
  ·
    refine ⟨26484674836057192533741925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35312899781409590044989233 26484674836057192533741925)
    ·
      refine ⟨4965876531760723600076611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26484674836057192533741925 4965876531760723600076611)
      ·
        refine ⟨7448814797641085400114917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965876531760723600076611 7448814797641085400114917)
        ·
          refine ⟨1396652774557703512521547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7448814797641085400114917 1396652774557703512521547)
          ·
            refine ⟨2094979161836555268782321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396652774557703512521547 2094979161836555268782321)
            ·
              refine ⟨1571234371377416451586741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094979161836555268782321 1571234371377416451586741)
              ·
                refine ⟨147303222316632792336257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571234371377416451586741 147303222316632792336257)
                ·
                  rfl

theorem cell20_968193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_968193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968193 prefixEnd_968193 := by exact prefixLift 968193
  have htrace : WordTrace (prefixWord ++ tailWord_968193) baseStart_968193 baseEnd_968193 := by
    simpa [prefixWord, tailWord_968193, baseEnd_968193] using wordTrace_append hprefix tailTrace_968193
  have hstable : (prefixWord ++ tailWord_968193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968193).length < 2 ^ (prefixWord ++ tailWord_968193).sum := by decide
  have hdescent : baseEnd_968193 < baseStart_968193 := by decide
  rcases family_descends (prefixWord ++ tailWord_968193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968293 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 3]
def baseStart_968293 : Nat := 118140960795 + 968293 * 2 ^ 59
def prefixEnd_968293 : Nat := 4983230072969 + 3 ^ 40 * 968293 * 2
def baseEnd_968293 : Nat := 441955309674742473675029

theorem tailTrace_968293 : CollatzResearch.WordTrace tailWord_968293 prefixEnd_968293 441955309674742473675029 := by
  unfold tailWord_968293
  simp only [CollatzResearch.WordTrace]
  refine ⟨35316547081047307123629533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23544364720698204749086355 35316547081047307123629533)
  ·
    refine ⟨13243705155392740171361075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35316547081047307123629533 13243705155392740171361075)
    ·
      refine ⟨19865557733089110257041613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13243705155392740171361075 19865557733089110257041613)
      ·
        refine ⟨7449584149908416346390605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19865557733089110257041613 7449584149908416346390605)
        ·
          refine ⟨2793594056215656129896477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7449584149908416346390605 2793594056215656129896477)
          ·
            refine ⟨1047597771080871048711179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2793594056215656129896477 1047597771080871048711179)
            ·
              refine ⟨1571396656621306573066769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047597771080871048711179 1571396656621306573066769)
              ·
                refine ⟨1178547492465979929800077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571396656621306573066769 1178547492465979929800077)
                ·
                  refine ⟨441955309674742473675029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178547492465979929800077 441955309674742473675029)
                  ·
                    rfl

theorem cell20_968293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_968293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968293 prefixEnd_968293 := by exact prefixLift 968293
  have htrace : WordTrace (prefixWord ++ tailWord_968293) baseStart_968293 baseEnd_968293 := by
    simpa [prefixWord, tailWord_968293, baseEnd_968293] using wordTrace_append hprefix tailTrace_968293
  have hstable : (prefixWord ++ tailWord_968293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968293).length < 2 ^ (prefixWord ++ tailWord_968293).sum := by decide
  have hdescent : baseEnd_968293 < baseStart_968293 := by decide
  rcases family_descends (prefixWord ++ tailWord_968293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968310 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_968310 : Nat := 118140960795 + 968310 * 2 ^ 59
def prefixEnd_968310 : Nat := 4983230072969 + 3 ^ 40 * 968310 * 2
def baseEnd_968310 : Nat := 441963068937965970108293

theorem tailTrace_968310 : CollatzResearch.WordTrace tailWord_968310 prefixEnd_968310 441963068937965970108293 := by
  unfold tailWord_968310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207322945124107439187399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23544778081323812684665589 2207322945124107439187399)
  ·
    refine ⟨3310984417686161158781099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2207322945124107439187399 3310984417686161158781099)
    ·
      refine ⟨4966476626529241738171649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310984417686161158781099 4966476626529241738171649)
      ·
        refine ⟨3724857469896931303628737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4966476626529241738171649 3724857469896931303628737)
        ·
          refine ⟨2793643102422698477721553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3724857469896931303628737 2793643102422698477721553)
          ·
            refine ⟨2095232326817023858291165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2793643102422698477721553 2095232326817023858291165)
            ·
              refine ⟨785712122556383946859187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2095232326817023858291165 785712122556383946859187)
              ·
                refine ⟨1178568183834575920288781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785712122556383946859187 1178568183834575920288781)
                ·
                  refine ⟨441963068937965970108293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178568183834575920288781 441963068937965970108293)
                  ·
                    rfl

theorem cell20_968310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_968310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968310 prefixEnd_968310 := by exact prefixLift 968310
  have htrace : WordTrace (prefixWord ++ tailWord_968310) baseStart_968310 baseEnd_968310 := by
    simpa [prefixWord, tailWord_968310, baseEnd_968310] using wordTrace_append hprefix tailTrace_968310
  have hstable : (prefixWord ++ tailWord_968310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968310).length < 2 ^ (prefixWord ++ tailWord_968310).sum := by decide
  have hdescent : baseEnd_968310 < baseStart_968310 := by decide
  rcases family_descends (prefixWord ++ tailWord_968310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968311 : List Nat := [1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_968311 : Nat := 118140960795 + 968311 * 2 ^ 59
def prefixEnd_968311 : Nat := 4983230072969 + 3 ^ 40 * 968311 * 2
def baseEnd_968311 : Nat := 147321175121738137024985

theorem tailTrace_968311 : CollatzResearch.WordTrace tailWord_968311 prefixEnd_968311 147321175121738137024985 := by
  unfold tailWord_968311
  simp only [CollatzResearch.WordTrace]
  refine ⟨35317203594982096197784787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23544802396654730798523191 35317203594982096197784787)
  ·
    refine ⟨52975805392473144296677181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35317203594982096197784787 52975805392473144296677181)
    ·
      refine ⟨19865927022177429111253943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52975805392473144296677181 19865927022177429111253943)
      ·
        refine ⟨29798890533266143666880915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19865927022177429111253943 29798890533266143666880915)
        ·
          refine ⟨44698335799899215500321373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29798890533266143666880915 44698335799899215500321373)
          ·
            refine ⟨16761875924962205812620515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44698335799899215500321373 16761875924962205812620515)
            ·
              refine ⟨25142813887443308718930773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761875924962205812620515 25142813887443308718930773)
              ·
                refine ⟨147321175121738137024985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25142813887443308718930773 147321175121738137024985)
                ·
                  rfl

theorem cell20_968311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_968311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968311 prefixEnd_968311 := by exact prefixLift 968311
  have htrace : WordTrace (prefixWord ++ tailWord_968311) baseStart_968311 baseEnd_968311 := by
    simpa [prefixWord, tailWord_968311, baseEnd_968311] using wordTrace_append hprefix tailTrace_968311
  have hstable : (prefixWord ++ tailWord_968311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968311).length < 2 ^ (prefixWord ++ tailWord_968311).sum := by decide
  have hdescent : baseEnd_968311 < baseStart_968311 := by decide
  rcases family_descends (prefixWord ++ tailWord_968311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968321 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_968321 : Nat := 118140960795 + 968321 * 2 ^ 59
def prefixEnd_968321 : Nat := 4983230072969 + 3 ^ 40 * 968321 * 2
def baseEnd_968321 : Nat := 441968089637698820741581

theorem tailTrace_968321 : CollatzResearch.WordTrace tailWord_968321 prefixEnd_968321 441968089637698820741581 := by
  unfold tailWord_968321
  simp only [CollatzResearch.WordTrace]
  refine ⟨35317568324945867905648817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23545045549963911937099211 35317568324945867905648817)
  ·
    refine ⟨26488176243709400929236613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35317568324945867905648817 26488176243709400929236613)
    ·
      refine ⟨4966533045695512674231865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26488176243709400929236613 4966533045695512674231865)
      ·
        refine ⟨3724899784271634505673899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4966533045695512674231865 3724899784271634505673899)
        ·
          refine ⟨5587349676407451758510849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724899784271634505673899 5587349676407451758510849)
          ·
            refine ⟨4190512257305588818883137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587349676407451758510849 4190512257305588818883137)
            ·
              refine ⟨3142884192979191614162353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4190512257305588818883137 3142884192979191614162353)
              ·
                refine ⟨2357163144734393710621765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3142884192979191614162353 2357163144734393710621765)
                ·
                  refine ⟨441968089637698820741581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2357163144734393710621765 441968089637698820741581)
                  ·
                    rfl

theorem cell20_968321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_968321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968321 prefixEnd_968321 := by exact prefixLift 968321
  have htrace : WordTrace (prefixWord ++ tailWord_968321) baseStart_968321 baseEnd_968321 := by
    simpa [prefixWord, tailWord_968321, baseEnd_968321] using wordTrace_append hprefix tailTrace_968321
  have hstable : (prefixWord ++ tailWord_968321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968321).length < 2 ^ (prefixWord ++ tailWord_968321).sum := by decide
  have hdescent : baseEnd_968321 < baseStart_968321 := by decide
  rcases family_descends (prefixWord ++ tailWord_968321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968324 : List Nat := [2, 3, 2, 1, 4, 2, 2, 4]
def baseStart_968324 : Nat := 118140960795 + 968324 * 2 ^ 59
def prefixEnd_968324 : Nat := 4983230072969 + 3 ^ 40 * 968324 * 2
def baseEnd_968324 : Nat := 147323152973148047880523

theorem tailTrace_968324 : CollatzResearch.WordTrace tailWord_968324 prefixEnd_968324 147323152973148047880523 := by
  unfold tailWord_968324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658838871967499709004013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23545118495956666278672017 17658838871967499709004013)
  ·
    refine ⟨6622064576987812390876505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17658838871967499709004013 6622064576987812390876505)
    ·
      refine ⟨4966548432740859293157379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6622064576987812390876505 4966548432740859293157379)
      ·
        refine ⟨7449822649111288939736069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966548432740859293157379 7449822649111288939736069)
        ·
          refine ⟨1396841746708366676200513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7449822649111288939736069 1396841746708366676200513)
          ·
            refine ⟨1047631310031275007150385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396841746708366676200513 1047631310031275007150385)
            ·
              refine ⟨785723482523456255362789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047631310031275007150385 785723482523456255362789)
              ·
                refine ⟨147323152973148047880523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785723482523456255362789 147323152973148047880523)
                ·
                  rfl

theorem cell20_968324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_968324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968324 prefixEnd_968324 := by exact prefixLift 968324
  have htrace : WordTrace (prefixWord ++ tailWord_968324) baseStart_968324 baseEnd_968324 := by
    simpa [prefixWord, tailWord_968324, baseEnd_968324] using wordTrace_append hprefix tailTrace_968324
  have hstable : (prefixWord ++ tailWord_968324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968324).length < 2 ^ (prefixWord ++ tailWord_968324).sum := by decide
  have hdescent : baseEnd_968324 < baseStart_968324 := by decide
  rcases family_descends (prefixWord ++ tailWord_968324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968404 : List Nat := [2, 4, 1, 3, 1, 9]
def baseStart_968404 : Nat := 118140960795 + 968404 * 2 ^ 59
def prefixEnd_968404 : Nat := 4983230072969 + 3 ^ 40 * 968404 * 2
def baseEnd_968404 : Nat := 16370591596271089665725

theorem tailTrace_968404 : CollatzResearch.WordTrace tailWord_968404 prefixEnd_968404 16370591596271089665725 := by
  unfold tailWord_968404
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660297791822586540460133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23547063722430115387280177 17660297791822586540460133)
  ·
    refine ⟨3311305835966734976336275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17660297791822586540460133 3311305835966734976336275)
    ·
      refine ⟨4966958753950102464504413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311305835966734976336275 4966958753950102464504413)
      ·
        refine ⟨1862609532731288424189155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4966958753950102464504413 1862609532731288424189155)
        ·
          refine ⟨2793914299096932636283733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862609532731288424189155 2793914299096932636283733)
          ·
            refine ⟨16370591596271089665725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2793914299096932636283733 16370591596271089665725)
            ·
              rfl

theorem cell20_968404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 9].length) (baseStart_968404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968404 prefixEnd_968404 := by exact prefixLift 968404
  have htrace : WordTrace (prefixWord ++ tailWord_968404) baseStart_968404 baseEnd_968404 := by
    simpa [prefixWord, tailWord_968404, baseEnd_968404] using wordTrace_append hprefix tailTrace_968404
  have hstable : (prefixWord ++ tailWord_968404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968404).length < 2 ^ (prefixWord ++ tailWord_968404).sum := by decide
  have hdescent : baseEnd_968404 < baseStart_968404 := by decide
  rcases family_descends (prefixWord ++ tailWord_968404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968406 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_968406 : Nat := 118140960795 + 968406 * 2 ^ 59
def prefixEnd_968406 : Nat := 4983230072969 + 3 ^ 40 * 968406 * 2
def baseEnd_968406 : Nat := 442006885953816302907901

theorem tailTrace_968406 : CollatzResearch.WordTrace tailWord_968406 prefixEnd_968406 442006885953816302907901 := by
  unfold tailWord_968406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207541783102370463905817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23547112353091951614995381 2207541783102370463905817)
  ·
    refine ⟨1655656337326777847929363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2207541783102370463905817 1655656337326777847929363)
    ·
      refine ⟨2483484505990166771894045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655656337326777847929363 2483484505990166771894045)
      ·
        refine ⟨931306689746312539460267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2483484505990166771894045 931306689746312539460267)
        ·
          refine ⟨1396960034619468809190401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931306689746312539460267 1396960034619468809190401)
          ·
            refine ⟨1047720025964601606892801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396960034619468809190401 1047720025964601606892801)
            ·
              refine ⟨785790019473451205169601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047720025964601606892801 785790019473451205169601)
              ·
                refine ⟨589342514605088403877201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785790019473451205169601 589342514605088403877201)
                ·
                  refine ⟨442006885953816302907901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589342514605088403877201 442006885953816302907901)
                  ·
                    rfl

theorem cell20_968406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_968406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968406 prefixEnd_968406 := by exact prefixLift 968406
  have htrace : WordTrace (prefixWord ++ tailWord_968406) baseStart_968406 baseEnd_968406 := by
    simpa [prefixWord, tailWord_968406, baseEnd_968406] using wordTrace_append hprefix tailTrace_968406
  have hstable : (prefixWord ++ tailWord_968406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968406).length < 2 ^ (prefixWord ++ tailWord_968406).sum := by decide
  have hdescent : baseEnd_968406 < baseStart_968406 := by decide
  rcases family_descends (prefixWord ++ tailWord_968406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968452 : List Nat := [2, 3, 2, 2, 1, 2, 1, 5, 2]
def baseStart_968452 : Nat := 118140960795 + 968452 * 2 ^ 59
def prefixEnd_968452 : Nat := 4983230072969 + 3 ^ 40 * 968452 * 2
def baseEnd_968452 : Nat := 442027881607244587374379

theorem tailTrace_968452 : CollatzResearch.WordTrace tailWord_968452 prefixEnd_968452 442027881607244587374379 := by
  unfold tailWord_968452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661173143735638639333805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23548230858314184852445073 17661173143735638639333805)
  ·
    refine ⟨6622939928900864489750177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17661173143735638639333805 6622939928900864489750177)
    ·
      refine ⟨4967204946675648367312633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6622939928900864489750177 4967204946675648367312633)
      ·
        refine ⟨3725403710006736275484475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4967204946675648367312633 3725403710006736275484475)
        ·
          refine ⟨5588105565010104413226713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725403710006736275484475 5588105565010104413226713)
          ·
            refine ⟨4191079173757578309920035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5588105565010104413226713 4191079173757578309920035)
            ·
              refine ⟨6286618760636367464880053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191079173757578309920035 6286618760636367464880053)
              ·
                refine ⟨589370508809659449832505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6286618760636367464880053 589370508809659449832505)
                ·
                  refine ⟨442027881607244587374379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589370508809659449832505 442027881607244587374379)
                  ·
                    rfl

theorem cell20_968452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_968452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968452 prefixEnd_968452 := by exact prefixLift 968452
  have htrace : WordTrace (prefixWord ++ tailWord_968452) baseStart_968452 baseEnd_968452 := by
    simpa [prefixWord, tailWord_968452, baseEnd_968452] using wordTrace_append hprefix tailTrace_968452
  have hstable : (prefixWord ++ tailWord_968452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968452).length < 2 ^ (prefixWord ++ tailWord_968452).sum := by decide
  have hdescent : baseEnd_968452 < baseStart_968452 := by decide
  rcases family_descends (prefixWord ++ tailWord_968452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968454 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_968454 : Nat := 118140960795 + 968454 * 2 ^ 59
def prefixEnd_968454 : Nat := 4983230072969 + 3 ^ 40 * 968454 * 2
def baseEnd_968454 : Nat := 442028794461741469307705

theorem tailTrace_968454 : CollatzResearch.WordTrace tailWord_968454 prefixEnd_968454 442028794461741469307705 := by
  unfold tailWord_968454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103825601045750988132513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23548279488976021080160277 1103825601045750988132513)
  ·
    refine ⟨827869200784313241099385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1103825601045750988132513 827869200784313241099385)
    ·
      refine ⟨620901900588234930824539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 827869200784313241099385 620901900588234930824539)
      ·
        refine ⟨931352850882352396236809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620901900588234930824539 931352850882352396236809)
        ·
          refine ⟨698514638161764297177607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931352850882352396236809 698514638161764297177607)
          ·
            refine ⟨1047771957242646445766411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698514638161764297177607 1047771957242646445766411)
            ·
              refine ⟨1571657935863969668649617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047771957242646445766411 1571657935863969668649617)
              ·
                refine ⟨1178743451897977251487213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571657935863969668649617 1178743451897977251487213)
                ·
                  refine ⟨442028794461741469307705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178743451897977251487213 442028794461741469307705)
                  ·
                    rfl

theorem cell20_968454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_968454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968454 prefixEnd_968454 := by exact prefixLift 968454
  have htrace : WordTrace (prefixWord ++ tailWord_968454) baseStart_968454 baseEnd_968454 := by
    simpa [prefixWord, tailWord_968454, baseEnd_968454] using wordTrace_append hprefix tailTrace_968454
  have hstable : (prefixWord ++ tailWord_968454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968454).length < 2 ^ (prefixWord ++ tailWord_968454).sum := by decide
  have hdescent : baseEnd_968454 < baseStart_968454 := by decide
  rcases family_descends (prefixWord ++ tailWord_968454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968456 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_968456 : Nat := 118140960795 + 968456 * 2 ^ 59
def prefixEnd_968456 : Nat := 4983230072969 + 3 ^ 40 * 968456 * 2
def baseEnd_968456 : Nat := 442029707316238351241029

theorem tailTrace_968456 : CollatzResearch.WordTrace tailWord_968456 prefixEnd_968456 442029707316238351241029 := by
  unfold tailWord_968456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661246089728392980906611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23548328119637857307875481 17661246089728392980906611)
  ·
    refine ⟨26491869134592589471359917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17661246089728392980906611 26491869134592589471359917)
    ·
      refine ⟨9934450925472221051759969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26491869134592589471359917 9934450925472221051759969)
      ·
        refine ⟨7450838194104165788819977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9934450925472221051759969 7450838194104165788819977)
        ·
          refine ⟨5588128645578124341614983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7450838194104165788819977 5588128645578124341614983)
          ·
            refine ⟨8382192968367186512422475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588128645578124341614983 8382192968367186512422475)
            ·
              refine ⟨12573289452550779768633713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382192968367186512422475 12573289452550779768633713)
              ·
                refine ⟨9429967089413084826475285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573289452550779768633713 9429967089413084826475285)
                ·
                  refine ⟨442029707316238351241029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9429967089413084826475285 442029707316238351241029)
                  ·
                    rfl

theorem cell20_968456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_968456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968456 prefixEnd_968456 := by exact prefixLift 968456
  have htrace : WordTrace (prefixWord ++ tailWord_968456) baseStart_968456 baseEnd_968456 := by
    simpa [prefixWord, tailWord_968456, baseEnd_968456] using wordTrace_append hprefix tailTrace_968456
  have hstable : (prefixWord ++ tailWord_968456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968456).length < 2 ^ (prefixWord ++ tailWord_968456).sum := by decide
  have hdescent : baseEnd_968456 < baseStart_968456 := by decide
  rcases family_descends (prefixWord ++ tailWord_968456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968497 : List Nat := [1, 2, 2, 3, 2, 4, 2, 4]
def baseStart_968497 : Nat := 118140960795 + 968497 * 2 ^ 59
def prefixEnd_968497 : Nat := 4983230072969 + 3 ^ 40 * 968497 * 2
def baseEnd_968497 : Nat := 147349473611141476958065

theorem tailTrace_968497 : CollatzResearch.WordTrace tailWord_968497 prefixEnd_968497 147349473611141476958065 := by
  unfold tailWord_968497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35323987572308249964055745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23549325048205499976037163 35323987572308249964055745)
  ·
    refine ⟨26492990679231187473041809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35323987572308249964055745 26492990679231187473041809)
    ·
      refine ⟨19869743009423390604781357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26492990679231187473041809 19869743009423390604781357)
      ·
        refine ⟨7451153628533771476793009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19869743009423390604781357 7451153628533771476793009)
        ·
          refine ⟨5588365221400328607594757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7451153628533771476793009 5588365221400328607594757)
          ·
            refine ⟨1047818479012561613924017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5588365221400328607594757 1047818479012561613924017)
            ·
              refine ⟨785863859259421210443013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047818479012561613924017 785863859259421210443013)
              ·
                refine ⟨147349473611141476958065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785863859259421210443013 147349473611141476958065)
                ·
                  rfl

theorem cell20_968497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_968497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968497 prefixEnd_968497 := by exact prefixLift 968497
  have htrace : WordTrace (prefixWord ++ tailWord_968497) baseStart_968497 baseEnd_968497 := by
    simpa [prefixWord, tailWord_968497, baseEnd_968497] using wordTrace_append hprefix tailTrace_968497
  have hstable : (prefixWord ++ tailWord_968497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968497).length < 2 ^ (prefixWord ++ tailWord_968497).sum := by decide
  have hdescent : baseEnd_968497 < baseStart_968497 := by decide
  rcases family_descends (prefixWord ++ tailWord_968497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968590 : List Nat := [4, 1, 1, 5, 1, 2, 1, 5]
def baseStart_968590 : Nat := 118140960795 + 968590 * 2 ^ 59
def prefixEnd_968590 : Nat := 4983230072969 + 3 ^ 40 * 968590 * 2
def baseEnd_968590 : Nat := 147363622855843146924605

theorem tailTrace_968590 : CollatzResearch.WordTrace tailWord_968590 prefixEnd_968590 147363622855843146924605 := by
  unfold tailWord_968590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415922445121415855898903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23551586373980884564794149 4415922445121415855898903)
  ·
    refine ⟨6623883667682123783848355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4415922445121415855898903 6623883667682123783848355)
    ·
      refine ⟨9935825501523185675772533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623883667682123783848355 9935825501523185675772533)
      ·
        refine ⟨931483640767798657103675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9935825501523185675772533 931483640767798657103675)
        ·
          refine ⟨1397225461151697985655513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931483640767798657103675 1397225461151697985655513)
          ·
            refine ⟨1047919095863773489241635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397225461151697985655513 1047919095863773489241635)
            ·
              refine ⟨1571878643795660233862453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047919095863773489241635 1571878643795660233862453)
              ·
                refine ⟨147363622855843146924605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571878643795660233862453 147363622855843146924605)
                ·
                  rfl

theorem cell20_968590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_968590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968590 prefixEnd_968590 := by exact prefixLift 968590
  have htrace : WordTrace (prefixWord ++ tailWord_968590) baseStart_968590 baseEnd_968590 := by
    simpa [prefixWord, tailWord_968590, baseEnd_968590] using wordTrace_append hprefix tailTrace_968590
  have hstable : (prefixWord ++ tailWord_968590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968590).length < 2 ^ (prefixWord ++ tailWord_968590).sum := by decide
  have hdescent : baseEnd_968590 < baseStart_968590 := by decide
  rcases family_descends (prefixWord ++ tailWord_968590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968601 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_968601 : Nat := 118140960795 + 968601 * 2 ^ 59
def prefixEnd_968601 : Nat := 4983230072969 + 3 ^ 40 * 968601 * 2
def baseEnd_968601 : Nat := 442095889267262291407103

theorem tailTrace_968601 : CollatzResearch.WordTrace tailWord_968601 prefixEnd_968601 442095889267262291407103 := by
  unfold tailWord_968601
  simp only [CollatzResearch.WordTrace]
  refine ⟨35327780763931475725841657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23551853842620983817227771 35327780763931475725841657)
  ·
    refine ⟨26495835572948606794381243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35327780763931475725841657 26495835572948606794381243)
    ·
      refine ⟨39743753359422910191571865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26495835572948606794381243 39743753359422910191571865)
      ·
        refine ⟨29807815019567182643678899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39743753359422910191571865 29807815019567182643678899)
        ·
          refine ⟨44711722529350773965518349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29807815019567182643678899 44711722529350773965518349)
          ·
            refine ⟨16766895948506540237069381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44711722529350773965518349 16766895948506540237069381)
            ·
              refine ⟨3143792990344976294450509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16766895948506540237069381 3143792990344976294450509)
              ·
                refine ⟨1178922371379366110418941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3143792990344976294450509 1178922371379366110418941)
                ·
                  refine ⟨442095889267262291407103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178922371379366110418941 442095889267262291407103)
                  ·
                    rfl

theorem cell20_968601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_968601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968601 prefixEnd_968601 := by exact prefixLift 968601
  have htrace : WordTrace (prefixWord ++ tailWord_968601) baseStart_968601 baseEnd_968601 := by
    simpa [prefixWord, tailWord_968601, baseEnd_968601] using wordTrace_append hprefix tailTrace_968601
  have hstable : (prefixWord ++ tailWord_968601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968601).length < 2 ^ (prefixWord ++ tailWord_968601).sum := by decide
  have hdescent : baseEnd_968601 < baseStart_968601 := by decide
  rcases family_descends (prefixWord ++ tailWord_968601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968666 : List Nat := [3, 1, 1, 2, 6, 1, 2, 4]
def baseStart_968666 : Nat := 118140960795 + 968666 * 2 ^ 59
def prefixEnd_968666 : Nat := 4983230072969 + 3 ^ 40 * 968666 * 2
def baseEnd_968666 : Nat := 147375185679470318080057

theorem tailTrace_968666 : CollatzResearch.WordTrace tailWord_968666 prefixEnd_968666 147375185679470318080057 := by
  unfold tailWord_968666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832537877173997956739463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23553434339130661217971901 8832537877173997956739463)
  ·
    refine ⟨13248806815760996935109195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8832537877173997956739463 13248806815760996935109195)
    ·
      refine ⟨19873210223641495402663793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13248806815760996935109195 19873210223641495402663793)
      ·
        refine ⟨14904907667731121551997845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19873210223641495402663793 14904907667731121551997845)
        ·
          refine ⟨698667546924896322749899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14904907667731121551997845 698667546924896322749899)
          ·
            refine ⟨1048001320387344484124849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698667546924896322749899 1048001320387344484124849)
            ·
              refine ⟨786000990290508363093637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048001320387344484124849 786000990290508363093637)
              ·
                refine ⟨147375185679470318080057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786000990290508363093637 147375185679470318080057)
                ·
                  rfl

theorem cell20_968666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_968666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968666 prefixEnd_968666 := by exact prefixLift 968666
  have htrace : WordTrace (prefixWord ++ tailWord_968666) baseStart_968666 baseEnd_968666 := by
    simpa [prefixWord, tailWord_968666, baseEnd_968666] using wordTrace_append hprefix tailTrace_968666
  have hstable : (prefixWord ++ tailWord_968666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968666).length < 2 ^ (prefixWord ++ tailWord_968666).sum := by decide
  have hdescent : baseEnd_968666 < baseStart_968666 := by decide
  rcases family_descends (prefixWord ++ tailWord_968666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968701 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 2]
def baseStart_968701 : Nat := 118140960795 + 968701 * 2 ^ 59
def prefixEnd_968701 : Nat := 4983230072969 + 3 ^ 40 * 968701 * 2
def baseEnd_968701 : Nat := 442141531992106388073361

theorem tailTrace_968701 : CollatzResearch.WordTrace tailWord_968701 prefixEnd_968701 442141531992106388073361 := by
  unfold tailWord_968701
  simp only [CollatzResearch.WordTrace]
  refine ⟨35331428063569192804481957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23554285375712795202987971 35331428063569192804481957)
  ·
    refine ⟨6624642761919223650840367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35331428063569192804481957 6624642761919223650840367)
    ·
      refine ⟨9936964142878835476260551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624642761919223650840367 9936964142878835476260551)
      ·
        refine ⟨14905446214318253214390827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9936964142878835476260551 14905446214318253214390827)
        ·
          refine ⟨22358169321477379821586241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14905446214318253214390827 22358169321477379821586241)
          ·
            refine ⟨16768626991108034866189681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22358169321477379821586241 16768626991108034866189681)
            ·
              refine ⟨12576470243331026149642261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16768626991108034866189681 12576470243331026149642261)
              ·
                refine ⟨589522042656141850764481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12576470243331026149642261 589522042656141850764481)
                ·
                  refine ⟨442141531992106388073361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589522042656141850764481 442141531992106388073361)
                  ·
                    rfl

theorem cell20_968701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_968701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968701 prefixEnd_968701 := by exact prefixLift 968701
  have htrace : WordTrace (prefixWord ++ tailWord_968701) baseStart_968701 baseEnd_968701 := by
    simpa [prefixWord, tailWord_968701, baseEnd_968701] using wordTrace_append hprefix tailTrace_968701
  have hstable : (prefixWord ++ tailWord_968701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968701).length < 2 ^ (prefixWord ++ tailWord_968701).sum := by decide
  have hdescent : baseEnd_968701 < baseStart_968701 := by decide
  rcases family_descends (prefixWord ++ tailWord_968701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968711 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 3]
def baseStart_968711 : Nat := 118140960795 + 968711 * 2 ^ 59
def prefixEnd_968711 : Nat := 4983230072969 + 3 ^ 40 * 968711 * 2
def baseEnd_968711 : Nat := 442146096264590797739987

theorem tailTrace_968711 : CollatzResearch.WordTrace tailWord_968711 prefixEnd_968711 442146096264590797739987 := by
  unfold tailWord_968711
  simp only [CollatzResearch.WordTrace]
  refine ⟨35331792793532964512345987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23554528529021976341563991 35331792793532964512345987)
  ·
    refine ⟨52997689190299446768518981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35331792793532964512345987 52997689190299446768518981)
    ·
      refine ⟨9937066723181146269097309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52997689190299446768518981 9937066723181146269097309)
      ·
        refine ⟨3726400021192929850911491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9937066723181146269097309 3726400021192929850911491)
        ·
          refine ⟨5589600031789394776367237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726400021192929850911491 5589600031789394776367237)
          ·
            refine ⟨1048050005960511520568857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5589600031789394776367237 1048050005960511520568857)
            ·
              refine ⟨786037504470383640426643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048050005960511520568857 786037504470383640426643)
              ·
                refine ⟨1179056256705575460639965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786037504470383640426643 1179056256705575460639965)
                ·
                  refine ⟨442146096264590797739987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179056256705575460639965 442146096264590797739987)
                  ·
                    rfl

theorem cell20_968711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_968711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968711 prefixEnd_968711 := by exact prefixLift 968711
  have htrace : WordTrace (prefixWord ++ tailWord_968711) baseStart_968711 baseEnd_968711 := by
    simpa [prefixWord, tailWord_968711, baseEnd_968711] using wordTrace_append hprefix tailTrace_968711
  have hstable : (prefixWord ++ tailWord_968711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968711).length < 2 ^ (prefixWord ++ tailWord_968711).sum := by decide
  have hdescent : baseEnd_968711 < baseStart_968711 := by decide
  rcases family_descends (prefixWord ++ tailWord_968711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968715 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_968715 : Nat := 118140960795 + 968715 * 2 ^ 59
def prefixEnd_968715 : Nat := 4983230072969 + 3 ^ 40 * 968715 * 2
def baseEnd_968715 : Nat := 442147921973584561606637

theorem tailTrace_968715 : CollatzResearch.WordTrace tailWord_968715 prefixEnd_968715 442147921973584561606637 := by
  unfold tailWord_968715
  simp only [CollatzResearch.WordTrace]
  refine ⟨35331938685518473195491599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23554625790345648796994399 35331938685518473195491599)
  ·
    refine ⟨52997908028277709793237399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35331938685518473195491599 52997908028277709793237399)
    ·
      refine ⟨79496862042416564689856099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52997908028277709793237399 79496862042416564689856099)
      ·
        refine ⟨119245293063624847034784149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79496862042416564689856099 119245293063624847034784149)
        ·
          refine ⟨5589623112357414704755507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119245293063624847034784149 5589623112357414704755507)
          ·
            refine ⟨8384434668536122057133261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589623112357414704755507 8384434668536122057133261)
            ·
              refine ⟨3144163000701045771424973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8384434668536122057133261 3144163000701045771424973)
              ·
                refine ⟨1179061125262892164284365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3144163000701045771424973 1179061125262892164284365)
                ·
                  refine ⟨442147921973584561606637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179061125262892164284365 442147921973584561606637)
                  ·
                    rfl

theorem cell20_968715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_968715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968715 prefixEnd_968715 := by exact prefixLift 968715
  have htrace : WordTrace (prefixWord ++ tailWord_968715) baseStart_968715 baseEnd_968715 := by
    simpa [prefixWord, tailWord_968715, baseEnd_968715] using wordTrace_append hprefix tailTrace_968715
  have hstable : (prefixWord ++ tailWord_968715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968715).length < 2 ^ (prefixWord ++ tailWord_968715).sum := by decide
  have hdescent : baseEnd_968715 < baseStart_968715 := by decide
  rcases family_descends (prefixWord ++ tailWord_968715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968739 : List Nat := [1, 1, 1, 4, 3, 1, 2, 5, 2]
def baseStart_968739 : Nat := 118140960795 + 968739 * 2 ^ 59
def prefixEnd_968739 : Nat := 4983230072969 + 3 ^ 40 * 968739 * 2
def baseEnd_968739 : Nat := 442158876227547144806539

theorem tailTrace_968739 : CollatzResearch.WordTrace tailWord_968739 prefixEnd_968739 442158876227547144806539 := by
  unfold tailWord_968739
  simp only [CollatzResearch.WordTrace]
  refine ⟨35332814037431525294365271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23555209358287683529576847 35332814037431525294365271)
  ·
    refine ⟨52999221056147287941547907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35332814037431525294365271 52999221056147287941547907)
    ·
      refine ⟨79498831584220931912321861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52999221056147287941547907 79498831584220931912321861)
      ·
        refine ⟨14906030922041424733560349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79498831584220931912321861 14906030922041424733560349)
        ·
          refine ⟨5589761595765534275085131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14906030922041424733560349 5589761595765534275085131)
          ·
            refine ⟨8384642393648301412627697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589761595765534275085131 8384642393648301412627697)
            ·
              refine ⟨6288481795236226059470773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8384642393648301412627697 6288481795236226059470773)
              ·
                refine ⟨589545168303396193075385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6288481795236226059470773 589545168303396193075385)
                ·
                  refine ⟨442158876227547144806539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589545168303396193075385 442158876227547144806539)
                  ·
                    rfl

theorem cell20_968739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 2].length) (baseStart_968739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968739 prefixEnd_968739 := by exact prefixLift 968739
  have htrace : WordTrace (prefixWord ++ tailWord_968739) baseStart_968739 baseEnd_968739 := by
    simpa [prefixWord, tailWord_968739, baseEnd_968739] using wordTrace_append hprefix tailTrace_968739
  have hstable : (prefixWord ++ tailWord_968739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968739).length < 2 ^ (prefixWord ++ tailWord_968739).sum := by decide
  have hdescent : baseEnd_968739 < baseStart_968739 := by decide
  rcases family_descends (prefixWord ++ tailWord_968739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968753 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_968753 : Nat := 118140960795 + 968753 * 2 ^ 59
def prefixEnd_968753 : Nat := 4983230072969 + 3 ^ 40 * 968753 * 2
def baseEnd_968753 : Nat := 442165266209025318339815

theorem tailTrace_968753 : CollatzResearch.WordTrace tailWord_968753 prefixEnd_968753 442165266209025318339815 := by
  unfold tailWord_968753
  simp only [CollatzResearch.WordTrace]
  refine ⟨35333324659380805685374913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23555549772920537123583275 35333324659380805685374913)
  ·
    refine ⟨26499993494535604264031185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35333324659380805685374913 26499993494535604264031185)
    ·
      refine ⟨19874995120901703198023389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26499993494535604264031185 19874995120901703198023389)
      ·
        refine ⟨7453123170338138699258771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19874995120901703198023389 7453123170338138699258771)
        ·
          refine ⟨11179684755507208048888157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453123170338138699258771 11179684755507208048888157)
          ·
            refine ⟨4192381783315203018333059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11179684755507208048888157 4192381783315203018333059)
            ·
              refine ⟨6288572674972804527499589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192381783315203018333059 6288572674972804527499589)
              ·
                refine ⟨1179107376557400848906173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6288572674972804527499589 1179107376557400848906173)
                ·
                  refine ⟨442165266209025318339815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179107376557400848906173 442165266209025318339815)
                  ·
                    rfl

theorem cell20_968753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_968753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968753 prefixEnd_968753 := by exact prefixLift 968753
  have htrace : WordTrace (prefixWord ++ tailWord_968753) baseStart_968753 baseEnd_968753 := by
    simpa [prefixWord, tailWord_968753, baseEnd_968753] using wordTrace_append hprefix tailTrace_968753
  have hstable : (prefixWord ++ tailWord_968753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968753).length < 2 ^ (prefixWord ++ tailWord_968753).sum := by decide
  have hdescent : baseEnd_968753 < baseStart_968753 := by decide
  rcases family_descends (prefixWord ++ tailWord_968753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968767 : List Nat := [1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_968767 : Nat := 118140960795 + 968767 * 2 ^ 59
def prefixEnd_968767 : Nat := 4983230072969 + 3 ^ 40 * 968767 * 2
def baseEnd_968767 : Nat := 147390552063501163957697

theorem tailTrace_968767 : CollatzResearch.WordTrace tailWord_968767 prefixEnd_968767 147390552063501163957697 := by
  unfold tailWord_968767
  simp only [CollatzResearch.WordTrace]
  refine ⟨35333835281330086076384555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23555890187553390717589703 35333835281330086076384555)
  ·
    refine ⟨53000752921995129114576833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35333835281330086076384555 53000752921995129114576833)
    ·
      refine ⟨39750564691496346835932625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53000752921995129114576833 39750564691496346835932625)
      ·
        refine ⟨29812923518622260126949469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39750564691496346835932625 29812923518622260126949469)
        ·
          refine ⟨11179846319483347547606051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29812923518622260126949469 11179846319483347547606051)
          ·
            refine ⟨16769769479225021321409077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11179846319483347547606051 16769769479225021321409077)
            ·
              refine ⟨1572165888677345748882101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16769769479225021321409077 1572165888677345748882101)
              ·
                refine ⟨147390552063501163957697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1572165888677345748882101 147390552063501163957697)
                ·
                  rfl

theorem cell20_968767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_968767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968767 prefixEnd_968767 := by exact prefixLift 968767
  have htrace : WordTrace (prefixWord ++ tailWord_968767) baseStart_968767 baseEnd_968767 := by
    simpa [prefixWord, tailWord_968767, baseEnd_968767] using wordTrace_append hprefix tailTrace_968767
  have hstable : (prefixWord ++ tailWord_968767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968767).length < 2 ^ (prefixWord ++ tailWord_968767).sum := by decide
  have hdescent : baseEnd_968767 < baseStart_968767 := by decide
  rcases family_descends (prefixWord ++ tailWord_968767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968790 : List Nat := [5, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_968790 : Nat := 118140960795 + 968790 * 2 ^ 59
def prefixEnd_968790 : Nat := 4983230072969 + 3 ^ 40 * 968790 * 2
def baseEnd_968790 : Nat := 442182154017217634106331

theorem tailTrace_968790 : CollatzResearch.WordTrace tailWord_968790 prefixEnd_968790 442182154017217634106331 := by
  unfold tailWord_968790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208417135015422562779489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23556449440164507336314549 2208417135015422562779489)
  ·
    refine ⟨1656312851261566922084617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2208417135015422562779489 1656312851261566922084617)
    ·
      refine ⟨1242234638446175191563463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656312851261566922084617 1242234638446175191563463)
      ·
        refine ⟨1863351957669262787345195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242234638446175191563463 1863351957669262787345195)
        ·
          refine ⟨2795027936503894181017793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863351957669262787345195 2795027936503894181017793)
          ·
            refine ⟨2096270952377920635763345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795027936503894181017793 2096270952377920635763345)
            ·
              refine ⟨1572203214283440476822509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096270952377920635763345 1572203214283440476822509)
              ·
                refine ⟨589576205356290178808441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1572203214283440476822509 589576205356290178808441)
                ·
                  refine ⟨442182154017217634106331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589576205356290178808441 442182154017217634106331)
                  ·
                    rfl

theorem cell20_968790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_968790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968790 prefixEnd_968790 := by exact prefixLift 968790
  have htrace : WordTrace (prefixWord ++ tailWord_968790) baseStart_968790 baseEnd_968790 := by
    simpa [prefixWord, tailWord_968790, baseEnd_968790] using wordTrace_append hprefix tailTrace_968790
  have hstable : (prefixWord ++ tailWord_968790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968790).length < 2 ^ (prefixWord ++ tailWord_968790).sum := by decide
  have hdescent : baseEnd_968790 < baseStart_968790 := by decide
  rcases family_descends (prefixWord ++ tailWord_968790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968805 : List Nat := [1, 3, 1, 3, 2, 3, 7]
def baseStart_968805 : Nat := 118140960795 + 968805 * 2 ^ 59
def prefixEnd_968805 : Nat := 4983230072969 + 3 ^ 40 * 968805 * 2
def baseEnd_968805 : Nat := 49132111158438249845141

theorem tailTrace_968805 : CollatzResearch.WordTrace tailWord_968805 prefixEnd_968805 49132111158438249845141 := by
  unfold tailWord_968805
  simp only [CollatzResearch.WordTrace]
  refine ⟨35335221255192418566267869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23556814170128279044178579 35335221255192418566267869)
  ·
    refine ⟨13250707970697156962350451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35335221255192418566267869 13250707970697156962350451)
    ·
      refine ⟨19876061956045735443525677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13250707970697156962350451 19876061956045735443525677)
      ·
        refine ⟨7453523233517150791322129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19876061956045735443525677 7453523233517150791322129)
        ·
          refine ⟨5590142425137863093491597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7453523233517150791322129 5590142425137863093491597)
          ·
            refine ⟨2096303409426698660059349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5590142425137863093491597 2096303409426698660059349)
            ·
              refine ⟨49132111158438249845141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2096303409426698660059349 49132111158438249845141)
              ·
                rfl

theorem cell20_968805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_968805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968805 prefixEnd_968805 := by exact prefixLift 968805
  have htrace : WordTrace (prefixWord ++ tailWord_968805) baseStart_968805 baseEnd_968805 := by
    simpa [prefixWord, tailWord_968805, baseEnd_968805] using wordTrace_append hprefix tailTrace_968805
  have hstable : (prefixWord ++ tailWord_968805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968805).length < 2 ^ (prefixWord ++ tailWord_968805).sum := by decide
  have hdescent : baseEnd_968805 < baseStart_968805 := by decide
  rcases family_descends (prefixWord ++ tailWord_968805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968815 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 2]
def baseStart_968815 : Nat := 118140960795 + 968815 * 2 ^ 59
def prefixEnd_968815 : Nat := 4983230072969 + 3 ^ 40 * 968815 * 2
def baseEnd_968815 : Nat := 442193564698428658272895

theorem tailTrace_968815 : CollatzResearch.WordTrace tailWord_968815 prefixEnd_968815 442193564698428658272895 := by
  unfold tailWord_968815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35335585985156190274131899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23557057323437460182754599 35335585985156190274131899)
  ·
    refine ⟨53003378977734285411197849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35335585985156190274131899 53003378977734285411197849)
    ·
      refine ⟨39752534233300714058398387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53003378977734285411197849 39752534233300714058398387)
      ·
        refine ⟨59628801349951071087597581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39752534233300714058398387 59628801349951071087597581)
        ·
          refine ⟨22360800506231651657849093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59628801349951071087597581 22360800506231651657849093)
          ·
            refine ⟨4192650094918434685846705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22360800506231651657849093 4192650094918434685846705)
            ·
              refine ⟨3144487571188826014385029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192650094918434685846705 3144487571188826014385029)
              ·
                refine ⟨589591419597904877697193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3144487571188826014385029 589591419597904877697193)
                ·
                  refine ⟨442193564698428658272895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589591419597904877697193 442193564698428658272895)
                  ·
                    rfl

theorem cell20_968815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 2].length) (baseStart_968815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968815 prefixEnd_968815 := by exact prefixLift 968815
  have htrace : WordTrace (prefixWord ++ tailWord_968815) baseStart_968815 baseEnd_968815 := by
    simpa [prefixWord, tailWord_968815, baseEnd_968815] using wordTrace_append hprefix tailTrace_968815
  have hstable : (prefixWord ++ tailWord_968815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968815).length < 2 ^ (prefixWord ++ tailWord_968815).sum := by decide
  have hdescent : baseEnd_968815 < baseStart_968815 := by decide
  rcases family_descends (prefixWord ++ tailWord_968815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968836 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_968836 : Nat := 118140960795 + 968836 * 2 ^ 59
def prefixEnd_968836 : Nat := 4983230072969 + 3 ^ 40 * 968836 * 2
def baseEnd_968836 : Nat := 442203149670645918572809

theorem tailTrace_968836 : CollatzResearch.WordTrace tailWord_968836 prefixEnd_968836 442203149670645918572809 := by
  unfold tailWord_968836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668175959040055430323181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23557567945386740573764241 17668175959040055430323181)
  ·
    refine ⟨6625565984640020786371193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17668175959040055430323181 6625565984640020786371193)
    ·
      refine ⟨4969174488480015589778395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625565984640020786371193 4969174488480015589778395)
      ·
        refine ⟨7453761732720023384667593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969174488480015589778395 7453761732720023384667593)
        ·
          refine ⟨5590321299540017538500695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7453761732720023384667593 5590321299540017538500695)
          ·
            refine ⟨8385481949310026307751043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590321299540017538500695 8385481949310026307751043)
            ·
              refine ⟨12578222923965039461626565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385481949310026307751043 12578222923965039461626565)
              ·
                refine ⟨2358416798243444899054981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12578222923965039461626565 2358416798243444899054981)
                ·
                  refine ⟨442203149670645918572809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2358416798243444899054981 442203149670645918572809)
                  ·
                    rfl

theorem cell20_968836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_968836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968836 prefixEnd_968836 := by exact prefixLift 968836
  have htrace : WordTrace (prefixWord ++ tailWord_968836) baseStart_968836 baseEnd_968836 := by
    simpa [prefixWord, tailWord_968836, baseEnd_968836] using wordTrace_append hprefix tailTrace_968836
  have hstable : (prefixWord ++ tailWord_968836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968836).length < 2 ^ (prefixWord ++ tailWord_968836).sum := by decide
  have hdescent : baseEnd_968836 < baseStart_968836 := by decide
  rcases family_descends (prefixWord ++ tailWord_968836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968857 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_968857 : Nat := 118140960795 + 968857 * 2 ^ 59
def prefixEnd_968857 : Nat := 4983230072969 + 3 ^ 40 * 968857 * 2
def baseEnd_968857 : Nat := 442212734642863178872723

theorem tailTrace_968857 : CollatzResearch.WordTrace tailWord_968857 prefixEnd_968857 442212734642863178872723 := by
  unfold tailWord_968857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35337117851004031447160825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23558078567336020964773883 35337117851004031447160825)
  ·
    refine ⟨26502838388253023585370619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35337117851004031447160825 26502838388253023585370619)
    ·
      refine ⟨39754257582379535378055929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26502838388253023585370619 39754257582379535378055929)
      ·
        refine ⟨29815693186784651533541947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39754257582379535378055929 29815693186784651533541947)
        ·
          refine ⟨44723539780176977300312921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29815693186784651533541947 44723539780176977300312921)
          ·
            refine ⟨33542654835132732975234691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44723539780176977300312921 33542654835132732975234691)
            ·
              refine ⟨50313982252699099462852037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33542654835132732975234691 50313982252699099462852037)
              ·
                refine ⟨9433871672381081149284757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50313982252699099462852037 9433871672381081149284757)
                ·
                  refine ⟨442212734642863178872723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9433871672381081149284757 442212734642863178872723)
                  ·
                    rfl

theorem cell20_968857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_968857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968857 prefixEnd_968857 := by exact prefixLift 968857
  have htrace : WordTrace (prefixWord ++ tailWord_968857) baseStart_968857 baseEnd_968857 := by
    simpa [prefixWord, tailWord_968857, baseEnd_968857] using wordTrace_append hprefix tailTrace_968857
  have hstable : (prefixWord ++ tailWord_968857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968857).length < 2 ^ (prefixWord ++ tailWord_968857).sum := by decide
  have hdescent : baseEnd_968857 < baseStart_968857 := by decide
  rcases family_descends (prefixWord ++ tailWord_968857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968895 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_968895 : Nat := 118140960795 + 968895 * 2 ^ 59
def prefixEnd_968895 : Nat := 4983230072969 + 3 ^ 40 * 968895 * 2
def baseEnd_968895 : Nat := 442230078878303935605901

theorem tailTrace_968895 : CollatzResearch.WordTrace tailWord_968895 prefixEnd_968895 442230078878303935605901 := by
  unfold tailWord_968895
  simp only [CollatzResearch.WordTrace]
  refine ⟨35338503824866363937044139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23559002549910909291362759 35338503824866363937044139)
  ·
    refine ⟨53007755737299545905566209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35338503824866363937044139 53007755737299545905566209)
    ·
      refine ⟨39755816802974659429174657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53007755737299545905566209 39755816802974659429174657)
      ·
        refine ⟨29816862602230994571880993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39755816802974659429174657 29816862602230994571880993)
        ·
          refine ⟨22362646951673245928910745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29816862602230994571880993 22362646951673245928910745)
          ·
            refine ⟨16771985213754934446683059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22362646951673245928910745 16771985213754934446683059)
            ·
              refine ⟨25157977820632401670024589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16771985213754934446683059 25157977820632401670024589)
              ·
                refine ⟨9434241682737150626259221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25157977820632401670024589 9434241682737150626259221)
                ·
                  refine ⟨442230078878303935605901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9434241682737150626259221 442230078878303935605901)
                  ·
                    rfl

theorem cell20_968895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_968895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968895 prefixEnd_968895 := by exact prefixLift 968895
  have htrace : WordTrace (prefixWord ++ tailWord_968895) baseStart_968895 baseEnd_968895 := by
    simpa [prefixWord, tailWord_968895, baseEnd_968895] using wordTrace_append hprefix tailTrace_968895
  have hstable : (prefixWord ++ tailWord_968895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968895).length < 2 ^ (prefixWord ++ tailWord_968895).sum := by decide
  have hdescent : baseEnd_968895 < baseStart_968895 := by decide
  rcases family_descends (prefixWord ++ tailWord_968895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968925 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 2]
def baseStart_968925 : Nat := 118140960795 + 968925 * 2 ^ 59
def prefixEnd_968925 : Nat := 4983230072969 + 3 ^ 40 * 968925 * 2
def baseEnd_968925 : Nat := 442243771695757164605779

theorem tailTrace_968925 : CollatzResearch.WordTrace tailWord_968925 prefixEnd_968925 442243771695757164605779 := by
  unfold tailWord_968925
  simp only [CollatzResearch.WordTrace]
  refine ⟨35339598014757679060636229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23559732009838452707090819 35339598014757679060636229)
  ·
    refine ⟨6626174627767064823869293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35339598014757679060636229 6626174627767064823869293)
    ·
      refine ⟨2484815485412649308950985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6626174627767064823869293 2484815485412649308950985)
      ·
        refine ⟨1863611614059486981713239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2484815485412649308950985 1863611614059486981713239)
        ·
          refine ⟨2795417421089230472569859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863611614059486981713239 2795417421089230472569859)
          ·
            refine ⟨4193126131633845708854789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795417421089230472569859 4193126131633845708854789)
            ·
              refine ⟨786211149681346070410273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4193126131633845708854789 786211149681346070410273)
              ·
                refine ⟨589658362261009552807705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786211149681346070410273 589658362261009552807705)
                ·
                  refine ⟨442243771695757164605779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589658362261009552807705 442243771695757164605779)
                  ·
                    rfl

theorem cell20_968925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_968925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968925 prefixEnd_968925 := by exact prefixLift 968925
  have htrace : WordTrace (prefixWord ++ tailWord_968925) baseStart_968925 baseEnd_968925 := by
    simpa [prefixWord, tailWord_968925, baseEnd_968925] using wordTrace_append hprefix tailTrace_968925
  have hstable : (prefixWord ++ tailWord_968925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968925).length < 2 ^ (prefixWord ++ tailWord_968925).sum := by decide
  have hdescent : baseEnd_968925 < baseStart_968925 := by decide
  rcases family_descends (prefixWord ++ tailWord_968925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968929 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 2]
def baseStart_968929 : Nat := 118140960795 + 968929 * 2 ^ 59
def prefixEnd_968929 : Nat := 4983230072969 + 3 ^ 40 * 968929 * 2
def baseEnd_968929 : Nat := 442245597404750928472429

theorem tailTrace_968929 : CollatzResearch.WordTrace tailWord_968929 prefixEnd_968929 442245597404750928472429 := by
  unfold tailWord_968929
  simp only [CollatzResearch.WordTrace]
  refine ⟨35339743906743187743781841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23559829271162125162521227 35339743906743187743781841)
  ·
    refine ⟨26504807930057390807836381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35339743906743187743781841 26504807930057390807836381)
    ·
      refine ⟨9939302973771521552938643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26504807930057390807836381 9939302973771521552938643)
      ·
        refine ⟨14908954460657282329407965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939302973771521552938643 14908954460657282329407965)
        ·
          refine ⟨5590857922746480873527987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14908954460657282329407965 5590857922746480873527987)
          ·
            refine ⟨8386286884119721310291981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590857922746480873527987 8386286884119721310291981)
            ·
              refine ⟨3144857581544895491359493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8386286884119721310291981 3144857581544895491359493)
              ·
                refine ⟨589660796539667904629905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3144857581544895491359493 589660796539667904629905)
                ·
                  refine ⟨442245597404750928472429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589660796539667904629905 442245597404750928472429)
                  ·
                    rfl

theorem cell20_968929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_968929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968929 prefixEnd_968929 := by exact prefixLift 968929
  have htrace : WordTrace (prefixWord ++ tailWord_968929) baseStart_968929 baseEnd_968929 := by
    simpa [prefixWord, tailWord_968929, baseEnd_968929] using wordTrace_append hprefix tailTrace_968929
  have hstable : (prefixWord ++ tailWord_968929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968929).length < 2 ^ (prefixWord ++ tailWord_968929).sum := by decide
  have hdescent : baseEnd_968929 < baseStart_968929 := by decide
  rcases family_descends (prefixWord ++ tailWord_968929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968936 : List Nat := [2, 1, 4, 1, 2, 4, 1, 5]
def baseStart_968936 : Nat := 118140960795 + 968936 * 2 ^ 59
def prefixEnd_968936 : Nat := 4983230072969 + 3 ^ 40 * 968936 * 2
def baseEnd_968936 : Nat := 147416264131830005079689

theorem tailTrace_968936 : CollatzResearch.WordTrace tailWord_968936 prefixEnd_968936 147416264131830005079689 := by
  unfold tailWord_968936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669999608858913969643331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23559999478478551959524441 17669999608858913969643331)
  ·
    refine ⟨26504999413288370954464997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17669999608858913969643331 26504999413288370954464997)
    ·
      refine ⟨4969687389991569553962187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26504999413288370954464997 4969687389991569553962187)
      ·
        refine ⟨7454531084987354330943281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969687389991569553962187 7454531084987354330943281)
        ·
          refine ⟨5590898313740515748207461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7454531084987354330943281 5590898313740515748207461)
          ·
            refine ⟨1048293433826346702788899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5590898313740515748207461 1048293433826346702788899)
            ·
              refine ⟨1572440150739520054183349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048293433826346702788899 1572440150739520054183349)
              ·
                refine ⟨147416264131830005079689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1572440150739520054183349 147416264131830005079689)
                ·
                  rfl

theorem cell20_968936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_968936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968936 prefixEnd_968936 := by exact prefixLift 968936
  have htrace : WordTrace (prefixWord ++ tailWord_968936) baseStart_968936 baseEnd_968936 := by
    simpa [prefixWord, tailWord_968936, baseEnd_968936] using wordTrace_append hprefix tailTrace_968936
  have hstable : (prefixWord ++ tailWord_968936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968936).length < 2 ^ (prefixWord ++ tailWord_968936).sum := by decide
  have hdescent : baseEnd_968936 < baseStart_968936 := by decide
  rcases family_descends (prefixWord ++ tailWord_968936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968943 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_968943 : Nat := 118140960795 + 968943 * 2 ^ 59
def prefixEnd_968943 : Nat := 4983230072969 + 3 ^ 40 * 968943 * 2
def baseEnd_968943 : Nat := 442251987386229102005705

theorem tailTrace_968943 : CollatzResearch.WordTrace tailWord_968943 prefixEnd_968943 442251987386229102005705 := by
  unfold tailWord_968943
  simp only [CollatzResearch.WordTrace]
  refine ⟨35340254528692468134791483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23560169685794978756527655 35340254528692468134791483)
  ·
    refine ⟨53010381793038702202187225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35340254528692468134791483 53010381793038702202187225)
    ·
      refine ⟨39757786344779026651640419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53010381793038702202187225 39757786344779026651640419)
      ·
        refine ⟨59636679517168539977460629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39757786344779026651640419 59636679517168539977460629)
        ·
          refine ⟨2795469352367275311443467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59636679517168539977460629 2795469352367275311443467)
          ·
            refine ⟨4193204028550912967165201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795469352367275311443467 4193204028550912967165201)
            ·
              refine ⟨3144903021413184725373901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193204028550912967165201 3144903021413184725373901)
              ·
                refine ⟨1179338633029944272015213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3144903021413184725373901 1179338633029944272015213)
                ·
                  refine ⟨442251987386229102005705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179338633029944272015213 442251987386229102005705)
                  ·
                    rfl

theorem cell20_968943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_968943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968943 prefixEnd_968943 := by exact prefixLift 968943
  have htrace : WordTrace (prefixWord ++ tailWord_968943) baseStart_968943 baseEnd_968943 := by
    simpa [prefixWord, tailWord_968943, baseEnd_968943] using wordTrace_append hprefix tailTrace_968943
  have hstable : (prefixWord ++ tailWord_968943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968943).length < 2 ^ (prefixWord ++ tailWord_968943).sum := by decide
  have hdescent : baseEnd_968943 < baseStart_968943 := by decide
  rcases family_descends (prefixWord ++ tailWord_968943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968950 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_968950 : Nat := 118140960795 + 968950 * 2 ^ 59
def prefixEnd_968950 : Nat := 4983230072969 + 3 ^ 40 * 968950 * 2
def baseEnd_968950 : Nat := 442255182376968188772343

theorem tailTrace_968950 : CollatzResearch.WordTrace tailWord_968950 prefixEnd_968950 442255182376968188772343 := by
  unfold tailWord_968950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208781864979194270643519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23560339893111405553530869 2208781864979194270643519)
  ·
    refine ⟨3313172797468791405965279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2208781864979194270643519 3313172797468791405965279)
    ·
      refine ⟨4969759196203187108947919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313172797468791405965279 4969759196203187108947919)
      ·
        refine ⟨7454638794304780663421879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969759196203187108947919 7454638794304780663421879)
        ·
          refine ⟨11181958191457170995132819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454638794304780663421879 11181958191457170995132819)
          ·
            refine ⟨16772937287185756492699229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11181958191457170995132819 16772937287185756492699229)
            ·
              refine ⟨6289851482694658684762211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16772937287185756492699229 6289851482694658684762211)
              ·
                refine ⟨9434777224041988027143317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289851482694658684762211 9434777224041988027143317)
                ·
                  refine ⟨442255182376968188772343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9434777224041988027143317 442255182376968188772343)
                  ·
                    rfl

theorem cell20_968950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_968950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968950 prefixEnd_968950 := by exact prefixLift 968950
  have htrace : WordTrace (prefixWord ++ tailWord_968950) baseStart_968950 baseEnd_968950 := by
    simpa [prefixWord, tailWord_968950, baseEnd_968950] using wordTrace_append hprefix tailTrace_968950
  have hstable : (prefixWord ++ tailWord_968950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968950).length < 2 ^ (prefixWord ++ tailWord_968950).sum := by decide
  have hdescent : baseEnd_968950 < baseStart_968950 := by decide
  rcases family_descends (prefixWord ++ tailWord_968950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968971 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_968971 : Nat := 118140960795 + 968971 * 2 ^ 59
def prefixEnd_968971 : Nat := 4983230072969 + 3 ^ 40 * 968971 * 2
def baseEnd_968971 : Nat := 442264767349185449072257

theorem tailTrace_968971 : CollatzResearch.WordTrace tailWord_968971 prefixEnd_968971 442264767349185449072257 := by
  unfold tailWord_968971
  simp only [CollatzResearch.WordTrace]
  refine ⟨35341275772591028916810767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23560850515060685944540511 35341275772591028916810767)
  ·
    refine ⟨53011913658886543375216151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35341275772591028916810767 53011913658886543375216151)
    ·
      refine ⟨79517870488329815062824227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53011913658886543375216151 79517870488329815062824227)
      ·
        refine ⟨119276805732494722594236341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79517870488329815062824227 119276805732494722594236341)
        ·
          refine ⟨11182200537421380243209657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119276805732494722594236341 11182200537421380243209657)
          ·
            refine ⟨8386650403066035182407243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11182200537421380243209657 8386650403066035182407243)
            ·
              refine ⟨12579975604599052773610865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386650403066035182407243 12579975604599052773610865)
              ·
                refine ⟨9434981703449289580208149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12579975604599052773610865 9434981703449289580208149)
                ·
                  refine ⟨442264767349185449072257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9434981703449289580208149 442264767349185449072257)
                  ·
                    rfl

theorem cell20_968971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_968971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968971 prefixEnd_968971 := by exact prefixLift 968971
  have htrace : WordTrace (prefixWord ++ tailWord_968971) baseStart_968971 baseEnd_968971 := by
    simpa [prefixWord, tailWord_968971, baseEnd_968971] using wordTrace_append hprefix tailTrace_968971
  have hstable : (prefixWord ++ tailWord_968971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968971).length < 2 ^ (prefixWord ++ tailWord_968971).sum := by decide
  have hdescent : baseEnd_968971 < baseStart_968971 := by decide
  rcases family_descends (prefixWord ++ tailWord_968971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968981 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_968981 : Nat := 118140960795 + 968981 * 2 ^ 59
def prefixEnd_968981 : Nat := 4983230072969 + 3 ^ 40 * 968981 * 2
def baseEnd_968981 : Nat := 442269331621669858738883

theorem tailTrace_968981 : CollatzResearch.WordTrace tailWord_968981 prefixEnd_968981 442269331621669858738883 := by
  unfold tailWord_968981
  simp only [CollatzResearch.WordTrace]
  refine ⟨35341640502554800624674797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23561093668369867083116531 35341640502554800624674797)
  ·
    refine ⟨13253115188458050234253049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35341640502554800624674797 13253115188458050234253049)
    ·
      refine ⟨9939836391343537675689787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13253115188458050234253049 9939836391343537675689787)
      ·
        refine ⟨14909754587015306513534681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939836391343537675689787 14909754587015306513534681)
        ·
          refine ⟨11182315940261479885151011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14909754587015306513534681 11182315940261479885151011)
          ·
            refine ⟨16773473910392219827726517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182315940261479885151011 16773473910392219827726517)
            ·
              refine ⟨1572513179099270608849361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16773473910392219827726517 1572513179099270608849361)
              ·
                refine ⟨1179384884324452956637021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572513179099270608849361 1179384884324452956637021)
                ·
                  refine ⟨442269331621669858738883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179384884324452956637021 442269331621669858738883)
                  ·
                    rfl

theorem cell20_968981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_968981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_968981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_968981 prefixEnd_968981 := by exact prefixLift 968981
  have htrace : WordTrace (prefixWord ++ tailWord_968981) baseStart_968981 baseEnd_968981 := by
    simpa [prefixWord, tailWord_968981, baseEnd_968981] using wordTrace_append hprefix tailTrace_968981
  have hstable : (prefixWord ++ tailWord_968981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968981).length < 2 ^ (prefixWord ++ tailWord_968981).sum := by decide
  have hdescent : baseEnd_968981 < baseStart_968981 := by decide
  rcases family_descends (prefixWord ++ tailWord_968981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969012 : List Nat := [2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_969012 : Nat := 118140960795 + 969012 * 2 ^ 59
def prefixEnd_969012 : Nat := 4983230072969 + 3 ^ 40 * 969012 * 2
def baseEnd_969012 : Nat := 147427826955457176235141

theorem tailTrace_969012 : CollatzResearch.WordTrace tailWord_969012 prefixEnd_969012 147427826955457176235141 := by
  unfold tailWord_969012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671385582721246459526645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23561847443628328612702193 17671385582721246459526645)
  ·
    refine ⟨1656692398380116855580623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17671385582721246459526645 1656692398380116855580623)
    ·
      refine ⟨2485038597570175283370935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656692398380116855580623 2485038597570175283370935)
      ·
        refine ⟨3727557896355262925056403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2485038597570175283370935 3727557896355262925056403)
        ·
          refine ⟨5591336844532894387584605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727557896355262925056403 5591336844532894387584605)
          ·
            refine ⟨2096751316699835395344227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5591336844532894387584605 2096751316699835395344227)
            ·
              refine ⟨3145126975049753093016341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096751316699835395344227 3145126975049753093016341)
              ·
                refine ⟨147427826955457176235141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3145126975049753093016341 147427826955457176235141)
                ·
                  rfl

theorem cell20_969012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_969012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969012 prefixEnd_969012 := by exact prefixLift 969012
  have htrace : WordTrace (prefixWord ++ tailWord_969012) baseStart_969012 baseEnd_969012 := by
    simpa [prefixWord, tailWord_969012, baseEnd_969012] using wordTrace_append hprefix tailTrace_969012
  have hstable : (prefixWord ++ tailWord_969012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969012).length < 2 ^ (prefixWord ++ tailWord_969012).sum := by decide
  have hdescent : baseEnd_969012 < baseStart_969012 := by decide
  rcases family_descends (prefixWord ++ tailWord_969012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969022 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_969022 : Nat := 118140960795 + 969022 * 2 ^ 59
def prefixEnd_969022 : Nat := 4983230072969 + 3 ^ 40 * 969022 * 2
def baseEnd_969022 : Nat := 442288045138855938372049

theorem tailTrace_969022 : CollatzResearch.WordTrace tailWord_969022 prefixEnd_969022 442288045138855938372049 := by
  unfold tailWord_969022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417891986925783078364665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23562090596937509751278213 4417891986925783078364665)
  ·
    refine ⟨3313418990194337308773499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4417891986925783078364665 3313418990194337308773499)
    ·
      refine ⟨4970128485291505963160249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313418990194337308773499 4970128485291505963160249)
      ·
        refine ⟨3727596363968629472370187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4970128485291505963160249 3727596363968629472370187)
        ·
          refine ⟨5591394545952944208555281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727596363968629472370187 5591394545952944208555281)
          ·
            refine ⟨4193545909464708156416461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591394545952944208555281 4193545909464708156416461)
            ·
              refine ⟨1572579716049265558656173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4193545909464708156416461 1572579716049265558656173)
              ·
                refine ⟨589717393518474584496065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1572579716049265558656173 589717393518474584496065)
                ·
                  refine ⟨442288045138855938372049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589717393518474584496065 442288045138855938372049)
                  ·
                    rfl

theorem cell20_969022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_969022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969022 prefixEnd_969022 := by exact prefixLift 969022
  have htrace : WordTrace (prefixWord ++ tailWord_969022) baseStart_969022 baseEnd_969022 := by
    simpa [prefixWord, tailWord_969022, baseEnd_969022] using wordTrace_append hprefix tailTrace_969022
  have hstable : (prefixWord ++ tailWord_969022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969022).length < 2 ^ (prefixWord ++ tailWord_969022).sum := by decide
  have hdescent : baseEnd_969022 < baseStart_969022 := by decide
  rcases family_descends (prefixWord ++ tailWord_969022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969040 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_969040 : Nat := 118140960795 + 969040 * 2 ^ 59
def prefixEnd_969040 : Nat := 4983230072969 + 3 ^ 40 * 969040 * 2
def baseEnd_969040 : Nat := 442296260829327875771975

theorem tailTrace_969040 : CollatzResearch.WordTrace tailWord_969040 prefixEnd_969040 442296260829327875771975 := by
  unfold tailWord_969040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671896204670526850536287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23562528272894035800715049 17671896204670526850536287)
  ·
    refine ⟨26507844307005790275804431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17671896204670526850536287 26507844307005790275804431)
    ·
      refine ⟨39761766460508685413706647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26507844307005790275804431 39761766460508685413706647)
      ·
        refine ⟨59642649690763028120559971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39761766460508685413706647 59642649690763028120559971)
        ·
          refine ⟨89463974536144542180839957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59642649690763028120559971 89463974536144542180839957)
          ·
            refine ⟨4193623806381775414726873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89463974536144542180839957 4193623806381775414726873)
            ·
              refine ⟨3145217854786331561045155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193623806381775414726873 3145217854786331561045155)
              ·
                refine ⟨4717826782179497341567733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145217854786331561045155 4717826782179497341567733)
                ·
                  refine ⟨442296260829327875771975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4717826782179497341567733 442296260829327875771975)
                  ·
                    rfl

theorem cell20_969040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_969040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969040 prefixEnd_969040 := by exact prefixLift 969040
  have htrace : WordTrace (prefixWord ++ tailWord_969040) baseStart_969040 baseEnd_969040 := by
    simpa [prefixWord, tailWord_969040, baseEnd_969040] using wordTrace_append hprefix tailTrace_969040
  have hstable : (prefixWord ++ tailWord_969040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969040).length < 2 ^ (prefixWord ++ tailWord_969040).sum := by decide
  have hdescent : baseEnd_969040 < baseStart_969040 := by decide
  rcases family_descends (prefixWord ++ tailWord_969040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969095 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_969095 : Nat := 118140960795 + 969095 * 2 ^ 59
def prefixEnd_969095 : Nat := 4983230072969 + 3 ^ 40 * 969095 * 2
def baseEnd_969095 : Nat := 442321364327992128938417

theorem tailTrace_969095 : CollatzResearch.WordTrace tailWord_969095 prefixEnd_969095 442321364327992128938417 := by
  unfold tailWord_969095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35345798424141798094324739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23563865616094532062883159 35345798424141798094324739)
  ·
    refine ⟨53018697636212697141487109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35345798424141798094324739 53018697636212697141487109)
    ·
      refine ⟨9941005806789880714028833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53018697636212697141487109 9941005806789880714028833)
      ·
        refine ⟨7455754355092410535521625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9941005806789880714028833 7455754355092410535521625)
        ·
          refine ⟨5591815766319307901641219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7455754355092410535521625 5591815766319307901641219)
          ·
            refine ⟨8387723649478961852461829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591815766319307901641219 8387723649478961852461829)
            ·
              refine ⟨1572698184277305347336593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8387723649478961852461829 1572698184277305347336593)
              ·
                refine ⟨1179523638207979010502445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572698184277305347336593 1179523638207979010502445)
                ·
                  refine ⟨442321364327992128938417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179523638207979010502445 442321364327992128938417)
                  ·
                    rfl

theorem cell20_969095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_969095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969095 prefixEnd_969095 := by exact prefixLift 969095
  have htrace : WordTrace (prefixWord ++ tailWord_969095) baseStart_969095 baseEnd_969095 := by
    simpa [prefixWord, tailWord_969095, baseEnd_969095] using wordTrace_append hprefix tailTrace_969095
  have hstable : (prefixWord ++ tailWord_969095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969095).length < 2 ^ (prefixWord ++ tailWord_969095).sum := by decide
  have hdescent : baseEnd_969095 < baseStart_969095 := by decide
  rcases family_descends (prefixWord ++ tailWord_969095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969123 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_969123 : Nat := 118140960795 + 969123 * 2 ^ 59
def prefixEnd_969123 : Nat := 4983230072969 + 3 ^ 40 * 969123 * 2
def baseEnd_969123 : Nat := 442334144290948476004969

theorem tailTrace_969123 : CollatzResearch.WordTrace tailWord_969123 prefixEnd_969123 442334144290948476004969 := by
  unfold tailWord_969123
  simp only [CollatzResearch.WordTrace]
  refine ⟨35346819668040358876344023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23564546445360239250896015 35346819668040358876344023)
  ·
    refine ⟨53020229502060538314516035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35346819668040358876344023 53020229502060538314516035)
    ·
      refine ⟨79530344253090807471774053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53020229502060538314516035 79530344253090807471774053)
      ·
        refine ⟨14911939547454526400957635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79530344253090807471774053 14911939547454526400957635)
        ·
          refine ⟨22367909321181789601436453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14911939547454526400957635 22367909321181789601436453)
          ·
            refine ⟨4193982997721585550269335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22367909321181789601436453 4193982997721585550269335)
            ·
              refine ⟨6290974496582378325404003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193982997721585550269335 6290974496582378325404003)
              ·
                refine ⟨9436461744873567488106005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290974496582378325404003 9436461744873567488106005)
                ·
                  refine ⟨442334144290948476004969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9436461744873567488106005 442334144290948476004969)
                  ·
                    rfl

theorem cell20_969123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_969123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969123 prefixEnd_969123 := by exact prefixLift 969123
  have htrace : WordTrace (prefixWord ++ tailWord_969123) baseStart_969123 baseEnd_969123 := by
    simpa [prefixWord, tailWord_969123, baseEnd_969123] using wordTrace_append hprefix tailTrace_969123
  have hstable : (prefixWord ++ tailWord_969123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969123).length < 2 ^ (prefixWord ++ tailWord_969123).sum := by decide
  have hdescent : baseEnd_969123 < baseStart_969123 := by decide
  rcases family_descends (prefixWord ++ tailWord_969123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969153 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 4]
def baseStart_969153 : Nat := 118140960795 + 969153 * 2 ^ 59
def prefixEnd_969153 : Nat := 4983230072969 + 3 ^ 40 * 969153 * 2
def baseEnd_969153 : Nat := 442347837108401705004847

theorem tailTrace_969153 : CollatzResearch.WordTrace tailWord_969153 prefixEnd_969153 442347837108401705004847 := by
  unfold tailWord_969153
  simp only [CollatzResearch.WordTrace]
  refine ⟨35347913857931673999936113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23565275905287782666624075 35347913857931673999936113)
  ·
    refine ⟨26510935393448755499952085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35347913857931673999936113 26510935393448755499952085)
    ·
      refine ⟨621350048283955207030127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26510935393448755499952085 621350048283955207030127)
      ·
        refine ⟨932025072425932810545191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621350048283955207030127 932025072425932810545191)
        ·
          refine ⟨1398037608638899215817787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932025072425932810545191 1398037608638899215817787)
          ·
            refine ⟨2097056412958348823726681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398037608638899215817787 2097056412958348823726681)
            ·
              refine ⟨1572792309718761617795011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097056412958348823726681 1572792309718761617795011)
              ·
                refine ⟨2359188464578142426692517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572792309718761617795011 2359188464578142426692517)
                ·
                  refine ⟨442347837108401705004847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359188464578142426692517 442347837108401705004847)
                  ·
                    rfl

theorem cell20_969153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_969153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969153 prefixEnd_969153 := by exact prefixLift 969153
  have htrace : WordTrace (prefixWord ++ tailWord_969153) baseStart_969153 baseEnd_969153 := by
    simpa [prefixWord, tailWord_969153, baseEnd_969153] using wordTrace_append hprefix tailTrace_969153
  have hstable : (prefixWord ++ tailWord_969153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969153).length < 2 ^ (prefixWord ++ tailWord_969153).sum := by decide
  have hdescent : baseEnd_969153 < baseStart_969153 := by decide
  rcases family_descends (prefixWord ++ tailWord_969153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969161 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_969161 : Nat := 118140960795 + 969161 * 2 ^ 59
def prefixEnd_969161 : Nat := 4983230072969 + 3 ^ 40 * 969161 * 2
def baseEnd_969161 : Nat := 442351488526389232738147

theorem tailTrace_969161 : CollatzResearch.WordTrace tailWord_969161 prefixEnd_969161 442351488526389232738147 := by
  unfold tailWord_969161
  simp only [CollatzResearch.WordTrace]
  refine ⟨35348205641902691366227337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23565470427935127577484891 35348205641902691366227337)
  ·
    refine ⟨26511154231427018524670503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35348205641902691366227337 26511154231427018524670503)
    ·
      refine ⟨39766731347140527787005755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26511154231427018524670503 39766731347140527787005755)
      ·
        refine ⟨59650097020710791680508633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39766731347140527787005755 59650097020710791680508633)
        ·
          refine ⟨44737572765533093760381475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59650097020710791680508633 44737572765533093760381475)
          ·
            refine ⟨67106359148299640640572213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44737572765533093760381475 67106359148299640640572213)
            ·
              refine ⟨6291221170153091310053645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67106359148299640640572213 6291221170153091310053645)
              ·
                refine ⟨2359207938807409241270117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6291221170153091310053645 2359207938807409241270117)
                ·
                  refine ⟨442351488526389232738147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359207938807409241270117 442351488526389232738147)
                  ·
                    rfl

theorem cell20_969161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_969161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969161 prefixEnd_969161 := by exact prefixLift 969161
  have htrace : WordTrace (prefixWord ++ tailWord_969161) baseStart_969161 baseEnd_969161 := by
    simpa [prefixWord, tailWord_969161, baseEnd_969161] using wordTrace_append hprefix tailTrace_969161
  have hstable : (prefixWord ++ tailWord_969161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969161).length < 2 ^ (prefixWord ++ tailWord_969161).sum := by decide
  have hdescent : baseEnd_969161 < baseStart_969161 := by decide
  rcases family_descends (prefixWord ++ tailWord_969161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969192 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_969192 : Nat := 118140960795 + 969192 * 2 ^ 59
def prefixEnd_969192 : Nat := 4983230072969 + 3 ^ 40 * 969192 * 2
def baseEnd_969192 : Nat := 442365637771090902704687

theorem tailTrace_969192 : CollatzResearch.WordTrace tailWord_969192 prefixEnd_969192 442365637771090902704687 := by
  unfold tailWord_969192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674668152395191830302915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23566224203193589107070553 17674668152395191830302915)
  ·
    refine ⟨26512002228592787745454373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17674668152395191830302915 26512002228592787745454373)
    ·
      refine ⟨4971000417861147702272695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26512002228592787745454373 4971000417861147702272695)
      ·
        refine ⟨7456500626791721553409043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971000417861147702272695 7456500626791721553409043)
        ·
          refine ⟨11184750940187582330113565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456500626791721553409043 11184750940187582330113565)
          ·
            refine ⟨4194281602570343373792587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11184750940187582330113565 4194281602570343373792587)
            ·
              refine ⟨6291422403855515060688881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194281602570343373792587 6291422403855515060688881)
              ·
                refine ⟨4718566802891636295516661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291422403855515060688881 4718566802891636295516661)
                ·
                  refine ⟨442365637771090902704687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4718566802891636295516661 442365637771090902704687)
                  ·
                    rfl

theorem cell20_969192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_969192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969192 prefixEnd_969192 := by exact prefixLift 969192
  have htrace : WordTrace (prefixWord ++ tailWord_969192) baseStart_969192 baseEnd_969192 := by
    simpa [prefixWord, tailWord_969192, baseEnd_969192] using wordTrace_append hprefix tailTrace_969192
  have hstable : (prefixWord ++ tailWord_969192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969192).length < 2 ^ (prefixWord ++ tailWord_969192).sum := by decide
  have hdescent : baseEnd_969192 < baseStart_969192 := by decide
  rcases family_descends (prefixWord ++ tailWord_969192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969202 : List Nat := [3, 2, 1, 4, 2, 2, 6]
def baseStart_969202 : Nat := 118140960795 + 969202 * 2 ^ 59
def prefixEnd_969202 : Nat := 4983230072969 + 3 ^ 40 * 969202 * 2
def baseEnd_969202 : Nat := 49152244671508368041257

theorem tailTrace_969202 : CollatzResearch.WordTrace tailWord_969202 prefixEnd_969202 49152244671508368041257 := by
  unfold tailWord_969202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8837425258688538842117465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23566467356502770245646573 8837425258688538842117465)
  ·
    refine ⟨6628068944016404131588099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8837425258688538842117465 6628068944016404131588099)
    ·
      refine ⟨9942103416024606197382149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628068944016404131588099 9942103416024606197382149)
      ·
        refine ⟨1864144390504613662009153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9942103416024606197382149 1864144390504613662009153)
        ·
          refine ⟨1398108292878460246506865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1864144390504613662009153 1398108292878460246506865)
          ·
            refine ⟨1048581219658845184880149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398108292878460246506865 1048581219658845184880149)
            ·
              refine ⟨49152244671508368041257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1048581219658845184880149 49152244671508368041257)
              ·
                rfl

theorem cell20_969202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 6].length) (baseStart_969202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969202 prefixEnd_969202 := by exact prefixLift 969202
  have htrace : WordTrace (prefixWord ++ tailWord_969202) baseStart_969202 baseEnd_969202 := by
    simpa [prefixWord, tailWord_969202, baseEnd_969202] using wordTrace_append hprefix tailTrace_969202
  have hstable : (prefixWord ++ tailWord_969202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969202).length < 2 ^ (prefixWord ++ tailWord_969202).sum := by decide
  have hdescent : baseEnd_969202 < baseStart_969202 := by decide
  rcases family_descends (prefixWord ++ tailWord_969202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969222 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_969222 : Nat := 118140960795 + 969222 * 2 ^ 59
def prefixEnd_969222 : Nat := 4983230072969 + 3 ^ 40 * 969222 * 2
def baseEnd_969222 : Nat := 442379330588544131704565

theorem tailTrace_969222 : CollatzResearch.WordTrace tailWord_969222 prefixEnd_969222 442379330588544131704565 := by
  unfold tailWord_969222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104700952958803087006185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23566953663121132522798613 1104700952958803087006185)
  ·
    refine ⟨828525714719102315254639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104700952958803087006185 828525714719102315254639)
    ·
      refine ⟨1242788572078653472881959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828525714719102315254639 1242788572078653472881959)
      ·
        refine ⟨1864182858117980209322939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242788572078653472881959 1864182858117980209322939)
        ·
          refine ⟨2796274287176970313984409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864182858117980209322939 2796274287176970313984409)
          ·
            refine ⟨2097205715382727735488307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796274287176970313984409 2097205715382727735488307)
            ·
              refine ⟨3145808573074091603232461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097205715382727735488307 3145808573074091603232461)
              ·
                refine ⟨1179678214902784351212173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3145808573074091603232461 1179678214902784351212173)
                ·
                  refine ⟨442379330588544131704565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179678214902784351212173 442379330588544131704565)
                  ·
                    rfl

theorem cell20_969222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_969222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969222 prefixEnd_969222 := by exact prefixLift 969222
  have htrace : WordTrace (prefixWord ++ tailWord_969222) baseStart_969222 baseEnd_969222 := by
    simpa [prefixWord, tailWord_969222, baseEnd_969222] using wordTrace_append hprefix tailTrace_969222
  have hstable : (prefixWord ++ tailWord_969222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969222).length < 2 ^ (prefixWord ++ tailWord_969222).sum := by decide
  have hdescent : baseEnd_969222 < baseStart_969222 := by decide
  rcases family_descends (prefixWord ++ tailWord_969222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969237 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_969237 : Nat := 118140960795 + 969237 * 2 ^ 59
def prefixEnd_969237 : Nat := 4983230072969 + 3 ^ 40 * 969237 * 2
def baseEnd_969237 : Nat := 442386176997270746204503

theorem tailTrace_969237 : CollatzResearch.WordTrace tailWord_969237 prefixEnd_969237 442386176997270746204503 := by
  unfold tailWord_969237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35350977589627356345993965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23567318393084904230662643 35350977589627356345993965)
  ·
    refine ⟨13256616596110258629747737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35350977589627356345993965 13256616596110258629747737)
    ·
      refine ⟨9942462447082693972310803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13256616596110258629747737 9942462447082693972310803)
      ·
        refine ⟨14913693670624040958466205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942462447082693972310803 14913693670624040958466205)
        ·
          refine ⟨5592635126484015359424827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14913693670624040958466205 5592635126484015359424827)
          ·
            refine ⟨8388952689726023039137241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592635126484015359424827 8388952689726023039137241)
            ·
              refine ⟨6291714517294517279352931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8388952689726023039137241 6291714517294517279352931)
              ·
                refine ⟨9437571775941775919029397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291714517294517279352931 9437571775941775919029397)
                ·
                  refine ⟨442386176997270746204503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9437571775941775919029397 442386176997270746204503)
                  ·
                    rfl

theorem cell20_969237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_969237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969237 prefixEnd_969237 := by exact prefixLift 969237
  have htrace : WordTrace (prefixWord ++ tailWord_969237) baseStart_969237 baseEnd_969237 := by
    simpa [prefixWord, tailWord_969237, baseEnd_969237] using wordTrace_append hprefix tailTrace_969237
  have hstable : (prefixWord ++ tailWord_969237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969237).length < 2 ^ (prefixWord ++ tailWord_969237).sum := by decide
  have hdescent : baseEnd_969237 < baseStart_969237 := by decide
  rcases family_descends (prefixWord ++ tailWord_969237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969289 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_969289 : Nat := 118140960795 + 969289 * 2 ^ 59
def prefixEnd_969289 : Nat := 4983230072969 + 3 ^ 40 * 969289 * 2
def baseEnd_969289 : Nat := 442409911214189676470957

theorem tailTrace_969289 : CollatzResearch.WordTrace tailWord_969289 prefixEnd_969289 442409911214189676470957 := by
  unfold tailWord_969289
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352874185438969226886921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23568582790292646151257947 35352874185438969226886921)
  ·
    refine ⟨26514655639079226920165191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35352874185438969226886921 26514655639079226920165191)
    ·
      refine ⟨39771983458618840380247787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26514655639079226920165191 39771983458618840380247787)
      ·
        refine ⟨59657975187928260570371681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39771983458618840380247787 59657975187928260570371681)
        ·
          refine ⟨44743481390946195427778761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59657975187928260570371681 44743481390946195427778761)
          ·
            refine ⟨33557611043209646570834071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44743481390946195427778761 33557611043209646570834071)
            ·
              refine ⟨50336416564814469856251107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33557611043209646570834071 50336416564814469856251107)
              ·
                refine ⟨75504624847221704784376661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50336416564814469856251107 75504624847221704784376661)
                ·
                  refine ⟨442409911214189676470957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75504624847221704784376661 442409911214189676470957)
                  ·
                    rfl

theorem cell20_969289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_969289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969289 prefixEnd_969289 := by exact prefixLift 969289
  have htrace : WordTrace (prefixWord ++ tailWord_969289) baseStart_969289 baseEnd_969289 := by
    simpa [prefixWord, tailWord_969289, baseEnd_969289] using wordTrace_append hprefix tailTrace_969289
  have hstable : (prefixWord ++ tailWord_969289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969289).length < 2 ^ (prefixWord ++ tailWord_969289).sum := by decide
  have hdescent : baseEnd_969289 < baseStart_969289 := by decide
  rcases family_descends (prefixWord ++ tailWord_969289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969346 : List Nat := [3, 4, 3, 1, 2, 1, 2, 4]
def baseStart_969346 : Nat := 118140960795 + 969346 * 2 ^ 59
def prefixEnd_969346 : Nat := 4983230072969 + 3 ^ 40 * 969346 * 2
def baseEnd_969346 : Nat := 147478642522450270523575

theorem tailTrace_969346 : CollatzResearch.WordTrace tailWord_969346 prefixEnd_969346 147478642522450270523575 := by
  unfold tailWord_969346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8838738286558116990427973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23569968764154978641141261 8838738286558116990427973)
  ·
    refine ⟨1657263428729646935705245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8838738286558116990427973 1657263428729646935705245)
    ·
      refine ⟨621473785773617600889467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1657263428729646935705245 621473785773617600889467)
      ·
        refine ⟨932210678660426401334201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621473785773617600889467 932210678660426401334201)
        ·
          refine ⟨699158008995319801000651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932210678660426401334201 699158008995319801000651)
          ·
            refine ⟨1048737013492979701500977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699158008995319801000651 1048737013492979701500977)
            ·
              refine ⟨786552760119734776125733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048737013492979701500977 786552760119734776125733)
              ·
                refine ⟨147478642522450270523575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786552760119734776125733 147478642522450270523575)
                ·
                  rfl

theorem cell20_969346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_969346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969346 prefixEnd_969346 := by exact prefixLift 969346
  have htrace : WordTrace (prefixWord ++ tailWord_969346) baseStart_969346 baseEnd_969346 := by
    simpa [prefixWord, tailWord_969346, baseEnd_969346] using wordTrace_append hprefix tailTrace_969346
  have hstable : (prefixWord ++ tailWord_969346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969346).length < 2 ^ (prefixWord ++ tailWord_969346).sum := by decide
  have hdescent : baseEnd_969346 < baseStart_969346 := by decide
  rcases family_descends (prefixWord ++ tailWord_969346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969351 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_969351 : Nat := 118140960795 + 969351 * 2 ^ 59
def prefixEnd_969351 : Nat := 4983230072969 + 3 ^ 40 * 969351 * 2
def baseEnd_969351 : Nat := 442438209703593016404037

theorem tailTrace_969351 : CollatzResearch.WordTrace tailWord_969351 prefixEnd_969351 442438209703593016404037 := by
  unfold tailWord_969351
  simp only [CollatzResearch.WordTrace]
  refine ⟨35355135511214353815643907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23570090340809569210429271 35355135511214353815643907)
  ·
    refine ⟨53032703266821530723465861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35355135511214353815643907 53032703266821530723465861)
    ·
      refine ⟨9943631862529037010649849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53032703266821530723465861 9943631862529037010649849)
      ·
        refine ⟨7457723896896777757987387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9943631862529037010649849 7457723896896777757987387)
        ·
          refine ⟨11186585845345166636981081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457723896896777757987387 11186585845345166636981081)
          ·
            refine ⟨8389939384008874977735811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11186585845345166636981081 8389939384008874977735811)
            ·
              refine ⟨12584909076013312466603717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389939384008874977735811 12584909076013312466603717)
              ·
                refine ⟨2359670451752496087488197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12584909076013312466603717 2359670451752496087488197)
                ·
                  refine ⟨442438209703593016404037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359670451752496087488197 442438209703593016404037)
                  ·
                    rfl

theorem cell20_969351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_969351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969351 prefixEnd_969351 := by exact prefixLift 969351
  have htrace : WordTrace (prefixWord ++ tailWord_969351) baseStart_969351 baseEnd_969351 := by
    simpa [prefixWord, tailWord_969351, baseEnd_969351] using wordTrace_append hprefix tailTrace_969351
  have hstable : (prefixWord ++ tailWord_969351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969351).length < 2 ^ (prefixWord ++ tailWord_969351).sum := by decide
  have hdescent : baseEnd_969351 < baseStart_969351 := by decide
  rcases family_descends (prefixWord ++ tailWord_969351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969364 : List Nat := [2, 4, 2, 2, 1, 1, 3, 3, 2]
def baseStart_969364 : Nat := 118140960795 + 969364 * 2 ^ 59
def prefixEnd_969364 : Nat := 4983230072969 + 3 ^ 40 * 969364 * 2
def baseEnd_969364 : Nat := 442444143257822748970651

theorem tailTrace_969364 : CollatzResearch.WordTrace tailWord_969364 prefixEnd_969364 442444143257822748970651 := by
  unfold tailWord_969364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17677804830083628517933573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23570406440111504690578097 17677804830083628517933573)
  ·
    refine ⟨3314588405640680347112545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17677804830083628517933573 3314588405640680347112545)
    ·
      refine ⟨2485941304230510260334409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3314588405640680347112545 2485941304230510260334409)
      ·
        refine ⟨1864455978172882695250807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2485941304230510260334409 1864455978172882695250807)
        ·
          refine ⟨2796683967259324042876211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864455978172882695250807 2796683967259324042876211)
          ·
            refine ⟨4195025950888986064314317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796683967259324042876211 4195025950888986064314317)
            ·
              refine ⟨1573134731583369774117869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4195025950888986064314317 1573134731583369774117869)
              ·
                refine ⟨589925524343763665294201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573134731583369774117869 589925524343763665294201)
                ·
                  refine ⟨442444143257822748970651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589925524343763665294201 442444143257822748970651)
                  ·
                    rfl

theorem cell20_969364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_969364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969364 prefixEnd_969364 := by exact prefixLift 969364
  have htrace : WordTrace (prefixWord ++ tailWord_969364) baseStart_969364 baseEnd_969364 := by
    simpa [prefixWord, tailWord_969364, baseEnd_969364] using wordTrace_append hprefix tailTrace_969364
  have hstable : (prefixWord ++ tailWord_969364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969364).length < 2 ^ (prefixWord ++ tailWord_969364).sum := by decide
  have hdescent : baseEnd_969364 < baseStart_969364 := by decide
  rcases family_descends (prefixWord ++ tailWord_969364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969399 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_969399 : Nat := 118140960795 + 969399 * 2 ^ 59
def prefixEnd_969399 : Nat := 4983230072969 + 3 ^ 40 * 969399 * 2
def baseEnd_969399 : Nat := 442460118211518182803841

theorem tailTrace_969399 : CollatzResearch.WordTrace tailWord_969399 prefixEnd_969399 442460118211518182803841 := by
  unfold tailWord_969399
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356886215040458013391251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23571257476693638675594167 35356886215040458013391251)
  ·
    refine ⟨53035329322560687020086877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35356886215040458013391251 53035329322560687020086877)
    ·
      refine ⟨19888248495960257632532579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53035329322560687020086877 19888248495960257632532579)
      ·
        refine ⟨29832372743940386448798869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19888248495960257632532579 29832372743940386448798869)
        ·
          refine ⟨1398392472372205614787447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29832372743940386448798869 1398392472372205614787447)
          ·
            refine ⟨2097588708558308422181171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398392472372205614787447 2097588708558308422181171)
            ·
              refine ⟨3146383062837462633271757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097588708558308422181171 3146383062837462633271757)
              ·
                refine ⟨1179893648564048487476909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3146383062837462633271757 1179893648564048487476909)
                ·
                  refine ⟨442460118211518182803841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179893648564048487476909 442460118211518182803841)
                  ·
                    rfl

theorem cell20_969399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_969399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969399 prefixEnd_969399 := by exact prefixLift 969399
  have htrace : WordTrace (prefixWord ++ tailWord_969399) baseStart_969399 baseEnd_969399 := by
    simpa [prefixWord, tailWord_969399, baseEnd_969399] using wordTrace_append hprefix tailTrace_969399
  have hstable : (prefixWord ++ tailWord_969399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969399).length < 2 ^ (prefixWord ++ tailWord_969399).sum := by decide
  have hdescent : baseEnd_969399 < baseStart_969399 := by decide
  rcases family_descends (prefixWord ++ tailWord_969399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969503 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_969503 : Nat := 118140960795 + 969503 * 2 ^ 59
def prefixEnd_969503 : Nat := 4983230072969 + 3 ^ 40 * 969503 * 2
def baseEnd_969503 : Nat := 442507586645356043336749

theorem tailTrace_969503 : CollatzResearch.WordTrace tailWord_969503 prefixEnd_969503 442507586645356043336749 := by
  unfold tailWord_969503
  simp only [CollatzResearch.WordTrace]
  refine ⟨35360679406663683775177163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23573786271109122516784775 35360679406663683775177163)
  ·
    refine ⟨53041019109995525662765745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35360679406663683775177163 53041019109995525662765745)
    ·
      refine ⟨39780764332496644247074309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53041019109995525662765745 39780764332496644247074309)
      ·
        refine ⟨7458893312343120796326433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39780764332496644247074309 7458893312343120796326433)
        ·
          refine ⟨5594169984257340597244825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7458893312343120796326433 5594169984257340597244825)
          ·
            refine ⟨4195627488193005447933619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5594169984257340597244825 4195627488193005447933619)
            ·
              refine ⟨6293441232289508171900429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195627488193005447933619 6293441232289508171900429)
              ·
                refine ⟨2360040462108565564462661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6293441232289508171900429 2360040462108565564462661)
                ·
                  refine ⟨442507586645356043336749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360040462108565564462661 442507586645356043336749)
                  ·
                    rfl

theorem cell20_969503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_969503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969503 prefixEnd_969503 := by exact prefixLift 969503
  have htrace : WordTrace (prefixWord ++ tailWord_969503) baseStart_969503 baseEnd_969503 := by
    simpa [prefixWord, tailWord_969503, baseEnd_969503] using wordTrace_append hprefix tailTrace_969503
  have hstable : (prefixWord ++ tailWord_969503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969503).length < 2 ^ (prefixWord ++ tailWord_969503).sum := by decide
  have hdescent : baseEnd_969503 < baseStart_969503 := by decide
  rcases family_descends (prefixWord ++ tailWord_969503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969533 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 2]
def baseStart_969533 : Nat := 118140960795 + 969533 * 2 ^ 59
def prefixEnd_969533 : Nat := 4983230072969 + 3 ^ 40 * 969533 * 2
def baseEnd_969533 : Nat := 442521279462809272336627

theorem tailTrace_969533 : CollatzResearch.WordTrace tailWord_969533 prefixEnd_969533 442521279462809272336627 := by
  unfold tailWord_969533
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361773596554998898769253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23574515731036665932512835 35361773596554998898769253)
  ·
    refine ⟨6630332549354062293519235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35361773596554998898769253 6630332549354062293519235)
    ·
      refine ⟨9945498824031093440278853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630332549354062293519235 9945498824031093440278853)
      ·
        refine ⟨1864781029505830020052285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9945498824031093440278853 1864781029505830020052285)
        ·
          refine ⟨699292886064686257519607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1864781029505830020052285 699292886064686257519607)
          ·
            refine ⟨1048939329097029386279411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699292886064686257519607 1048939329097029386279411)
            ·
              refine ⟨1573408993645544079419117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048939329097029386279411 1573408993645544079419117)
              ·
                refine ⟨590028372617079029782169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573408993645544079419117 590028372617079029782169)
                ·
                  refine ⟨442521279462809272336627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590028372617079029782169 442521279462809272336627)
                  ·
                    rfl

theorem cell20_969533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_969533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969533 prefixEnd_969533 := by exact prefixLift 969533
  have htrace : WordTrace (prefixWord ++ tailWord_969533) baseStart_969533 baseEnd_969533 := by
    simpa [prefixWord, tailWord_969533, baseEnd_969533] using wordTrace_append hprefix tailTrace_969533
  have hstable : (prefixWord ++ tailWord_969533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969533).length < 2 ^ (prefixWord ++ tailWord_969533).sum := by decide
  have hdescent : baseEnd_969533 < baseStart_969533 := by decide
  rcases family_descends (prefixWord ++ tailWord_969533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969548 : List Nat := [2, 2, 1, 3, 3, 1, 8]
def baseStart_969548 : Nat := 118140960795 + 969548 * 2 ^ 59
def prefixEnd_969548 : Nat := 4983230072969 + 3 ^ 40 * 969548 * 2
def baseEnd_969548 : Nat := 49169791763503987426285

theorem tailTrace_969548 : CollatzResearch.WordTrace tailWord_969548 prefixEnd_969548 49169791763503987426285 := by
  unfold tailWord_969548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17681160345750328230282649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23574880461000437640376865 17681160345750328230282649)
  ·
    refine ⟨13260870259312746172711987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17681160345750328230282649 13260870259312746172711987)
    ·
      refine ⟨19891305388969119259067981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13260870259312746172711987 19891305388969119259067981)
      ·
        refine ⟨7459239520863419722150493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19891305388969119259067981 7459239520863419722150493)
        ·
          refine ⟨2797214820323782395806435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7459239520863419722150493 2797214820323782395806435)
          ·
            refine ⟨4195822230485673593709653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797214820323782395806435 4195822230485673593709653)
            ·
              refine ⟨49169791763503987426285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4195822230485673593709653 49169791763503987426285)
              ·
                rfl

theorem cell20_969548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_969548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969548 prefixEnd_969548 := by exact prefixLift 969548
  have htrace : WordTrace (prefixWord ++ tailWord_969548) baseStart_969548 baseEnd_969548 := by
    simpa [prefixWord, tailWord_969548, baseEnd_969548] using wordTrace_append hprefix tailTrace_969548
  have hstable : (prefixWord ++ tailWord_969548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969548).length < 2 ^ (prefixWord ++ tailWord_969548).sum := by decide
  have hdescent : baseEnd_969548 < baseStart_969548 := by decide
  rcases family_descends (prefixWord ++ tailWord_969548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969586 : List Nat := [3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_969586 : Nat := 118140960795 + 969586 * 2 ^ 59
def prefixEnd_969586 : Nat := 4983230072969 + 3 ^ 40 * 969586 * 2
def baseEnd_969586 : Nat := 147515156702325547856581

theorem tailTrace_969586 : CollatzResearch.WordTrace tailWord_969586 prefixEnd_969586 147515156702325547856581 := by
  unfold tailWord_969586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840926666340747237612153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23575804443575325966965741 8840926666340747237612153)
  ·
    refine ⟨6630694999755560428209115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8840926666340747237612153 6630694999755560428209115)
    ·
      refine ⟨9946042499633340642313673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630694999755560428209115 9946042499633340642313673)
      ·
        refine ⟨7459531874725005481735255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9946042499633340642313673 7459531874725005481735255)
        ·
          refine ⟨11189297812087508222602883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459531874725005481735255 11189297812087508222602883)
          ·
            refine ⟨16783946718131262333904325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11189297812087508222602883 16783946718131262333904325)
            ·
              refine ⟨3146990009649611687607061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16783946718131262333904325 3146990009649611687607061)
              ·
                refine ⟨147515156702325547856581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3146990009649611687607061 147515156702325547856581)
                ·
                  rfl

theorem cell20_969586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_969586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969586 prefixEnd_969586 := by exact prefixLift 969586
  have htrace : WordTrace (prefixWord ++ tailWord_969586) baseStart_969586 baseEnd_969586 := by
    simpa [prefixWord, tailWord_969586, baseEnd_969586] using wordTrace_append hprefix tailTrace_969586
  have hstable : (prefixWord ++ tailWord_969586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969586).length < 2 ^ (prefixWord ++ tailWord_969586).sum := by decide
  have hdescent : baseEnd_969586 < baseStart_969586 := by decide
  rcases family_descends (prefixWord ++ tailWord_969586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969600 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_969600 : Nat := 118140960795 + 969600 * 2 ^ 59
def prefixEnd_969600 : Nat := 4983230072969 + 3 ^ 40 * 969600 * 2
def baseEnd_969600 : Nat := 442551860088454817103019

theorem tailTrace_969600 : CollatzResearch.WordTrace tailWord_969600 prefixEnd_969600 442551860088454817103019 := by
  unfold tailWord_969600
  simp only [CollatzResearch.WordTrace]
  refine ⟨17682108643656134670729127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23576144858208179560972169 17682108643656134670729127)
  ·
    refine ⟨26523162965484202006093691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17682108643656134670729127 26523162965484202006093691)
    ·
      refine ⟨39784744448226303009140537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26523162965484202006093691 39784744448226303009140537)
      ·
        refine ⟨29838558336169727256855403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39784744448226303009140537 29838558336169727256855403)
        ·
          refine ⟨44757837504254590885283105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29838558336169727256855403 44757837504254590885283105)
          ·
            refine ⟨33568378128190943163962329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44757837504254590885283105 33568378128190943163962329)
            ·
              refine ⟨25176283596143207372971747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33568378128190943163962329 25176283596143207372971747)
              ·
                refine ⟨37764425394214811059457621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25176283596143207372971747 37764425394214811059457621)
                ·
                  refine ⟨442551860088454817103019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37764425394214811059457621 442551860088454817103019)
                  ·
                    rfl

theorem cell20_969600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_969600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969600 prefixEnd_969600 := by exact prefixLift 969600
  have htrace : WordTrace (prefixWord ++ tailWord_969600) baseStart_969600 baseEnd_969600 := by
    simpa [prefixWord, tailWord_969600, baseEnd_969600] using wordTrace_append hprefix tailTrace_969600
  have hstable : (prefixWord ++ tailWord_969600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969600).length < 2 ^ (prefixWord ++ tailWord_969600).sum := by decide
  have hdescent : baseEnd_969600 < baseStart_969600 := by decide
  rcases family_descends (prefixWord ++ tailWord_969600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969634 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_969634 : Nat := 118140960795 + 969634 * 2 ^ 59
def prefixEnd_969634 : Nat := 4983230072969 + 3 ^ 40 * 969634 * 2
def baseEnd_969634 : Nat := 442567378614901809969547

theorem tailTrace_969634 : CollatzResearch.WordTrace tailWord_969634 prefixEnd_969634 442567378614901809969547 := by
  unfold tailWord_969634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841364342297273287048989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23576971579459395432130637 8841364342297273287048989)
  ·
    refine ⟨3315511628361477482643371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8841364342297273287048989 3315511628361477482643371)
    ·
      refine ⟨4973267442542216223965057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315511628361477482643371 4973267442542216223965057)
      ·
        refine ⟨3729950581906662167973793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4973267442542216223965057 3729950581906662167973793)
        ·
          refine ⟨2797462936429996625980345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3729950581906662167973793 2797462936429996625980345)
          ·
            refine ⟨2098097202322497469485259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797462936429996625980345 2098097202322497469485259)
            ·
              refine ⟨3147145803483746204227889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098097202322497469485259 3147145803483746204227889)
              ·
                refine ⟨2360359352612809653170917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147145803483746204227889 2360359352612809653170917)
                ·
                  refine ⟨442567378614901809969547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360359352612809653170917 442567378614901809969547)
                  ·
                    rfl

theorem cell20_969634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_969634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969634 prefixEnd_969634 := by exact prefixLift 969634
  have htrace : WordTrace (prefixWord ++ tailWord_969634) baseStart_969634 baseEnd_969634 := by
    simpa [prefixWord, tailWord_969634, baseEnd_969634] using wordTrace_append hprefix tailTrace_969634
  have hstable : (prefixWord ++ tailWord_969634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969634).length < 2 ^ (prefixWord ++ tailWord_969634).sum := by decide
  have hdescent : baseEnd_969634 < baseStart_969634 := by decide
  rcases family_descends (prefixWord ++ tailWord_969634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969662 : List Nat := [4, 2, 1, 1, 1, 2, 9]
def baseStart_969662 : Nat := 118140960795 + 969662 * 2 ^ 59
def prefixEnd_969662 : Nat := 4983230072969 + 3 ^ 40 * 969662 * 2
def baseEnd_969662 : Nat := 49175573175317573004011

theorem tailTrace_969662 : CollatzResearch.WordTrace tailWord_969662 prefixEnd_969662 49175573175317573004011 := by
  unfold tailWord_969662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420809826635956741276905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23577652408725102620143493 4420809826635956741276905)
  ·
    refine ⟨3315607369976967555957679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4420809826635956741276905 3315607369976967555957679)
    ·
      refine ⟨4973411054965451333936519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315607369976967555957679 4973411054965451333936519)
      ·
        refine ⟨7460116582448177000904779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973411054965451333936519 7460116582448177000904779)
        ·
          refine ⟨11190174873672265501357169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460116582448177000904779 11190174873672265501357169)
          ·
            refine ⟨8392631155254199126017877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190174873672265501357169 8392631155254199126017877)
            ·
              refine ⟨49175573175317573004011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8392631155254199126017877 49175573175317573004011)
              ·
                rfl

theorem cell20_969662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_969662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969662 prefixEnd_969662 := by exact prefixLift 969662
  have htrace : WordTrace (prefixWord ++ tailWord_969662) baseStart_969662 baseEnd_969662 := by
    simpa [prefixWord, tailWord_969662, baseEnd_969662] using wordTrace_append hprefix tailTrace_969662
  have hstable : (prefixWord ++ tailWord_969662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969662).length < 2 ^ (prefixWord ++ tailWord_969662).sum := by decide
  have hdescent : baseEnd_969662 < baseStart_969662 := by decide
  rcases family_descends (prefixWord ++ tailWord_969662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969672 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_969672 : Nat := 118140960795 + 969672 * 2 ^ 59
def prefixEnd_969672 : Nat := 4983230072969 + 3 ^ 40 * 969672 * 2
def baseEnd_969672 : Nat := 442584722850342566702725

theorem tailTrace_969672 : CollatzResearch.WordTrace tailWord_969672 prefixEnd_969672 442584722850342566702725 := by
  unfold tailWord_969672
  simp only [CollatzResearch.WordTrace]
  refine ⟨17683421671525712819039635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23577895562034283758719513 17683421671525712819039635)
  ·
    refine ⟨26525132507288569228559453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17683421671525712819039635 26525132507288569228559453)
    ·
      refine ⟨9946924690233213460709795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26525132507288569228559453 9946924690233213460709795)
      ·
        refine ⟨14920387035349820191064693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9946924690233213460709795 14920387035349820191064693)
        ·
          refine ⟨1398786284564045642912315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14920387035349820191064693 1398786284564045642912315)
          ·
            refine ⟨2098179426846068464368473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398786284564045642912315 2098179426846068464368473)
            ·
              refine ⟨1573634570134551348276355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098179426846068464368473 1573634570134551348276355)
              ·
                refine ⟨2360451855201827022414533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573634570134551348276355 2360451855201827022414533)
                ·
                  refine ⟨442584722850342566702725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2360451855201827022414533 442584722850342566702725)
                  ·
                    rfl

theorem cell20_969672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_969672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969672 prefixEnd_969672 := by exact prefixLift 969672
  have htrace : WordTrace (prefixWord ++ tailWord_969672) baseStart_969672 baseEnd_969672 := by
    simpa [prefixWord, tailWord_969672, baseEnd_969672] using wordTrace_append hprefix tailTrace_969672
  have hstable : (prefixWord ++ tailWord_969672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969672).length < 2 ^ (prefixWord ++ tailWord_969672).sum := by decide
  have hdescent : baseEnd_969672 < baseStart_969672 := by decide
  rcases family_descends (prefixWord ++ tailWord_969672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969682 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_969682 : Nat := 118140960795 + 969682 * 2 ^ 59
def prefixEnd_969682 : Nat := 4983230072969 + 3 ^ 40 * 969682 * 2
def baseEnd_969682 : Nat := 442589287122826976369351

theorem tailTrace_969682 : CollatzResearch.WordTrace tailWord_969682 prefixEnd_969682 442589287122826976369351 := by
  unfold tailWord_969682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841802018253799336485825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23578138715343464897295533 8841802018253799336485825)
  ·
    refine ⟨6631351513690349502364369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8841802018253799336485825 6631351513690349502364369)
    ·
      refine ⟨4973513635267762126773277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6631351513690349502364369 4973513635267762126773277)
      ·
        refine ⟨1865067613225410797539979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4973513635267762126773277 1865067613225410797539979)
        ·
          refine ⟨2797601419838116196309969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865067613225410797539979 2797601419838116196309969)
          ·
            refine ⟨2098201064878587147232477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797601419838116196309969 2098201064878587147232477)
            ·
              refine ⟨786825399329470180212179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2098201064878587147232477 786825399329470180212179)
              ·
                refine ⟨1180238098994205270318269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786825399329470180212179 1180238098994205270318269)
                ·
                  refine ⟨442589287122826976369351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180238098994205270318269 442589287122826976369351)
                  ·
                    rfl

theorem cell20_969682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_969682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969682 prefixEnd_969682 := by exact prefixLift 969682
  have htrace : WordTrace (prefixWord ++ tailWord_969682) baseStart_969682 baseEnd_969682 := by
    simpa [prefixWord, tailWord_969682, baseEnd_969682] using wordTrace_append hprefix tailTrace_969682
  have hstable : (prefixWord ++ tailWord_969682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969682).length < 2 ^ (prefixWord ++ tailWord_969682).sum := by decide
  have hdescent : baseEnd_969682 < baseStart_969682 := by decide
  rcases family_descends (prefixWord ++ tailWord_969682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969738 : List Nat := [3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_969738 : Nat := 118140960795 + 969738 * 2 ^ 59
def prefixEnd_969738 : Nat := 4983230072969 + 3 ^ 40 * 969738 * 2
def baseEnd_969738 : Nat := 147538282349579890167485

theorem tailTrace_969738 : CollatzResearch.WordTrace tailWord_969738 prefixEnd_969738 147538282349579890167485 := by
  unfold tailWord_969738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842312640203079727495467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23579500373874879273321245 8842312640203079727495467)
  ·
    refine ⟨13263468960304619591243201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8842312640203079727495467 13263468960304619591243201)
    ·
      refine ⟨9947601720228464693432401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13263468960304619591243201 9947601720228464693432401)
      ·
        refine ⟨7460701290171348520074301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9947601720228464693432401 7460701290171348520074301)
        ·
          refine ⟨2797762983814255695027863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7460701290171348520074301 2797762983814255695027863)
          ·
            refine ⟨4196644475721383542541795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797762983814255695027863 4196644475721383542541795)
            ·
              refine ⟨6294966713582075313812693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196644475721383542541795 6294966713582075313812693)
              ·
                refine ⟨147538282349579890167485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6294966713582075313812693 147538282349579890167485)
                ·
                  rfl

theorem cell20_969738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_969738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969738 prefixEnd_969738 := by exact prefixLift 969738
  have htrace : WordTrace (prefixWord ++ tailWord_969738) baseStart_969738 baseEnd_969738 := by
    simpa [prefixWord, tailWord_969738, baseEnd_969738] using wordTrace_append hprefix tailTrace_969738
  have hstable : (prefixWord ++ tailWord_969738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969738).length < 2 ^ (prefixWord ++ tailWord_969738).sum := by decide
  have hdescent : baseEnd_969738 < baseStart_969738 := by decide
  rcases family_descends (prefixWord ++ tailWord_969738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969782 : List Nat := [5, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_969782 : Nat := 118140960795 + 969782 * 2 ^ 59
def prefixEnd_969782 : Nat := 4983230072969 + 3 ^ 40 * 969782 * 2
def baseEnd_969782 : Nat := 442634929847671073035609

theorem tailTrace_969782 : CollatzResearch.WordTrace tailWord_969782 prefixEnd_969782 442634929847671073035609 := by
  unfold tailWord_969782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210678460790807151536475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23580570248435276283055733 2210678460790807151536475)
  ·
    refine ⟨3316017691186210727304713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210678460790807151536475 3316017691186210727304713)
    ·
      refine ⟨2487013268389658045478535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3316017691186210727304713 2487013268389658045478535)
      ·
        refine ⟨3730519902584487068217803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487013268389658045478535 3730519902584487068217803)
        ·
          refine ⟨5595779853876730602326705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730519902584487068217803 5595779853876730602326705)
          ·
            refine ⟨4196834890407547951745029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5595779853876730602326705 4196834890407547951745029)
            ·
              refine ⟨786906541951415240952193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4196834890407547951745029 786906541951415240952193)
              ·
                refine ⟨590179906463561430714145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786906541951415240952193 590179906463561430714145)
                ·
                  refine ⟨442634929847671073035609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590179906463561430714145 442634929847671073035609)
                  ·
                    rfl

theorem cell20_969782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_969782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969782 prefixEnd_969782 := by exact prefixLift 969782
  have htrace : WordTrace (prefixWord ++ tailWord_969782) baseStart_969782 baseEnd_969782 := by
    simpa [prefixWord, tailWord_969782, baseEnd_969782] using wordTrace_append hprefix tailTrace_969782
  have hstable : (prefixWord ++ tailWord_969782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969782).length < 2 ^ (prefixWord ++ tailWord_969782).sum := by decide
  have hdescent : baseEnd_969782 < baseStart_969782 := by decide
  rcases family_descends (prefixWord ++ tailWord_969782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969824 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 2]
def baseStart_969824 : Nat := 118140960795 + 969824 * 2 ^ 59
def prefixEnd_969824 : Nat := 4983230072969 + 3 ^ 40 * 969824 * 2
def baseEnd_969824 : Nat := 442654099792105593635437

theorem tailTrace_969824 : CollatzResearch.WordTrace tailWord_969824 prefixEnd_969824 442654099792105593635437 := by
  unfold tailWord_969824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686193619250377798806263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23581591492333837065075017 17686193619250377798806263)
  ·
    refine ⟨26529290428875566698209395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17686193619250377798806263 26529290428875566698209395)
    ·
      refine ⟨39793935643313350047314093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26529290428875566698209395 39793935643313350047314093)
      ·
        refine ⟨14922725866242506267742785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39793935643313350047314093 14922725866242506267742785)
        ·
          refine ⟨11192044399681879700807089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14922725866242506267742785 11192044399681879700807089)
          ·
            refine ⟨8394033299761409775605317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11192044399681879700807089 8394033299761409775605317)
            ·
              refine ⟨1573881243705264332925997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8394033299761409775605317 1573881243705264332925997)
              ·
                refine ⟨590205466389474124847249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573881243705264332925997 590205466389474124847249)
                ·
                  refine ⟨442654099792105593635437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590205466389474124847249 442654099792105593635437)
                  ·
                    rfl

theorem cell20_969824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_969824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969824 prefixEnd_969824 := by exact prefixLift 969824
  have htrace : WordTrace (prefixWord ++ tailWord_969824) baseStart_969824 baseEnd_969824 := by
    simpa [prefixWord, tailWord_969824, baseEnd_969824] using wordTrace_append hprefix tailTrace_969824
  have hstable : (prefixWord ++ tailWord_969824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969824).length < 2 ^ (prefixWord ++ tailWord_969824).sum := by decide
  have hdescent : baseEnd_969824 < baseStart_969824 := by decide
  rcases family_descends (prefixWord ++ tailWord_969824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969828 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_969828 : Nat := 118140960795 + 969828 * 2 ^ 59
def prefixEnd_969828 : Nat := 4983230072969 + 3 ^ 40 * 969828 * 2
def baseEnd_969828 : Nat := 442655925501099357502087

theorem tailTrace_969828 : CollatzResearch.WordTrace tailWord_969828 prefixEnd_969828 442655925501099357502087 := by
  unfold tailWord_969828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686266565243132140379069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23581688753657509520505425 17686266565243132140379069)
  ·
    refine ⟨6632349961966174552642151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17686266565243132140379069 6632349961966174552642151)
    ·
      refine ⟨9948524942949261828963227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6632349961966174552642151 9948524942949261828963227)
      ·
        refine ⟨14922787414423892743444841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9948524942949261828963227 14922787414423892743444841)
        ·
          refine ⟨11192090560817919557583631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14922787414423892743444841 11192090560817919557583631)
          ·
            refine ⟨16788135841226879336375447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11192090560817919557583631 16788135841226879336375447)
            ·
              refine ⟨25182203761840319004563171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16788135841226879336375447 25182203761840319004563171)
              ·
                refine ⟨37773305642760478506844757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25182203761840319004563171 37773305642760478506844757)
                ·
                  refine ⟨442655925501099357502087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37773305642760478506844757 442655925501099357502087)
                  ·
                    rfl

theorem cell20_969828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_969828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969828 prefixEnd_969828 := by exact prefixLift 969828
  have htrace : WordTrace (prefixWord ++ tailWord_969828) baseStart_969828 baseEnd_969828 := by
    simpa [prefixWord, tailWord_969828, baseEnd_969828] using wordTrace_append hprefix tailTrace_969828
  have hstable : (prefixWord ++ tailWord_969828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969828).length < 2 ^ (prefixWord ++ tailWord_969828).sum := by decide
  have hdescent : baseEnd_969828 < baseStart_969828 := by decide
  rcases family_descends (prefixWord ++ tailWord_969828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969838 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_969838 : Nat := 118140960795 + 969838 * 2 ^ 59
def prefixEnd_969838 : Nat := 4983230072969 + 3 ^ 40 * 969838 * 2
def baseEnd_969838 : Nat := 442660489773583767168713

theorem tailTrace_969838 : CollatzResearch.WordTrace tailWord_969838 prefixEnd_969838 442660489773583767168713 := by
  unfold tailWord_969838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421612232556254498577771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23581931906966690659081445 4421612232556254498577771)
  ·
    refine ⟨6632418348834381747866657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4421612232556254498577771 6632418348834381747866657)
    ·
      refine ⟨4974313761625786310899993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6632418348834381747866657 4974313761625786310899993)
      ·
        refine ⟨3730735321219339733174995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4974313761625786310899993 3730735321219339733174995)
        ·
          refine ⟨5596102981829009599762493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730735321219339733174995 5596102981829009599762493)
          ·
            refine ⟨2098538618185878599910935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5596102981829009599762493 2098538618185878599910935)
            ·
              refine ⟨3147807927278817899866403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098538618185878599910935 3147807927278817899866403)
              ·
                refine ⟨4721711890918226849799605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147807927278817899866403 4721711890918226849799605)
                ·
                  refine ⟨442660489773583767168713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4721711890918226849799605 442660489773583767168713)
                  ·
                    rfl

theorem cell20_969838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_969838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969838 prefixEnd_969838 := by exact prefixLift 969838
  have htrace : WordTrace (prefixWord ++ tailWord_969838) baseStart_969838 baseEnd_969838 := by
    simpa [prefixWord, tailWord_969838, baseEnd_969838] using wordTrace_append hprefix tailTrace_969838
  have hstable : (prefixWord ++ tailWord_969838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969838).length < 2 ^ (prefixWord ++ tailWord_969838).sum := by decide
  have hdescent : baseEnd_969838 < baseStart_969838 := by decide
  rcases family_descends (prefixWord ++ tailWord_969838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969879 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 2]
def baseStart_969879 : Nat := 118140960795 + 969879 * 2 ^ 59
def prefixEnd_969879 : Nat := 4983230072969 + 3 ^ 40 * 969879 * 2
def baseEnd_969879 : Nat := 442679203290769846801879

theorem tailTrace_969879 : CollatzResearch.WordTrace tailWord_969879 prefixEnd_969879 442679203290769846801879 := by
  unfold tailWord_969879
  simp only [CollatzResearch.WordTrace]
  refine ⟨35374393253301499990864691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23582928835534333327243127 35374393253301499990864691)
  ·
    refine ⟨53061589879952249986297037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35374393253301499990864691 53061589879952249986297037)
    ·
      refine ⟨19898096204982093744861389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53061589879952249986297037 19898096204982093744861389)
      ·
        refine ⟨7461786076868285154323021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19898096204982093744861389 7461786076868285154323021)
        ·
          refine ⟨2798169778825606932871133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7461786076868285154323021 2798169778825606932871133)
          ·
            refine ⟨1049313667059602599826675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2798169778825606932871133 1049313667059602599826675)
            ·
              refine ⟨1573970500589403899740013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049313667059602599826675 1573970500589403899740013)
              ·
                refine ⟨590238937721026462402505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573970500589403899740013 590238937721026462402505)
                ·
                  refine ⟨442679203290769846801879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590238937721026462402505 442679203290769846801879)
                  ·
                    rfl

theorem cell20_969879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 2].length) (baseStart_969879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969879 prefixEnd_969879 := by exact prefixLift 969879
  have htrace : WordTrace (prefixWord ++ tailWord_969879) baseStart_969879 baseEnd_969879 := by
    simpa [prefixWord, tailWord_969879, baseEnd_969879] using wordTrace_append hprefix tailTrace_969879
  have hstable : (prefixWord ++ tailWord_969879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969879).length < 2 ^ (prefixWord ++ tailWord_969879).sum := by decide
  have hdescent : baseEnd_969879 < baseStart_969879 := by decide
  rcases family_descends (prefixWord ++ tailWord_969879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969938 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_969938 : Nat := 118140960795 + 969938 * 2 ^ 59
def prefixEnd_969938 : Nat := 4983230072969 + 3 ^ 40 * 969938 * 2
def baseEnd_969938 : Nat := 442706132498427863834971

theorem tailTrace_969938 : CollatzResearch.WordTrace tailWord_969938 prefixEnd_969938 442706132498427863834971 := by
  unfold tailWord_969938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844136290021938266815617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23584363440058502044841645 8844136290021938266815617)
  ·
    refine ⟨6633102217516453700111713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8844136290021938266815617 6633102217516453700111713)
    ·
      refine ⟨4974826663137340275083785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6633102217516453700111713 4974826663137340275083785)
      ·
        refine ⟨3731119997353005206312839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4974826663137340275083785 3731119997353005206312839)
        ·
          refine ⟨5596679996029507809469259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731119997353005206312839 5596679996029507809469259)
          ·
            refine ⟨8395019994044261714203889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596679996029507809469259 8395019994044261714203889)
            ·
              refine ⟨6296264995533196285652917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8395019994044261714203889 6296264995533196285652917)
              ·
                refine ⟨590274843331237151779961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6296264995533196285652917 590274843331237151779961)
                ·
                  refine ⟨442706132498427863834971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590274843331237151779961 442706132498427863834971)
                  ·
                    rfl

theorem cell20_969938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_969938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969938 prefixEnd_969938 := by exact prefixLift 969938
  have htrace : WordTrace (prefixWord ++ tailWord_969938) baseStart_969938 baseEnd_969938 := by
    simpa [prefixWord, tailWord_969938, baseEnd_969938] using wordTrace_append hprefix tailTrace_969938
  have hstable : (prefixWord ++ tailWord_969938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969938).length < 2 ^ (prefixWord ++ tailWord_969938).sum := by decide
  have hdescent : baseEnd_969938 < baseStart_969938 := by decide
  rcases family_descends (prefixWord ++ tailWord_969938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969952 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_969952 : Nat := 118140960795 + 969952 * 2 ^ 59
def prefixEnd_969952 : Nat := 4983230072969 + 3 ^ 40 * 969952 * 2
def baseEnd_969952 : Nat := 442712522479906037368247

theorem tailTrace_969952 : CollatzResearch.WordTrace tailWord_969952 prefixEnd_969952 442712522479906037368247 := by
  unfold tailWord_969952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17688527891018516729136055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23584703854691355638848073 17688527891018516729136055)
  ·
    refine ⟨26532791836527775093704083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17688527891018516729136055 26532791836527775093704083)
    ·
      refine ⟨39799187754791662640556125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26532791836527775093704083 39799187754791662640556125)
      ·
        refine ⟨14924695408046873490208547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39799187754791662640556125 14924695408046873490208547)
        ·
          refine ⟨22387043112070310235312821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14924695408046873490208547 22387043112070310235312821)
          ·
            refine ⟨2098785291756591584560577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22387043112070310235312821 2098785291756591584560577)
            ·
              refine ⟨1574088968817443688420433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098785291756591584560577 1574088968817443688420433)
              ·
                refine ⟨1180566726613082766315325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574088968817443688420433 1180566726613082766315325)
                ·
                  refine ⟨442712522479906037368247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180566726613082766315325 442712522479906037368247)
                  ·
                    rfl

theorem cell20_969952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_969952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969952 prefixEnd_969952 := by exact prefixLift 969952
  have htrace : WordTrace (prefixWord ++ tailWord_969952) baseStart_969952 baseEnd_969952 := by
    simpa [prefixWord, tailWord_969952, baseEnd_969952] using wordTrace_append hprefix tailTrace_969952
  have hstable : (prefixWord ++ tailWord_969952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969952).length < 2 ^ (prefixWord ++ tailWord_969952).sum := by decide
  have hdescent : baseEnd_969952 < baseStart_969952 := by decide
  rcases family_descends (prefixWord ++ tailWord_969952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969966 : List Nat := [4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_969966 : Nat := 118140960795 + 969966 * 2 ^ 59
def prefixEnd_969966 : Nat := 4983230072969 + 3 ^ 40 * 969966 * 2
def baseEnd_969966 : Nat := 147572970820461403633841

theorem tailTrace_969966 : CollatzResearch.WordTrace tailWord_969966 prefixEnd_969966 147572970820461403633841 := by
  unfold tailWord_969966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422195800498289231160219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23585044269324209232854501 4422195800498289231160219)
  ·
    refine ⟨6633293700747433846740329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422195800498289231160219 6633293700747433846740329)
    ·
      refine ⟨4974970275560575385055247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6633293700747433846740329 4974970275560575385055247)
      ·
        refine ⟨7462455413340863077582871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974970275560575385055247 7462455413340863077582871)
        ·
          refine ⟨11193683120011294616374307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7462455413340863077582871 11193683120011294616374307)
          ·
            refine ⟨16790524680016941924561461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11193683120011294616374307 16790524680016941924561461)
            ·
              refine ⟨1574111688751588305427637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16790524680016941924561461 1574111688751588305427637)
              ·
                refine ⟨147572970820461403633841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574111688751588305427637 147572970820461403633841)
                ·
                  rfl

theorem cell20_969966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_969966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969966 prefixEnd_969966 := by exact prefixLift 969966
  have htrace : WordTrace (prefixWord ++ tailWord_969966) baseStart_969966 baseEnd_969966 := by
    simpa [prefixWord, tailWord_969966, baseEnd_969966] using wordTrace_append hprefix tailTrace_969966
  have hstable : (prefixWord ++ tailWord_969966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969966).length < 2 ^ (prefixWord ++ tailWord_969966).sum := by decide
  have hdescent : baseEnd_969966 < baseStart_969966 := by decide
  rcases family_descends (prefixWord ++ tailWord_969966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969972 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_969972 : Nat := 118140960795 + 969972 * 2 ^ 59
def prefixEnd_969972 : Nat := 4983230072969 + 3 ^ 40 * 969972 * 2
def baseEnd_969972 : Nat := 442721651024874856701499

theorem tailTrace_969972 : CollatzResearch.WordTrace tailWord_969972 prefixEnd_969972 442721651024874856701499 := by
  unfold tailWord_969972
  simp only [CollatzResearch.WordTrace]
  refine ⟨17688892620982288437000085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23585190161309717916000113 17688892620982288437000085)
  ·
    refine ⟨829166841608544770484379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17688892620982288437000085 829166841608544770484379)
    ·
      refine ⟨1243750262412817155726569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829166841608544770484379 1243750262412817155726569)
      ·
        refine ⟨932812696809612866794927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1243750262412817155726569 932812696809612866794927)
        ·
          refine ⟨1399219045214419300192391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932812696809612866794927 1399219045214419300192391)
          ·
            refine ⟨2098828567821628950288587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399219045214419300192391 2098828567821628950288587)
            ·
              refine ⟨3148242851732443425432881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098828567821628950288587 3148242851732443425432881)
              ·
                refine ⟨2361182138799332569074661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148242851732443425432881 2361182138799332569074661)
                ·
                  refine ⟨442721651024874856701499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361182138799332569074661 442721651024874856701499)
                  ·
                    rfl

theorem cell20_969972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_969972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_969972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_969972 prefixEnd_969972 := by exact prefixLift 969972
  have htrace : WordTrace (prefixWord ++ tailWord_969972) baseStart_969972 baseEnd_969972 := by
    simpa [prefixWord, tailWord_969972, baseEnd_969972] using wordTrace_append hprefix tailTrace_969972
  have hstable : (prefixWord ++ tailWord_969972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969972).length < 2 ^ (prefixWord ++ tailWord_969972).sum := by decide
  have hdescent : baseEnd_969972 < baseStart_969972 := by decide
  rcases family_descends (prefixWord ++ tailWord_969972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970038 : List Nat := [5, 1, 2, 3, 1, 1, 1, 6]
def baseStart_970038 : Nat := 118140960795 + 970038 * 2 ^ 59
def prefixEnd_970038 : Nat := 4983230072969 + 3 ^ 40 * 970038 * 2
def baseEnd_970038 : Nat := 147583925074423986833743

theorem tailTrace_970038 : CollatzResearch.WordTrace tailWord_970038 prefixEnd_970038 147583925074423986833743 := by
  unfold tailWord_970038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211262028732841884118923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23586794973150313430601845 2211262028732841884118923)
  ·
    refine ⟨3316893043099262826178385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2211262028732841884118923 3316893043099262826178385)
    ·
      refine ⟨2487669782324447119633789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3316893043099262826178385 2487669782324447119633789)
      ·
        refine ⟨932876168371667669862671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2487669782324447119633789 932876168371667669862671)
        ·
          refine ⟨1399314252557501504794007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932876168371667669862671 1399314252557501504794007)
          ·
            refine ⟨2098971378836252257191011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399314252557501504794007 2098971378836252257191011)
            ·
              refine ⟨3148457068254378385786517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098971378836252257191011 3148457068254378385786517)
              ·
                refine ⟨147583925074423986833743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3148457068254378385786517 147583925074423986833743)
                ·
                  rfl

theorem cell20_970038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_970038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970038 prefixEnd_970038 := by exact prefixLift 970038
  have htrace : WordTrace (prefixWord ++ tailWord_970038) baseStart_970038 baseEnd_970038 := by
    simpa [prefixWord, tailWord_970038, baseEnd_970038] using wordTrace_append hprefix tailTrace_970038
  have hstable : (prefixWord ++ tailWord_970038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970038).length < 2 ^ (prefixWord ++ tailWord_970038).sum := by decide
  have hdescent : baseEnd_970038 < baseStart_970038 := by decide
  rcases family_descends (prefixWord ++ tailWord_970038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970069 : List Nat := [1, 3, 2, 2, 3, 2, 3, 2, 2]
def baseStart_970069 : Nat := 118140960795 + 970069 * 2 ^ 59
def prefixEnd_970069 : Nat := 4983230072969 + 3 ^ 40 * 970069 * 2
def baseEnd_970069 : Nat := 442765924467973630467769

theorem tailTrace_970069 : CollatzResearch.WordTrace tailWord_970069 prefixEnd_970069 442765924467973630467769 := by
  unfold tailWord_970069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35381323122613162440281261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23587548748408774960187507 35381323122613162440281261)
  ·
    refine ⟨13267996170979935915105473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35381323122613162440281261 13267996170979935915105473)
    ·
      refine ⟨9950997128234951936329105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13267996170979935915105473 9950997128234951936329105)
      ·
        refine ⟨7463247846176213952246829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9950997128234951936329105 7463247846176213952246829)
        ·
          refine ⟨2798717942316080232092561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7463247846176213952246829 2798717942316080232092561)
          ·
            refine ⟨2099038456737060174069421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798717942316080232092561 2099038456737060174069421)
            ·
              refine ⟨787139421276397565276033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2099038456737060174069421 787139421276397565276033)
              ·
                refine ⟨590354565957298173957025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787139421276397565276033 590354565957298173957025)
                ·
                  refine ⟨442765924467973630467769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590354565957298173957025 442765924467973630467769)
                  ·
                    rfl

theorem cell20_970069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_970069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970069 prefixEnd_970069 := by exact prefixLift 970069
  have htrace : WordTrace (prefixWord ++ tailWord_970069) baseStart_970069 baseEnd_970069 := by
    simpa [prefixWord, tailWord_970069, baseEnd_970069] using wordTrace_append hprefix tailTrace_970069
  have hstable : (prefixWord ++ tailWord_970069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970069).length < 2 ^ (prefixWord ++ tailWord_970069).sum := by decide
  have hdescent : baseEnd_970069 < baseStart_970069 := by decide
  rcases family_descends (prefixWord ++ tailWord_970069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970073 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 2]
def baseStart_970073 : Nat := 118140960795 + 970073 * 2 ^ 59
def prefixEnd_970073 : Nat := 4983230072969 + 3 ^ 40 * 970073 * 2
def baseEnd_970073 : Nat := 442767750176967394334419

theorem tailTrace_970073 : CollatzResearch.WordTrace tailWord_970073 prefixEnd_970073 442767750176967394334419 := by
  unfold tailWord_970073
  simp only [CollatzResearch.WordTrace]
  refine ⟨35381469014598671123426873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23587646009732447415617915 35381469014598671123426873)
  ·
    refine ⟨26536101760949003342570155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35381469014598671123426873 26536101760949003342570155)
    ·
      refine ⟨39804152641423505013855233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26536101760949003342570155 39804152641423505013855233)
      ·
        refine ⟨29853114481067628760391425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39804152641423505013855233 29853114481067628760391425)
        ·
          refine ⟨22389835860800721570293569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29853114481067628760391425 22389835860800721570293569)
          ·
            refine ⟨16792376895600541177720177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22389835860800721570293569 16792376895600541177720177)
            ·
              refine ⟨12594282671700405883290133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16792376895600541177720177 12594282671700405883290133)
              ·
                refine ⟨590357000235956525779225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12594282671700405883290133 590357000235956525779225)
                ·
                  refine ⟨442767750176967394334419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590357000235956525779225 442767750176967394334419)
                  ·
                    rfl

theorem cell20_970073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_970073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970073 prefixEnd_970073 := by exact prefixLift 970073
  have htrace : WordTrace (prefixWord ++ tailWord_970073) baseStart_970073 baseEnd_970073 := by
    simpa [prefixWord, tailWord_970073, baseEnd_970073] using wordTrace_append hprefix tailTrace_970073
  have hstable : (prefixWord ++ tailWord_970073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970073).length < 2 ^ (prefixWord ++ tailWord_970073).sum := by decide
  have hdescent : baseEnd_970073 < baseStart_970073 := by decide
  rcases family_descends (prefixWord ++ tailWord_970073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970080 : List Nat := [2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_970080 : Nat := 118140960795 + 970080 * 2 ^ 59
def prefixEnd_970080 : Nat := 4983230072969 + 3 ^ 40 * 970080 * 2
def baseEnd_970080 : Nat := 147590315055902160367019

theorem tailTrace_970080 : CollatzResearch.WordTrace tailWord_970080 prefixEnd_970080 147590315055902160367019 := by
  unfold tailWord_970080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17690862162786655659465847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23587816217048874212621129 17690862162786655659465847)
  ·
    refine ⟨26536293244179983489198771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17690862162786655659465847 26536293244179983489198771)
    ·
      refine ⟨39804439866269975233798157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26536293244179983489198771 39804439866269975233798157)
      ·
        refine ⟨14926664949851240712674309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39804439866269975233798157 14926664949851240712674309)
        ·
          refine ⟨2798749678097107633626433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14926664949851240712674309 2798749678097107633626433)
          ·
            refine ⟨2099062258572830725219825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798749678097107633626433 2099062258572830725219825)
            ·
              refine ⟨1574296693929623043914869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2099062258572830725219825 1574296693929623043914869)
              ·
                refine ⟨147590315055902160367019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574296693929623043914869 147590315055902160367019)
                ·
                  rfl

theorem cell20_970080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_970080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970080 prefixEnd_970080 := by exact prefixLift 970080
  have htrace : WordTrace (prefixWord ++ tailWord_970080) baseStart_970080 baseEnd_970080 := by
    simpa [prefixWord, tailWord_970080, baseEnd_970080] using wordTrace_append hprefix tailTrace_970080
  have hstable : (prefixWord ++ tailWord_970080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970080).length < 2 ^ (prefixWord ++ tailWord_970080).sum := by decide
  have hdescent : baseEnd_970080 < baseStart_970080 := by decide
  rcases family_descends (prefixWord ++ tailWord_970080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970083 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 3]
def baseStart_970083 : Nat := 118140960795 + 970083 * 2 ^ 59
def prefixEnd_970083 : Nat := 4983230072969 + 3 ^ 40 * 970083 * 2
def baseEnd_970083 : Nat := 442772314449451804001045

theorem tailTrace_970083 : CollatzResearch.WordTrace tailWord_970083 prefixEnd_970083 442772314449451804001045 := by
  unfold tailWord_970083
  simp only [CollatzResearch.WordTrace]
  refine ⟨35381833744562442831290903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23587889163041628554193935 35381833744562442831290903)
  ·
    refine ⟨53072750616843664246936355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35381833744562442831290903 53072750616843664246936355)
    ·
      refine ⟨79609125925265496370404533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53072750616843664246936355 79609125925265496370404533)
      ·
        refine ⟨7463355555493640284725425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79609125925265496370404533 7463355555493640284725425)
        ·
          refine ⟨5597516666620230213544069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7463355555493640284725425 5597516666620230213544069)
          ·
            refine ⟨1049534374991293165039513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5597516666620230213544069 1049534374991293165039513)
            ·
              refine ⟨787150781243469873779635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049534374991293165039513 787150781243469873779635)
              ·
                refine ⟨1180726171865204810669453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787150781243469873779635 1180726171865204810669453)
                ·
                  refine ⟨442772314449451804001045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180726171865204810669453 442772314449451804001045)
                  ·
                    rfl

theorem cell20_970083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_970083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970083 prefixEnd_970083 := by exact prefixLift 970083
  have htrace : WordTrace (prefixWord ++ tailWord_970083) baseStart_970083 baseEnd_970083 := by
    simpa [prefixWord, tailWord_970083, baseEnd_970083] using wordTrace_append hprefix tailTrace_970083
  have hstable : (prefixWord ++ tailWord_970083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970083).length < 2 ^ (prefixWord ++ tailWord_970083).sum := by decide
  have hdescent : baseEnd_970083 < baseStart_970083 := by decide
  rcases family_descends (prefixWord ++ tailWord_970083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970152 : List Nat := [2, 1, 6, 1, 2, 1, 3, 4]
def baseStart_970152 : Nat := 118140960795 + 970152 * 2 ^ 59
def prefixEnd_970152 : Nat := 4983230072969 + 3 ^ 40 * 970152 * 2
def baseEnd_970152 : Nat := 147601269309864743566921

theorem tailTrace_970152 : CollatzResearch.WordTrace tailWord_970152 prefixEnd_970152 147601269309864743566921 := by
  unfold tailWord_970152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692175190656233807776355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23589566920874978410368473 17692175190656233807776355)
  ·
    refine ⟨26538262785984350711664533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692175190656233807776355 26538262785984350711664533)
    ·
      refine ⟨1243981068093016439609275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26538262785984350711664533 1243981068093016439609275)
      ·
        refine ⟨1865971602139524659413913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243981068093016439609275 1865971602139524659413913)
        ·
          refine ⟨1399478701604643494560435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865971602139524659413913 1399478701604643494560435)
          ·
            refine ⟨2099218052406965241840653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399478701604643494560435 2099218052406965241840653)
            ·
              refine ⟨787206769652611965690245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2099218052406965241840653 787206769652611965690245)
              ·
                refine ⟨147601269309864743566921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 787206769652611965690245 147601269309864743566921)
                ·
                  rfl

theorem cell20_970152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_970152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970152 prefixEnd_970152 := by exact prefixLift 970152
  have htrace : WordTrace (prefixWord ++ tailWord_970152) baseStart_970152 baseEnd_970152 := by
    simpa [prefixWord, tailWord_970152, baseEnd_970152] using wordTrace_append hprefix tailTrace_970152
  have hstable : (prefixWord ++ tailWord_970152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970152).length < 2 ^ (prefixWord ++ tailWord_970152).sum := by decide
  have hdescent : baseEnd_970152 < baseStart_970152 := by decide
  rcases family_descends (prefixWord ++ tailWord_970152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970180 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_970180 : Nat := 118140960795 + 970180 * 2 ^ 59
def prefixEnd_970180 : Nat := 4983230072969 + 3 ^ 40 * 970180 * 2
def baseEnd_970180 : Nat := 442816587892550577767315

theorem tailTrace_970180 : CollatzResearch.WordTrace tailWord_970180 prefixEnd_970180 442816587892550577767315 := by
  unfold tailWord_970180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692685812605514198785997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23590247750140685598381329 17692685812605514198785997)
  ·
    refine ⟨6634757179727067824544749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17692685812605514198785997 6634757179727067824544749)
    ·
      refine ⟨2488033942397650434204281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6634757179727067824544749 2488033942397650434204281)
      ·
        refine ⟨1866025456798237825653211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488033942397650434204281 1866025456798237825653211)
        ·
          refine ⟨2799038185197356738479817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866025456798237825653211 2799038185197356738479817)
          ·
            refine ⟨2099278638898017553859863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2799038185197356738479817 2099278638898017553859863)
            ·
              refine ⟨3148917958347026330789795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099278638898017553859863 3148917958347026330789795)
              ·
                refine ⟨4723376937520539496184693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148917958347026330789795 4723376937520539496184693)
                ·
                  refine ⟨442816587892550577767315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4723376937520539496184693 442816587892550577767315)
                  ·
                    rfl

theorem cell20_970180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_970180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970180 prefixEnd_970180 := by exact prefixLift 970180
  have htrace : WordTrace (prefixWord ++ tailWord_970180) baseStart_970180 baseEnd_970180 := by
    simpa [prefixWord, tailWord_970180, baseEnd_970180] using wordTrace_append hprefix tailTrace_970180
  have hstable : (prefixWord ++ tailWord_970180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970180).length < 2 ^ (prefixWord ++ tailWord_970180).sum := by decide
  have hdescent : baseEnd_970180 < baseStart_970180 := by decide
  rcases family_descends (prefixWord ++ tailWord_970180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970187 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 2]
def baseStart_970187 : Nat := 118140960795 + 970187 * 2 ^ 59
def prefixEnd_970187 : Nat := 4983230072969 + 3 ^ 40 * 970187 * 2
def baseEnd_970187 : Nat := 442819782883289664533953

theorem tailTrace_970187 : CollatzResearch.WordTrace tailWord_970187 prefixEnd_970187 442819782883289664533953 := by
  unfold tailWord_970187
  simp only [CollatzResearch.WordTrace]
  refine ⟨35385626936185668593076815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23590417957457112395384543 35385626936185668593076815)
  ·
    refine ⟨53078440404278502889615223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35385626936185668593076815 53078440404278502889615223)
    ·
      refine ⟨79617660606417754334422835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53078440404278502889615223 79617660606417754334422835)
      ·
        refine ⟨119426490909626631501634253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79617660606417754334422835 119426490909626631501634253)
        ·
          refine ⟨44784934091109986813112845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119426490909626631501634253 44784934091109986813112845)
          ·
            refine ⟨16794350284166245054917317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44784934091109986813112845 16794350284166245054917317)
            ·
              refine ⟨3148940678281170947796997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16794350284166245054917317 3148940678281170947796997)
              ·
                refine ⟨590426377177719552711937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3148940678281170947796997 590426377177719552711937)
                ·
                  refine ⟨442819782883289664533953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590426377177719552711937 442819782883289664533953)
                  ·
                    rfl

theorem cell20_970187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 2].length) (baseStart_970187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970187 prefixEnd_970187 := by exact prefixLift 970187
  have htrace : WordTrace (prefixWord ++ tailWord_970187) baseStart_970187 baseEnd_970187 := by
    simpa [prefixWord, tailWord_970187, baseEnd_970187] using wordTrace_append hprefix tailTrace_970187
  have hstable : (prefixWord ++ tailWord_970187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970187).length < 2 ^ (prefixWord ++ tailWord_970187).sum := by decide
  have hdescent : baseEnd_970187 < baseStart_970187 := by decide
  rcases family_descends (prefixWord ++ tailWord_970187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970211 : List Nat := [1, 1, 1, 6, 2, 3, 2, 4]
def baseStart_970211 : Nat := 118140960795 + 970211 * 2 ^ 59
def prefixEnd_970211 : Nat := 4983230072969 + 3 ^ 40 * 970211 * 2
def baseEnd_970211 : Nat := 147610245712417415911285

theorem tailTrace_970211 : CollatzResearch.WordTrace tailWord_970211 prefixEnd_970211 147610245712417415911285 := by
  unfold tailWord_970211
  simp only [CollatzResearch.WordTrace]
  refine ⟨35386502288098720691950487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23591001525399147127966991 35386502288098720691950487)
  ·
    refine ⟨53079753432148081037925731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35386502288098720691950487 53079753432148081037925731)
    ·
      refine ⟨79619630148222121556888597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53079753432148081037925731 79619630148222121556888597)
      ·
        refine ⟨3732170163197911947979153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79619630148222121556888597 3732170163197911947979153)
        ·
          refine ⟨2799127622398433960984365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732170163197911947979153 2799127622398433960984365)
          ·
            refine ⟨1049672858399412735369137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2799127622398433960984365 1049672858399412735369137)
            ·
              refine ⟨787254643799559551526853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049672858399412735369137 787254643799559551526853)
              ·
                refine ⟨147610245712417415911285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 787254643799559551526853 147610245712417415911285)
                ·
                  rfl

theorem cell20_970211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_970211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970211 prefixEnd_970211 := by exact prefixLift 970211
  have htrace : WordTrace (prefixWord ++ tailWord_970211) baseStart_970211 baseEnd_970211 := by
    simpa [prefixWord, tailWord_970211, baseEnd_970211] using wordTrace_append hprefix tailTrace_970211
  have hstable : (prefixWord ++ tailWord_970211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970211).length < 2 ^ (prefixWord ++ tailWord_970211).sum := by decide
  have hdescent : baseEnd_970211 < baseStart_970211 := by decide
  rcases family_descends (prefixWord ++ tailWord_970211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970238 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_970238 : Nat := 118140960795 + 970238 * 2 ^ 59
def prefixEnd_970238 : Nat := 4983230072969 + 3 ^ 40 * 970238 * 2
def baseEnd_970238 : Nat := 442843060672960153833745

theorem tailTrace_970238 : CollatzResearch.WordTrace tailWord_970238 prefixEnd_970238 442843060672960153833745 := by
  unfold tailWord_970238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423435882375113037897921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23591658039333936202122245 4423435882375113037897921)
  ·
    refine ⟨3317576911781334778423441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4423435882375113037897921 3317576911781334778423441)
    ·
      refine ⟨2488182683836001083817581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3317576911781334778423441 2488182683836001083817581)
      ·
        refine ⟨933068506438500406431593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2488182683836001083817581 933068506438500406431593)
        ·
          refine ⟨699801379828875304823695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933068506438500406431593 699801379828875304823695)
          ·
            refine ⟨1049702069743312957235543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699801379828875304823695 1049702069743312957235543)
            ·
              refine ⟨1574553104614969435853315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049702069743312957235543 1574553104614969435853315)
              ·
                refine ⟨2361829656922454153779973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574553104614969435853315 2361829656922454153779973)
                ·
                  refine ⟨442843060672960153833745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361829656922454153779973 442843060672960153833745)
                  ·
                    rfl

theorem cell20_970238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_970238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970238 prefixEnd_970238 := by exact prefixLift 970238
  have htrace : WordTrace (prefixWord ++ tailWord_970238) baseStart_970238 baseEnd_970238 := by
    simpa [prefixWord, tailWord_970238, baseEnd_970238] using wordTrace_append hprefix tailTrace_970238
  have hstable : (prefixWord ++ tailWord_970238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970238).length < 2 ^ (prefixWord ++ tailWord_970238).sum := by decide
  have hdescent : baseEnd_970238 < baseStart_970238 := by decide
  rcases family_descends (prefixWord ++ tailWord_970238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970242 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_970242 : Nat := 118140960795 + 970242 * 2 ^ 59
def prefixEnd_970242 : Nat := 4983230072969 + 3 ^ 40 * 970242 * 2
def baseEnd_970242 : Nat := 442844886381953917700395

theorem tailTrace_970242 : CollatzResearch.WordTrace tailWord_970242 prefixEnd_970242 442844886381953917700395 := by
  unfold tailWord_970242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8846908237746603246582245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23591755300657608657552653 8846908237746603246582245)
  ·
    refine ⟨1658795294577488108734171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8846908237746603246582245 1658795294577488108734171)
    ·
      refine ⟨2488192941866232163101257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658795294577488108734171 2488192941866232163101257)
      ·
        refine ⟨1866144706399674122325943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488192941866232163101257 1866144706399674122325943)
        ·
          refine ⟨2799217059599511183488915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866144706399674122325943 2799217059599511183488915)
          ·
            refine ⟨4198825589399266775233373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799217059599511183488915 4198825589399266775233373)
            ·
              refine ⟨1574559596024725040712515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4198825589399266775233373 1574559596024725040712515)
              ·
                refine ⟨2361839394037087561068773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574559596024725040712515 2361839394037087561068773)
                ·
                  refine ⟨442844886381953917700395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2361839394037087561068773 442844886381953917700395)
                  ·
                    rfl

theorem cell20_970242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_970242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970242 prefixEnd_970242 := by exact prefixLift 970242
  have htrace : WordTrace (prefixWord ++ tailWord_970242) baseStart_970242 baseEnd_970242 := by
    simpa [prefixWord, tailWord_970242, baseEnd_970242] using wordTrace_append hprefix tailTrace_970242
  have hstable : (prefixWord ++ tailWord_970242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970242).length < 2 ^ (prefixWord ++ tailWord_970242).sum := by decide
  have hdescent : baseEnd_970242 < baseStart_970242 := by decide
  rcases family_descends (prefixWord ++ tailWord_970242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970252 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 3]
def baseStart_970252 : Nat := 118140960795 + 970252 * 2 ^ 59
def prefixEnd_970252 : Nat := 4983230072969 + 3 ^ 40 * 970252 * 2
def baseEnd_970252 : Nat := 442849450654438327367021

theorem tailTrace_970252 : CollatzResearch.WordTrace tailWord_970252 prefixEnd_970252 442849450654438327367021 := by
  unfold tailWord_970252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693998840475092347096505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23591998453966789796128673 17693998840475092347096505)
  ·
    refine ⟨13270499130356319260322379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17693998840475092347096505 13270499130356319260322379)
    ·
      refine ⟨19905748695534478890483569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13270499130356319260322379 19905748695534478890483569)
      ·
        refine ⟨14929311521650859167862677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19905748695534478890483569 14929311521650859167862677)
        ·
          refine ⟨699811477577384023493563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14929311521650859167862677 699811477577384023493563)
          ·
            refine ⟨1049717216366076035240345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699811477577384023493563 1049717216366076035240345)
            ·
              refine ⟨787287912274557026430259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049717216366076035240345 787287912274557026430259)
              ·
                refine ⟨1180931868411835539645389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787287912274557026430259 1180931868411835539645389)
                ·
                  refine ⟨442849450654438327367021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180931868411835539645389 442849450654438327367021)
                  ·
                    rfl

theorem cell20_970252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_970252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970252 prefixEnd_970252 := by exact prefixLift 970252
  have htrace : WordTrace (prefixWord ++ tailWord_970252) baseStart_970252 baseEnd_970252 := by
    simpa [prefixWord, tailWord_970252, baseEnd_970252] using wordTrace_append hprefix tailTrace_970252
  have hstable : (prefixWord ++ tailWord_970252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970252).length < 2 ^ (prefixWord ++ tailWord_970252).sum := by decide
  have hdescent : baseEnd_970252 < baseStart_970252 := by decide
  rcases family_descends (prefixWord ++ tailWord_970252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970297 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 2]
def baseStart_970297 : Nat := 118140960795 + 970297 * 2 ^ 59
def prefixEnd_970297 : Nat := 4983230072969 + 3 ^ 40 * 970297 * 2
def baseEnd_970297 : Nat := 442869989880618170866837

theorem tailTrace_970297 : CollatzResearch.WordTrace tailWord_970297 prefixEnd_970297 442869989880618170866837 := by
  unfold tailWord_970297
  simp only [CollatzResearch.WordTrace]
  refine ⟨35389638965787157379581145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23593092643858104919720763 35389638965787157379581145)
  ·
    refine ⟨26542229224340368034685859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35389638965787157379581145 26542229224340368034685859)
    ·
      refine ⟨39813343836510552052028789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26542229224340368034685859 39813343836510552052028789)
      ·
        refine ⟨3732500984672864254877699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39813343836510552052028789 3732500984672864254877699)
        ·
          refine ⟨5598751477009296382316549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732500984672864254877699 5598751477009296382316549)
          ·
            refine ⟨1049765901939243071684353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5598751477009296382316549 1049765901939243071684353)
            ·
              refine ⟨787324426454432303763265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049765901939243071684353 787324426454432303763265)
              ·
                refine ⟨590493319840824227822449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787324426454432303763265 590493319840824227822449)
                ·
                  refine ⟨442869989880618170866837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590493319840824227822449 442869989880618170866837)
                  ·
                    rfl

theorem cell20_970297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_970297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970297 prefixEnd_970297 := by exact prefixLift 970297
  have htrace : WordTrace (prefixWord ++ tailWord_970297) baseStart_970297 baseEnd_970297 := by
    simpa [prefixWord, tailWord_970297, baseEnd_970297] using wordTrace_append hprefix tailTrace_970297
  have hstable : (prefixWord ++ tailWord_970297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970297).length < 2 ^ (prefixWord ++ tailWord_970297).sum := by decide
  have hdescent : baseEnd_970297 < baseStart_970297 := by decide
  rcases family_descends (prefixWord ++ tailWord_970297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970322 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_970322 : Nat := 118140960795 + 970322 * 2 ^ 59
def prefixEnd_970322 : Nat := 4983230072969 + 3 ^ 40 * 970322 * 2
def baseEnd_970322 : Nat := 442881400561829195033401

theorem tailTrace_970322 : CollatzResearch.WordTrace tailWord_970322 prefixEnd_970322 442881400561829195033401 := by
  unfold tailWord_970322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847637697674146662310305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23593700527131057766160813 8847637697674146662310305)
  ·
    refine ⟨6635728273255609996732729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8847637697674146662310305 6635728273255609996732729)
    ·
      refine ⟨4976796204941707497549547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6635728273255609996732729 4976796204941707497549547)
      ·
        refine ⟨7465194307412561246324321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976796204941707497549547 7465194307412561246324321)
        ·
          refine ⟨5598895730559420934743241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7465194307412561246324321 5598895730559420934743241)
          ·
            refine ⟨4199171797919565701057431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598895730559420934743241 4199171797919565701057431)
            ·
              refine ⟨6298757696879348551586147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199171797919565701057431 6298757696879348551586147)
              ·
                refine ⟨9448136545319022827379221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298757696879348551586147 9448136545319022827379221)
                ·
                  refine ⟨442881400561829195033401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9448136545319022827379221 442881400561829195033401)
                  ·
                    rfl

theorem cell20_970322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_970322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970322 prefixEnd_970322 := by exact prefixLift 970322
  have htrace : WordTrace (prefixWord ++ tailWord_970322) baseStart_970322 baseEnd_970322 := by
    simpa [prefixWord, tailWord_970322, baseEnd_970322] using wordTrace_append hprefix tailTrace_970322
  have hstable : (prefixWord ++ tailWord_970322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970322).length < 2 ^ (prefixWord ++ tailWord_970322).sum := by decide
  have hdescent : baseEnd_970322 < baseStart_970322 := by decide
  rcases family_descends (prefixWord ++ tailWord_970322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970336 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_970336 : Nat := 118140960795 + 970336 * 2 ^ 59
def prefixEnd_970336 : Nat := 4983230072969 + 3 ^ 40 * 970336 * 2
def baseEnd_970336 : Nat := 442887790543307368566677

theorem tailTrace_970336 : CollatzResearch.WordTrace tailWord_970336 prefixEnd_970336 442887790543307368566677 := by
  unfold tailWord_970336
  simp only [CollatzResearch.WordTrace]
  refine ⟨17695530706322933520125431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23594040941763911360167241 17695530706322933520125431)
  ·
    refine ⟨26543296059484400280188147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17695530706322933520125431 26543296059484400280188147)
    ·
      refine ⟨39814944089226600420282221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26543296059484400280188147 39814944089226600420282221)
      ·
        refine ⟨14930604033459975157605833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39814944089226600420282221 14930604033459975157605833)
        ·
          refine ⟨11197953025094981368204375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14930604033459975157605833 11197953025094981368204375)
          ·
            refine ⟨16796929537642472052306563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197953025094981368204375 16796929537642472052306563)
            ·
              refine ⟨25195394306463708078459845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16796929537642472052306563 25195394306463708078459845)
              ·
                refine ⟨4724136432461945264711221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25195394306463708078459845 4724136432461945264711221)
                ·
                  refine ⟨442887790543307368566677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4724136432461945264711221 442887790543307368566677)
                  ·
                    rfl

theorem cell20_970336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_970336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970336 prefixEnd_970336 := by exact prefixLift 970336
  have htrace : WordTrace (prefixWord ++ tailWord_970336) baseStart_970336 baseEnd_970336 := by
    simpa [prefixWord, tailWord_970336, baseEnd_970336] using wordTrace_append hprefix tailTrace_970336
  have hstable : (prefixWord ++ tailWord_970336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970336).length < 2 ^ (prefixWord ++ tailWord_970336).sum := by decide
  have hdescent : baseEnd_970336 < baseStart_970336 := by decide
  rcases family_descends (prefixWord ++ tailWord_970336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970339 : List Nat := [1, 1, 1, 5, 1, 3, 1, 5, 2]
def baseStart_970339 : Nat := 118140960795 + 970339 * 2 ^ 59
def prefixEnd_970339 : Nat := 4983230072969 + 3 ^ 40 * 970339 * 2
def baseEnd_970339 : Nat := 442889159825052691466665

theorem tailTrace_970339 : CollatzResearch.WordTrace tailWord_970339 prefixEnd_970339 442889159825052691466665 := by
  unfold tailWord_970339
  simp only [CollatzResearch.WordTrace]
  refine ⟨35391170831634998552610071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23594113887756665701740047 35391170831634998552610071)
  ·
    refine ⟨53086756247452497828915107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35391170831634998552610071 53086756247452497828915107)
    ·
      refine ⟨79630134371178746743372661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53086756247452497828915107 79630134371178746743372661)
      ·
        refine ⟨7465325097298007507191187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79630134371178746743372661 7465325097298007507191187)
        ·
          refine ⟨11197987645947011260786781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7465325097298007507191187 11197987645947011260786781)
          ·
            refine ⟨4199245367230129222795043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11197987645947011260786781 4199245367230129222795043)
            ·
              refine ⟨6298868050845193834192565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199245367230129222795043 6298868050845193834192565)
              ·
                refine ⟨590518879766736921955553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6298868050845193834192565 590518879766736921955553)
                ·
                  refine ⟨442889159825052691466665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590518879766736921955553 442889159825052691466665)
                  ·
                    rfl

theorem cell20_970339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 2].length) (baseStart_970339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970339 prefixEnd_970339 := by exact prefixLift 970339
  have htrace : WordTrace (prefixWord ++ tailWord_970339) baseStart_970339 baseEnd_970339 := by
    simpa [prefixWord, tailWord_970339, baseEnd_970339] using wordTrace_append hprefix tailTrace_970339
  have hstable : (prefixWord ++ tailWord_970339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970339).length < 2 ^ (prefixWord ++ tailWord_970339).sum := by decide
  have hdescent : baseEnd_970339 < baseStart_970339 := by decide
  rcases family_descends (prefixWord ++ tailWord_970339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970349 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 3]
def baseStart_970349 : Nat := 118140960795 + 970349 * 2 ^ 59
def prefixEnd_970349 : Nat := 4983230072969 + 3 ^ 40 * 970349 * 2
def baseEnd_970349 : Nat := 442893724097537101133291

theorem tailTrace_970349 : CollatzResearch.WordTrace tailWord_970349 prefixEnd_970349 442893724097537101133291 := by
  unfold tailWord_970349
  simp only [CollatzResearch.WordTrace]
  refine ⟨35391535561598770260474101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23594357041065846840316067 35391535561598770260474101)
  ·
    refine ⟨3317956458899884711919447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35391535561598770260474101 3317956458899884711919447)
    ·
      refine ⟨4976934688349827067879171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3317956458899884711919447 4976934688349827067879171)
      ·
        refine ⟨7465402032524740601818757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976934688349827067879171 7465402032524740601818757)
        ·
          refine ⟨1399762881098388862841017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7465402032524740601818757 1399762881098388862841017)
          ·
            refine ⟨1049822160823791647130763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1399762881098388862841017 1049822160823791647130763)
            ·
              refine ⟨1574733241235687470696145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049822160823791647130763 1574733241235687470696145)
              ·
                refine ⟨1181049930926765603022109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574733241235687470696145 1181049930926765603022109)
                ·
                  refine ⟨442893724097537101133291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181049930926765603022109 442893724097537101133291)
                  ·
                    rfl

theorem cell20_970349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_970349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970349 prefixEnd_970349 := by exact prefixLift 970349
  have htrace : WordTrace (prefixWord ++ tailWord_970349) baseStart_970349 baseEnd_970349 := by
    simpa [prefixWord, tailWord_970349, baseEnd_970349] using wordTrace_append hprefix tailTrace_970349
  have hstable : (prefixWord ++ tailWord_970349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970349).length < 2 ^ (prefixWord ++ tailWord_970349).sum := by decide
  have hdescent : baseEnd_970349 < baseStart_970349 := by decide
  rcases family_descends (prefixWord ++ tailWord_970349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970429 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_970429 : Nat := 118140960795 + 970429 * 2 ^ 59
def prefixEnd_970429 : Nat := 4983230072969 + 3 ^ 40 * 970429 * 2
def baseEnd_970429 : Nat := 442930238277412378466297

theorem tailTrace_970429 : CollatzResearch.WordTrace tailWord_970429 prefixEnd_970429 442930238277412378466297 := by
  unfold tailWord_970429
  simp only [CollatzResearch.WordTrace]
  refine ⟨35394453401308943923386341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23596302267539295948924227 35394453401308943923386341)
  ·
    refine ⟨6636460012745426985634939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35394453401308943923386341 6636460012745426985634939)
    ·
      refine ⟨9954690019118140478452409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6636460012745426985634939 9954690019118140478452409)
      ·
        refine ⟨7466017514338605358839307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9954690019118140478452409 7466017514338605358839307)
        ·
          refine ⟨11199026271507908038258961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466017514338605358839307 11199026271507908038258961)
          ·
            refine ⟨8399269703630931028694221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11199026271507908038258961 8399269703630931028694221)
            ·
              refine ⟨3149726138861599135760333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8399269703630931028694221 3149726138861599135760333)
              ·
                refine ⟨1181147302073099675910125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3149726138861599135760333 1181147302073099675910125)
                ·
                  refine ⟨442930238277412378466297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181147302073099675910125 442930238277412378466297)
                  ·
                    rfl

theorem cell20_970429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_970429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970429 prefixEnd_970429 := by exact prefixLift 970429
  have htrace : WordTrace (prefixWord ++ tailWord_970429) baseStart_970429 baseEnd_970429 := by
    simpa [prefixWord, tailWord_970429, baseEnd_970429] using wordTrace_append hprefix tailTrace_970429
  have hstable : (prefixWord ++ tailWord_970429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970429).length < 2 ^ (prefixWord ++ tailWord_970429).sum := by decide
  have hdescent : baseEnd_970429 < baseStart_970429 := by decide
  rcases family_descends (prefixWord ++ tailWord_970429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970436 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_970436 : Nat := 118140960795 + 970436 * 2 ^ 59
def prefixEnd_970436 : Nat := 4983230072969 + 3 ^ 40 * 970436 * 2
def baseEnd_970436 : Nat := 442933433268151465232935

theorem tailTrace_970436 : CollatzResearch.WordTrace tailWord_970436 prefixEnd_970436 442933433268151465232935 := by
  unfold tailWord_970436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697354356141792059445581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23596472474855722745927441 17697354356141792059445581)
  ·
    refine ⟨6636507883553172022292093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17697354356141792059445581 6636507883553172022292093)
    ·
      refine ⟨2488690456332439508359535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6636507883553172022292093 2488690456332439508359535)
      ·
        refine ⟨3733035684498659262539303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488690456332439508359535 3733035684498659262539303)
        ·
          refine ⟨5599553526747988893808955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733035684498659262539303 5599553526747988893808955)
          ·
            refine ⟨8399330290121983340713433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599553526747988893808955 8399330290121983340713433)
            ·
              refine ⟨6299497717591487505535075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8399330290121983340713433 6299497717591487505535075)
              ·
                refine ⟨9449246576387231258302613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299497717591487505535075 9449246576387231258302613)
                ·
                  refine ⟨442933433268151465232935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9449246576387231258302613 442933433268151465232935)
                  ·
                    rfl

theorem cell20_970436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_970436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970436 prefixEnd_970436 := by exact prefixLift 970436
  have htrace : WordTrace (prefixWord ++ tailWord_970436) baseStart_970436 baseEnd_970436 := by
    simpa [prefixWord, tailWord_970436, baseEnd_970436] using wordTrace_append hprefix tailTrace_970436
  have hstable : (prefixWord ++ tailWord_970436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970436).length < 2 ^ (prefixWord ++ tailWord_970436).sum := by decide
  have hdescent : baseEnd_970436 < baseStart_970436 := by decide
  rcases family_descends (prefixWord ++ tailWord_970436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970460 : List Nat := [2, 2, 5, 1, 2, 8]
def baseStart_970460 : Nat := 118140960795 + 970460 * 2 ^ 59
def prefixEnd_970460 : Nat := 4983230072969 + 3 ^ 40 * 970460 * 2
def baseEnd_970460 : Nat := 16405347686004224016031

theorem tailTrace_970460 : CollatzResearch.WordTrace tailWord_970460 prefixEnd_970460 16405347686004224016031 := by
  unfold tailWord_970460
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697792032098318108882417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23597056042797757478509889 17697792032098318108882417)
  ·
    refine ⟨13273344024073738581661813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17697792032098318108882417 13273344024073738581661813)
    ·
      refine ⟨1244376002256912992030795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13273344024073738581661813 1244376002256912992030795)
      ·
        refine ⟨1866564003385369488046193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244376002256912992030795 1866564003385369488046193)
        ·
          refine ⟨1399923002539027116034645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866564003385369488046193 1399923002539027116034645)
          ·
            refine ⟨16405347686004224016031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1399923002539027116034645 16405347686004224016031)
            ·
              rfl

theorem cell20_970460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 8].length) (baseStart_970460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970460 prefixEnd_970460 := by exact prefixLift 970460
  have htrace : WordTrace (prefixWord ++ tailWord_970460) baseStart_970460 baseEnd_970460 := by
    simpa [prefixWord, tailWord_970460, baseEnd_970460] using wordTrace_append hprefix tailTrace_970460
  have hstable : (prefixWord ++ tailWord_970460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970460).length < 2 ^ (prefixWord ++ tailWord_970460).sum := by decide
  have hdescent : baseEnd_970460 < baseStart_970460 := by decide
  rcases family_descends (prefixWord ++ tailWord_970460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970481 : List Nat := [1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_970481 : Nat := 118140960795 + 970481 * 2 ^ 59
def prefixEnd_970481 : Nat := 4983230072969 + 3 ^ 40 * 970481 * 2
def baseEnd_970481 : Nat := 147651324164777102910917

theorem tailTrace_970481 : CollatzResearch.WordTrace tailWord_970481 prefixEnd_970481 147651324164777102910917 := by
  unfold tailWord_970481
  simp only [CollatzResearch.WordTrace]
  refine ⟨35396349997120556804279297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23597566664747037869519531 35396349997120556804279297)
  ·
    refine ⟨26547262497840417603209473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35396349997120556804279297 26547262497840417603209473)
    ·
      refine ⟨19910446873380313202407105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26547262497840417603209473 19910446873380313202407105)
      ·
        refine ⟨14932835155035234901805329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19910446873380313202407105 14932835155035234901805329)
        ·
          refine ⟨11199626366276426176353997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14932835155035234901805329 11199626366276426176353997)
          ·
            refine ⟨4199859887353659816132749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11199626366276426176353997 4199859887353659816132749)
            ·
              refine ⟨1574947457757622431049781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4199859887353659816132749 1574947457757622431049781)
              ·
                refine ⟨147651324164777102910917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574947457757622431049781 147651324164777102910917)
                ·
                  rfl

theorem cell20_970481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_970481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970481 prefixEnd_970481 := by exact prefixLift 970481
  have htrace : WordTrace (prefixWord ++ tailWord_970481) baseStart_970481 baseEnd_970481 := by
    simpa [prefixWord, tailWord_970481, baseEnd_970481] using wordTrace_append hprefix tailTrace_970481
  have hstable : (prefixWord ++ tailWord_970481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970481).length < 2 ^ (prefixWord ++ tailWord_970481).sum := by decide
  have hdescent : baseEnd_970481 < baseStart_970481 := by decide
  rcases family_descends (prefixWord ++ tailWord_970481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970495 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_970495 : Nat := 118140960795 + 970495 * 2 ^ 59
def prefixEnd_970495 : Nat := 4983230072969 + 3 ^ 40 * 970495 * 2
def baseEnd_970495 : Nat := 442960362475809482266027

theorem tailTrace_970495 : CollatzResearch.WordTrace tailWord_970495 prefixEnd_970495 442960362475809482266027 := by
  unfold tailWord_970495
  simp only [CollatzResearch.WordTrace]
  refine ⟨35396860619069837195288939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23597907079379891463525959 35396860619069837195288939)
  ·
    refine ⟨53095290928604755792933409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35396860619069837195288939 53095290928604755792933409)
    ·
      refine ⟨39821468196453566844700057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53095290928604755792933409 39821468196453566844700057)
      ·
        refine ⟨29866101147340175133525043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39821468196453566844700057 29866101147340175133525043)
        ·
          refine ⟨44799151721010262700287565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29866101147340175133525043 44799151721010262700287565)
          ·
            refine ⟨16799681895378848512607837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44799151721010262700287565 16799681895378848512607837)
            ·
              refine ⟨6299880710767068192227939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16799681895378848512607837 6299880710767068192227939)
              ·
                refine ⟨9449821066150602288341909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299880710767068192227939 9449821066150602288341909)
                ·
                  refine ⟨442960362475809482266027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9449821066150602288341909 442960362475809482266027)
                  ·
                    rfl

theorem cell20_970495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_970495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970495 prefixEnd_970495 := by exact prefixLift 970495
  have htrace : WordTrace (prefixWord ++ tailWord_970495) baseStart_970495 baseEnd_970495 := by
    simpa [prefixWord, tailWord_970495, baseEnd_970495] using wordTrace_append hprefix tailTrace_970495
  have hstable : (prefixWord ++ tailWord_970495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970495).length < 2 ^ (prefixWord ++ tailWord_970495).sum := by decide
  have hdescent : baseEnd_970495 < baseStart_970495 := by decide
  rcases family_descends (prefixWord ++ tailWord_970495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970519 : List Nat := [1, 1, 3, 4, 2, 2, 7]
def baseStart_970519 : Nat := 118140960795 + 970519 * 2 ^ 59
def prefixEnd_970519 : Nat := 4983230072969 + 3 ^ 40 * 970519 * 2
def baseEnd_970519 : Nat := 49219035192196896162881

theorem tailTrace_970519 : CollatzResearch.WordTrace tailWord_970519 prefixEnd_970519 49219035192196896162881 := by
  unfold tailWord_970519
  simp only [CollatzResearch.WordTrace]
  refine ⟨35397735970982889294162611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23598490647321926196108407 35397735970982889294162611)
  ·
    refine ⟨53096603956474333941243917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35397735970982889294162611 53096603956474333941243917)
    ·
      refine ⟨19911226483677875227966469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53096603956474333941243917 19911226483677875227966469)
      ·
        refine ⟨3733354965689601605243713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19911226483677875227966469 3733354965689601605243713)
        ·
          refine ⟨2800016224267201203932785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3733354965689601605243713 2800016224267201203932785)
          ·
            refine ⟨2100012168200400902949589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800016224267201203932785 2100012168200400902949589)
            ·
              refine ⟨49219035192196896162881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2100012168200400902949589 49219035192196896162881)
              ·
                rfl

theorem cell20_970519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_970519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970519 prefixEnd_970519 := by exact prefixLift 970519
  have htrace : WordTrace (prefixWord ++ tailWord_970519) baseStart_970519 baseEnd_970519 := by
    simpa [prefixWord, tailWord_970519, baseEnd_970519] using wordTrace_append hprefix tailTrace_970519
  have hstable : (prefixWord ++ tailWord_970519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970519).length < 2 ^ (prefixWord ++ tailWord_970519).sum := by decide
  have hdescent : baseEnd_970519 < baseStart_970519 := by decide
  rcases family_descends (prefixWord ++ tailWord_970519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970522 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_970522 : Nat := 118140960795 + 970522 * 2 ^ 59
def prefixEnd_970522 : Nat := 4983230072969 + 3 ^ 40 * 970522 * 2
def baseEnd_970522 : Nat := 442972686011517388365917

theorem tailTrace_970522 : CollatzResearch.WordTrace tailWord_970522 prefixEnd_970522 442972686011517388365917 := by
  unfold tailWord_970522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8849461347493005201630455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23598563593314680537681213 8849461347493005201630455)
  ·
    refine ⟨13274192021239507802445683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8849461347493005201630455 13274192021239507802445683)
    ·
      refine ⟨19911288031859261703668525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13274192021239507802445683 19911288031859261703668525)
      ·
        refine ⟨7466733011947223138875697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19911288031859261703668525 7466733011947223138875697)
        ·
          refine ⟨5600049758960417354156773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7466733011947223138875697 5600049758960417354156773)
          ·
            refine ⟨1050009329805078253904395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5600049758960417354156773 1050009329805078253904395)
            ·
              refine ⟨1575013994707617380856593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050009329805078253904395 1575013994707617380856593)
              ·
                refine ⟨1181260496030713035642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575013994707617380856593 1181260496030713035642445)
                ·
                  refine ⟨442972686011517388365917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181260496030713035642445 442972686011517388365917)
                  ·
                    rfl

theorem cell20_970522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_970522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970522 prefixEnd_970522 := by exact prefixLift 970522
  have htrace : WordTrace (prefixWord ++ tailWord_970522) baseStart_970522 baseEnd_970522 := by
    simpa [prefixWord, tailWord_970522, baseEnd_970522] using wordTrace_append hprefix tailTrace_970522
  have hstable : (prefixWord ++ tailWord_970522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970522).length < 2 ^ (prefixWord ++ tailWord_970522).sum := by decide
  have hdescent : baseEnd_970522 < baseStart_970522 := by decide
  rcases family_descends (prefixWord ++ tailWord_970522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970529 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 2]
def baseStart_970529 : Nat := 118140960795 + 970529 * 2 ^ 59
def prefixEnd_970529 : Nat := 4983230072969 + 3 ^ 40 * 970529 * 2
def baseEnd_970529 : Nat := 442975881002256475132555

theorem tailTrace_970529 : CollatzResearch.WordTrace tailWord_970529 prefixEnd_970529 442975881002256475132555 := by
  unfold tailWord_970529
  simp only [CollatzResearch.WordTrace]
  refine ⟨35398100700946661002026641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23598733800631107334684427 35398100700946661002026641)
  ·
    refine ⟨26548575525709995751519981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35398100700946661002026641 26548575525709995751519981)
    ·
      refine ⟨9955715822141248406819993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26548575525709995751519981 9955715822141248406819993)
      ·
        refine ⟨7466786866605936305114995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9955715822141248406819993 7466786866605936305114995)
        ·
          refine ⟨11200180299908904457672493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466786866605936305114995 11200180299908904457672493)
          ·
            refine ⟨4200067612465839171627185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11200180299908904457672493 4200067612465839171627185)
            ·
              refine ⟨3150050709349379378720389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200067612465839171627185 3150050709349379378720389)
              ·
                refine ⟨590634508003008633510073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3150050709349379378720389 590634508003008633510073)
                ·
                  refine ⟨442975881002256475132555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590634508003008633510073 442975881002256475132555)
                  ·
                    rfl

theorem cell20_970529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_970529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970529 prefixEnd_970529 := by exact prefixLift 970529
  have htrace : WordTrace (prefixWord ++ tailWord_970529) baseStart_970529 baseEnd_970529 := by
    simpa [prefixWord, tailWord_970529, baseEnd_970529] using wordTrace_append hprefix tailTrace_970529
  have hstable : (prefixWord ++ tailWord_970529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970529).length < 2 ^ (prefixWord ++ tailWord_970529).sum := by decide
  have hdescent : baseEnd_970529 < baseStart_970529 := by decide
  rcases family_descends (prefixWord ++ tailWord_970529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970567 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 2]
def baseStart_970567 : Nat := 118140960795 + 970567 * 2 ^ 59
def prefixEnd_970567 : Nat := 4983230072969 + 3 ^ 40 * 970567 * 2
def baseEnd_970567 : Nat := 442993225237697231865733

theorem tailTrace_970567 : CollatzResearch.WordTrace tailWord_970567 prefixEnd_970567 442993225237697231865733 := by
  unfold tailWord_970567
  simp only [CollatzResearch.WordTrace]
  refine ⟨35399486674808993491909955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23599657783205995661273303 35399486674808993491909955)
  ·
    refine ⟨53099230012213490237864933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35399486674808993491909955 53099230012213490237864933)
    ·
      refine ⟨9956105627290029419599675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53099230012213490237864933 9956105627290029419599675)
      ·
        refine ⟨14934158440935044129399513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9956105627290029419599675 14934158440935044129399513)
        ·
          refine ⟨11200618830701283097049635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14934158440935044129399513 11200618830701283097049635)
          ·
            refine ⟨16800928246051924645574453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11200618830701283097049635 16800928246051924645574453)
            ·
              refine ⟨1575087023067367935522605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16800928246051924645574453 1575087023067367935522605)
              ·
                refine ⟨590657633650262975820977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575087023067367935522605 590657633650262975820977)
                ·
                  refine ⟨442993225237697231865733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590657633650262975820977 442993225237697231865733)
                  ·
                    rfl

theorem cell20_970567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 2].length) (baseStart_970567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970567 prefixEnd_970567 := by exact prefixLift 970567
  have htrace : WordTrace (prefixWord ++ tailWord_970567) baseStart_970567 baseEnd_970567 := by
    simpa [prefixWord, tailWord_970567, baseEnd_970567] using wordTrace_append hprefix tailTrace_970567
  have hstable : (prefixWord ++ tailWord_970567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970567).length < 2 ^ (prefixWord ++ tailWord_970567).sum := by decide
  have hdescent : baseEnd_970567 < baseStart_970567 := by decide
  rcases family_descends (prefixWord ++ tailWord_970567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970609 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_970609 : Nat := 118140960795 + 970609 * 2 ^ 59
def prefixEnd_970609 : Nat := 4983230072969 + 3 ^ 40 * 970609 * 2
def baseEnd_970609 : Nat := 443012395182131752465561

theorem tailTrace_970609 : CollatzResearch.WordTrace tailWord_970609 prefixEnd_970609 443012395182131752465561 := by
  unfold tailWord_970609
  simp only [CollatzResearch.WordTrace]
  refine ⟨35401018540656834664938881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23600679027104556443292587 35401018540656834664938881)
  ·
    refine ⟨26550763905492625998704161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35401018540656834664938881 26550763905492625998704161)
    ·
      refine ⟨19913072929119469499028121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26550763905492625998704161 19913072929119469499028121)
      ·
        refine ⟨14934804696839602124271091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19913072929119469499028121 14934804696839602124271091)
        ·
          refine ⟨22402207045259403186406637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14934804696839602124271091 22402207045259403186406637)
          ·
            refine ⟨8400827641972276194902489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22402207045259403186406637 8400827641972276194902489)
            ·
              refine ⟨6300620731479207146176867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8400827641972276194902489 6300620731479207146176867)
              ·
                refine ⟨9450931097218810719265301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300620731479207146176867 9450931097218810719265301)
                ·
                  refine ⟨443012395182131752465561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9450931097218810719265301 443012395182131752465561)
                  ·
                    rfl

theorem cell20_970609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_970609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970609 prefixEnd_970609 := by exact prefixLift 970609
  have htrace : WordTrace (prefixWord ++ tailWord_970609) baseStart_970609 baseEnd_970609 := by
    simpa [prefixWord, tailWord_970609, baseEnd_970609] using wordTrace_append hprefix tailTrace_970609
  have hstable : (prefixWord ++ tailWord_970609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970609).length < 2 ^ (prefixWord ++ tailWord_970609).sum := by decide
  have hdescent : baseEnd_970609 < baseStart_970609 := by decide
  rcases family_descends (prefixWord ++ tailWord_970609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970640 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_970640 : Nat := 118140960795 + 970640 * 2 ^ 59
def prefixEnd_970640 : Nat := 4983230072969 + 3 ^ 40 * 970640 * 2
def baseEnd_970640 : Nat := 443026544426833422432101

theorem tailTrace_970640 : CollatzResearch.WordTrace tailWord_970640 prefixEnd_970640 443026544426833422432101 := by
  unfold tailWord_970640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701074601772263479658687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23601432802363017972878249 17701074601772263479658687)
  ·
    refine ⟨26551611902658395219488031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17701074601772263479658687 26551611902658395219488031)
    ·
      refine ⟨39827417853987592829232047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26551611902658395219488031 39827417853987592829232047)
      ·
        refine ⟨59741126780981389243848071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39827417853987592829232047 59741126780981389243848071)
        ·
          refine ⟨89611690171472083865772107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59741126780981389243848071 89611690171472083865772107)
          ·
            refine ⟨134417535257208125798658161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89611690171472083865772107 134417535257208125798658161)
            ·
              refine ⟨100813151442906094348993621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134417535257208125798658161 100813151442906094348993621)
              ·
                refine ⟨1181404118471555793152269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 100813151442906094348993621 1181404118471555793152269)
                ·
                  refine ⟨443026544426833422432101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181404118471555793152269 443026544426833422432101)
                  ·
                    rfl

theorem cell20_970640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_970640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970640 prefixEnd_970640 := by exact prefixLift 970640
  have htrace : WordTrace (prefixWord ++ tailWord_970640) baseStart_970640 baseEnd_970640 := by
    simpa [prefixWord, tailWord_970640, baseEnd_970640] using wordTrace_append hprefix tailTrace_970640
  have hstable : (prefixWord ++ tailWord_970640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970640).length < 2 ^ (prefixWord ++ tailWord_970640).sum := by decide
  have hdescent : baseEnd_970640 < baseStart_970640 := by decide
  rcases family_descends (prefixWord ++ tailWord_970640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970650 : List Nat := [3, 1, 1, 4, 2, 3, 1, 5]
def baseStart_970650 : Nat := 118140960795 + 970650 * 2 ^ 59
def prefixEnd_970650 : Nat := 4983230072969 + 3 ^ 40 * 970650 * 2
def baseEnd_970650 : Nat := 147677036233105944032909

theorem tailTrace_970650 : CollatzResearch.WordTrace tailWord_970650 prefixEnd_970650 147677036233105944032909 := by
  unfold tailWord_970650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850628483377074666795351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23601675955672199111454269 8850628483377074666795351)
  ·
    refine ⟨13275942725065612000193027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8850628483377074666795351 13275942725065612000193027)
    ·
      refine ⟨19913914087598418000289541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13275942725065612000193027 19913914087598418000289541)
      ·
        refine ⟨3733858891424703375054289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19913914087598418000289541 3733858891424703375054289)
        ·
          refine ⟨2800394168568527531290717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3733858891424703375054289 2800394168568527531290717)
          ·
            refine ⟨1050147813213197824234019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2800394168568527531290717 1050147813213197824234019)
            ·
              refine ⟨1575221719819796736351029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050147813213197824234019 1575221719819796736351029)
              ·
                refine ⟨147677036233105944032909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1575221719819796736351029 147677036233105944032909)
                ·
                  rfl

theorem cell20_970650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_970650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970650 prefixEnd_970650 := by exact prefixLift 970650
  have htrace : WordTrace (prefixWord ++ tailWord_970650) baseStart_970650 baseEnd_970650 := by
    simpa [prefixWord, tailWord_970650, baseEnd_970650] using wordTrace_append hprefix tailTrace_970650
  have hstable : (prefixWord ++ tailWord_970650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970650).length < 2 ^ (prefixWord ++ tailWord_970650).sum := by decide
  have hdescent : baseEnd_970650 < baseStart_970650 := by decide
  rcases family_descends (prefixWord ++ tailWord_970650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970671 : List Nat := [1, 1, 2, 1, 2, 2, 7, 4]
def baseStart_970671 : Nat := 118140960795 + 970671 * 2 ^ 59
def prefixEnd_970671 : Nat := 4983230072969 + 3 ^ 40 * 970671 * 2
def baseEnd_970671 : Nat := 147680231223845030799547

theorem tailTrace_970671 : CollatzResearch.WordTrace tailWord_970671 prefixEnd_970671 147680231223845030799547 := by
  unfold tailWord_970671
  simp only [CollatzResearch.WordTrace]
  refine ⟨35403279866432219253695867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23602186577621479502463911 35403279866432219253695867)
  ·
    refine ⟨53104919799648328880543801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35403279866432219253695867 53104919799648328880543801)
    ·
      refine ⟨39828689849736246660407851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53104919799648328880543801 39828689849736246660407851)
      ·
        refine ⟨59743034774604369990611777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39828689849736246660407851 59743034774604369990611777)
        ·
          refine ⟨44807276080953277492958833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59743034774604369990611777 44807276080953277492958833)
          ·
            refine ⟨33605457060714958119719125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44807276080953277492958833 33605457060714958119719125)
            ·
              refine ⟨787627899860506830930917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33605457060714958119719125 787627899860506830930917)
              ·
                refine ⟨147680231223845030799547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 787627899860506830930917 147680231223845030799547)
                ·
                  rfl

theorem cell20_970671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_970671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970671 prefixEnd_970671 := by exact prefixLift 970671
  have htrace : WordTrace (prefixWord ++ tailWord_970671) baseStart_970671 baseEnd_970671 := by
    simpa [prefixWord, tailWord_970671, baseEnd_970671] using wordTrace_append hprefix tailTrace_970671
  have hstable : (prefixWord ++ tailWord_970671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970671).length < 2 ^ (prefixWord ++ tailWord_970671).sum := by decide
  have hdescent : baseEnd_970671 < baseStart_970671 := by decide
  rcases family_descends (prefixWord ++ tailWord_970671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970681 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 2]
def baseStart_970681 : Nat := 118140960795 + 970681 * 2 ^ 59
def prefixEnd_970681 : Nat := 4983230072969 + 3 ^ 40 * 970681 * 2
def baseEnd_970681 : Nat := 443045257944019502065267

theorem tailTrace_970681 : CollatzResearch.WordTrace tailWord_970681 prefixEnd_970681 443045257944019502065267 := by
  unfold tailWord_970681
  simp only [CollatzResearch.WordTrace]
  refine ⟨35403644596395990961559897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23602429730930660641039931 35403644596395990961559897)
  ·
    refine ⟨26552733447296993221169923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35403644596395990961559897 26552733447296993221169923)
    ·
      refine ⟨39829100170945489831754885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26552733447296993221169923 39829100170945489831754885)
      ·
        refine ⟨7467956282052279343454041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39829100170945489831754885 7467956282052279343454041)
        ·
          refine ⟨5600967211539209507590531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7467956282052279343454041 5600967211539209507590531)
          ·
            refine ⟨8401450817308814261385797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600967211539209507590531 8401450817308814261385797)
            ·
              refine ⟨1575272028245402674009837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8401450817308814261385797 1575272028245402674009837)
              ·
                refine ⟨590727010592026002753689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575272028245402674009837 590727010592026002753689)
                ·
                  refine ⟨443045257944019502065267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590727010592026002753689 443045257944019502065267)
                  ·
                    rfl

theorem cell20_970681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_970681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970681 prefixEnd_970681 := by exact prefixLift 970681
  have htrace : WordTrace (prefixWord ++ tailWord_970681) baseStart_970681 baseEnd_970681 := by
    simpa [prefixWord, tailWord_970681, baseEnd_970681] using wordTrace_append hprefix tailTrace_970681
  have hstable : (prefixWord ++ tailWord_970681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970681).length < 2 ^ (prefixWord ++ tailWord_970681).sum := by decide
  have hdescent : baseEnd_970681 < baseStart_970681 := by decide
  rcases family_descends (prefixWord ++ tailWord_970681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970702 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_970702 : Nat := 118140960795 + 970702 * 2 ^ 59
def prefixEnd_970702 : Nat := 4983230072969 + 3 ^ 40 * 970702 * 2
def baseEnd_970702 : Nat := 443054842916236762365181

theorem tailTrace_970702 : CollatzResearch.WordTrace tailWord_970702 prefixEnd_970702 443054842916236762365181 := by
  unfold tailWord_970702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425551316164988943509295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23602940352879941032049573 4425551316164988943509295)
  ·
    refine ⟨6638326974247483415263943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425551316164988943509295 6638326974247483415263943)
    ·
      refine ⟨9957490461371225122895915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6638326974247483415263943 9957490461371225122895915)
      ·
        refine ⟨14936235692056837684343873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9957490461371225122895915 14936235692056837684343873)
        ·
          refine ⟨11202176769042628263257905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14936235692056837684343873 11202176769042628263257905)
          ·
            refine ⟨8401632576781971197443429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11202176769042628263257905 8401632576781971197443429)
            ·
              refine ⟨1575306108146619599520643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8401632576781971197443429 1575306108146619599520643)
              ·
                refine ⟨2362959162219929399280965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575306108146619599520643 2362959162219929399280965)
                ·
                  refine ⟨443054842916236762365181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2362959162219929399280965 443054842916236762365181)
                  ·
                    rfl

theorem cell20_970702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_970702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970702 prefixEnd_970702 := by exact prefixLift 970702
  have htrace : WordTrace (prefixWord ++ tailWord_970702) baseStart_970702 baseEnd_970702 := by
    simpa [prefixWord, tailWord_970702, baseEnd_970702] using wordTrace_append hprefix tailTrace_970702
  have hstable : (prefixWord ++ tailWord_970702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970702).length < 2 ^ (prefixWord ++ tailWord_970702).sum := by decide
  have hdescent : baseEnd_970702 < baseStart_970702 := by decide
  rcases family_descends (prefixWord ++ tailWord_970702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970722 : List Nat := [3, 3, 3, 1, 2, 2, 2, 4]
def baseStart_970722 : Nat := 118140960795 + 970722 * 2 ^ 59
def prefixEnd_970722 : Nat := 4983230072969 + 3 ^ 40 * 970722 * 2
def baseEnd_970722 : Nat := 147687990487068527232811

theorem tailTrace_970722 : CollatzResearch.WordTrace tailWord_970722 prefixEnd_970722 147687990487068527232811 := by
  unfold tailWord_970722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851284997311863740950605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23603426659498303309201613 8851284997311863740950605)
  ·
    refine ⟨3319231873991948902856477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8851284997311863740950605 3319231873991948902856477)
    ·
      refine ⟨1244711952746980838571179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3319231873991948902856477 1244711952746980838571179)
      ·
        refine ⟨1867067929120471257856769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244711952746980838571179 1867067929120471257856769)
        ·
          refine ⟨1400300946840353443392577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867067929120471257856769 1400300946840353443392577)
          ·
            refine ⟨1050225710130265082544433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400300946840353443392577 1050225710130265082544433)
            ·
              refine ⟨787669282597698811908325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050225710130265082544433 787669282597698811908325)
              ·
                refine ⟨147687990487068527232811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 787669282597698811908325 147687990487068527232811)
                ·
                  rfl

theorem cell20_970722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_970722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970722 prefixEnd_970722 := by exact prefixLift 970722
  have htrace : WordTrace (prefixWord ++ tailWord_970722) baseStart_970722 baseEnd_970722 := by
    simpa [prefixWord, tailWord_970722, baseEnd_970722] using wordTrace_append hprefix tailTrace_970722
  have hstable : (prefixWord ++ tailWord_970722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970722).length < 2 ^ (prefixWord ++ tailWord_970722).sum := by decide
  have hdescent : baseEnd_970722 < baseStart_970722 := by decide
  rcases family_descends (prefixWord ++ tailWord_970722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970771 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 3]
def baseStart_970771 : Nat := 118140960795 + 970771 * 2 ^ 59
def prefixEnd_970771 : Nat := 4983230072969 + 3 ^ 40 * 970771 * 2
def baseEnd_970771 : Nat := 443086336396379189064899

theorem tailTrace_970771 : CollatzResearch.WordTrace tailWord_970771 prefixEnd_970771 443086336396379189064899 := by
  unfold tailWord_970771
  simp only [CollatzResearch.WordTrace]
  refine ⟨35406927166069936332336167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23604618110713290888224111 35406927166069936332336167)
  ·
    refine ⟨53110390749104904498504251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35406927166069936332336167 53110390749104904498504251)
    ·
      refine ⟨79665586123657356747756377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53110390749104904498504251 79665586123657356747756377)
      ·
        refine ⟨59749189592743017560817283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79665586123657356747756377 59749189592743017560817283)
        ·
          refine ⟨89623784389114526341225925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59749189592743017560817283 89623784389114526341225925)
          ·
            refine ⟨16804459572958973688979861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89623784389114526341225925 16804459572958973688979861)
            ·
              refine ⟨787709042482451891670931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16804459572958973688979861 787709042482451891670931)
              ·
                refine ⟨1181563563723677837506397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787709042482451891670931 1181563563723677837506397)
                ·
                  refine ⟨443086336396379189064899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181563563723677837506397 443086336396379189064899)
                  ·
                    rfl

theorem cell20_970771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_970771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970771 prefixEnd_970771 := by exact prefixLift 970771
  have htrace : WordTrace (prefixWord ++ tailWord_970771) baseStart_970771 baseEnd_970771 := by
    simpa [prefixWord, tailWord_970771, baseEnd_970771] using wordTrace_append hprefix tailTrace_970771
  have hstable : (prefixWord ++ tailWord_970771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970771).length < 2 ^ (prefixWord ++ tailWord_970771).sum := by decide
  have hdescent : baseEnd_970771 < baseStart_970771 := by decide
  rcases family_descends (prefixWord ++ tailWord_970771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970837 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_970837 : Nat := 118140960795 + 970837 * 2 ^ 59
def prefixEnd_970837 : Nat := 4983230072969 + 3 ^ 40 * 970837 * 2
def baseEnd_970837 : Nat := 443116460594776292864629

theorem tailTrace_970837 : CollatzResearch.WordTrace tailWord_970837 prefixEnd_970837 443116460594776292864629 := by
  unfold tailWord_970837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35409334383830829604238765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23606222922553886402825843 35409334383830829604238765)
  ·
    refine ⟨13278500393936561101589537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35409334383830829604238765 13278500393936561101589537)
    ·
      refine ⟨9958875295452420826192153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13278500393936561101589537 9958875295452420826192153)
      ·
        refine ⟨7469156471589315619644115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9958875295452420826192153 7469156471589315619644115)
        ·
          refine ⟨11203734707383973429466173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469156471589315619644115 11203734707383973429466173)
          ·
            refine ⟨4201400515268990036049815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11203734707383973429466173 4201400515268990036049815)
            ·
              refine ⟨6302100772903485054074723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4201400515268990036049815 6302100772903485054074723)
              ·
                refine ⟨9453151159355227581112085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302100772903485054074723 9453151159355227581112085)
                ·
                  refine ⟨443116460594776292864629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9453151159355227581112085 443116460594776292864629)
                  ·
                    rfl

theorem cell20_970837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_970837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970837 prefixEnd_970837 := by exact prefixLift 970837
  have htrace : WordTrace (prefixWord ++ tailWord_970837) baseStart_970837 baseEnd_970837 := by
    simpa [prefixWord, tailWord_970837, baseEnd_970837] using wordTrace_append hprefix tailTrace_970837
  have hstable : (prefixWord ++ tailWord_970837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970837).length < 2 ^ (prefixWord ++ tailWord_970837).sum := by decide
  have hdescent : baseEnd_970837 < baseStart_970837 := by decide
  rcases family_descends (prefixWord ++ tailWord_970837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970846 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_970846 : Nat := 118140960795 + 970846 * 2 ^ 59
def prefixEnd_970846 : Nat := 4983230072969 + 3 ^ 40 * 970846 * 2
def baseEnd_970846 : Nat := 443120568440012261564593

theorem tailTrace_970846 : CollatzResearch.WordTrace tailWord_970846 prefixEnd_970846 443120568440012261564593 := by
  unfold tailWord_970846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426207830099778017664549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23606441760532149427544261 4426207830099778017664549)
  ·
    refine ⟨829913968143708378312103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4426207830099778017664549 829913968143708378312103)
    ·
      refine ⟨1244870952215562567468155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829913968143708378312103 1244870952215562567468155)
      ·
        refine ⟨1867306428323343851202233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244870952215562567468155 1867306428323343851202233)
        ·
          refine ⟨1400479821242507888401675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867306428323343851202233 1400479821242507888401675)
          ·
            refine ⟨2100719731863761832602513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400479821242507888401675 2100719731863761832602513)
            ·
              refine ⟨1575539798897821374451885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100719731863761832602513 1575539798897821374451885)
              ·
                refine ⟨590827424586683015419457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575539798897821374451885 590827424586683015419457)
                ·
                  refine ⟨443120568440012261564593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590827424586683015419457 443120568440012261564593)
                  ·
                    rfl

theorem cell20_970846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_970846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970846 prefixEnd_970846 := by exact prefixLift 970846
  have htrace : WordTrace (prefixWord ++ tailWord_970846) baseStart_970846 baseEnd_970846 := by
    simpa [prefixWord, tailWord_970846, baseEnd_970846] using wordTrace_append hprefix tailTrace_970846
  have hstable : (prefixWord ++ tailWord_970846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970846).length < 2 ^ (prefixWord ++ tailWord_970846).sum := by decide
  have hdescent : baseEnd_970846 < baseStart_970846 := by decide
  rcases family_descends (prefixWord ++ tailWord_970846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970909 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 2]
def baseStart_970909 : Nat := 118140960795 + 970909 * 2 ^ 59
def prefixEnd_970909 : Nat := 4983230072969 + 3 ^ 40 * 970909 * 2
def baseEnd_970909 : Nat := 443149323356664042464335

theorem tailTrace_970909 : CollatzResearch.WordTrace tailWord_970909 prefixEnd_970909 443149323356664042464335 := by
  unfold tailWord_970909
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411960439569985900859781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23607973626379990600573187 35411960439569985900859781)
  ·
    refine ⟨6639742582419372356411209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35411960439569985900859781 6639742582419372356411209)
    ·
      refine ⟨4979806936814529267308407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6639742582419372356411209 4979806936814529267308407)
      ·
        refine ⟨7469710405221793900962611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979806936814529267308407 7469710405221793900962611)
        ·
          refine ⟨11204565607832690851443917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469710405221793900962611 11204565607832690851443917)
          ·
            refine ⟨4201712102937259069291469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11204565607832690851443917 4201712102937259069291469)
            ·
              refine ⟨1575642038601472150984301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4201712102937259069291469 1575642038601472150984301)
              ·
                refine ⟨590865764475552056619113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575642038601472150984301 590865764475552056619113)
                ·
                  refine ⟨443149323356664042464335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 590865764475552056619113 443149323356664042464335)
                  ·
                    rfl

theorem cell20_970909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_970909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970909 prefixEnd_970909 := by exact prefixLift 970909
  have htrace : WordTrace (prefixWord ++ tailWord_970909) baseStart_970909 baseEnd_970909 := by
    simpa [prefixWord, tailWord_970909, baseEnd_970909] using wordTrace_append hprefix tailTrace_970909
  have hstable : (prefixWord ++ tailWord_970909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970909).length < 2 ^ (prefixWord ++ tailWord_970909).sum := by decide
  have hdescent : baseEnd_970909 < baseStart_970909 := by decide
  rcases family_descends (prefixWord ++ tailWord_970909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970916 : List Nat := [2, 3, 1, 2, 5, 1, 6]
def baseStart_970916 : Nat := 118140960795 + 970916 * 2 ^ 59
def prefixEnd_970916 : Nat := 4983230072969 + 3 ^ 40 * 970916 * 2
def baseEnd_970916 : Nat := 49239168705267014358997

theorem tailTrace_970916 : CollatzResearch.WordTrace tailWord_970916 prefixEnd_970916 49239168705267014358997 := by
  unfold tailWord_970916
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706107875272313048182301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23608143833696417397576401 17706107875272313048182301)
  ·
    refine ⟨6639790453227117393068363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17706107875272313048182301 6639790453227117393068363)
    ·
      refine ⟨9959685679840676089602545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639790453227117393068363 9959685679840676089602545)
      ·
        refine ⟨7469764259880507067201909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9959685679840676089602545 7469764259880507067201909)
        ·
          refine ⟨700290399363797537550179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7469764259880507067201909 700290399363797537550179)
          ·
            refine ⟨1050435599045696306325269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700290399363797537550179 1050435599045696306325269)
            ·
              refine ⟨49239168705267014358997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1050435599045696306325269 49239168705267014358997)
              ·
                rfl

theorem cell20_970916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 6].length) (baseStart_970916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970916 prefixEnd_970916 := by exact prefixLift 970916
  have htrace : WordTrace (prefixWord ++ tailWord_970916) baseStart_970916 baseEnd_970916 := by
    simpa [prefixWord, tailWord_970916, baseEnd_970916] using wordTrace_append hprefix tailTrace_970916
  have hstable : (prefixWord ++ tailWord_970916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970916).length < 2 ^ (prefixWord ++ tailWord_970916).sum := by decide
  have hdescent : baseEnd_970916 < baseStart_970916 := by decide
  rcases family_descends (prefixWord ++ tailWord_970916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970932 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 3]
def baseStart_970932 : Nat := 118140960795 + 970932 * 2 ^ 59
def prefixEnd_970932 : Nat := 4983230072969 + 3 ^ 40 * 970932 * 2
def baseEnd_970932 : Nat := 443159821183378184697575

theorem tailTrace_970932 : CollatzResearch.WordTrace tailWord_970932 prefixEnd_970932 443159821183378184697575 := by
  unfold tailWord_970932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17706399659243330414473525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23608532878991107219298033 17706399659243330414473525)
  ·
    refine ⟨1659974968054062226356893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17706399659243330414473525 1659974968054062226356893)
    ·
      refine ⟨622490613020273334883835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1659974968054062226356893 622490613020273334883835)
      ·
        refine ⟨933735919530410002325753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622490613020273334883835 933735919530410002325753)
        ·
          refine ⟨700301939647807501744315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933735919530410002325753 700301939647807501744315)
          ·
            refine ⟨1050452909471711252616473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700301939647807501744315 1050452909471711252616473)
            ·
              refine ⟨787839682103783439462355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050452909471711252616473 787839682103783439462355)
              ·
                refine ⟨1181759523155675159193533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787839682103783439462355 1181759523155675159193533)
                ·
                  refine ⟨443159821183378184697575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181759523155675159193533 443159821183378184697575)
                  ·
                    rfl

theorem cell20_970932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_970932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_970932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_970932 prefixEnd_970932 := by exact prefixLift 970932
  have htrace : WordTrace (prefixWord ++ tailWord_970932) baseStart_970932 baseEnd_970932 := by
    simpa [prefixWord, tailWord_970932, baseEnd_970932] using wordTrace_append hprefix tailTrace_970932
  have hstable : (prefixWord ++ tailWord_970932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970932).length < 2 ^ (prefixWord ++ tailWord_970932).sum := by decide
  have hdescent : baseEnd_970932 < baseStart_970932 := by decide
  rcases family_descends (prefixWord ++ tailWord_970932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971006 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_971006 : Nat := 118140960795 + 971006 * 2 ^ 59
def prefixEnd_971006 : Nat := 4983230072969 + 3 ^ 40 * 971006 * 2
def baseEnd_971006 : Nat := 443193596799762816230605

theorem tailTrace_971006 : CollatzResearch.WordTrace tailWord_971006 prefixEnd_971006 443193596799762816230605 := by
  unfold tailWord_971006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426937290027321433392609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23610332213479047644760581 4426937290027321433392609)
  ·
    refine ⟨3320202967520491075044457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4426937290027321433392609 3320202967520491075044457)
    ·
      refine ⟨2490152225640368306283343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3320202967520491075044457 2490152225640368306283343)
      ·
        refine ⟨3735228338460552459425015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490152225640368306283343 3735228338460552459425015)
        ·
          refine ⟨5602842507690828689137523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735228338460552459425015 5602842507690828689137523)
          ·
            refine ⟨8404263761536243033706285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602842507690828689137523 8404263761536243033706285)
            ·
              refine ⟨3151598910576091137639857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8404263761536243033706285 3151598910576091137639857)
              ·
                refine ⟨2363699182932068353229893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151598910576091137639857 2363699182932068353229893)
                ·
                  refine ⟨443193596799762816230605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363699182932068353229893 443193596799762816230605)
                  ·
                    rfl

theorem cell20_971006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_971006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971006 prefixEnd_971006 := by exact prefixLift 971006
  have htrace : WordTrace (prefixWord ++ tailWord_971006) baseStart_971006 baseEnd_971006 := by
    simpa [prefixWord, tailWord_971006, baseEnd_971006] using wordTrace_append hprefix tailTrace_971006
  have hstable : (prefixWord ++ tailWord_971006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971006).length < 2 ^ (prefixWord ++ tailWord_971006).sum := by decide
  have hdescent : baseEnd_971006 < baseStart_971006 := by decide
  rcases family_descends (prefixWord ++ tailWord_971006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971037 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_971037 : Nat := 118140960795 + 971037 * 2 ^ 59
def prefixEnd_971037 : Nat := 4983230072969 + 3 ^ 40 * 971037 * 2
def baseEnd_971037 : Nat := 443207746044464486197145

theorem tailTrace_971037 : CollatzResearch.WordTrace tailWord_971037 prefixEnd_971037 443207746044464486197145 := by
  unfold tailWord_971037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35416628983106263761519365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23611085988737509174346243 35416628983106263761519365)
  ·
    refine ⟨6640617934332424455284881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35416628983106263761519365 6640617934332424455284881)
    ·
      refine ⟨4980463450749318341463661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6640617934332424455284881 4980463450749318341463661)
      ·
        refine ⟨1867673794030994378048873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4980463450749318341463661 1867673794030994378048873)
        ·
          refine ⟨1400755345523245783536655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867673794030994378048873 1400755345523245783536655)
          ·
            refine ⟨2101133018284868675304983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400755345523245783536655 2101133018284868675304983)
            ·
              refine ⟨3151699527427303012957475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101133018284868675304983 3151699527427303012957475)
              ·
                refine ⟨4727549291140954519436213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151699527427303012957475 4727549291140954519436213)
                ·
                  refine ⟨443207746044464486197145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4727549291140954519436213 443207746044464486197145)
                  ·
                    rfl

theorem cell20_971037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_971037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971037 prefixEnd_971037 := by exact prefixLift 971037
  have htrace : WordTrace (prefixWord ++ tailWord_971037) baseStart_971037 baseEnd_971037 := by
    simpa [prefixWord, tailWord_971037, baseEnd_971037] using wordTrace_append hprefix tailTrace_971037
  have hstable : (prefixWord ++ tailWord_971037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971037).length < 2 ^ (prefixWord ++ tailWord_971037).sum := by decide
  have hdescent : baseEnd_971037 < baseStart_971037 := by decide
  rcases family_descends (prefixWord ++ tailWord_971037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971044 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_971044 : Nat := 118140960795 + 971044 * 2 ^ 59
def prefixEnd_971044 : Nat := 4983230072969 + 3 ^ 40 * 971044 * 2
def baseEnd_971044 : Nat := 443210941035203572963783

theorem tailTrace_971044 : CollatzResearch.WordTrace tailWord_971044 prefixEnd_971044 443210941035203572963783 := by
  unfold tailWord_971044
  simp only [CollatzResearch.WordTrace]
  refine ⟨17708442147040451978512093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23611256196053935971349457 17708442147040451978512093)
  ·
    refine ⟨6640665805140169491942035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17708442147040451978512093 6640665805140169491942035)
    ·
      refine ⟨9960998707710254237913053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6640665805140169491942035 9960998707710254237913053)
      ·
        refine ⟨3735374515391345339217395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9960998707710254237913053 3735374515391345339217395)
        ·
          refine ⟨5603061773087018008826093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735374515391345339217395 5603061773087018008826093)
          ·
            refine ⟨2101148164907631753309785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5603061773087018008826093 2101148164907631753309785)
            ·
              refine ⟨1575861123680723814982339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101148164907631753309785 1575861123680723814982339)
              ·
                refine ⟨2363791685521085722473509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575861123680723814982339 2363791685521085722473509)
                ·
                  refine ⟨443210941035203572963783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363791685521085722473509 443210941035203572963783)
                  ·
                    rfl

theorem cell20_971044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_971044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971044 prefixEnd_971044 := by exact prefixLift 971044
  have htrace : WordTrace (prefixWord ++ tailWord_971044) baseStart_971044 baseEnd_971044 := by
    simpa [prefixWord, tailWord_971044, baseEnd_971044] using wordTrace_append hprefix tailTrace_971044
  have hstable : (prefixWord ++ tailWord_971044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971044).length < 2 ^ (prefixWord ++ tailWord_971044).sum := by decide
  have hdescent : baseEnd_971044 < baseStart_971044 := by decide
  rcases family_descends (prefixWord ++ tailWord_971044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971079 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_971079 : Nat := 118140960795 + 971079 * 2 ^ 59
def prefixEnd_971079 : Nat := 4983230072969 + 3 ^ 40 * 971079 * 2
def baseEnd_971079 : Nat := 443226915988899006796973

theorem tailTrace_971079 : CollatzResearch.WordTrace tailWord_971079 prefixEnd_971079 443226915988899006796973 := by
  unfold tailWord_971079
  simp only [CollatzResearch.WordTrace]
  refine ⟨35418160848954104934548291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23612107232636069956365527 35418160848954104934548291)
  ·
    refine ⟨53127241273431157401822437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35418160848954104934548291 53127241273431157401822437)
    ·
      refine ⟨9961357738768342012841707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53127241273431157401822437 9961357738768342012841707)
      ·
        refine ⟨14942036608152513019262561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9961357738768342012841707 14942036608152513019262561)
        ·
          refine ⟨11206527456114384764446921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14942036608152513019262561 11206527456114384764446921)
          ·
            refine ⟨8404895592085788573335191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11206527456114384764446921 8404895592085788573335191)
            ·
              refine ⟨12607343388128682860002787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8404895592085788573335191 12607343388128682860002787)
              ·
                refine ⟨18911015082193024290004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12607343388128682860002787 18911015082193024290004181)
                ·
                  refine ⟨443226915988899006796973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18911015082193024290004181 443226915988899006796973)
                  ·
                    rfl

theorem cell20_971079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_971079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971079 prefixEnd_971079 := by exact prefixLift 971079
  have htrace : WordTrace (prefixWord ++ tailWord_971079) baseStart_971079 baseEnd_971079 := by
    simpa [prefixWord, tailWord_971079, baseEnd_971079] using wordTrace_append hprefix tailTrace_971079
  have hstable : (prefixWord ++ tailWord_971079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971079).length < 2 ^ (prefixWord ++ tailWord_971079).sum := by decide
  have hdescent : baseEnd_971079 < baseStart_971079 := by decide
  rcases family_descends (prefixWord ++ tailWord_971079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971103 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_971103 : Nat := 118140960795 + 971103 * 2 ^ 59
def prefixEnd_971103 : Nat := 4983230072969 + 3 ^ 40 * 971103 * 2
def baseEnd_971103 : Nat := 443237870242861589996875

theorem tailTrace_971103 : CollatzResearch.WordTrace tailWord_971103 prefixEnd_971103 443237870242861589996875 := by
  unfold tailWord_971103
  simp only [CollatzResearch.WordTrace]
  refine ⟨35419036200867157033421963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23612690800578104688947975 35419036200867157033421963)
  ·
    refine ⟨53128554301300735550132945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35419036200867157033421963 53128554301300735550132945)
    ·
      refine ⟨39846415725975551662599709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53128554301300735550132945 39846415725975551662599709)
      ·
        refine ⟨14942405897240831873474891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39846415725975551662599709 14942405897240831873474891)
        ·
          refine ⟨22413608845861247810212337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14942405897240831873474891 22413608845861247810212337)
          ·
            refine ⟨16810206634395935857659253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22413608845861247810212337 16810206634395935857659253)
            ·
              refine ⟨1575956871974618986655555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16810206634395935857659253 1575956871974618986655555)
              ·
                refine ⟨2363935307961928479983333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575956871974618986655555 2363935307961928479983333)
                ·
                  refine ⟨443237870242861589996875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2363935307961928479983333 443237870242861589996875)
                  ·
                    rfl

theorem cell20_971103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_971103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971103 prefixEnd_971103 := by exact prefixLift 971103
  have htrace : WordTrace (prefixWord ++ tailWord_971103) baseStart_971103 baseEnd_971103 := by
    simpa [prefixWord, tailWord_971103, baseEnd_971103] using wordTrace_append hprefix tailTrace_971103
  have hstable : (prefixWord ++ tailWord_971103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971103).length < 2 ^ (prefixWord ++ tailWord_971103).sum := by decide
  have hdescent : baseEnd_971103 < baseStart_971103 := by decide
  rcases family_descends (prefixWord ++ tailWord_971103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971172 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_971172 : Nat := 118140960795 + 971172 * 2 ^ 59
def prefixEnd_971172 : Nat := 4983230072969 + 3 ^ 40 * 971172 * 2
def baseEnd_971172 : Nat := 443269363723004016696593

theorem tailTrace_971172 : CollatzResearch.WordTrace tailWord_971172 prefixEnd_971172 443269363723004016696593 := by
  unfold tailWord_971172
  simp only [CollatzResearch.WordTrace]
  refine ⟨17710776418808590908841885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23614368558411454545122513 17710776418808590908841885)
  ·
    refine ⟨6641541157053221590815707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17710776418808590908841885 6641541157053221590815707)
    ·
      refine ⟨9962311735579832386223561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6641541157053221590815707 9962311735579832386223561)
      ·
        refine ⟨7471733801684874289667671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9962311735579832386223561 7471733801684874289667671)
        ·
          refine ⟨11207600702527311434501507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7471733801684874289667671 11207600702527311434501507)
          ·
            refine ⟨16811401053790967151752261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11207600702527311434501507 16811401053790967151752261)
            ·
              refine ⟨3152137697585806340953549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16811401053790967151752261 3152137697585806340953549)
              ·
                refine ⟨1182051636594677377857581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3152137697585806340953549 1182051636594677377857581)
                ·
                  refine ⟨443269363723004016696593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182051636594677377857581 443269363723004016696593)
                  ·
                    rfl

theorem cell20_971172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_971172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971172 prefixEnd_971172 := by exact prefixLift 971172
  have htrace : WordTrace (prefixWord ++ tailWord_971172) baseStart_971172 baseEnd_971172 := by
    simpa [prefixWord, tailWord_971172, baseEnd_971172] using wordTrace_append hprefix tailTrace_971172
  have hstable : (prefixWord ++ tailWord_971172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971172).length < 2 ^ (prefixWord ++ tailWord_971172).sum := by decide
  have hdescent : baseEnd_971172 < baseStart_971172 := by decide
  rcases family_descends (prefixWord ++ tailWord_971172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971178 : List Nat := [3, 1, 6, 1, 1, 1, 3, 4]
def baseStart_971178 : Nat := 118140960795 + 971178 * 2 ^ 59
def prefixEnd_971178 : Nat := 4983230072969 + 3 ^ 40 * 971178 * 2
def baseEnd_971178 : Nat := 147757367428831554165523

theorem tailTrace_971178 : CollatzResearch.WordTrace tailWord_971178 prefixEnd_971178 147757367428831554165523 := by
  unfold tailWord_971178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855442918898861210600547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23614514450396963228268125 8855442918898861210600547)
  ·
    refine ⟨13283164378348291815900821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8855442918898861210600547 13283164378348291815900821)
    ·
      refine ⟨622648330235076178870351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13283164378348291815900821 622648330235076178870351)
      ·
        refine ⟨933972495352614268305527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622648330235076178870351 933972495352614268305527)
        ·
          refine ⟨1400958743028921402458291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933972495352614268305527 1400958743028921402458291)
          ·
            refine ⟨2101438114543382103687437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400958743028921402458291 2101438114543382103687437)
            ·
              refine ⟨788039292953768288882789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101438114543382103687437 788039292953768288882789)
              ·
                refine ⟨147757367428831554165523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788039292953768288882789 147757367428831554165523)
                ·
                  rfl

theorem cell20_971178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_971178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971178 prefixEnd_971178 := by exact prefixLift 971178
  have htrace : WordTrace (prefixWord ++ tailWord_971178) baseStart_971178 baseEnd_971178 := by
    simpa [prefixWord, tailWord_971178, baseEnd_971178] using wordTrace_append hprefix tailTrace_971178
  have hstable : (prefixWord ++ tailWord_971178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971178).length < 2 ^ (prefixWord ++ tailWord_971178).sum := by decide
  have hdescent : baseEnd_971178 < baseStart_971178 := by decide
  rcases family_descends (prefixWord ++ tailWord_971178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971200 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_971200 : Nat := 118140960795 + 971200 * 2 ^ 59
def prefixEnd_971200 : Nat := 4983230072969 + 3 ^ 40 * 971200 * 2
def baseEnd_971200 : Nat := 443282143685960363763145

theorem tailTrace_971200 : CollatzResearch.WordTrace tailWord_971200 prefixEnd_971200 443282143685960363763145 := by
  unfold tailWord_971200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711287040757871299851527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23615049387677161733135369 17711287040757871299851527)
  ·
    refine ⟨26566930561136806949777291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711287040757871299851527 26566930561136806949777291)
    ·
      refine ⟨39850395841705210424665937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26566930561136806949777291 39850395841705210424665937)
      ·
        refine ⟨29887796881278907818499453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39850395841705210424665937 29887796881278907818499453)
        ·
          refine ⟨11207923830479590431937295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29887796881278907818499453 11207923830479590431937295)
          ·
            refine ⟨16811885745719385647905943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11207923830479590431937295 16811885745719385647905943)
            ·
              refine ⟨25217828618579078471858915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16811885745719385647905943 25217828618579078471858915)
              ·
                refine ⟨37826742927868617707788373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25217828618579078471858915 37826742927868617707788373)
                ·
                  refine ⟨443282143685960363763145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37826742927868617707788373 443282143685960363763145)
                  ·
                    rfl

theorem cell20_971200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_971200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971200 prefixEnd_971200 := by exact prefixLift 971200
  have htrace : WordTrace (prefixWord ++ tailWord_971200) baseStart_971200 baseEnd_971200 := by
    simpa [prefixWord, tailWord_971200, baseEnd_971200] using wordTrace_append hprefix tailTrace_971200
  have hstable : (prefixWord ++ tailWord_971200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971200).length < 2 ^ (prefixWord ++ tailWord_971200).sum := by decide
  have hdescent : baseEnd_971200 < baseStart_971200 := by decide
  rcases family_descends (prefixWord ++ tailWord_971200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971237 : List Nat := [1, 3, 1, 5, 3, 1, 2, 4]
def baseStart_971237 : Nat := 118140960795 + 971237 * 2 ^ 59
def prefixEnd_971237 : Nat := 4983230072969 + 3 ^ 40 * 971237 * 2
def baseEnd_971237 : Nat := 147766343831384226509887

theorem tailTrace_971237 : CollatzResearch.WordTrace tailWord_971237 prefixEnd_971237 147766343831384226509887 := by
  unfold tailWord_971237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35423923582381697918799965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23615949054921131945866643 35423923582381697918799965)
  ·
    refine ⟨13283971343393136719549987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35423923582381697918799965 13283971343393136719549987)
    ·
      refine ⟨19925957015089705079324981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13283971343393136719549987 19925957015089705079324981)
      ·
        refine ⟨1868058470164659851186717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19925957015089705079324981 1868058470164659851186717)
        ·
          refine ⟨700521926311747444195019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1868058470164659851186717 700521926311747444195019)
          ·
            refine ⟨1050782889467621166292529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700521926311747444195019 1050782889467621166292529)
            ·
              refine ⟨788087167100715874719397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050782889467621166292529 788087167100715874719397)
              ·
                refine ⟨147766343831384226509887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788087167100715874719397 147766343831384226509887)
                ·
                  rfl

theorem cell20_971237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].length) (baseStart_971237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971237 prefixEnd_971237 := by exact prefixLift 971237
  have htrace : WordTrace (prefixWord ++ tailWord_971237) baseStart_971237 baseEnd_971237 := by
    simpa [prefixWord, tailWord_971237, baseEnd_971237] using wordTrace_append hprefix tailTrace_971237
  have hstable : (prefixWord ++ tailWord_971237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971237).length < 2 ^ (prefixWord ++ tailWord_971237).sum := by decide
  have hdescent : baseEnd_971237 < baseStart_971237 := by decide
  rcases family_descends (prefixWord ++ tailWord_971237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971268 : List Nat := [2, 3, 2, 3, 1, 2, 3, 2, 2]
def baseStart_971268 : Nat := 118140960795 + 971268 * 2 ^ 59
def prefixEnd_971268 : Nat := 4983230072969 + 3 ^ 40 * 971268 * 2
def baseEnd_971268 : Nat := 443313180738854349496201

theorem tailTrace_971268 : CollatzResearch.WordTrace tailWord_971268 prefixEnd_971268 443313180738854349496201 := by
  unfold tailWord_971268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17712527122634695106589229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23616702830179593475452305 17712527122634695106589229)
  ·
    refine ⟨6642197670988010664970961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17712527122634695106589229 6642197670988010664970961)
    ·
      refine ⟨4981648253241007998728221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6642197670988010664970961 4981648253241007998728221)
      ·
        refine ⟨1868118094965377999523083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4981648253241007998728221 1868118094965377999523083)
        ·
          refine ⟨2802177142448066999284625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868118094965377999523083 2802177142448066999284625)
          ·
            refine ⟨2101632856836050249463469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802177142448066999284625 2101632856836050249463469)
            ·
              refine ⟨788112321313518843548801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2101632856836050249463469 788112321313518843548801)
              ·
                refine ⟨591084240985139132661601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788112321313518843548801 591084240985139132661601)
                ·
                  refine ⟨443313180738854349496201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591084240985139132661601 443313180738854349496201)
                  ·
                    rfl

theorem cell20_971268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_971268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971268 prefixEnd_971268 := by exact prefixLift 971268
  have htrace : WordTrace (prefixWord ++ tailWord_971268) baseStart_971268 baseEnd_971268 := by
    simpa [prefixWord, tailWord_971268, baseEnd_971268] using wordTrace_append hprefix tailTrace_971268
  have hstable : (prefixWord ++ tailWord_971268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971268).length < 2 ^ (prefixWord ++ tailWord_971268).sum := by decide
  have hdescent : baseEnd_971268 < baseStart_971268 := by decide
  rcases family_descends (prefixWord ++ tailWord_971268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971269 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_971269 : Nat := 118140960795 + 971269 * 2 ^ 59
def prefixEnd_971269 : Nat := 4983230072969 + 3 ^ 40 * 971269 * 2
def baseEnd_971269 : Nat := 443313637166102790462863

theorem tailTrace_971269 : CollatzResearch.WordTrace tailWord_971269 prefixEnd_971269 443313637166102790462863 := by
  unfold tailWord_971269
  simp only [CollatzResearch.WordTrace]
  refine ⟨35425090718265767383964861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23616727145510511589309907 35425090718265767383964861)
  ·
    refine ⟨13284409019349662768986823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35425090718265767383964861 13284409019349662768986823)
    ·
      refine ⟨19926613529024494153480235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13284409019349662768986823 19926613529024494153480235)
      ·
        refine ⟨29889920293536741230220353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19926613529024494153480235 29889920293536741230220353)
        ·
          refine ⟨22417440220152555922665265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29889920293536741230220353 22417440220152555922665265)
          ·
            refine ⟨16813080165114416941998949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22417440220152555922665265 16813080165114416941998949)
            ·
              refine ⟨3152452530958953176624803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16813080165114416941998949 3152452530958953176624803)
              ·
                refine ⟨4728678796438429764937205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152452530958953176624803 4728678796438429764937205)
                ·
                  refine ⟨443313637166102790462863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4728678796438429764937205 443313637166102790462863)
                  ·
                    rfl

theorem cell20_971269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_971269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971269 prefixEnd_971269 := by exact prefixLift 971269
  have htrace : WordTrace (prefixWord ++ tailWord_971269) baseStart_971269 baseEnd_971269 := by
    simpa [prefixWord, tailWord_971269, baseEnd_971269] using wordTrace_append hprefix tailTrace_971269
  have hstable : (prefixWord ++ tailWord_971269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971269).length < 2 ^ (prefixWord ++ tailWord_971269).sum := by decide
  have hdescent : baseEnd_971269 < baseStart_971269 := by decide
  rcases family_descends (prefixWord ++ tailWord_971269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971324 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_971324 : Nat := 118140960795 + 971324 * 2 ^ 59
def prefixEnd_971324 : Nat := 4983230072969 + 3 ^ 40 * 971324 * 2
def baseEnd_971324 : Nat := 443338740664767043629305

theorem tailTrace_971324 : CollatzResearch.WordTrace tailWord_971324 prefixEnd_971324 443338740664767043629305 := by
  unfold tailWord_971324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17713548366533255888608513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23618064488711007851478017 17713548366533255888608513)
  ·
    refine ⟨13285161274899941916456385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17713548366533255888608513 13285161274899941916456385)
    ·
      refine ⟨9963870956174956437342289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13285161274899941916456385 9963870956174956437342289)
      ·
        refine ⟨7472903217131217328006717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9963870956174956437342289 7472903217131217328006717)
        ·
          refine ⟨2802338706424206498002519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7472903217131217328006717 2802338706424206498002519)
          ·
            refine ⟨4203508059636309747003779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802338706424206498002519 4203508059636309747003779)
            ·
              refine ⟨6305262089454464620505669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203508059636309747003779 6305262089454464620505669)
              ·
                refine ⟨1182236641772712116344813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6305262089454464620505669 1182236641772712116344813)
                ·
                  refine ⟨443338740664767043629305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182236641772712116344813 443338740664767043629305)
                  ·
                    rfl

theorem cell20_971324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_971324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971324 prefixEnd_971324 := by exact prefixLift 971324
  have htrace : WordTrace (prefixWord ++ tailWord_971324) baseStart_971324 baseEnd_971324 := by
    simpa [prefixWord, tailWord_971324, baseEnd_971324] using wordTrace_append hprefix tailTrace_971324
  have hstable : (prefixWord ++ tailWord_971324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971324).length < 2 ^ (prefixWord ++ tailWord_971324).sum := by decide
  have hdescent : baseEnd_971324 < baseStart_971324 := by decide
  rcases family_descends (prefixWord ++ tailWord_971324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971334 : List Nat := [6, 1, 1, 1, 2, 1, 3, 5]
def baseStart_971334 : Nat := 118140960795 + 971334 * 2 ^ 59
def prefixEnd_971334 : Nat := 4983230072969 + 3 ^ 40 * 971334 * 2
def baseEnd_971334 : Nat := 147781101645750484431977

theorem tailTrace_971334 : CollatzResearch.WordTrace tailWord_971334 prefixEnd_971334 147781101645750484431977 := by
  unfold tailWord_971334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107108170719696358908783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23618307642020188990054037 1107108170719696358908783)
  ·
    refine ⟨1660662256079544538363175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107108170719696358908783 1660662256079544538363175)
    ·
      refine ⟨2490993384119316807544763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660662256079544538363175 2490993384119316807544763)
      ·
        refine ⟨3736490076178975211317145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490993384119316807544763 3736490076178975211317145)
        ·
          refine ⟨2802367557134231408487859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3736490076178975211317145 2802367557134231408487859)
          ·
            refine ⟨4203551335701347112731789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802367557134231408487859 4203551335701347112731789)
            ·
              refine ⟨1576331750888005167274421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4203551335701347112731789 1576331750888005167274421)
              ·
                refine ⟨147781101645750484431977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1576331750888005167274421 147781101645750484431977)
                ·
                  rfl

theorem cell20_971334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_971334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971334 prefixEnd_971334 := by exact prefixLift 971334
  have htrace : WordTrace (prefixWord ++ tailWord_971334) baseStart_971334 baseEnd_971334 := by
    simpa [prefixWord, tailWord_971334, baseEnd_971334] using wordTrace_append hprefix tailTrace_971334
  have hstable : (prefixWord ++ tailWord_971334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971334).length < 2 ^ (prefixWord ++ tailWord_971334).sum := by decide
  have hdescent : baseEnd_971334 < baseStart_971334 := by decide
  rcases family_descends (prefixWord ++ tailWord_971334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971338 : List Nat := [3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_971338 : Nat := 118140960795 + 971338 * 2 ^ 59
def prefixEnd_971338 : Nat := 4983230072969 + 3 ^ 40 * 971338 * 2
def baseEnd_971338 : Nat := 147781710215415072387527

theorem tailTrace_971338 : CollatzResearch.WordTrace tailWord_971338 prefixEnd_971338 147781710215415072387527 := by
  unfold tailWord_971338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856901838753948042056667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23618404903343861445484445 8856901838753948042056667)
  ·
    refine ⟨13285352758130922063085001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856901838753948042056667 13285352758130922063085001)
    ·
      refine ⟨9964014568598191547313751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13285352758130922063085001 9964014568598191547313751)
      ·
        refine ⟨14946021852897287320970627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9964014568598191547313751 14946021852897287320970627)
        ·
          refine ⟨22419032779345930981455941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14946021852897287320970627 22419032779345930981455941)
          ·
            refine ⟨4203568646127362059022989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22419032779345930981455941 4203568646127362059022989)
            ·
              refine ⟨1576338242297760772133621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4203568646127362059022989 1576338242297760772133621)
              ·
                refine ⟨147781710215415072387527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1576338242297760772133621 147781710215415072387527)
                ·
                  rfl

theorem cell20_971338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_971338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971338 prefixEnd_971338 := by exact prefixLift 971338
  have htrace : WordTrace (prefixWord ++ tailWord_971338) baseStart_971338 baseEnd_971338 := by
    simpa [prefixWord, tailWord_971338, baseEnd_971338] using wordTrace_append hprefix tailTrace_971338
  have hstable : (prefixWord ++ tailWord_971338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971338).length < 2 ^ (prefixWord ++ tailWord_971338).sum := by decide
  have hdescent : baseEnd_971338 < baseStart_971338 := by decide
  rcases family_descends (prefixWord ++ tailWord_971338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971341 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_971341 : Nat := 118140960795 + 971341 * 2 ^ 59
def prefixEnd_971341 : Nat := 4983230072969 + 3 ^ 40 * 971341 * 2
def baseEnd_971341 : Nat := 443346499927990540062569

theorem tailTrace_971341 : CollatzResearch.WordTrace tailWord_971341 prefixEnd_971341 443346499927990540062569 := by
  unfold tailWord_971341
  simp only [CollatzResearch.WordTrace]
  refine ⟨35427716774004923680585877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23618477849336615787057251 35427716774004923680585877)
  ·
    refine ⟨1660674223781480797527463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35427716774004923680585877 1660674223781480797527463)
    ·
      refine ⟨2491011335672221196291195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660674223781480797527463 2491011335672221196291195)
      ·
        refine ⟨3736517003508331794436793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491011335672221196291195 3736517003508331794436793)
        ·
          refine ⟨2802387752631248845827595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3736517003508331794436793 2802387752631248845827595)
          ·
            refine ⟨4203581628946873268741393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802387752631248845827595 4203581628946873268741393)
            ·
              refine ⟨3152686221710154951556045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4203581628946873268741393 3152686221710154951556045)
              ·
                refine ⟨1182257333141308106833517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3152686221710154951556045 1182257333141308106833517)
                ·
                  refine ⟨443346499927990540062569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182257333141308106833517 443346499927990540062569)
                  ·
                    rfl

theorem cell20_971341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_971341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971341 prefixEnd_971341 := by exact prefixLift 971341
  have htrace : WordTrace (prefixWord ++ tailWord_971341) baseStart_971341 baseEnd_971341 := by
    simpa [prefixWord, tailWord_971341, baseEnd_971341] using wordTrace_append hprefix tailTrace_971341
  have hstable : (prefixWord ++ tailWord_971341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971341).length < 2 ^ (prefixWord ++ tailWord_971341).sum := by decide
  have hdescent : baseEnd_971341 < baseStart_971341 := by decide
  rcases family_descends (prefixWord ++ tailWord_971341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971352 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_971352 : Nat := 118140960795 + 971352 * 2 ^ 59
def prefixEnd_971352 : Nat := 4983230072969 + 3 ^ 40 * 971352 * 2
def baseEnd_971352 : Nat := 443351520627723390695857

theorem tailTrace_971352 : CollatzResearch.WordTrace tailWord_971352 prefixEnd_971352 443351520627723390695857 := by
  unfold tailWord_971352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714058988482536279618155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23618745317976715039490873 17714058988482536279618155)
  ·
    refine ⟨26571088482723804419427233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17714058988482536279618155 26571088482723804419427233)
    ·
      refine ⟨19928316362042853314570425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26571088482723804419427233 19928316362042853314570425)
      ·
        refine ⟨14946237271532139985927819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19928316362042853314570425 14946237271532139985927819)
        ·
          refine ⟨22419355907298209978891729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14946237271532139985927819 22419355907298209978891729)
          ·
            refine ⟨16814516930473657484168797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22419355907298209978891729 16814516930473657484168797)
            ·
              refine ⟨6305443848927621556563299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16814516930473657484168797 6305443848927621556563299)
              ·
                refine ⟨9458165773391432334844949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305443848927621556563299 9458165773391432334844949)
                ·
                  refine ⟨443351520627723390695857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9458165773391432334844949 443351520627723390695857)
                  ·
                    rfl

theorem cell20_971352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_971352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971352 prefixEnd_971352 := by exact prefixLift 971352
  have htrace : WordTrace (prefixWord ++ tailWord_971352) baseStart_971352 baseEnd_971352 := by
    simpa [prefixWord, tailWord_971352, baseEnd_971352] using wordTrace_append hprefix tailTrace_971352
  have hstable : (prefixWord ++ tailWord_971352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971352).length < 2 ^ (prefixWord ++ tailWord_971352).sum := by decide
  have hdescent : baseEnd_971352 < baseStart_971352 := by decide
  rcases family_descends (prefixWord ++ tailWord_971352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971359 : List Nat := [1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_971359 : Nat := 118140960795 + 971359 * 2 ^ 59
def prefixEnd_971359 : Nat := 4983230072969 + 3 ^ 40 * 971359 * 2
def baseEnd_971359 : Nat := 147784905206154159154165

theorem tailTrace_971359 : CollatzResearch.WordTrace tailWord_971359 prefixEnd_971359 147784905206154159154165 := by
  unfold tailWord_971359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35428373287939712754741131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23618915525293141836494087 35428373287939712754741131)
  ·
    refine ⟨53142559931909569132111697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35428373287939712754741131 53142559931909569132111697)
    ·
      refine ⟨39856919948932176849083773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53142559931909569132111697 39856919948932176849083773)
      ·
        refine ⟨14946344980849566318406415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39856919948932176849083773 14946344980849566318406415)
        ·
          refine ⟨22419517471274349477609623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14946344980849566318406415 22419517471274349477609623)
          ·
            refine ⟨33629276206911524216414435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22419517471274349477609623 33629276206911524216414435)
            ·
              refine ⟨50443914310367286324621653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33629276206911524216414435 50443914310367286324621653)
              ·
                refine ⟨147784905206154159154165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50443914310367286324621653 147784905206154159154165)
                ·
                  rfl

theorem cell20_971359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_971359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971359 prefixEnd_971359 := by exact prefixLift 971359
  have htrace : WordTrace (prefixWord ++ tailWord_971359) baseStart_971359 baseEnd_971359 := by
    simpa [prefixWord, tailWord_971359, baseEnd_971359] using wordTrace_append hprefix tailTrace_971359
  have hstable : (prefixWord ++ tailWord_971359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971359).length < 2 ^ (prefixWord ++ tailWord_971359).sum := by decide
  have hdescent : baseEnd_971359 < baseStart_971359 := by decide
  rcases family_descends (prefixWord ++ tailWord_971359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971365 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 2]
def baseStart_971365 : Nat := 118140960795 + 971365 * 2 ^ 59
def prefixEnd_971365 : Nat := 4983230072969 + 3 ^ 40 * 971365 * 2
def baseEnd_971365 : Nat := 443357454181953123262471

theorem tailTrace_971365 : CollatzResearch.WordTrace tailWord_971365 prefixEnd_971365 443357454181953123262471 := by
  unfold tailWord_971365
  simp only [CollatzResearch.WordTrace]
  refine ⟨35428592125917975779459549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23619061417278650519639699 35428592125917975779459549)
  ·
    refine ⟨13285722047219240917297331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35428592125917975779459549 13285722047219240917297331)
    ·
      refine ⟨19928583070828861375945997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13285722047219240917297331 19928583070828861375945997)
      ·
        refine ⟨7473218651560823015979749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19928583070828861375945997 7473218651560823015979749)
        ·
          refine ⟨1401228497167654315496203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7473218651560823015979749 1401228497167654315496203)
          ·
            refine ⟨2101842745751481473244305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401228497167654315496203 2101842745751481473244305)
            ·
              refine ⟨1576382059313611104933229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101842745751481473244305 1576382059313611104933229)
              ·
                refine ⟨591143272242604164349961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1576382059313611104933229 591143272242604164349961)
                ·
                  refine ⟨443357454181953123262471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591143272242604164349961 443357454181953123262471)
                  ·
                    rfl

theorem cell20_971365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_971365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971365 prefixEnd_971365 := by exact prefixLift 971365
  have htrace : WordTrace (prefixWord ++ tailWord_971365) baseStart_971365 baseEnd_971365 := by
    simpa [prefixWord, tailWord_971365, baseEnd_971365] using wordTrace_append hprefix tailTrace_971365
  have hstable : (prefixWord ++ tailWord_971365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971365).length < 2 ^ (prefixWord ++ tailWord_971365).sum := by decide
  have hdescent : baseEnd_971365 < baseStart_971365 := by decide
  rcases family_descends (prefixWord ++ tailWord_971365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971376 : List Nat := [2, 1, 1, 1, 7, 1, 7]
def baseStart_971376 : Nat := 118140960795 + 971376 * 2 ^ 59
def prefixEnd_971376 : Nat := 4983230072969 + 3 ^ 40 * 971376 * 2
def baseEnd_971376 : Nat := 49262497209076219321751

theorem tailTrace_971376 : CollatzResearch.WordTrace tailWord_971376 prefixEnd_971376 49262497209076219321751 := by
  unfold tailWord_971376
  simp only [CollatzResearch.WordTrace]
  refine ⟨17714496664439062329054991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23619328885918749772073321 17714496664439062329054991)
  ·
    refine ⟨26571744996658593493582487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17714496664439062329054991 26571744996658593493582487)
    ·
      refine ⟨39857617494987890240373731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26571744996658593493582487 39857617494987890240373731)
      ·
        refine ⟨59786426242481835360560597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39857617494987890240373731 59786426242481835360560597)
        ·
          refine ⟨1401244365058168016263139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59786426242481835360560597 1401244365058168016263139)
          ·
            refine ⟨2101866547587252024394709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401244365058168016263139 2101866547587252024394709)
            ·
              refine ⟨49262497209076219321751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2101866547587252024394709 49262497209076219321751)
              ·
                rfl

theorem cell20_971376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 7].length) (baseStart_971376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971376 prefixEnd_971376 := by exact prefixLift 971376
  have htrace : WordTrace (prefixWord ++ tailWord_971376) baseStart_971376 baseEnd_971376 := by
    simpa [prefixWord, tailWord_971376, baseEnd_971376] using wordTrace_append hprefix tailTrace_971376
  have hstable : (prefixWord ++ tailWord_971376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971376).length < 2 ^ (prefixWord ++ tailWord_971376).sum := by decide
  have hdescent : baseEnd_971376 < baseStart_971376 := by decide
  rcases family_descends (prefixWord ++ tailWord_971376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971410 : List Nat := [3, 2, 3, 1, 2, 3, 2, 4]
def baseStart_971410 : Nat := 118140960795 + 971410 * 2 ^ 59
def prefixEnd_971410 : Nat := 4983230072969 + 3 ^ 40 * 971410 * 2
def baseEnd_971410 : Nat := 147792664469377655587429

theorem tailTrace_971410 : CollatzResearch.WordTrace tailWord_971410 prefixEnd_971410 147792664469377655587429 := by
  unfold tailWord_971410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8857558352688737116211921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23620155607169965643231789 8857558352688737116211921)
  ·
    refine ⟨6643168764516552837158941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8857558352688737116211921 6643168764516552837158941)
    ·
      refine ⟨2491188286693707313934603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6643168764516552837158941 2491188286693707313934603)
      ·
        refine ⟨3736782430040560970901905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491188286693707313934603 3736782430040560970901905)
        ·
          refine ⟨2802586822530420728176429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3736782430040560970901905 2802586822530420728176429)
          ·
            refine ⟨1050970058448907773066161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2802586822530420728176429 1050970058448907773066161)
            ·
              refine ⟨788227543836680829799621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050970058448907773066161 788227543836680829799621)
              ·
                refine ⟨147792664469377655587429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788227543836680829799621 147792664469377655587429)
                ·
                  rfl

theorem cell20_971410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_971410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971410 prefixEnd_971410 := by exact prefixLift 971410
  have htrace : WordTrace (prefixWord ++ tailWord_971410) baseStart_971410 baseEnd_971410 := by
    simpa [prefixWord, tailWord_971410, baseEnd_971410] using wordTrace_append hprefix tailTrace_971410
  have hstable : (prefixWord ++ tailWord_971410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971410).length < 2 ^ (prefixWord ++ tailWord_971410).sum := by decide
  have hdescent : baseEnd_971410 < baseStart_971410 := by decide
  rcases family_descends (prefixWord ++ tailWord_971410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971421 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_971421 : Nat := 118140960795 + 971421 * 2 ^ 59
def prefixEnd_971421 : Nat := 4983230072969 + 3 ^ 40 * 971421 * 2
def baseEnd_971421 : Nat := 443383014107865817395575

theorem tailTrace_971421 : CollatzResearch.WordTrace tailWord_971421 prefixEnd_971421 443383014107865817395575 := by
  unfold tailWord_971421
  simp only [CollatzResearch.WordTrace]
  refine ⟨35430634613715097343498117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23620423075810064895665411 35430634613715097343498117)
  ·
    refine ⟨6643243990071580751905897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35430634613715097343498117 6643243990071580751905897)
    ·
      refine ⟨4982432992553685563929423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6643243990071580751905897 4982432992553685563929423)
      ·
        refine ⟨7473649488830528345894135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982432992553685563929423 7473649488830528345894135)
        ·
          refine ⟨11210474233245792518841203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473649488830528345894135 11210474233245792518841203)
          ·
            refine ⟨16815711349868688778261805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11210474233245792518841203 16815711349868688778261805)
            ·
              refine ⟨6305891756200758291848177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16815711349868688778261805 6305891756200758291848177)
              ·
                refine ⟨4729418817150568718886133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6305891756200758291848177 4729418817150568718886133)
                ·
                  refine ⟨443383014107865817395575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4729418817150568718886133 443383014107865817395575)
                  ·
                    rfl

theorem cell20_971421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_971421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971421 prefixEnd_971421 := by exact prefixLift 971421
  have htrace : WordTrace (prefixWord ++ tailWord_971421) baseStart_971421 baseEnd_971421 := by
    simpa [prefixWord, tailWord_971421, baseEnd_971421] using wordTrace_append hprefix tailTrace_971421
  have hstable : (prefixWord ++ tailWord_971421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971421).length < 2 ^ (prefixWord ++ tailWord_971421).sum := by decide
  have hdescent : baseEnd_971421 < baseStart_971421 := by decide
  rcases family_descends (prefixWord ++ tailWord_971421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971441 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 4]
def baseStart_971441 : Nat := 118140960795 + 971441 * 2 ^ 59
def prefixEnd_971441 : Nat := 4983230072969 + 3 ^ 40 * 971441 * 2
def baseEnd_971441 : Nat := 443392142652834636728827

theorem tailTrace_971441 : CollatzResearch.WordTrace tailWord_971441 prefixEnd_971441 443392142652834636728827 := by
  unfold tailWord_971441
  simp only [CollatzResearch.WordTrace]
  refine ⟨35431364073642640759226177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23620909382428427172817451 35431364073642640759226177)
  ·
    refine ⟨26573523055231980569419633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35431364073642640759226177 26573523055231980569419633)
    ·
      refine ⟨19930142291423985427064725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26573523055231980569419633 19930142291423985427064725)
      ·
        refine ⟨934225419910499316893659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19930142291423985427064725 934225419910499316893659)
        ·
          refine ⟨1401338129865748975340489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934225419910499316893659 1401338129865748975340489)
          ·
            refine ⟨1051003597399311731505367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401338129865748975340489 1051003597399311731505367)
            ·
              refine ⟨1576505396098967597258051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051003597399311731505367 1576505396098967597258051)
              ·
                refine ⟨2364758094148451395887077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576505396098967597258051 2364758094148451395887077)
                ·
                  refine ⟨443392142652834636728827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2364758094148451395887077 443392142652834636728827)
                  ·
                    rfl

theorem cell20_971441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_971441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971441 prefixEnd_971441 := by exact prefixLift 971441
  have htrace : WordTrace (prefixWord ++ tailWord_971441) baseStart_971441 baseEnd_971441 := by
    simpa [prefixWord, tailWord_971441, baseEnd_971441] using wordTrace_append hprefix tailTrace_971441
  have hstable : (prefixWord ++ tailWord_971441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971441).length < 2 ^ (prefixWord ++ tailWord_971441).sum := by decide
  have hdescent : baseEnd_971441 < baseStart_971441 := by decide
  rcases family_descends (prefixWord ++ tailWord_971441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971452 : List Nat := [2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_971452 : Nat := 118140960795 + 971452 * 2 ^ 59
def prefixEnd_971452 : Nat := 4983230072969 + 3 ^ 40 * 971452 * 2
def baseEnd_971452 : Nat := 147799054450855829120705

theorem tailTrace_971452 : CollatzResearch.WordTrace tailWord_971452 prefixEnd_971452 147799054450855829120705 := by
  unfold tailWord_971452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17715882638301394818938305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23621176851068526425251073 17715882638301394818938305)
  ·
    refine ⟨13286911978726046114203729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17715882638301394818938305 13286911978726046114203729)
    ·
      refine ⟨9965183984044534585652797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13286911978726046114203729 9965183984044534585652797)
      ·
        refine ⟨3736943994016700469619799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9965183984044534585652797 3736943994016700469619799)
        ·
          refine ⟨5605415991025050704429699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736943994016700469619799 5605415991025050704429699)
          ·
            refine ⟨8408123986537576056644549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5605415991025050704429699 8408123986537576056644549)
            ·
              refine ⟨1576523247475795510620853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8408123986537576056644549 1576523247475795510620853)
              ·
                refine ⟨147799054450855829120705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1576523247475795510620853 147799054450855829120705)
                ·
                  rfl

theorem cell20_971452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_971452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971452 prefixEnd_971452 := by exact prefixLift 971452
  have htrace : WordTrace (prefixWord ++ tailWord_971452) baseStart_971452 baseEnd_971452 := by
    simpa [prefixWord, tailWord_971452, baseEnd_971452] using wordTrace_append hprefix tailTrace_971452
  have hstable : (prefixWord ++ tailWord_971452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971452).length < 2 ^ (prefixWord ++ tailWord_971452).sum := by decide
  have hdescent : baseEnd_971452 < baseStart_971452 := by decide
  rcases family_descends (prefixWord ++ tailWord_971452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971455 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 3]
def baseStart_971455 : Nat := 118140960795 + 971455 * 2 ^ 59
def prefixEnd_971455 : Nat := 4983230072969 + 3 ^ 40 * 971455 * 2
def baseEnd_971455 : Nat := 443398532634312810262103

theorem tailTrace_971455 : CollatzResearch.WordTrace tailWord_971455 prefixEnd_971455 443398532634312810262103 := by
  unfold tailWord_971455
  simp only [CollatzResearch.WordTrace]
  refine ⟨35431874695591921150235819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23621249797061280766823879 35431874695591921150235819)
  ·
    refine ⟨53147812043387881725353729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35431874695591921150235819 53147812043387881725353729)
    ·
      refine ⟨39860859032540911294015297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53147812043387881725353729 39860859032540911294015297)
      ·
        refine ⟨29895644274405683470511473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39860859032540911294015297 29895644274405683470511473)
        ·
          refine ⟨22421733205804262602883605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29895644274405683470511473 22421733205804262602883605)
          ·
            refine ⟨1051018744022074809510169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22421733205804262602883605 1051018744022074809510169)
            ·
              refine ⟨788264058016556107132627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051018744022074809510169 788264058016556107132627)
              ·
                refine ⟨1182396087024834160698941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788264058016556107132627 1182396087024834160698941)
                ·
                  refine ⟨443398532634312810262103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182396087024834160698941 443398532634312810262103)
                  ·
                    rfl

theorem cell20_971455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_971455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971455 prefixEnd_971455 := by exact prefixLift 971455
  have htrace : WordTrace (prefixWord ++ tailWord_971455) baseStart_971455 baseEnd_971455 := by
    simpa [prefixWord, tailWord_971455, baseEnd_971455] using wordTrace_append hprefix tailTrace_971455
  have hstable : (prefixWord ++ tailWord_971455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971455).length < 2 ^ (prefixWord ++ tailWord_971455).sum := by decide
  have hdescent : baseEnd_971455 < baseStart_971455 := by decide
  rcases family_descends (prefixWord ++ tailWord_971455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971473 : List Nat := [1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_971473 : Nat := 118140960795 + 971473 * 2 ^ 59
def prefixEnd_971473 : Nat := 4983230072969 + 3 ^ 40 * 971473 * 2
def baseEnd_971473 : Nat := 147802249441594915887343

theorem tailTrace_971473 : CollatzResearch.WordTrace tailWord_971473 prefixEnd_971473 147802249441594915887343 := by
  unfold tailWord_971473
  simp only [CollatzResearch.WordTrace]
  refine ⟨35432531209526710224391073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23621687473017806816260715 35432531209526710224391073)
  ·
    refine ⟨26574398407145032668293305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35432531209526710224391073 26574398407145032668293305)
    ·
      refine ⟨19930798805358774501219979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26574398407145032668293305 19930798805358774501219979)
      ·
        refine ⟨29896198208038161751829969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19930798805358774501219979 29896198208038161751829969)
        ·
          refine ⟨22422148656028621313872477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29896198208038161751829969 22422148656028621313872477)
          ·
            refine ⟨8408305746010732992702179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22422148656028621313872477 8408305746010732992702179)
            ·
              refine ⟨12612458619016099489053269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8408305746010732992702179 12612458619016099489053269)
              ·
                refine ⟨147802249441594915887343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12612458619016099489053269 147802249441594915887343)
                ·
                  rfl

theorem cell20_971473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_971473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971473 prefixEnd_971473 := by exact prefixLift 971473
  have htrace : WordTrace (prefixWord ++ tailWord_971473) baseStart_971473 baseEnd_971473 := by
    simpa [prefixWord, tailWord_971473, baseEnd_971473] using wordTrace_append hprefix tailTrace_971473
  have hstable : (prefixWord ++ tailWord_971473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971473).length < 2 ^ (prefixWord ++ tailWord_971473).sum := by decide
  have hdescent : baseEnd_971473 < baseStart_971473 := by decide
  rcases family_descends (prefixWord ++ tailWord_971473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971496 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 2]
def baseStart_971496 : Nat := 118140960795 + 971496 * 2 ^ 59
def prefixEnd_971496 : Nat := 4983230072969 + 3 ^ 40 * 971496 * 2
def baseEnd_971496 : Nat := 443417246151498889895269

theorem tailTrace_971496 : CollatzResearch.WordTrace tailWord_971496 prefixEnd_971496 443417246151498889895269 := by
  unfold tailWord_971496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17716685044221692576239171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23622246725628923434985561 17716685044221692576239171)
  ·
    refine ⟨26575027566332538864358757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17716685044221692576239171 26575027566332538864358757)
    ·
      refine ⟨4982817668687351037067267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26575027566332538864358757 4982817668687351037067267)
      ·
        refine ⟨7474226503031026555600901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982817668687351037067267 7474226503031026555600901)
        ·
          refine ⟨1401417469318317479175169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7474226503031026555600901 1401417469318317479175169)
          ·
            refine ⟨1051063101988738109381377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401417469318317479175169 1051063101988738109381377)
            ·
              refine ⟨788297326491553582036033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051063101988738109381377 788297326491553582036033)
              ·
                refine ⟨591222994868665186527025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788297326491553582036033 591222994868665186527025)
                ·
                  refine ⟨443417246151498889895269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591222994868665186527025 443417246151498889895269)
                  ·
                    rfl

theorem cell20_971496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_971496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971496 prefixEnd_971496 := by exact prefixLift 971496
  have htrace : WordTrace (prefixWord ++ tailWord_971496) baseStart_971496 baseEnd_971496 := by
    simpa [prefixWord, tailWord_971496, baseEnd_971496] using wordTrace_append hprefix tailTrace_971496
  have hstable : (prefixWord ++ tailWord_971496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971496).length < 2 ^ (prefixWord ++ tailWord_971496).sum := by decide
  have hdescent : baseEnd_971496 < baseStart_971496 := by decide
  rcases family_descends (prefixWord ++ tailWord_971496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971497 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_971497 : Nat := 118140960795 + 971497 * 2 ^ 59
def prefixEnd_971497 : Nat := 4983230072969 + 3 ^ 40 * 971497 * 2
def baseEnd_971497 : Nat := 443417702578747330861931

theorem tailTrace_971497 : CollatzResearch.WordTrace tailWord_971497 prefixEnd_971497 443417702578747330861931 := by
  unfold tailWord_971497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35433406561439762323264745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23622271040959841548843163 35433406561439762323264745)
  ·
    refine ⟨26575054921079821742448559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35433406561439762323264745 26575054921079821742448559)
    ·
      refine ⟨39862582381619732613672839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26575054921079821742448559 39862582381619732613672839)
      ·
        refine ⟨59793873572429598920509259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39862582381619732613672839 59793873572429598920509259)
        ·
          refine ⟨89690810358644398380763889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59793873572429598920509259 89690810358644398380763889)
          ·
            refine ⟨67268107768983298785572917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89690810358644398380763889 67268107768983298785572917)
            ·
              refine ⟨6306385103342184261147461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67268107768983298785572917 6306385103342184261147461)
              ·
                refine ⟨1182447206876659548965149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6306385103342184261147461 1182447206876659548965149)
                ·
                  refine ⟨443417702578747330861931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182447206876659548965149 443417702578747330861931)
                  ·
                    rfl

theorem cell20_971497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_971497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971497 prefixEnd_971497 := by exact prefixLift 971497
  have htrace : WordTrace (prefixWord ++ tailWord_971497) baseStart_971497 baseEnd_971497 := by
    simpa [prefixWord, tailWord_971497, baseEnd_971497] using wordTrace_append hprefix tailTrace_971497
  have hstable : (prefixWord ++ tailWord_971497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971497).length < 2 ^ (prefixWord ++ tailWord_971497).sum := by decide
  have hdescent : baseEnd_971497 < baseStart_971497 := by decide
  rcases family_descends (prefixWord ++ tailWord_971497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971504 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_971504 : Nat := 118140960795 + 971504 * 2 ^ 59
def prefixEnd_971504 : Nat := 4983230072969 + 3 ^ 40 * 971504 * 2
def baseEnd_971504 : Nat := 443420897569486417628569

theorem tailTrace_971504 : CollatzResearch.WordTrace tailWord_971504 prefixEnd_971504 443420897569486417628569 := by
  unfold tailWord_971504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17716830936207201259384783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23622441248276268345846377 17716830936207201259384783)
  ·
    refine ⟨26575246404310801889077175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17716830936207201259384783 26575246404310801889077175)
    ·
      refine ⟨39862869606466202833615763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26575246404310801889077175 39862869606466202833615763)
      ·
        refine ⟨59794304409699304250423645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39862869606466202833615763 59794304409699304250423645)
        ·
          refine ⟨22422864153637239093908867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59794304409699304250423645 22422864153637239093908867)
          ·
            refine ⟨33634296230455858640863301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22422864153637239093908867 33634296230455858640863301)
            ·
              refine ⟨6306430543210473495161869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33634296230455858640863301 6306430543210473495161869)
              ·
                refine ⟨2364911453703927560685701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6306430543210473495161869 2364911453703927560685701)
                ·
                  refine ⟨443420897569486417628569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2364911453703927560685701 443420897569486417628569)
                  ·
                    rfl

theorem cell20_971504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_971504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971504 prefixEnd_971504 := by exact prefixLift 971504
  have htrace : WordTrace (prefixWord ++ tailWord_971504) baseStart_971504 baseEnd_971504 := by
    simpa [prefixWord, tailWord_971504, baseEnd_971504] using wordTrace_append hprefix tailTrace_971504
  have hstable : (prefixWord ++ tailWord_971504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971504).length < 2 ^ (prefixWord ++ tailWord_971504).sum := by decide
  have hdescent : baseEnd_971504 < baseStart_971504 := by decide
  rcases family_descends (prefixWord ++ tailWord_971504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971552 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_971552 : Nat := 118140960795 + 971552 * 2 ^ 59
def prefixEnd_971552 : Nat := 4983230072969 + 3 ^ 40 * 971552 * 2
def baseEnd_971552 : Nat := 443442806077411584028373

theorem tailTrace_971552 : CollatzResearch.WordTrace tailWord_971552 prefixEnd_971552 443442806077411584028373 := by
  unfold tailWord_971552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17717706288120253358258455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23623608384160337811011273 17717706288120253358258455)
  ·
    refine ⟨26576559432180380037387683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17717706288120253358258455 26576559432180380037387683)
    ·
      refine ⟨39864839148270570056081525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26576559432180380037387683 39864839148270570056081525)
      ·
        refine ⟨3737328670150365942757643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39864839148270570056081525 3737328670150365942757643)
        ·
          refine ⟨5605993005225548914136465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3737328670150365942757643 5605993005225548914136465)
          ·
            refine ⟨4204494753919161685602349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5605993005225548914136465 4204494753919161685602349)
            ·
              refine ⟨1576685532719685632100881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4204494753919161685602349 1576685532719685632100881)
              ·
                refine ⟨1182514149539764224075661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576685532719685632100881 1182514149539764224075661)
                ·
                  refine ⟨443442806077411584028373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182514149539764224075661 443442806077411584028373)
                  ·
                    rfl

theorem cell20_971552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_971552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971552 prefixEnd_971552 := by exact prefixLift 971552
  have htrace : WordTrace (prefixWord ++ tailWord_971552) baseStart_971552 baseEnd_971552 := by
    simpa [prefixWord, tailWord_971552, baseEnd_971552] using wordTrace_append hprefix tailTrace_971552
  have hstable : (prefixWord ++ tailWord_971552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971552).length < 2 ^ (prefixWord ++ tailWord_971552).sum := by decide
  have hdescent : baseEnd_971552 < baseStart_971552 := by decide
  rcases family_descends (prefixWord ++ tailWord_971552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971565 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 3]
def baseStart_971565 : Nat := 118140960795 + 971565 * 2 ^ 59
def prefixEnd_971565 : Nat := 4983230072969 + 3 ^ 40 * 971565 * 2
def baseEnd_971565 : Nat := 443448739631641316594987

theorem tailTrace_971565 : CollatzResearch.WordTrace tailWord_971565 prefixEnd_971565 443448739631641316594987 := by
  unfold tailWord_971565
  simp only [CollatzResearch.WordTrace]
  refine ⟨35435886725193409936740149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23623924483462273291160099 35435886725193409936740149)
  ·
    refine ⟨3322114380486882181569389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35435886725193409936740149 3322114380486882181569389)
    ·
      refine ⟨1245792892682580818088521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3322114380486882181569389 1245792892682580818088521)
      ·
        refine ⟨934344669511935613566391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1245792892682580818088521 934344669511935613566391)
        ·
          refine ⟨1401517004267903420349587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934344669511935613566391 1401517004267903420349587)
          ·
            refine ⟨2102275506401855130524381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401517004267903420349587 2102275506401855130524381)
            ·
              refine ⟨788353314900695673946643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2102275506401855130524381 788353314900695673946643)
              ·
                refine ⟨1182529972351043510919965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788353314900695673946643 1182529972351043510919965)
                ·
                  refine ⟨443448739631641316594987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182529972351043510919965 443448739631641316594987)
                  ·
                    rfl

theorem cell20_971565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_971565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971565 prefixEnd_971565 := by exact prefixLift 971565
  have htrace : WordTrace (prefixWord ++ tailWord_971565) baseStart_971565 baseEnd_971565 := by
    simpa [prefixWord, tailWord_971565, baseEnd_971565] using wordTrace_append hprefix tailTrace_971565
  have hstable : (prefixWord ++ tailWord_971565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971565).length < 2 ^ (prefixWord ++ tailWord_971565).sum := by decide
  have hdescent : baseEnd_971565 < baseStart_971565 := by decide
  rcases family_descends (prefixWord ++ tailWord_971565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971583 : List Nat := [1, 1, 2, 2, 5, 3, 2, 4]
def baseStart_971583 : Nat := 118140960795 + 971583 * 2 ^ 59
def prefixEnd_971583 : Nat := 4983230072969 + 3 ^ 40 * 971583 * 2
def baseEnd_971583 : Nat := 147818985107371084664971

theorem tailTrace_971583 : CollatzResearch.WordTrace tailWord_971583 prefixEnd_971583 147818985107371084664971 := by
  unfold tailWord_971583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436543239128199010895403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23624362159418799340596935 35436543239128199010895403)
  ·
    refine ⟨53154814858692298516343105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35436543239128199010895403 53154814858692298516343105)
    ·
      refine ⟨39866111144019223887257329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53154814858692298516343105 39866111144019223887257329)
      ·
        refine ⟨29899583358014417915442997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39866111144019223887257329 29899583358014417915442997)
        ·
          refine ⟨2803085939813851679572781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29899583358014417915442997 2803085939813851679572781)
          ·
            refine ⟨1051157227430194379839793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2803085939813851679572781 1051157227430194379839793)
            ·
              refine ⟨788367920572645784879845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051157227430194379839793 788367920572645784879845)
              ·
                refine ⟨147818985107371084664971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788367920572645784879845 147818985107371084664971)
                ·
                  rfl

theorem cell20_971583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_971583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971583 prefixEnd_971583 := by exact prefixLift 971583
  have htrace : WordTrace (prefixWord ++ tailWord_971583) baseStart_971583 baseEnd_971583 := by
    simpa [prefixWord, tailWord_971583, baseEnd_971583] using wordTrace_append hprefix tailTrace_971583
  have hstable : (prefixWord ++ tailWord_971583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971583).length < 2 ^ (prefixWord ++ tailWord_971583).sum := by decide
  have hdescent : baseEnd_971583 < baseStart_971583 := by decide
  rcases family_descends (prefixWord ++ tailWord_971583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971587 : List Nat := [1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_971587 : Nat := 118140960795 + 971587 * 2 ^ 59
def prefixEnd_971587 : Nat := 4983230072969 + 3 ^ 40 * 971587 * 2
def baseEnd_971587 : Nat := 147819593677035672620521

theorem tailTrace_971587 : CollatzResearch.WordTrace tailWord_971587 prefixEnd_971587 147819593677035672620521 := by
  unfold tailWord_971587
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436689131113707694041015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23624459420742471796027343 35436689131113707694041015)
  ·
    refine ⟨53155033696670561541061523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35436689131113707694041015 53155033696670561541061523)
    ·
      refine ⟨79732550545005842311592285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53155033696670561541061523 79732550545005842311592285)
      ·
        refine ⟨29899706454377190866847107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79732550545005842311592285 29899706454377190866847107)
        ·
          refine ⟨44849559681565786300270661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29899706454377190866847107 44849559681565786300270661)
          ·
            refine ⟨8409292440293584931300749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44849559681565786300270661 8409292440293584931300749)
            ·
              refine ⟨3153484665110094349237781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8409292440293584931300749 3153484665110094349237781)
              ·
                refine ⟨147819593677035672620521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3153484665110094349237781 147819593677035672620521)
                ·
                  rfl

theorem cell20_971587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_971587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971587 prefixEnd_971587 := by exact prefixLift 971587
  have htrace : WordTrace (prefixWord ++ tailWord_971587) baseStart_971587 baseEnd_971587 := by
    simpa [prefixWord, tailWord_971587, baseEnd_971587] using wordTrace_append hprefix tailTrace_971587
  have hstable : (prefixWord ++ tailWord_971587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971587).length < 2 ^ (prefixWord ++ tailWord_971587).sum := by decide
  have hdescent : baseEnd_971587 < baseStart_971587 := by decide
  rcases family_descends (prefixWord ++ tailWord_971587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971669 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 2]
def baseStart_971669 : Nat := 118140960795 + 971669 * 2 ^ 59
def prefixEnd_971669 : Nat := 4983230072969 + 3 ^ 40 * 971669 * 2
def baseEnd_971669 : Nat := 443496208065479177127895

theorem tailTrace_971669 : CollatzResearch.WordTrace tailWord_971669 prefixEnd_971669 443496208065479177127895 := by
  unfold tailWord_971669
  simp only [CollatzResearch.WordTrace]
  refine ⟨35439679916816635698526061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23626453277877757132350707 35439679916816635698526061)
  ·
    refine ⟨13289879968806238386947273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35439679916816635698526061 13289879968806238386947273)
    ·
      refine ⟨9967409976604678790210455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13289879968806238386947273 9967409976604678790210455)
      ·
        refine ⟨14951114964907018185315683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967409976604678790210455 14951114964907018185315683)
        ·
          refine ⟨22426672447360527277973525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14951114964907018185315683 22426672447360527277973525)
          ·
            refine ⟨1051250270970024716155009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22426672447360527277973525 1051250270970024716155009)
            ·
              refine ⟨788437703227518537116257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051250270970024716155009 788437703227518537116257)
              ·
                refine ⟨591328277420638902837193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788437703227518537116257 591328277420638902837193)
                ·
                  refine ⟨443496208065479177127895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591328277420638902837193 443496208065479177127895)
                  ·
                    rfl

theorem cell20_971669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_971669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971669 prefixEnd_971669 := by exact prefixLift 971669
  have htrace : WordTrace (prefixWord ++ tailWord_971669) baseStart_971669 baseEnd_971669 := by
    simpa [prefixWord, tailWord_971669, baseEnd_971669] using wordTrace_append hprefix tailTrace_971669
  have hstable : (prefixWord ++ tailWord_971669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971669).length < 2 ^ (prefixWord ++ tailWord_971669).sum := by decide
  have hdescent : baseEnd_971669 < baseStart_971669 := by decide
  rcases family_descends (prefixWord ++ tailWord_971669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971676 : List Nat := [2, 2, 3, 3, 3, 1, 1, 5]
def baseStart_971676 : Nat := 118140960795 + 971676 * 2 ^ 59
def prefixEnd_971676 : Nat := 4983230072969 + 3 ^ 40 * 971676 * 2
def baseEnd_971676 : Nat := 147833134352072754631511

theorem tailTrace_971676 : CollatzResearch.WordTrace tailWord_971676 prefixEnd_971676 147833134352072754631511 := by
  unfold tailWord_971676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17719967613895637947015441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23626623485194183929353921 17719967613895637947015441)
  ·
    refine ⟨13289975710421728460261581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17719967613895637947015441 13289975710421728460261581)
    ·
      refine ⟨4983740891408148172598093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13289975710421728460261581 4983740891408148172598093)
      ·
        refine ⟨1868902834278055564724285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4983740891408148172598093 1868902834278055564724285)
        ·
          refine ⟨700838562854270836771607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1868902834278055564724285 700838562854270836771607)
          ·
            refine ⟨1051257844281406255157411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700838562854270836771607 1051257844281406255157411)
            ·
              refine ⟨1576886766422109382736117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051257844281406255157411 1576886766422109382736117)
              ·
                refine ⟨147833134352072754631511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1576886766422109382736117 147833134352072754631511)
                ·
                  rfl

theorem cell20_971676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_971676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971676 prefixEnd_971676 := by exact prefixLift 971676
  have htrace : WordTrace (prefixWord ++ tailWord_971676) baseStart_971676 baseEnd_971676 := by
    simpa [prefixWord, tailWord_971676, baseEnd_971676] using wordTrace_append hprefix tailTrace_971676
  have hstable : (prefixWord ++ tailWord_971676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971676).length < 2 ^ (prefixWord ++ tailWord_971676).sum := by decide
  have hdescent : baseEnd_971676 < baseStart_971676 := by decide
  rcases family_descends (prefixWord ++ tailWord_971676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971697 : List Nat := [1, 2, 2, 4, 3, 1, 3, 4]
def baseStart_971697 : Nat := 118140960795 + 971697 * 2 ^ 59
def prefixEnd_971697 : Nat := 4983230072969 + 3 ^ 40 * 971697 * 2
def baseEnd_971697 : Nat := 147836329342811841398149

theorem tailTrace_971697 : CollatzResearch.WordTrace tailWord_971697 prefixEnd_971697 147836329342811841398149 := by
  unfold tailWord_971697
  simp only [CollatzResearch.WordTrace]
  refine ⟨35440701160715196480545345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23627134107143464320363563 35440701160715196480545345)
  ·
    refine ⟨26580525870536397360409009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35440701160715196480545345 26580525870536397360409009)
    ·
      refine ⟨19935394402902298020306757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26580525870536397360409009 19935394402902298020306757)
      ·
        refine ⟨3737886450544180878807517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19935394402902298020306757 3737886450544180878807517)
        ·
          refine ⟨1401707418954067829552819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3737886450544180878807517 1401707418954067829552819)
          ·
            refine ⟨2102561128431101744329229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401707418954067829552819 2102561128431101744329229)
            ·
              refine ⟨788460423161663154123461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2102561128431101744329229 788460423161663154123461)
              ·
                refine ⟨147836329342811841398149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788460423161663154123461 147836329342811841398149)
                ·
                  rfl

theorem cell20_971697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_971697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971697 prefixEnd_971697 := by exact prefixLift 971697
  have htrace : WordTrace (prefixWord ++ tailWord_971697) baseStart_971697 baseEnd_971697 := by
    simpa [prefixWord, tailWord_971697, baseEnd_971697] using wordTrace_append hprefix tailTrace_971697
  have hstable : (prefixWord ++ tailWord_971697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971697).length < 2 ^ (prefixWord ++ tailWord_971697).sum := by decide
  have hdescent : baseEnd_971697 < baseStart_971697 := by decide
  rcases family_descends (prefixWord ++ tailWord_971697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971762 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_971762 : Nat := 118140960795 + 971762 * 2 ^ 59
def prefixEnd_971762 : Nat := 4983230072969 + 3 ^ 40 * 971762 * 2
def baseEnd_971762 : Nat := 443538655799584187027515

theorem tailTrace_971762 : CollatzResearch.WordTrace tailWord_971762 prefixEnd_971762 443538655799584187027515 := by
  unfold tailWord_971762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860767976369928145415385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23628714603653141721107693 8860767976369928145415385)
  ·
    refine ⟨6645575982277446109061539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8860767976369928145415385 6645575982277446109061539)
    ·
      refine ⟨9968363973416169163592309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645575982277446109061539 9968363973416169163592309)
      ·
        refine ⟨934534122507765859086779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9968363973416169163592309 934534122507765859086779)
        ·
          refine ⟨1401801183761648788630169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934534122507765859086779 1401801183761648788630169)
          ·
            refine ⟨1051350887821236591472627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401801183761648788630169 1051350887821236591472627)
            ·
              refine ⟨1577026331731854887208941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051350887821236591472627 1577026331731854887208941)
              ·
                refine ⟨591384874399445582703353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577026331731854887208941 591384874399445582703353)
                ·
                  refine ⟨443538655799584187027515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591384874399445582703353 443538655799584187027515)
                  ·
                    rfl

theorem cell20_971762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_971762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971762 prefixEnd_971762 := by exact prefixLift 971762
  have htrace : WordTrace (prefixWord ++ tailWord_971762) baseStart_971762 baseEnd_971762 := by
    simpa [prefixWord, tailWord_971762, baseEnd_971762] using wordTrace_append hprefix tailTrace_971762
  have hstable : (prefixWord ++ tailWord_971762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971762).length < 2 ^ (prefixWord ++ tailWord_971762).sum := by decide
  have hdescent : baseEnd_971762 < baseStart_971762 := by decide
  rcases family_descends (prefixWord ++ tailWord_971762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971777 : List Nat := [1, 2, 4, 1, 2, 2, 8]
def baseStart_971777 : Nat := 118140960795 + 971777 * 2 ^ 59
def prefixEnd_971777 : Nat := 4983230072969 + 3 ^ 40 * 971777 * 2
def baseEnd_971777 : Nat := 49282833578701200169717

theorem tailTrace_971777 : CollatzResearch.WordTrace tailWord_971777 prefixEnd_971777 49282833578701200169717 := by
  unfold tailWord_971777
  simp only [CollatzResearch.WordTrace]
  refine ⟨35443619000425370143457585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23629079333616913428971723 35443619000425370143457585)
  ·
    refine ⟨26582714250319027607593189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35443619000425370143457585 26582714250319027607593189)
    ·
      refine ⟨4984258921934817676423723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26582714250319027607593189 4984258921934817676423723)
      ·
        refine ⟨7476388382902226514635585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984258921934817676423723 7476388382902226514635585)
        ·
          refine ⟨5607291287176669885976689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476388382902226514635585 5607291287176669885976689)
          ·
            refine ⟨4205468465382502414482517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5607291287176669885976689 4205468465382502414482517)
            ·
              refine ⟨49282833578701200169717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4205468465382502414482517 49282833578701200169717)
              ·
                rfl

theorem cell20_971777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_971777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971777 prefixEnd_971777 := by exact prefixLift 971777
  have htrace : WordTrace (prefixWord ++ tailWord_971777) baseStart_971777 baseEnd_971777 := by
    simpa [prefixWord, tailWord_971777, baseEnd_971777] using wordTrace_append hprefix tailTrace_971777
  have hstable : (prefixWord ++ tailWord_971777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971777).length < 2 ^ (prefixWord ++ tailWord_971777).sum := by decide
  have hdescent : baseEnd_971777 < baseStart_971777 := by decide
  rcases family_descends (prefixWord ++ tailWord_971777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971787 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 4]
def baseStart_971787 : Nat := 118140960795 + 971787 * 2 ^ 59
def prefixEnd_971787 : Nat := 4983230072969 + 3 ^ 40 * 971787 * 2
def baseEnd_971787 : Nat := 443550066480795211194079

theorem tailTrace_971787 : CollatzResearch.WordTrace tailWord_971787 prefixEnd_971787 443550066480795211194079 := by
  unfold tailWord_971787
  simp only [CollatzResearch.WordTrace]
  refine ⟨35443983730389141851321615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23629322486926094567547743 35443983730389141851321615)
  ·
    refine ⟨53165975595583712776982423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35443983730389141851321615 53165975595583712776982423)
    ·
      refine ⟨79748963393375569165473635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53165975595583712776982423 79748963393375569165473635)
      ·
        refine ⟨119623445090063353748210453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79748963393375569165473635 119623445090063353748210453)
        ·
          refine ⟨5607348988596719706947365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119623445090063353748210453 5607348988596719706947365)
          ·
            refine ⟨1051377935361884945052631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5607348988596719706947365 1051377935361884945052631)
            ·
              refine ⟨1577066903042827417578947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051377935361884945052631 1577066903042827417578947)
              ·
                refine ⟨2365600354564241126368421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577066903042827417578947 2365600354564241126368421)
                ·
                  refine ⟨443550066480795211194079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365600354564241126368421 443550066480795211194079)
                  ·
                    rfl

theorem cell20_971787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_971787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971787 prefixEnd_971787 := by exact prefixLift 971787
  have htrace : WordTrace (prefixWord ++ tailWord_971787) baseStart_971787 baseEnd_971787 := by
    simpa [prefixWord, tailWord_971787, baseEnd_971787] using wordTrace_append hprefix tailTrace_971787
  have hstable : (prefixWord ++ tailWord_971787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971787).length < 2 ^ (prefixWord ++ tailWord_971787).sum := by decide
  have hdescent : baseEnd_971787 < baseStart_971787 := by decide
  rcases family_descends (prefixWord ++ tailWord_971787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971791 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_971791 : Nat := 118140960795 + 971791 * 2 ^ 59
def prefixEnd_971791 : Nat := 4983230072969 + 3 ^ 40 * 971791 * 2
def baseEnd_971791 : Nat := 443551892189788975060729

theorem tailTrace_971791 : CollatzResearch.WordTrace tailWord_971791 prefixEnd_971791 443551892189788975060729 := by
  unfold tailWord_971791
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444129622374650534467227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23629419748249767022978151 35444129622374650534467227)
  ·
    refine ⟨53166194433561975801700841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35444129622374650534467227 53166194433561975801700841)
    ·
      refine ⟨39874645825171481851275631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53166194433561975801700841 39874645825171481851275631)
      ·
        refine ⟨59811968737757222776913447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39874645825171481851275631 59811968737757222776913447)
        ·
          refine ⟨89717953106635834165370171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59811968737757222776913447 89717953106635834165370171)
          ·
            refine ⟨134576929659953751248055257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89717953106635834165370171 134576929659953751248055257)
            ·
              refine ⟨100932697244965313436041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134576929659953751248055257 100932697244965313436041443)
              ·
                refine ⟨151399045867447970154062165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100932697244965313436041443 151399045867447970154062165)
                ·
                  refine ⟨443551892189788975060729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151399045867447970154062165 443551892189788975060729)
                  ·
                    rfl

theorem cell20_971791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_971791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971791 prefixEnd_971791 := by exact prefixLift 971791
  have htrace : WordTrace (prefixWord ++ tailWord_971791) baseStart_971791 baseEnd_971791 := by
    simpa [prefixWord, tailWord_971791, baseEnd_971791] using wordTrace_append hprefix tailTrace_971791
  have hstable : (prefixWord ++ tailWord_971791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971791).length < 2 ^ (prefixWord ++ tailWord_971791).sum := by decide
  have hdescent : baseEnd_971791 < baseStart_971791 := by decide
  rcases family_descends (prefixWord ++ tailWord_971791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971797 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 3]
def baseStart_971797 : Nat := 118140960795 + 971797 * 2 ^ 59
def prefixEnd_971797 : Nat := 4983230072969 + 3 ^ 40 * 971797 * 2
def baseEnd_971797 : Nat := 443554630753279620860705

theorem tailTrace_971797 : CollatzResearch.WordTrace tailWord_971797 prefixEnd_971797 443554630753279620860705 := by
  unfold tailWord_971797
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444348460352913559185645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23629565640235275706123763 35444348460352913559185645)
  ·
    refine ⟨13291630672632342584694617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35444348460352913559185645 13291630672632342584694617)
    ·
      refine ⟨9968723004474256938520963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13291630672632342584694617 9968723004474256938520963)
      ·
        refine ⟨14953084506711385407781445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968723004474256938520963 14953084506711385407781445)
        ·
          refine ⟨2803703345008384763959021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14953084506711385407781445 2803703345008384763959021)
          ·
            refine ⟨1051388754378144286484633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2803703345008384763959021 1051388754378144286484633)
            ·
              refine ⟨788541565783608214863475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051388754378144286484633 788541565783608214863475)
              ·
                refine ⟨1182812348675412322295213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788541565783608214863475 1182812348675412322295213)
                ·
                  refine ⟨443554630753279620860705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182812348675412322295213 443554630753279620860705)
                  ·
                    rfl

theorem cell20_971797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_971797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971797 prefixEnd_971797 := by exact prefixLift 971797
  have htrace : WordTrace (prefixWord ++ tailWord_971797) baseStart_971797 baseEnd_971797 := by
    simpa [prefixWord, tailWord_971797, baseEnd_971797] using wordTrace_append hprefix tailTrace_971797
  have hstable : (prefixWord ++ tailWord_971797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971797).length < 2 ^ (prefixWord ++ tailWord_971797).sum := by decide
  have hdescent : baseEnd_971797 < baseStart_971797 := by decide
  rcases family_descends (prefixWord ++ tailWord_971797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971825 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 2]
def baseStart_971825 : Nat := 118140960795 + 971825 * 2 ^ 59
def prefixEnd_971825 : Nat := 4983230072969 + 3 ^ 40 * 971825 * 2
def baseEnd_971825 : Nat := 443567410716235967927257

theorem tailTrace_971825 : CollatzResearch.WordTrace tailWord_971825 prefixEnd_971825 443567410716235967927257 := by
  unfold tailWord_971825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35445369704251474341204929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23630246469500982894136619 35445369704251474341204929)
  ·
    refine ⟨26584027278188605755903697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35445369704251474341204929 26584027278188605755903697)
    ·
      refine ⟨19938020458641454316927773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26584027278188605755903697 19938020458641454316927773)
      ·
        refine ⟨7476757671990545368847915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19938020458641454316927773 7476757671990545368847915)
        ·
          refine ⟨11215136507985818053271873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7476757671990545368847915 11215136507985818053271873)
          ·
            refine ⟨8411352380989363539953905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11215136507985818053271873 8411352380989363539953905)
            ·
              refine ⟨6308514285742022654965429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411352380989363539953905 6308514285742022654965429)
              ·
                refine ⟨591423214288314623903009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6308514285742022654965429 591423214288314623903009)
                ·
                  refine ⟨443567410716235967927257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591423214288314623903009 443567410716235967927257)
                  ·
                    rfl

theorem cell20_971825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_971825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971825 prefixEnd_971825 := by exact prefixLift 971825
  have htrace : WordTrace (prefixWord ++ tailWord_971825) baseStart_971825 baseEnd_971825 := by
    simpa [prefixWord, tailWord_971825, baseEnd_971825] using wordTrace_append hprefix tailTrace_971825
  have hstable : (prefixWord ++ tailWord_971825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971825).length < 2 ^ (prefixWord ++ tailWord_971825).sum := by decide
  have hdescent : baseEnd_971825 < baseStart_971825 := by decide
  rcases family_descends (prefixWord ++ tailWord_971825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971838 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_971838 : Nat := 118140960795 + 971838 * 2 ^ 59
def prefixEnd_971838 : Nat := 4983230072969 + 3 ^ 40 * 971838 * 2
def baseEnd_971838 : Nat := 443573344270465700493871

theorem tailTrace_971838 : CollatzResearch.WordTrace tailWord_971838 prefixEnd_971838 443573344270465700493871 := by
  unfold tailWord_971838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430730481650547195178521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23630562568802918374285445 4430730481650547195178521)
  ·
    refine ⟨3323047861237910396383891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4430730481650547195178521 3323047861237910396383891)
    ·
      refine ⟨4984571791856865594575837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323047861237910396383891 4984571791856865594575837)
      ·
        refine ⟨1869214421946324597965939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4984571791856865594575837 1869214421946324597965939)
        ·
          refine ⟨2803821632919486896948909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869214421946324597965939 2803821632919486896948909)
          ·
            refine ⟨1051433112344807586355841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2803821632919486896948909 1051433112344807586355841)
            ·
              refine ⟨788574834258605689766881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051433112344807586355841 788574834258605689766881)
              ·
                refine ⟨591431125693954267325161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788574834258605689766881 591431125693954267325161)
                ·
                  refine ⟨443573344270465700493871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591431125693954267325161 443573344270465700493871)
                  ·
                    rfl

theorem cell20_971838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_971838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971838 prefixEnd_971838 := by exact prefixLift 971838
  have htrace : WordTrace (prefixWord ++ tailWord_971838) baseStart_971838 baseEnd_971838 := by
    simpa [prefixWord, tailWord_971838, baseEnd_971838] using wordTrace_append hprefix tailTrace_971838
  have hstable : (prefixWord ++ tailWord_971838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971838).length < 2 ^ (prefixWord ++ tailWord_971838).sum := by decide
  have hdescent : baseEnd_971838 < baseStart_971838 := by decide
  rcases family_descends (prefixWord ++ tailWord_971838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971901 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 2]
def baseStart_971901 : Nat := 118140960795 + 971901 * 2 ^ 59
def prefixEnd_971901 : Nat := 4983230072969 + 3 ^ 40 * 971901 * 2
def baseEnd_971901 : Nat := 443602099187117481393613

theorem tailTrace_971901 : CollatzResearch.WordTrace tailWord_971901 prefixEnd_971901 443602099187117481393613 := by
  unfold tailWord_971901
  simp only [CollatzResearch.WordTrace]
  refine ⟨35448141651976139320971557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23632094434650759547314371 35448141651976139320971557)
  ·
    refine ⟨6646526559745526122682167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35448141651976139320971557 6646526559745526122682167)
    ·
      refine ⟨9969789839618289184023251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646526559745526122682167 9969789839618289184023251)
      ·
        refine ⟨14954684759427433776034877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9969789839618289184023251 14954684759427433776034877)
        ·
          refine ⟨5608006784785287666013079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14954684759427433776034877 5608006784785287666013079)
          ·
            refine ⟨8412010177177931499019619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608006784785287666013079 8412010177177931499019619)
            ·
              refine ⟨12618015265766897248529429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412010177177931499019619 12618015265766897248529429)
              ·
                refine ⟨591469465582823308524817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12618015265766897248529429 591469465582823308524817)
                ·
                  refine ⟨443602099187117481393613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591469465582823308524817 443602099187117481393613)
                  ·
                    rfl

theorem cell20_971901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_971901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971901 prefixEnd_971901 := by exact prefixLift 971901
  have htrace : WordTrace (prefixWord ++ tailWord_971901) baseStart_971901 baseEnd_971901 := by
    simpa [prefixWord, tailWord_971901, baseEnd_971901] using wordTrace_append hprefix tailTrace_971901
  have hstable : (prefixWord ++ tailWord_971901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971901).length < 2 ^ (prefixWord ++ tailWord_971901).sum := by decide
  have hdescent : baseEnd_971901 < baseStart_971901 := by decide
  rcases family_descends (prefixWord ++ tailWord_971901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971935 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 2]
def baseStart_971935 : Nat := 118140960795 + 971935 * 2 ^ 59
def prefixEnd_971935 : Nat := 4983230072969 + 3 ^ 40 * 971935 * 2
def baseEnd_971935 : Nat := 443617617713564474260141

theorem tailTrace_971935 : CollatzResearch.WordTrace tailWord_971935 prefixEnd_971935 443617617713564474260141 := by
  unfold tailWord_971935
  simp only [CollatzResearch.WordTrace]
  refine ⟨35449381733852963127709259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23632921155901975418472839 35449381733852963127709259)
  ·
    refine ⟨53174072600779444691563889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35449381733852963127709259 53174072600779444691563889)
    ·
      refine ⟨39880554450584583518672917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53174072600779444691563889 39880554450584583518672917)
      ·
        refine ⟨1869400989871152352437793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39880554450584583518672917 1869400989871152352437793)
        ·
          refine ⟨1402050742403364264328345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869400989871152352437793 1402050742403364264328345)
          ·
            refine ⟨1051538056802523198246259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402050742403364264328345 1051538056802523198246259)
            ·
              refine ⟨1577307085203784797369389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051538056802523198246259 1577307085203784797369389)
              ·
                refine ⟨591490156951419299013521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577307085203784797369389 591490156951419299013521)
                ·
                  refine ⟨443617617713564474260141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591490156951419299013521 443617617713564474260141)
                  ·
                    rfl

theorem cell20_971935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 2].length) (baseStart_971935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971935 prefixEnd_971935 := by exact prefixLift 971935
  have htrace : WordTrace (prefixWord ++ tailWord_971935) baseStart_971935 baseEnd_971935 := by
    simpa [prefixWord, tailWord_971935, baseEnd_971935] using wordTrace_append hprefix tailTrace_971935
  have hstable : (prefixWord ++ tailWord_971935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971935).length < 2 ^ (prefixWord ++ tailWord_971935).sum := by decide
  have hdescent : baseEnd_971935 < baseStart_971935 := by decide
  rcases family_descends (prefixWord ++ tailWord_971935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971936 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_971936 : Nat := 118140960795 + 971936 * 2 ^ 59
def prefixEnd_971936 : Nat := 4983230072969 + 3 ^ 40 * 971936 * 2
def baseEnd_971936 : Nat := 443618074140812915226803

theorem tailTrace_971936 : CollatzResearch.WordTrace tailWord_971936 prefixEnd_971936 443618074140812915226803 := by
  unfold tailWord_971936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724709103424670149247831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23632945471232893532330441 17724709103424670149247831)
  ·
    refine ⟨26587063655137005223871747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17724709103424670149247831 26587063655137005223871747)
    ·
      refine ⟨39880595482705507835807621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26587063655137005223871747 39880595482705507835807621)
      ·
        refine ⟨7477611653007282719213929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39880595482705507835807621 7477611653007282719213929)
        ·
          refine ⟨5608208739755462039410447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7477611653007282719213929 5608208739755462039410447)
          ·
            refine ⟨8412313109633193059115671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608208739755462039410447 8412313109633193059115671)
            ·
              refine ⟨12618469664449789588673507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412313109633193059115671 12618469664449789588673507)
              ·
                refine ⟨18927704496674684383010261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12618469664449789588673507 18927704496674684383010261)
                ·
                  refine ⟨443618074140812915226803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18927704496674684383010261 443618074140812915226803)
                  ·
                    rfl

theorem cell20_971936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_971936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971936 prefixEnd_971936 := by exact prefixLift 971936
  have htrace : WordTrace (prefixWord ++ tailWord_971936) baseStart_971936 baseEnd_971936 := by
    simpa [prefixWord, tailWord_971936, baseEnd_971936] using wordTrace_append hprefix tailTrace_971936
  have hstable : (prefixWord ++ tailWord_971936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971936).length < 2 ^ (prefixWord ++ tailWord_971936).sum := by decide
  have hdescent : baseEnd_971936 < baseStart_971936 := by decide
  rcases family_descends (prefixWord ++ tailWord_971936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971946 : List Nat := [3, 1, 5, 1, 1, 1, 8]
def baseStart_971946 : Nat := 118140960795 + 971946 * 2 ^ 59
def prefixEnd_971946 : Nat := 4983230072969 + 3 ^ 40 * 971946 * 2
def baseEnd_971946 : Nat := 49291404268144147210381

theorem tailTrace_971946 : CollatzResearch.WordTrace tailWord_971946 prefixEnd_971946 49291404268144147210381 := by
  unfold tailWord_971946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862445734203278001589923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23633188624542074670906461 8862445734203278001589923)
  ·
    refine ⟨13293668601304917002384885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8862445734203278001589923 13293668601304917002384885)
    ·
      refine ⟨1246281431372335968973583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13293668601304917002384885 1246281431372335968973583)
      ·
        refine ⟨1869422147058503953460375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246281431372335968973583 1869422147058503953460375)
        ·
          refine ⟨2804133220587755930190563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869422147058503953460375 2804133220587755930190563)
          ·
            refine ⟨4206199830881633895285845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804133220587755930190563 4206199830881633895285845)
            ·
              refine ⟨49291404268144147210381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4206199830881633895285845 49291404268144147210381)
              ·
                rfl

theorem cell20_971946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 8].length) (baseStart_971946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971946 prefixEnd_971946 := by exact prefixLift 971946
  have htrace : WordTrace (prefixWord ++ tailWord_971946) baseStart_971946 baseEnd_971946 := by
    simpa [prefixWord, tailWord_971946, baseEnd_971946] using wordTrace_append hprefix tailTrace_971946
  have hstable : (prefixWord ++ tailWord_971946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971946).length < 2 ^ (prefixWord ++ tailWord_971946).sum := by decide
  have hdescent : baseEnd_971946 < baseStart_971946 := by decide
  rcases family_descends (prefixWord ++ tailWord_971946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971953 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_971953 : Nat := 118140960795 + 971953 * 2 ^ 59
def prefixEnd_971953 : Nat := 4983230072969 + 3 ^ 40 * 971953 * 2
def baseEnd_971953 : Nat := 443625833404036411660067

theorem tailTrace_971953 : CollatzResearch.WordTrace tailWord_971953 prefixEnd_971953 443625833404036411660067 := by
  unfold tailWord_971953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35450038247787752201864513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23633358831858501467909675 35450038247787752201864513)
  ·
    refine ⟨26587528685840814151398385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35450038247787752201864513 26587528685840814151398385)
    ·
      refine ⟨19940646514380610613548789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26587528685840814151398385 19940646514380610613548789)
      ·
        refine ⟨1869435610723182245020199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19940646514380610613548789 1869435610723182245020199)
        ·
          refine ⟨2804153416084773367530299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869435610723182245020199 2804153416084773367530299)
          ·
            refine ⟨4206230124127160051295449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804153416084773367530299 4206230124127160051295449)
            ·
              refine ⟨3154672593095370038471587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4206230124127160051295449 3154672593095370038471587)
              ·
                refine ⟨4732008889643055057707381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154672593095370038471587 4732008889643055057707381)
                ·
                  refine ⟨443625833404036411660067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4732008889643055057707381 443625833404036411660067)
                  ·
                    rfl

theorem cell20_971953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_971953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_971953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_971953 prefixEnd_971953 := by exact prefixLift 971953
  have htrace : WordTrace (prefixWord ++ tailWord_971953) baseStart_971953 baseEnd_971953 := by
    simpa [prefixWord, tailWord_971953, baseEnd_971953] using wordTrace_append hprefix tailTrace_971953
  have hstable : (prefixWord ++ tailWord_971953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971953).length < 2 ^ (prefixWord ++ tailWord_971953).sum := by decide
  have hdescent : baseEnd_971953 < baseStart_971953 := by decide
  rcases family_descends (prefixWord ++ tailWord_971953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972005 : List Nat := [1, 3, 1, 4, 3, 8]
def baseStart_972005 : Nat := 118140960795 + 972005 * 2 ^ 59
def prefixEnd_972005 : Nat := 4983230072969 + 3 ^ 40 * 972005 * 2
def baseEnd_972005 : Nat := 16431465467442790441723

theorem tailTrace_972005 : CollatzResearch.WordTrace tailWord_972005 prefixEnd_972005 16431465467442790441723 := by
  unfold tailWord_972005
  simp only [CollatzResearch.WordTrace]
  refine ⟨35451934843599365082757469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23634623229066243388504979 35451934843599365082757469)
  ·
    refine ⟨13294475566349761906034051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35451934843599365082757469 13294475566349761906034051)
    ·
      refine ⟨19941713349524642859051077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13294475566349761906034051 19941713349524642859051077)
      ·
        refine ⟨3739071253035870536072077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19941713349524642859051077 3739071253035870536072077)
        ·
          refine ⟨1402151719888451451027029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3739071253035870536072077 1402151719888451451027029)
          ·
            refine ⟨16431465467442790441723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1402151719888451451027029 16431465467442790441723)
            ·
              rfl

theorem cell20_972005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 8].length) (baseStart_972005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972005 prefixEnd_972005 := by exact prefixLift 972005
  have htrace : WordTrace (prefixWord ++ tailWord_972005) baseStart_972005 baseEnd_972005 := by
    simpa [prefixWord, tailWord_972005, baseEnd_972005] using wordTrace_append hprefix tailTrace_972005
  have hstable : (prefixWord ++ tailWord_972005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972005).length < 2 ^ (prefixWord ++ tailWord_972005).sum := by decide
  have hdescent : baseEnd_972005 < baseStart_972005 := by decide
  rcases family_descends (prefixWord ++ tailWord_972005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972036 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_972036 : Nat := 118140960795 + 972036 * 2 ^ 59
def prefixEnd_972036 : Nat := 4983230072969 + 3 ^ 40 * 972036 * 2
def baseEnd_972036 : Nat := 443663716865657011893061

theorem tailTrace_972036 : CollatzResearch.WordTrace tailWord_972036 prefixEnd_972036 443663716865657011893061 := by
  unfold tailWord_972036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17726532753243528688567981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23635377004324704918090641 17726532753243528688567981)
  ·
    refine ⟨6647449782466323258212993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17726532753243528688567981 6647449782466323258212993)
    ·
      refine ⟨4985587336849742443659745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6647449782466323258212993 4985587336849742443659745)
      ·
        refine ⟨3739190502637306832744809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4985587336849742443659745 3739190502637306832744809)
        ·
          refine ⟨2804392876977980124558607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739190502637306832744809 2804392876977980124558607)
          ·
            refine ⟨4206589315466970186837911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804392876977980124558607 4206589315466970186837911)
            ·
              refine ⟨6309883973200455280256867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206589315466970186837911 6309883973200455280256867)
              ·
                refine ⟨9464825959800682920385301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309883973200455280256867 9464825959800682920385301)
                ·
                  refine ⟨443663716865657011893061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9464825959800682920385301 443663716865657011893061)
                  ·
                    rfl

theorem cell20_972036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_972036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972036 prefixEnd_972036 := by exact prefixLift 972036
  have htrace : WordTrace (prefixWord ++ tailWord_972036) baseStart_972036 baseEnd_972036 := by
    simpa [prefixWord, tailWord_972036, baseEnd_972036] using wordTrace_append hprefix tailTrace_972036
  have hstable : (prefixWord ++ tailWord_972036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972036).length < 2 ^ (prefixWord ++ tailWord_972036).sum := by decide
  have hdescent : baseEnd_972036 < baseStart_972036 := by decide
  rcases family_descends (prefixWord ++ tailWord_972036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972063 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 3]
def baseStart_972063 : Nat := 118140960795 + 972063 * 2 ^ 59
def prefixEnd_972063 : Nat := 4983230072969 + 3 ^ 40 * 972063 * 2
def baseEnd_972063 : Nat := 443676040401364917992951

theorem tailTrace_972063 : CollatzResearch.WordTrace tailWord_972063 prefixEnd_972063 443676040401364917992951 := by
  unfold tailWord_972063
  simp only [CollatzResearch.WordTrace]
  refine ⟨35454050277389240988368843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23636033518259493992245895 35454050277389240988368843)
  ·
    refine ⟨53181075416083861482553265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35454050277389240988368843 53181075416083861482553265)
    ·
      refine ⟨39885806562062896111914949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53181075416083861482553265 39885806562062896111914949)
      ·
        refine ⟨7478588730386793020984053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39885806562062896111914949 7478588730386793020984053)
        ·
          refine ⟨701117693473761845717255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7478588730386793020984053 701117693473761845717255)
          ·
            refine ⟨1051676540210642768575883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701117693473761845717255 1051676540210642768575883)
            ·
              refine ⟨1577514810315964152863825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051676540210642768575883 1577514810315964152863825)
              ·
                refine ⟨1183136107736973114647869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577514810315964152863825 1183136107736973114647869)
                ·
                  refine ⟨443676040401364917992951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183136107736973114647869 443676040401364917992951)
                  ·
                    rfl

theorem cell20_972063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 3].length) (baseStart_972063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972063 prefixEnd_972063 := by exact prefixLift 972063
  have htrace : WordTrace (prefixWord ++ tailWord_972063) baseStart_972063 baseEnd_972063 := by
    simpa [prefixWord, tailWord_972063, baseEnd_972063] using wordTrace_append hprefix tailTrace_972063
  have hstable : (prefixWord ++ tailWord_972063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972063).length < 2 ^ (prefixWord ++ tailWord_972063).sum := by decide
  have hdescent : baseEnd_972063 < baseStart_972063 := by decide
  rcases family_descends (prefixWord ++ tailWord_972063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972067 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_972067 : Nat := 118140960795 + 972067 * 2 ^ 59
def prefixEnd_972067 : Nat := 4983230072969 + 3 ^ 40 * 972067 * 2
def baseEnd_972067 : Nat := 443677866110358681859601

theorem tailTrace_972067 : CollatzResearch.WordTrace tailWord_972067 prefixEnd_972067 443677866110358681859601 := by
  unfold tailWord_972067
  simp only [CollatzResearch.WordTrace]
  refine ⟨35454196169374749671514455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23636130779583166447676303 35454196169374749671514455)
  ·
    refine ⟨53181294254062124507271683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35454196169374749671514455 53181294254062124507271683)
    ·
      refine ⟨79771941381093186760907525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53181294254062124507271683 79771941381093186760907525)
      ·
        refine ⟨14957239008954972517670161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79771941381093186760907525 14957239008954972517670161)
        ·
          refine ⟨11217929256716229388252621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14957239008954972517670161 11217929256716229388252621)
          ·
            refine ⟨4206723471268586020594733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11217929256716229388252621 4206723471268586020594733)
            ·
              refine ⟨1577521301725719757723025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4206723471268586020594733 1577521301725719757723025)
              ·
                refine ⟨1183140976294289818292269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577521301725719757723025 1183140976294289818292269)
                ·
                  refine ⟨443677866110358681859601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183140976294289818292269 443677866110358681859601)
                  ·
                    rfl

theorem cell20_972067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_972067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972067 prefixEnd_972067 := by exact prefixLift 972067
  have htrace : WordTrace (prefixWord ++ tailWord_972067) baseStart_972067 baseEnd_972067 := by
    simpa [prefixWord, tailWord_972067, baseEnd_972067] using wordTrace_append hprefix tailTrace_972067
  have hstable : (prefixWord ++ tailWord_972067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972067).length < 2 ^ (prefixWord ++ tailWord_972067).sum := by decide
  have hdescent : baseEnd_972067 < baseStart_972067 := by decide
  rcases family_descends (prefixWord ++ tailWord_972067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972108 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 2]
def baseStart_972108 : Nat := 118140960795 + 972108 * 2 ^ 59
def prefixEnd_972108 : Nat := 4983230072969 + 3 ^ 40 * 972108 * 2
def baseEnd_972108 : Nat := 443696579627544761492767

theorem tailTrace_972108 : CollatzResearch.WordTrace tailWord_972108 prefixEnd_972108 443696579627544761492767 := by
  unfold tailWord_972108
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727845781113106836878489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23637127708150809115837985 17727845781113106836878489)
  ·
    refine ⟨13295884335834830127658867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17727845781113106836878489 13295884335834830127658867)
    ·
      refine ⟨19943826503752245191488301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13295884335834830127658867 19943826503752245191488301)
      ·
        refine ⟨7478934938907091946808113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19943826503752245191488301 7478934938907091946808113)
        ·
          refine ⟨5609201204180318960106085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7478934938907091946808113 5609201204180318960106085)
          ·
            refine ⟨1051725225783809805019891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5609201204180318960106085 1051725225783809805019891)
            ·
              refine ⟨1577587838675714707529837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051725225783809805019891 1577587838675714707529837)
              ·
                refine ⟨591595439503393015323689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577587838675714707529837 591595439503393015323689)
                ·
                  refine ⟨443696579627544761492767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591595439503393015323689 443696579627544761492767)
                  ·
                    rfl

theorem cell20_972108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_972108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972108 prefixEnd_972108 := by exact prefixLift 972108
  have htrace : WordTrace (prefixWord ++ tailWord_972108) baseStart_972108 baseEnd_972108 := by
    simpa [prefixWord, tailWord_972108, baseEnd_972108] using wordTrace_append hprefix tailTrace_972108
  have hstable : (prefixWord ++ tailWord_972108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972108).length < 2 ^ (prefixWord ++ tailWord_972108).sum := by decide
  have hdescent : baseEnd_972108 < baseStart_972108 := by decide
  rcases family_descends (prefixWord ++ tailWord_972108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972119 : List Nat := [1, 1, 3, 2, 3, 4, 6]
def baseStart_972119 : Nat := 118140960795 + 972119 * 2 ^ 59
def prefixEnd_972119 : Nat := 4983230072969 + 3 ^ 40 * 972119 * 2
def baseEnd_972119 : Nat := 49300177814141956902895

theorem tailTrace_972119 : CollatzResearch.WordTrace tailWord_972119 prefixEnd_972119 49300177814141956902895 := by
  unfold tailWord_972119
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456092765186362552407411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23637395176790908368271607 35456092765186362552407411)
  ·
    refine ⟨53184139147779543828611117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35456092765186362552407411 53184139147779543828611117)
    ·
      refine ⟨19944052180417328935729169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53184139147779543828611117 19944052180417328935729169)
      ·
        refine ⟨14958039135312996701796877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19944052180417328935729169 14958039135312996701796877)
        ·
          refine ⟨5609264675742373763173829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14958039135312996701796877 5609264675742373763173829)
          ·
            refine ⟨1051737126701695080595093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5609264675742373763173829 1051737126701695080595093)
            ·
              refine ⟨49300177814141956902895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1051737126701695080595093 49300177814141956902895)
              ·
                rfl

theorem cell20_972119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_972119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972119 prefixEnd_972119 := by exact prefixLift 972119
  have htrace : WordTrace (prefixWord ++ tailWord_972119) baseStart_972119 baseEnd_972119 := by
    simpa [prefixWord, tailWord_972119, baseEnd_972119] using wordTrace_append hprefix tailTrace_972119
  have hstable : (prefixWord ++ tailWord_972119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972119).length < 2 ^ (prefixWord ++ tailWord_972119).sum := by decide
  have hdescent : baseEnd_972119 < baseStart_972119 := by decide
  rcases family_descends (prefixWord ++ tailWord_972119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972136 : List Nat := [2, 1, 4, 2, 3, 1, 2, 5]
def baseStart_972136 : Nat := 118140960795 + 972136 * 2 ^ 59
def prefixEnd_972136 : Nat := 4983230072969 + 3 ^ 40 * 972136 * 2
def baseEnd_972136 : Nat := 147903119863500369519773

theorem tailTrace_972136 : CollatzResearch.WordTrace tailWord_972136 prefixEnd_972136 147903119863500369519773 := by
  unfold tailWord_972136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17728356403062387227888131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23637808537416516303850841 17728356403062387227888131)
  ·
    refine ⟨26592534604593580841832197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17728356403062387227888131 26592534604593580841832197)
    ·
      refine ⟨4986100238361296407843537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26592534604593580841832197 4986100238361296407843537)
      ·
        refine ⟨3739575178770972305882653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4986100238361296407843537 3739575178770972305882653)
        ·
          refine ⟨1402340692039114614705995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3739575178770972305882653 1402340692039114614705995)
          ·
            refine ⟨2103511038058671922058993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402340692039114614705995 2103511038058671922058993)
            ·
              refine ⟨1577633278544003941544245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103511038058671922058993 1577633278544003941544245)
              ·
                refine ⟨147903119863500369519773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577633278544003941544245 147903119863500369519773)
                ·
                  rfl

theorem cell20_972136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_972136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972136 prefixEnd_972136 := by exact prefixLift 972136
  have htrace : WordTrace (prefixWord ++ tailWord_972136) baseStart_972136 baseEnd_972136 := by
    simpa [prefixWord, tailWord_972136, baseEnd_972136] using wordTrace_append hprefix tailTrace_972136
  have hstable : (prefixWord ++ tailWord_972136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972136).length < 2 ^ (prefixWord ++ tailWord_972136).sum := by decide
  have hdescent : baseEnd_972136 < baseStart_972136 := by decide
  rcases family_descends (prefixWord ++ tailWord_972136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972174 : List Nat := [4, 1, 1, 4, 3, 7]
def baseStart_972174 : Nat := 118140960795 + 972174 * 2 ^ 59
def prefixEnd_972174 : Nat := 4983230072969 + 3 ^ 40 * 972174 * 2
def baseEnd_972174 : Nat := 16434322363923772788611

theorem tailTrace_972174 : CollatzResearch.WordTrace tailWord_972174 prefixEnd_972174 16434322363923772788611 := by
  unfold tailWord_972174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432262347498388368207447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23638732519991404630439717 4432262347498388368207447)
  ·
    refine ⟨6648393521247582552311171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4432262347498388368207447 6648393521247582552311171)
    ·
      refine ⟨9972590281871373828466757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648393521247582552311171 9972590281871373828466757)
      ·
        refine ⟨1869860677850882592837517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9972590281871373828466757 1869860677850882592837517)
        ·
          refine ⟨701197754194080972314069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1869860677850882592837517 701197754194080972314069)
          ·
            refine ⟨16434322363923772788611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 701197754194080972314069 16434322363923772788611)
            ·
              rfl

theorem cell20_972174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 7].length) (baseStart_972174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972174 prefixEnd_972174 := by exact prefixLift 972174
  have htrace : WordTrace (prefixWord ++ tailWord_972174) baseStart_972174 baseEnd_972174 := by
    simpa [prefixWord, tailWord_972174, baseEnd_972174] using wordTrace_append hprefix tailTrace_972174
  have hstable : (prefixWord ++ tailWord_972174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972174).length < 2 ^ (prefixWord ++ tailWord_972174).sum := by decide
  have hdescent : baseEnd_972174 < baseStart_972174 := by decide
  rcases family_descends (prefixWord ++ tailWord_972174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972184 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 2]
def baseStart_972184 : Nat := 118140960795 + 972184 * 2 ^ 59
def prefixEnd_972184 : Nat := 4983230072969 + 3 ^ 40 * 972184 * 2
def baseEnd_972184 : Nat := 443731268098426274959123

theorem tailTrace_972184 : CollatzResearch.WordTrace tailWord_972184 prefixEnd_972184 443731268098426274959123 := by
  unfold tailWord_972184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729231754975439326761803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23638975673300585769015737 17729231754975439326761803)
  ·
    refine ⟨26593847632463158990142705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17729231754975439326761803 26593847632463158990142705)
    ·
      refine ⟨19945385724347369242607029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26593847632463158990142705 19945385724347369242607029)
      ·
        refine ⟨1869879911657565866494409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19945385724347369242607029 1869879911657565866494409)
        ·
          refine ⟨1402409933743174399870807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869879911657565866494409 1402409933743174399870807)
          ·
            refine ⟨2103614900614761599806211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402409933743174399870807 2103614900614761599806211)
            ·
              refine ⟨3155422350922142399709317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103614900614761599806211 3155422350922142399709317)
              ·
                refine ⟨591641690797901699945497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3155422350922142399709317 591641690797901699945497)
                ·
                  refine ⟨443731268098426274959123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591641690797901699945497 443731268098426274959123)
                  ·
                    rfl

theorem cell20_972184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_972184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972184 prefixEnd_972184 := by exact prefixLift 972184
  have htrace : WordTrace (prefixWord ++ tailWord_972184) baseStart_972184 baseEnd_972184 := by
    simpa [prefixWord, tailWord_972184, baseEnd_972184] using wordTrace_append hprefix tailTrace_972184
  have hstable : (prefixWord ++ tailWord_972184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972184).length < 2 ^ (prefixWord ++ tailWord_972184).sum := by decide
  have hdescent : baseEnd_972184 < baseStart_972184 := by decide
  rcases family_descends (prefixWord ++ tailWord_972184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972205 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_972205 : Nat := 118140960795 + 972205 * 2 ^ 59
def prefixEnd_972205 : Nat := 4983230072969 + 3 ^ 40 * 972205 * 2
def baseEnd_972205 : Nat := 443740853070643535259037

theorem tailTrace_972205 : CollatzResearch.WordTrace tailWord_972205 prefixEnd_972205 443740853070643535259037 := by
  unfold tailWord_972205
  simp only [CollatzResearch.WordTrace]
  refine ⟨35459229442874799240038069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23639486295249866160025379 35459229442874799240038069)
  ·
    refine ⟨3324302760269512428753569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35459229442874799240038069 3324302760269512428753569)
    ·
      refine ⟨2493227070202134321565177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3324302760269512428753569 2493227070202134321565177)
      ·
        refine ⟨1869920302651600741173883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2493227070202134321565177 1869920302651600741173883)
        ·
          refine ⟨2804880453977401111760825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869920302651600741173883 2804880453977401111760825)
          ·
            refine ⟨2103660340483050833820619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2804880453977401111760825 2103660340483050833820619)
            ·
              refine ⟨3155490510724576250730929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103660340483050833820619 3155490510724576250730929)
              ·
                refine ⟨2366617883043432188048197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155490510724576250730929 2366617883043432188048197)
                ·
                  refine ⟨443740853070643535259037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366617883043432188048197 443740853070643535259037)
                  ·
                    rfl

theorem cell20_972205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_972205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972205 prefixEnd_972205 := by exact prefixLift 972205
  have htrace : WordTrace (prefixWord ++ tailWord_972205) baseStart_972205 baseEnd_972205 := by
    simpa [prefixWord, tailWord_972205, baseEnd_972205] using wordTrace_append hprefix tailTrace_972205
  have hstable : (prefixWord ++ tailWord_972205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972205).length < 2 ^ (prefixWord ++ tailWord_972205).sum := by decide
  have hdescent : baseEnd_972205 < baseStart_972205 := by decide
  rcases family_descends (prefixWord ++ tailWord_972205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972216 : List Nat := [2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_972216 : Nat := 118140960795 + 972216 * 2 ^ 59
def prefixEnd_972216 : Nat := 4983230072969 + 3 ^ 40 * 972216 * 2
def baseEnd_972216 : Nat := 147915291256792128630775

theorem tailTrace_972216 : CollatzResearch.WordTrace tailWord_972216 prefixEnd_972216 147915291256792128630775 := by
  unfold tailWord_972216
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729815322917474059344251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23639753763889965412459001 17729815322917474059344251)
  ·
    refine ⟨26594722984376211089016377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17729815322917474059344251 26594722984376211089016377)
    ·
      refine ⟨19946042238282158316762283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26594722984376211089016377 19946042238282158316762283)
      ·
        refine ⟨29919063357423237475143425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19946042238282158316762283 29919063357423237475143425)
        ·
          refine ⟨22439297518067428106357569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29919063357423237475143425 22439297518067428106357569)
          ·
            refine ⟨16829473138550571079768177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22439297518067428106357569 16829473138550571079768177)
            ·
              refine ⟨12622104853912928309826133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16829473138550571079768177 12622104853912928309826133)
              ·
                refine ⟨147915291256792128630775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12622104853912928309826133 147915291256792128630775)
                ·
                  rfl

theorem cell20_972216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_972216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972216 prefixEnd_972216 := by exact prefixLift 972216
  have htrace : WordTrace (prefixWord ++ tailWord_972216) baseStart_972216 baseEnd_972216 := by
    simpa [prefixWord, tailWord_972216, baseEnd_972216] using wordTrace_append hprefix tailTrace_972216
  have hstable : (prefixWord ++ tailWord_972216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972216).length < 2 ^ (prefixWord ++ tailWord_972216).sum := by decide
  have hdescent : baseEnd_972216 < baseStart_972216 := by decide
  rcases family_descends (prefixWord ++ tailWord_972216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972236 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_972236 : Nat := 118140960795 + 972236 * 2 ^ 59
def prefixEnd_972236 : Nat := 4983230072969 + 3 ^ 40 * 972236 * 2
def baseEnd_972236 : Nat := 443755002315345205225577

theorem tailTrace_972236 : CollatzResearch.WordTrace tailWord_972236 prefixEnd_972236 443755002315345205225577 := by
  unfold tailWord_972236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17730180052881245767208281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23640240070508327689611041 17730180052881245767208281)
  ·
    refine ⟨13297635039660934325406211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17730180052881245767208281 13297635039660934325406211)
    ·
      refine ⟨19946452559491401488109317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13297635039660934325406211 19946452559491401488109317)
      ·
        refine ⟨3739959854904637779020497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19946452559491401488109317 3739959854904637779020497)
        ·
          refine ⟨2804969891178478334265373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739959854904637779020497 2804969891178478334265373)
          ·
            refine ⟨1051863709191929375349515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2804969891178478334265373 1051863709191929375349515)
            ·
              refine ⟨1577795563787894063024273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051863709191929375349515 1577795563787894063024273)
              ·
                refine ⟨1183346672840920547268205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577795563787894063024273 1183346672840920547268205)
                ·
                  refine ⟨443755002315345205225577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183346672840920547268205 443755002315345205225577)
                  ·
                    rfl

theorem cell20_972236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_972236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972236 prefixEnd_972236 := by exact prefixLift 972236
  have htrace : WordTrace (prefixWord ++ tailWord_972236) baseStart_972236 baseEnd_972236 := by
    simpa [prefixWord, tailWord_972236, baseEnd_972236] using wordTrace_append hprefix tailTrace_972236
  have hstable : (prefixWord ++ tailWord_972236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972236).length < 2 ^ (prefixWord ++ tailWord_972236).sum := by decide
  have hdescent : baseEnd_972236 < baseStart_972236 := by decide
  rcases family_descends (prefixWord ++ tailWord_972236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972271 : List Nat := [1, 1, 2, 1, 4, 1, 6, 4]
def baseStart_972271 : Nat := 118140960795 + 972271 * 2 ^ 59
def prefixEnd_972271 : Nat := 4983230072969 + 3 ^ 40 * 972271 * 2
def baseEnd_972271 : Nat := 147923659089680213019589

theorem tailTrace_972271 : CollatzResearch.WordTrace tailWord_972271 prefixEnd_972271 147923659089680213019589 := by
  unfold tailWord_972271
  simp only [CollatzResearch.WordTrace]
  refine ⟨35461636660635692511940667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23641091107090461674627111 35461636660635692511940667)
  ·
    refine ⟨53192454990953538767911001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35461636660635692511940667 53192454990953538767911001)
    ·
      refine ⟨39894341243215154075933251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53192454990953538767911001 39894341243215154075933251)
      ·
        refine ⟨59841511864822731113899877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39894341243215154075933251 59841511864822731113899877)
        ·
          refine ⟨11220283474654262083856227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59841511864822731113899877 11220283474654262083856227)
          ·
            refine ⟨16830425211981393125784341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11220283474654262083856227 16830425211981393125784341)
            ·
              refine ⟨788926181811627802771141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16830425211981393125784341 788926181811627802771141)
              ·
                refine ⟨147923659089680213019589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788926181811627802771141 147923659089680213019589)
                ·
                  rfl

theorem cell20_972271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_972271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972271 prefixEnd_972271 := by exact prefixLift 972271
  have htrace : WordTrace (prefixWord ++ tailWord_972271) baseStart_972271 baseEnd_972271 := by
    simpa [prefixWord, tailWord_972271, baseEnd_972271] using wordTrace_append hprefix tailTrace_972271
  have hstable : (prefixWord ++ tailWord_972271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972271).length < 2 ^ (prefixWord ++ tailWord_972271).sum := by decide
  have hdescent : baseEnd_972271 < baseStart_972271 := by decide
  rcases family_descends (prefixWord ++ tailWord_972271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972277 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 2]
def baseStart_972277 : Nat := 118140960795 + 972277 * 2 ^ 59
def prefixEnd_972277 : Nat := 4983230072969 + 3 ^ 40 * 972277 * 2
def baseEnd_972277 : Nat := 443773715832531284858743

theorem tailTrace_972277 : CollatzResearch.WordTrace tailWord_972277 prefixEnd_972277 443773715832531284858743 := by
  unfold tailWord_972277
  simp only [CollatzResearch.WordTrace]
  refine ⟨35461855498613955536659085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23641236999075970357772723 35461855498613955536659085)
  ·
    refine ⟨13298195811980233326247157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35461855498613955536659085 13298195811980233326247157)
    ·
      refine ⟨1246705857373146874335671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13298195811980233326247157 1246705857373146874335671)
      ·
        refine ⟨1870058786059720311503507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246705857373146874335671 1870058786059720311503507)
        ·
          refine ⟨2805088179089580467255261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870058786059720311503507 2805088179089580467255261)
          ·
            refine ⟨1051908067158592675220723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2805088179089580467255261 1051908067158592675220723)
            ·
              refine ⟨1577862100737889012831085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051908067158592675220723 1577862100737889012831085)
              ·
                refine ⟨591698287776708379811657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577862100737889012831085 591698287776708379811657)
                ·
                  refine ⟨443773715832531284858743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591698287776708379811657 443773715832531284858743)
                  ·
                    rfl

theorem cell20_972277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_972277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972277 prefixEnd_972277 := by exact prefixLift 972277
  have htrace : WordTrace (prefixWord ++ tailWord_972277) baseStart_972277 baseEnd_972277 := by
    simpa [prefixWord, tailWord_972277, baseEnd_972277] using wordTrace_append hprefix tailTrace_972277
  have hstable : (prefixWord ++ tailWord_972277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972277).length < 2 ^ (prefixWord ++ tailWord_972277).sum := by decide
  have hdescent : baseEnd_972277 < baseStart_972277 := by decide
  rcases family_descends (prefixWord ++ tailWord_972277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972294 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_972294 : Nat := 118140960795 + 972294 * 2 ^ 59
def prefixEnd_972294 : Nat := 4983230072969 + 3 ^ 40 * 972294 * 2
def baseEnd_972294 : Nat := 443781475095754781292007

theorem tailTrace_972294 : CollatzResearch.WordTrace tailWord_972294 prefixEnd_972294 443781475095754781292007 := by
  unfold tailWord_972294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108202360611011482500873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23641650359701578293351957 1108202360611011482500873)
  ·
    refine ⟨831151770458258611875655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1108202360611011482500873 831151770458258611875655)
    ·
      refine ⟨1246727655687387917813483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831151770458258611875655 1246727655687387917813483)
      ·
        refine ⟨1870091483531081876720225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246727655687387917813483 1870091483531081876720225)
        ·
          refine ⟨1402568612648311407540169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870091483531081876720225 1402568612648311407540169)
          ·
            refine ⟨1051926459486233555655127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402568612648311407540169 1051926459486233555655127)
            ·
              refine ⟨1577889689229350333482691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051926459486233555655127 1577889689229350333482691)
              ·
                refine ⟨2366834533844025500224037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577889689229350333482691 2366834533844025500224037)
                ·
                  refine ⟨443781475095754781292007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366834533844025500224037 443781475095754781292007)
                  ·
                    rfl

theorem cell20_972294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_972294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972294 prefixEnd_972294 := by exact prefixLift 972294
  have htrace : WordTrace (prefixWord ++ tailWord_972294) baseStart_972294 baseEnd_972294 := by
    simpa [prefixWord, tailWord_972294, baseEnd_972294] using wordTrace_append hprefix tailTrace_972294
  have hstable : (prefixWord ++ tailWord_972294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972294).length < 2 ^ (prefixWord ++ tailWord_972294).sum := by decide
  have hdescent : baseEnd_972294 < baseStart_972294 := by decide
  rcases family_descends (prefixWord ++ tailWord_972294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972298 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_972298 : Nat := 118140960795 + 972298 * 2 ^ 59
def prefixEnd_972298 : Nat := 4983230072969 + 3 ^ 40 * 972298 * 2
def baseEnd_972298 : Nat := 443783300804748545158657

theorem tailTrace_972298 : CollatzResearch.WordTrace tailWord_972298 prefixEnd_972298 443783300804748545158657 := by
  unfold tailWord_972298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865655357884469030793387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23641747621025250748782365 8865655357884469030793387)
  ·
    refine ⟨13298483036826703546190081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8865655357884469030793387 13298483036826703546190081)
    ·
      refine ⟨9973862277620027659642561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13298483036826703546190081 9973862277620027659642561)
      ·
        refine ⟨7480396708215020744731921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9973862277620027659642561 7480396708215020744731921)
        ·
          refine ⟨5610297531161265558548941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7480396708215020744731921 5610297531161265558548941)
          ·
            refine ⟨2103861574185474584455853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5610297531161265558548941 2103861574185474584455853)
            ·
              refine ⟨788948090319552969170945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2103861574185474584455853 788948090319552969170945)
              ·
                refine ⟨591711067739664726878209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788948090319552969170945 591711067739664726878209)
                ·
                  refine ⟨443783300804748545158657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591711067739664726878209 443783300804748545158657)
                  ·
                    rfl

theorem cell20_972298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_972298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972298 prefixEnd_972298 := by exact prefixLift 972298
  have htrace : WordTrace (prefixWord ++ tailWord_972298) baseStart_972298 baseEnd_972298 := by
    simpa [prefixWord, tailWord_972298, baseEnd_972298] using wordTrace_append hprefix tailTrace_972298
  have hstable : (prefixWord ++ tailWord_972298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972298).length < 2 ^ (prefixWord ++ tailWord_972298).sum := by decide
  have hdescent : baseEnd_972298 < baseStart_972298 := by decide
  rcases family_descends (prefixWord ++ tailWord_972298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972308 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_972308 : Nat := 118140960795 + 972308 * 2 ^ 59
def prefixEnd_972308 : Nat := 4983230072969 + 3 ^ 40 * 972308 * 2
def baseEnd_972308 : Nat := 443787865077232954825283

theorem tailTrace_972308 : CollatzResearch.WordTrace tailWord_972308 prefixEnd_972308 443787865077232954825283 := by
  unfold tailWord_972308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731493080750823915518789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23641990774334431887358385 17731493080750823915518789)
  ·
    refine ⟨3324654952640779484159773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17731493080750823915518789 3324654952640779484159773)
    ·
      refine ⟨1246745607240292306559915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3324654952640779484159773 1246745607240292306559915)
      ·
        refine ⟨1870118410860438459839873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246745607240292306559915 1870118410860438459839873)
        ·
          refine ⟨1402588808145328844879905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870118410860438459839873 1402588808145328844879905)
          ·
            refine ⟨1051941606108996633659929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402588808145328844879905 1051941606108996633659929)
            ·
              refine ⟨788956204581747475244947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051941606108996633659929 788956204581747475244947)
              ·
                refine ⟨1183434306872621212867421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788956204581747475244947 1183434306872621212867421)
                ·
                  refine ⟨443787865077232954825283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183434306872621212867421 443787865077232954825283)
                  ·
                    rfl

theorem cell20_972308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_972308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972308 prefixEnd_972308 := by exact prefixLift 972308
  have htrace : WordTrace (prefixWord ++ tailWord_972308) baseStart_972308 baseEnd_972308 := by
    simpa [prefixWord, tailWord_972308, baseEnd_972308] using wordTrace_append hprefix tailTrace_972308
  have hstable : (prefixWord ++ tailWord_972308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972308).length < 2 ^ (prefixWord ++ tailWord_972308).sum := by decide
  have hdescent : baseEnd_972308 < baseStart_972308 := by decide
  rcases family_descends (prefixWord ++ tailWord_972308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972309 : List Nat := [1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_972309 : Nat := 118140960795 + 972309 * 2 ^ 59
def prefixEnd_972309 : Nat := 4983230072969 + 3 ^ 40 * 972309 * 2
def baseEnd_972309 : Nat := 147929440501493798597315

theorem tailTrace_972309 : CollatzResearch.WordTrace tailWord_972309 prefixEnd_972309 147929440501493798597315 := by
  unfold tailWord_972309
  simp only [CollatzResearch.WordTrace]
  refine ⟨35463022634498025001823981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23642015089665350001215987 35463022634498025001823981)
  ·
    refine ⟨13298633487936759375683993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35463022634498025001823981 13298633487936759375683993)
    ·
      refine ⟨9973975115952569531762995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13298633487936759375683993 9973975115952569531762995)
      ·
        refine ⟨14960962673928854297644493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9973975115952569531762995 14960962673928854297644493)
        ·
          refine ⟨5610361002723320361616685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14960962673928854297644493 5610361002723320361616685)
          ·
            refine ⟨2103885376021245135606257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5610361002723320361616685 2103885376021245135606257)
            ·
              refine ⟨1577914032015933851704693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103885376021245135606257 1577914032015933851704693)
              ·
                refine ⟨147929440501493798597315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577914032015933851704693 147929440501493798597315)
                ·
                  rfl

theorem cell20_972309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_972309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972309 prefixEnd_972309 := by exact prefixLift 972309
  have htrace : WordTrace (prefixWord ++ tailWord_972309) baseStart_972309 baseEnd_972309 := by
    simpa [prefixWord, tailWord_972309, baseEnd_972309] using wordTrace_append hprefix tailTrace_972309
  have hstable : (prefixWord ++ tailWord_972309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972309).length < 2 ^ (prefixWord ++ tailWord_972309).sum := by decide
  have hdescent : baseEnd_972309 < baseStart_972309 := by decide
  rcases family_descends (prefixWord ++ tailWord_972309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972385 : List Nat := [1, 2, 3, 1, 1, 3, 5, 4]
def baseStart_972385 : Nat := 118140960795 + 972385 * 2 ^ 59
def prefixEnd_972385 : Nat := 4983230072969 + 3 ^ 40 * 972385 * 2
def baseEnd_972385 : Nat := 147941003325120969752767

theorem tailTrace_972385 : CollatzResearch.WordTrace tailWord_972385 prefixEnd_972385 147941003325120969752767 := by
  unfold tailWord_972385
  simp only [CollatzResearch.WordTrace]
  refine ⟨35465794582222689981590609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23643863054815126654393739 35465794582222689981590609)
  ·
    refine ⟨26599345936667017486192957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35465794582222689981590609 26599345936667017486192957)
    ·
      refine ⟨9974754726250131557322359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26599345936667017486192957 9974754726250131557322359)
      ·
        refine ⟨14962132089375197335983539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9974754726250131557322359 14962132089375197335983539)
        ·
          refine ⟨22443198134062796003975309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14962132089375197335983539 22443198134062796003975309)
          ·
            refine ⟨8416199300273548501490741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22443198134062796003975309 8416199300273548501490741)
            ·
              refine ⟨789018684400645172014757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8416199300273548501490741 789018684400645172014757)
              ·
                refine ⟨147941003325120969752767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789018684400645172014757 147941003325120969752767)
                ·
                  rfl

theorem cell20_972385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_972385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972385 prefixEnd_972385 := by exact prefixLift 972385
  have htrace : WordTrace (prefixWord ++ tailWord_972385) baseStart_972385 baseEnd_972385 := by
    simpa [prefixWord, tailWord_972385, baseEnd_972385] using wordTrace_append hprefix tailTrace_972385
  have hstable : (prefixWord ++ tailWord_972385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972385).length < 2 ^ (prefixWord ++ tailWord_972385).sum := by decide
  have hdescent : baseEnd_972385 < baseStart_972385 := by decide
  rcases family_descends (prefixWord ++ tailWord_972385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972416 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 2]
def baseStart_972416 : Nat := 118140960795 + 972416 * 2 ^ 59
def prefixEnd_972416 : Nat := 4983230072969 + 3 ^ 40 * 972416 * 2
def baseEnd_972416 : Nat := 443837159220064579224841

theorem tailTrace_972416 : CollatzResearch.WordTrace tailWord_972416 prefixEnd_972416 443837159220064579224841 := by
  unfold tailWord_972416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733462622555191137984551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23644616830073588183979401 17733462622555191137984551)
  ·
    refine ⟨26600193933832786706976827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17733462622555191137984551 26600193933832786706976827)
    ·
      refine ⟨39900290900749180060465241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26600193933832786706976827 39900290900749180060465241)
      ·
        refine ⟨29925218175561885045348931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39900290900749180060465241 29925218175561885045348931)
        ·
          refine ⟨44887827263342827568023397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29925218175561885045348931 44887827263342827568023397)
          ·
            refine ⟨8416467611876780169004387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44887827263342827568023397 8416467611876780169004387)
            ·
              refine ⟨12624701417815170253506581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416467611876780169004387 12624701417815170253506581)
              ·
                refine ⟨591782878960086105633121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12624701417815170253506581 591782878960086105633121)
                ·
                  refine ⟨443837159220064579224841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591782878960086105633121 443837159220064579224841)
                  ·
                    rfl

theorem cell20_972416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_972416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972416 prefixEnd_972416 := by exact prefixLift 972416
  have htrace : WordTrace (prefixWord ++ tailWord_972416) baseStart_972416 baseEnd_972416 := by
    simpa [prefixWord, tailWord_972416, baseEnd_972416] using wordTrace_append hprefix tailTrace_972416
  have hstable : (prefixWord ++ tailWord_972416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972416).length < 2 ^ (prefixWord ++ tailWord_972416).sum := by decide
  have hdescent : baseEnd_972416 < baseStart_972416 := by decide
  rcases family_descends (prefixWord ++ tailWord_972416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972426 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_972426 : Nat := 118140960795 + 972426 * 2 ^ 59
def prefixEnd_972426 : Nat := 4983230072969 + 3 ^ 40 * 972426 * 2
def baseEnd_972426 : Nat := 443841723492548988891467

theorem tailTrace_972426 : CollatzResearch.WordTrace tailWord_972426 prefixEnd_972426 443841723492548988891467 := by
  unfold tailWord_972426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866822493768538495958283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23644859983382769322555421 8866822493768538495958283)
  ·
    refine ⟨13300233740652807743937425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8866822493768538495958283 13300233740652807743937425)
    ·
      refine ⟨9975175305489605807953069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13300233740652807743937425 9975175305489605807953069)
      ·
        refine ⟨3740690739558602177982401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9975175305489605807953069 3740690739558602177982401)
        ·
          refine ⟨2805518054668951633486801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740690739558602177982401 2805518054668951633486801)
          ·
            refine ⟨2104138541001713725115101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2805518054668951633486801 2104138541001713725115101)
            ·
              refine ⟨789051952875642646918163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2104138541001713725115101 789051952875642646918163)
              ·
                refine ⟨1183577929313463970377245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789051952875642646918163 1183577929313463970377245)
                ·
                  refine ⟨443841723492548988891467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183577929313463970377245 443841723492548988891467)
                  ·
                    rfl

theorem cell20_972426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_972426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972426 prefixEnd_972426 := by exact prefixLift 972426
  have htrace : WordTrace (prefixWord ++ tailWord_972426) baseStart_972426 baseEnd_972426 := by
    simpa [prefixWord, tailWord_972426, baseEnd_972426] using wordTrace_append hprefix tailTrace_972426
  have hstable : (prefixWord ++ tailWord_972426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972426).length < 2 ^ (prefixWord ++ tailWord_972426).sum := by decide
  have hdescent : baseEnd_972426 < baseStart_972426 := by decide
  rcases family_descends (prefixWord ++ tailWord_972426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972436 : List Nat := [2, 4, 2, 2, 3, 1, 2, 4]
def baseStart_972436 : Nat := 118140960795 + 972436 * 2 ^ 59
def prefixEnd_972436 : Nat := 4983230072969 + 3 ^ 40 * 972436 * 2
def baseEnd_972436 : Nat := 147948762588344466186031

theorem tailTrace_972436 : CollatzResearch.WordTrace tailWord_972436 prefixEnd_972436 147948762588344466186031 := by
  unfold tailWord_972436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733827352518962845848581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23645103136691950461131441 17733827352518962845848581)
  ·
    refine ⟨3325092628597305533596609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17733827352518962845848581 3325092628597305533596609)
    ·
      refine ⟨2493819471447979150197457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325092628597305533596609 2493819471447979150197457)
      ·
        refine ⟨1870364603585984362648093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2493819471447979150197457 1870364603585984362648093)
        ·
          refine ⟨701386726344744135993035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1870364603585984362648093 701386726344744135993035)
          ·
            refine ⟨1052080089517116203989553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701386726344744135993035 1052080089517116203989553)
            ·
              refine ⟨789060067137837152992165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052080089517116203989553 789060067137837152992165)
              ·
                refine ⟨147948762588344466186031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789060067137837152992165 147948762588344466186031)
                ·
                  rfl

theorem cell20_972436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_972436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972436 prefixEnd_972436 := by exact prefixLift 972436
  have htrace : WordTrace (prefixWord ++ tailWord_972436) baseStart_972436 baseEnd_972436 := by
    simpa [prefixWord, tailWord_972436, baseEnd_972436] using wordTrace_append hprefix tailTrace_972436
  have hstable : (prefixWord ++ tailWord_972436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972436).length < 2 ^ (prefixWord ++ tailWord_972436).sum := by decide
  have hdescent : baseEnd_972436 < baseStart_972436 := by decide
  rcases family_descends (prefixWord ++ tailWord_972436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972440 : List Nat := [2, 1, 2, 4, 1, 4, 2, 4]
def baseStart_972440 : Nat := 118140960795 + 972440 * 2 ^ 59
def prefixEnd_972440 : Nat := 4983230072969 + 3 ^ 40 * 972440 * 2
def baseEnd_972440 : Nat := 147949371158009054141581

theorem tailTrace_972440 : CollatzResearch.WordTrace tailWord_972440 prefixEnd_972440 147949371158009054141581 := by
  unfold tailWord_972440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733900298511717187421387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23645200398015622916561849 17733900298511717187421387)
  ·
    refine ⟨26600850447767575781132081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17733900298511717187421387 26600850447767575781132081)
    ·
      refine ⟨19950637835825681835849061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26600850447767575781132081 19950637835825681835849061)
      ·
        refine ⟨3740744594217315344221699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19950637835825681835849061 3740744594217315344221699)
        ·
          refine ⟨5611116891325973016332549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740744594217315344221699 5611116891325973016332549)
          ·
            refine ⟨1052084417123619940562353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5611116891325973016332549 1052084417123619940562353)
            ·
              refine ⟨789063312842714955421765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052084417123619940562353 789063312842714955421765)
              ·
                refine ⟨147949371158009054141581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789063312842714955421765 147949371158009054141581)
                ·
                  rfl

theorem cell20_972440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_972440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972440 prefixEnd_972440 := by exact prefixLift 972440
  have htrace : WordTrace (prefixWord ++ tailWord_972440) baseStart_972440 baseEnd_972440 := by
    simpa [prefixWord, tailWord_972440, baseEnd_972440] using wordTrace_append hprefix tailTrace_972440
  have hstable : (prefixWord ++ tailWord_972440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972440).length < 2 ^ (prefixWord ++ tailWord_972440).sum := by decide
  have hdescent : baseEnd_972440 < baseStart_972440 := by decide
  rcases family_descends (prefixWord ++ tailWord_972440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972451 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_972451 : Nat := 118140960795 + 972451 * 2 ^ 59
def prefixEnd_972451 : Nat := 4983230072969 + 3 ^ 40 * 972451 * 2
def baseEnd_972451 : Nat := 443853134173760013058031

theorem tailTrace_972451 : CollatzResearch.WordTrace tailWord_972451 prefixEnd_972451 443853134173760013058031 := by
  unfold tailWord_972451
  simp only [CollatzResearch.WordTrace]
  refine ⟨35468201799983583253493207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23645467866655722168995471 35468201799983583253493207)
  ·
    refine ⟨53202302699975374880239811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35468201799983583253493207 53202302699975374880239811)
    ·
      refine ⟨79803454049963062320359717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53202302699975374880239811 79803454049963062320359717)
      ·
        refine ⟨14963147634368074185067447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79803454049963062320359717 14963147634368074185067447)
        ·
          refine ⟨22444721451552111277601171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14963147634368074185067447 22444721451552111277601171)
          ·
            refine ⟨33667082177328166916401757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22444721451552111277601171 33667082177328166916401757)
            ·
              refine ⟨12625155816498062593650659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33667082177328166916401757 12625155816498062593650659)
              ·
                refine ⟨18937733724747093890475989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625155816498062593650659 18937733724747093890475989)
                ·
                  refine ⟨443853134173760013058031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18937733724747093890475989 443853134173760013058031)
                  ·
                    rfl

theorem cell20_972451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_972451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972451 prefixEnd_972451 := by exact prefixLift 972451
  have htrace : WordTrace (prefixWord ++ tailWord_972451) baseStart_972451 baseEnd_972451 := by
    simpa [prefixWord, tailWord_972451, baseEnd_972451] using wordTrace_append hprefix tailTrace_972451
  have hstable : (prefixWord ++ tailWord_972451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972451).length < 2 ^ (prefixWord ++ tailWord_972451).sum := by decide
  have hdescent : baseEnd_972451 < baseStart_972451 := by decide
  rcases family_descends (prefixWord ++ tailWord_972451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972520 : List Nat := [2, 1, 4, 1, 3, 9]
def baseStart_972520 : Nat := 118140960795 + 972520 * 2 ^ 59
def prefixEnd_972520 : Nat := 4983230072969 + 3 ^ 40 * 972520 * 2
def baseEnd_972520 : Nat := 16440171394588979250287

theorem tailTrace_972520 : CollatzResearch.WordTrace tailWord_972520 prefixEnd_972520 16440171394588979250287 := by
  unfold tailWord_972520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17735359218366804018877507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23647145624489072025170009 17735359218366804018877507)
  ·
    refine ⟨26603038827550206028316261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17735359218366804018877507 26603038827550206028316261)
    ·
      refine ⟨4988069780165663630309299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26603038827550206028316261 4988069780165663630309299)
      ·
        refine ⟨7482104670248495445463949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988069780165663630309299 7482104670248495445463949)
        ·
          refine ⟨2805789251343185792048981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7482104670248495445463949 2805789251343185792048981)
          ·
            refine ⟨16440171394588979250287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2805789251343185792048981 16440171394588979250287)
            ·
              rfl

theorem cell20_972520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 9].length) (baseStart_972520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972520 prefixEnd_972520 := by exact prefixLift 972520
  have htrace : WordTrace (prefixWord ++ tailWord_972520) baseStart_972520 baseEnd_972520 := by
    simpa [prefixWord, tailWord_972520, baseEnd_972520] using wordTrace_append hprefix tailTrace_972520
  have hstable : (prefixWord ++ tailWord_972520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972520).length < 2 ^ (prefixWord ++ tailWord_972520).sum := by decide
  have hdescent : baseEnd_972520 < baseStart_972520 := by decide
  rcases family_descends (prefixWord ++ tailWord_972520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972558 : List Nat := [4, 1, 1, 2, 1, 1, 2, 8]
def baseStart_972558 : Nat := 118140960795 + 972558 * 2 ^ 59
def prefixEnd_972558 : Nat := 4983230072969 + 3 ^ 40 * 972558 * 2
def baseEnd_972558 : Nat := 147967323963114398830309

theorem tailTrace_972558 : CollatzResearch.WordTrace tailWord_972558 prefixEnd_972558 147967323963114398830309 := by
  unfold tailWord_972558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434013051324492565954791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23648069607063960351758885 4434013051324492565954791)
  ·
    refine ⟨6651019576986738848932187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4434013051324492565954791 6651019576986738848932187)
    ·
      refine ⟨9976529365480108273398281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651019576986738848932187 9976529365480108273398281)
      ·
        refine ⟨7482397024110081205048711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9976529365480108273398281 7482397024110081205048711)
        ·
          refine ⟨11223595536165121807573067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482397024110081205048711 11223595536165121807573067)
          ·
            refine ⟨16835393304247682711359601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223595536165121807573067 16835393304247682711359601)
            ·
              refine ⟨12626544978185762033519701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16835393304247682711359601 12626544978185762033519701)
              ·
                refine ⟨147967323963114398830309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12626544978185762033519701 147967323963114398830309)
                ·
                  rfl

theorem cell20_972558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_972558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972558 prefixEnd_972558 := by exact prefixLift 972558
  have htrace : WordTrace (prefixWord ++ tailWord_972558) baseStart_972558 baseEnd_972558 := by
    simpa [prefixWord, tailWord_972558, baseEnd_972558] using wordTrace_append hprefix tailTrace_972558
  have hstable : (prefixWord ++ tailWord_972558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972558).length < 2 ^ (prefixWord ++ tailWord_972558).sum := by decide
  have hdescent : baseEnd_972558 < baseStart_972558 := by decide
  rcases family_descends (prefixWord ++ tailWord_972558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972568 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 2]
def baseStart_972568 : Nat := 118140960795 + 972568 * 2 ^ 59
def prefixEnd_972568 : Nat := 4983230072969 + 3 ^ 40 * 972568 * 2
def baseEnd_972568 : Nat := 443906536161827606157553

theorem tailTrace_972568 : CollatzResearch.WordTrace tailWord_972568 prefixEnd_972568 443906536161827606157553 := by
  unfold tailWord_972568
  simp only [CollatzResearch.WordTrace]
  refine ⟨17736234570279856117751179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23648312760373141490334905 17736234570279856117751179)
  ·
    refine ⟨26604351855419784176626769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17736234570279856117751179 26604351855419784176626769)
    ·
      refine ⟨19953263891564838132470077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26604351855419784176626769 19953263891564838132470077)
      ·
        refine ⟨7482473959336814299676279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19953263891564838132470077 7482473959336814299676279)
        ·
          refine ⟨11223710939005221449514419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482473959336814299676279 11223710939005221449514419)
          ·
            refine ⟨16835566408507832174271629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223710939005221449514419 16835566408507832174271629)
            ·
              refine ⟨6313337403190437065351861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16835566408507832174271629 6313337403190437065351861)
              ·
                refine ⟨591875381549103474876737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6313337403190437065351861 591875381549103474876737)
                ·
                  refine ⟨443906536161827606157553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591875381549103474876737 443906536161827606157553)
                  ·
                    rfl

theorem cell20_972568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_972568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972568 prefixEnd_972568 := by exact prefixLift 972568
  have htrace : WordTrace (prefixWord ++ tailWord_972568) baseStart_972568 baseEnd_972568 := by
    simpa [prefixWord, tailWord_972568, baseEnd_972568] using wordTrace_append hprefix tailTrace_972568
  have hstable : (prefixWord ++ tailWord_972568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972568).length < 2 ^ (prefixWord ++ tailWord_972568).sum := by decide
  have hdescent : baseEnd_972568 < baseStart_972568 := by decide
  rcases family_descends (prefixWord ++ tailWord_972568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972574 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_972574 : Nat := 118140960795 + 972574 * 2 ^ 59
def prefixEnd_972574 : Nat := 4983230072969 + 3 ^ 40 * 972574 * 2
def baseEnd_972574 : Nat := 443909274725318251957529

theorem tailTrace_972574 : CollatzResearch.WordTrace tailWord_972574 prefixEnd_972574 443909274725318251957529 := by
  unfold tailWord_972574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434085997317246907527597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23648458652358650173480517 4434085997317246907527597)
  ·
    refine ⟨1662782248993967590322849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4434085997317246907527597 1662782248993967590322849)
    ·
      refine ⟨1247086686745475692742137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1662782248993967590322849 1247086686745475692742137)
      ·
        refine ⟨935315015059106769556603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247086686745475692742137 935315015059106769556603)
        ·
          refine ⟨1402972522588660154334905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935315015059106769556603 1402972522588660154334905)
          ·
            refine ⟨1052229391941495115751179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402972522588660154334905 1052229391941495115751179)
            ·
              refine ⟨1578344087912242673626769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052229391941495115751179 1578344087912242673626769)
              ·
                refine ⟨1183758065934182005220077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578344087912242673626769 1183758065934182005220077)
                ·
                  refine ⟨443909274725318251957529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183758065934182005220077 443909274725318251957529)
                  ·
                    rfl

theorem cell20_972574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_972574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972574 prefixEnd_972574 := by exact prefixLift 972574
  have htrace : WordTrace (prefixWord ++ tailWord_972574) baseStart_972574 baseEnd_972574 := by
    simpa [prefixWord, tailWord_972574, baseEnd_972574] using wordTrace_append hprefix tailTrace_972574
  have hstable : (prefixWord ++ tailWord_972574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972574).length < 2 ^ (prefixWord ++ tailWord_972574).sum := by decide
  have hdescent : baseEnd_972574 < baseStart_972574 := by decide
  rcases family_descends (prefixWord ++ tailWord_972574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972606 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_972606 : Nat := 118140960795 + 972606 * 2 ^ 59
def prefixEnd_972606 : Nat := 4983230072969 + 3 ^ 40 * 972606 * 2
def baseEnd_972606 : Nat := 443923880397268362890731

theorem tailTrace_972606 : CollatzResearch.WordTrace tailWord_972606 prefixEnd_972606 443923880397268362890731 := by
  unfold tailWord_972606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434231889302755590673209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23649236742948029816923781 4434231889302755590673209)
  ·
    refine ⟨3325673916977066693004907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4434231889302755590673209 3325673916977066693004907)
    ·
      refine ⟨4988510875465600039507361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325673916977066693004907 4988510875465600039507361)
      ·
        refine ⟨3741383156599200029630521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4988510875465600039507361 3741383156599200029630521)
        ·
          refine ⟨2806037367449400022222891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741383156599200029630521 2806037367449400022222891)
          ·
            refine ⟨4209056051174100033334337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806037367449400022222891 4209056051174100033334337)
            ·
              refine ⟨3156792038380575025000753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209056051174100033334337 3156792038380575025000753)
              ·
                refine ⟨2367594028785431268750565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156792038380575025000753 2367594028785431268750565)
                ·
                  refine ⟨443923880397268362890731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2367594028785431268750565 443923880397268362890731)
                  ·
                    rfl

theorem cell20_972606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_972606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972606 prefixEnd_972606 := by exact prefixLift 972606
  have htrace : WordTrace (prefixWord ++ tailWord_972606) baseStart_972606 baseEnd_972606 := by
    simpa [prefixWord, tailWord_972606, baseEnd_972606] using wordTrace_append hprefix tailTrace_972606
  have hstable : (prefixWord ++ tailWord_972606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972606).length < 2 ^ (prefixWord ++ tailWord_972606).sum := by decide
  have hdescent : baseEnd_972606 < baseStart_972606 := by decide
  rcases family_descends (prefixWord ++ tailWord_972606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972641 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_972641 : Nat := 118140960795 + 972641 * 2 ^ 59
def prefixEnd_972641 : Nat := 4983230072969 + 3 ^ 40 * 972641 * 2
def baseEnd_972641 : Nat := 443939855350963796723921

theorem tailTrace_972641 : CollatzResearch.WordTrace tailWord_972641 prefixEnd_972641 443939855350963796723921 := by
  unfold tailWord_972641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35475131669295245702909777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23650087779530163801939851 35475131669295245702909777)
  ·
    refine ⟨26606348751971434277182333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35475131669295245702909777 26606348751971434277182333)
    ·
      refine ⟨9977380781989287853943375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26606348751971434277182333 9977380781989287853943375)
      ·
        refine ⟨14966071172983931780915063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9977380781989287853943375 14966071172983931780915063)
        ·
          refine ⟨22449106759475897671372595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966071172983931780915063 22449106759475897671372595)
          ·
            refine ⟨33673660139213846507058893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22449106759475897671372595 33673660139213846507058893)
            ·
              refine ⟨12627622552205192440147085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33673660139213846507058893 12627622552205192440147085)
              ·
                refine ⟨4735358457076947165055157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12627622552205192440147085 4735358457076947165055157)
                ·
                  refine ⟨443939855350963796723921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735358457076947165055157 443939855350963796723921)
                  ·
                    rfl

theorem cell20_972641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_972641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972641 prefixEnd_972641 := by exact prefixLift 972641
  have htrace : WordTrace (prefixWord ++ tailWord_972641) baseStart_972641 baseEnd_972641 := by
    simpa [prefixWord, tailWord_972641, baseEnd_972641] using wordTrace_append hprefix tailTrace_972641
  have hstable : (prefixWord ++ tailWord_972641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972641).length < 2 ^ (prefixWord ++ tailWord_972641).sum := by decide
  have hdescent : baseEnd_972641 < baseStart_972641 := by decide
  rcases family_descends (prefixWord ++ tailWord_972641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972650 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_972650 : Nat := 118140960795 + 972650 * 2 ^ 59
def prefixEnd_972650 : Nat := 4983230072969 + 3 ^ 40 * 972650 * 2
def baseEnd_972650 : Nat := 443943963196199765423885

theorem tailTrace_972650 : CollatzResearch.WordTrace tailWord_972650 prefixEnd_972650 443943963196199765423885 := by
  unfold tailWord_972650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868864981565660059996851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23650306617508426826658269 8868864981565660059996851)
  ·
    refine ⟨13303297472348490089995277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8868864981565660059996851 13303297472348490089995277)
    ·
      refine ⟨4988736552130683783748229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13303297472348490089995277 4988736552130683783748229)
      ·
        refine ⟨935388103524503209452793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4988736552130683783748229 935388103524503209452793)
        ·
          refine ⟨701541077643377407089595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935388103524503209452793 701541077643377407089595)
          ·
            refine ⟨1052311616465066110634393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701541077643377407089595 1052311616465066110634393)
            ·
              refine ⟨789233712348799582975795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052311616465066110634393 789233712348799582975795)
              ·
                refine ⟨1183850568523199374463693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789233712348799582975795 1183850568523199374463693)
                ·
                  refine ⟨443943963196199765423885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183850568523199374463693 443943963196199765423885)
                  ·
                    rfl

theorem cell20_972650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_972650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972650 prefixEnd_972650 := by exact prefixLift 972650
  have htrace : WordTrace (prefixWord ++ tailWord_972650) baseStart_972650 baseEnd_972650 := by
    simpa [prefixWord, tailWord_972650, baseEnd_972650] using wordTrace_append hprefix tailTrace_972650
  have hstable : (prefixWord ++ tailWord_972650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972650).length < 2 ^ (prefixWord ++ tailWord_972650).sum := by decide
  have hdescent : baseEnd_972650 < baseStart_972650 := by decide
  rcases family_descends (prefixWord ++ tailWord_972650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972654 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_972654 : Nat := 118140960795 + 972654 * 2 ^ 59
def prefixEnd_972654 : Nat := 4983230072969 + 3 ^ 40 * 972654 * 2
def baseEnd_972654 : Nat := 443945788905193529290535

theorem tailTrace_972654 : CollatzResearch.WordTrace tailWord_972654 prefixEnd_972654 443945788905193529290535 := by
  unfold tailWord_972654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434450727281018615391627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23650403878832099282088677 4434450727281018615391627)
  ·
    refine ⟨6651676090921527923087441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4434450727281018615391627 6651676090921527923087441)
    ·
      refine ⟨4988757068191145942315581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6651676090921527923087441 4988757068191145942315581)
      ·
        refine ⟨1870783900571679728368343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4988757068191145942315581 1870783900571679728368343)
        ·
          refine ⟨2806175850857519592552515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870783900571679728368343 2806175850857519592552515)
          ·
            refine ⟨4209263776286279388828773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806175850857519592552515 4209263776286279388828773)
            ·
              refine ⟨789236958053677385405395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4209263776286279388828773 789236958053677385405395)
              ·
                refine ⟨1183855437080516078108093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789236958053677385405395 1183855437080516078108093)
                ·
                  refine ⟨443945788905193529290535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183855437080516078108093 443945788905193529290535)
                  ·
                    rfl

theorem cell20_972654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_972654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972654 prefixEnd_972654 := by exact prefixLift 972654
  have htrace : WordTrace (prefixWord ++ tailWord_972654) baseStart_972654 baseEnd_972654 := by
    simpa [prefixWord, tailWord_972654, baseEnd_972654] using wordTrace_append hprefix tailTrace_972654
  have hstable : (prefixWord ++ tailWord_972654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972654).length < 2 ^ (prefixWord ++ tailWord_972654).sum := by decide
  have hdescent : baseEnd_972654 < baseStart_972654 := by decide
  rcases family_descends (prefixWord ++ tailWord_972654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972702 : List Nat := [4, 3, 1, 3, 2, 1, 1, 5]
def baseStart_972702 : Nat := 118140960795 + 972702 * 2 ^ 59
def prefixEnd_972702 : Nat := 4983230072969 + 3 ^ 40 * 972702 * 2
def baseEnd_972702 : Nat := 147989232471039565230113

theorem tailTrace_972702 : CollatzResearch.WordTrace tailWord_972702 prefixEnd_972702 147989232471039565230113 := by
  unfold tailWord_972702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434669565259281640110045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23651571014716168747253573 4434669565259281640110045)
  ·
    refine ⟨1663001086972230615041267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4434669565259281640110045 1663001086972230615041267)
    ·
      refine ⟨2494501630458345922561901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663001086972230615041267 2494501630458345922561901)
      ·
        refine ⟨935438111421879720960713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2494501630458345922561901 935438111421879720960713)
        ·
          refine ⟨701578583566409790720535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935438111421879720960713 701578583566409790720535)
          ·
            refine ⟨1052367875349614686080803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701578583566409790720535 1052367875349614686080803)
            ·
              refine ⟨1578551813024422029121205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052367875349614686080803 1578551813024422029121205)
              ·
                refine ⟨147989232471039565230113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1578551813024422029121205 147989232471039565230113)
                ·
                  rfl

theorem cell20_972702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_972702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972702 prefixEnd_972702 := by exact prefixLift 972702
  have htrace : WordTrace (prefixWord ++ tailWord_972702) baseStart_972702 baseEnd_972702 := by
    simpa [prefixWord, tailWord_972702, baseEnd_972702] using wordTrace_append hprefix tailTrace_972702
  have hstable : (prefixWord ++ tailWord_972702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972702).length < 2 ^ (prefixWord ++ tailWord_972702).sum := by decide
  have hdescent : baseEnd_972702 < baseStart_972702 := by decide
  rcases family_descends (prefixWord ++ tailWord_972702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972706 : List Nat := [3, 3, 1, 2, 3, 2, 1, 5]
def baseStart_972706 : Nat := 118140960795 + 972706 * 2 ^ 59
def prefixEnd_972706 : Nat := 4983230072969 + 3 ^ 40 * 972706 * 2
def baseEnd_972706 : Nat := 147989841040704153185663

theorem tailTrace_972706 : CollatzResearch.WordTrace tailWord_972706 prefixEnd_972706 147989841040704153185663 := by
  unfold tailWord_972706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8869375603514940451006493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23651668276039841202683981 8869375603514940451006493)
  ·
    refine ⟨3326015851318102669127435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8869375603514940451006493 3326015851318102669127435)
    ·
      refine ⟨4989023776977154003691153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326015851318102669127435 4989023776977154003691153)
      ·
        refine ⟨3741767832732865502768365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4989023776977154003691153 3741767832732865502768365)
        ·
          refine ⟨1403162937274824563538137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3741767832732865502768365 1403162937274824563538137)
          ·
            refine ⟨1052372202956118422653603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403162937274824563538137 1052372202956118422653603)
            ·
              refine ⟨1578558304434177633980405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052372202956118422653603 1578558304434177633980405)
              ·
                refine ⟨147989841040704153185663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1578558304434177633980405 147989841040704153185663)
                ·
                  rfl

theorem cell20_972706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_972706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972706 prefixEnd_972706 := by exact prefixLift 972706
  have htrace : WordTrace (prefixWord ++ tailWord_972706) baseStart_972706 baseEnd_972706 := by
    simpa [prefixWord, tailWord_972706, baseEnd_972706] using wordTrace_append hprefix tailTrace_972706
  have hstable : (prefixWord ++ tailWord_972706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972706).length < 2 ^ (prefixWord ++ tailWord_972706).sum := by decide
  have hdescent : baseEnd_972706 < baseStart_972706 := by decide
  rcases family_descends (prefixWord ++ tailWord_972706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972748 : List Nat := [2, 2, 1, 4, 1, 3, 7]
def baseStart_972748 : Nat := 118140960795 + 972748 * 2 ^ 59
def prefixEnd_972748 : Nat := 4983230072969 + 3 ^ 40 * 972748 * 2
def baseEnd_972748 : Nat := 49332077007394108906313

theorem tailTrace_972748 : CollatzResearch.WordTrace tailWord_972748 prefixEnd_972748 49332077007394108906313 := by
  unfold tailWord_972748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739517139953801488527449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23652689519938401984703265 17739517139953801488527449)
  ·
    refine ⟨13304637854965351116395587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17739517139953801488527449 13304637854965351116395587)
    ·
      refine ⟨19956956782448026674593381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13304637854965351116395587 19956956782448026674593381)
      ·
        refine ⟨3741929396709005001486259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19956956782448026674593381 3741929396709005001486259)
        ·
          refine ⟨5612894095063507502229389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741929396709005001486259 5612894095063507502229389)
          ·
            refine ⟨2104835285648815313336021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5612894095063507502229389 2104835285648815313336021)
            ·
              refine ⟨49332077007394108906313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2104835285648815313336021 49332077007394108906313)
              ·
                rfl

theorem cell20_972748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_972748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972748 prefixEnd_972748 := by exact prefixLift 972748
  have htrace : WordTrace (prefixWord ++ tailWord_972748) baseStart_972748 baseEnd_972748 := by
    simpa [prefixWord, tailWord_972748, baseEnd_972748] using wordTrace_append hprefix tailTrace_972748
  have hstable : (prefixWord ++ tailWord_972748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972748).length < 2 ^ (prefixWord ++ tailWord_972748).sum := by decide
  have hdescent : baseEnd_972748 < baseStart_972748 := by decide
  rcases family_descends (prefixWord ++ tailWord_972748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972764 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 3]
def baseStart_972764 : Nat := 118140960795 + 972764 * 2 ^ 59
def prefixEnd_972764 : Nat := 4983230072969 + 3 ^ 40 * 972764 * 2
def baseEnd_972764 : Nat := 443995995902522035623419

theorem tailTrace_972764 : CollatzResearch.WordTrace tailWord_972764 prefixEnd_972764 443995995902522035623419 := by
  unfold tailWord_972764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739808923924818854818673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23653078565233091806424897 17739808923924818854818673)
  ·
    refine ⟨13304856692943614141114005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17739808923924818854818673 13304856692943614141114005)
    ·
      refine ⟨623665157481731912864719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13304856692943614141114005 623665157481731912864719)
      ·
        refine ⟨935497736222597869297079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623665157481731912864719 935497736222597869297079)
        ·
          refine ⟨1403246604333896803945619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935497736222597869297079 1403246604333896803945619)
          ·
            refine ⟨2104869906500845205918429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403246604333896803945619 2104869906500845205918429)
            ·
              refine ⟨789326214937816952219411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2104869906500845205918429 789326214937816952219411)
              ·
                refine ⟨1183989322406725428329117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789326214937816952219411 1183989322406725428329117)
                ·
                  refine ⟨443995995902522035623419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1183989322406725428329117 443995995902522035623419)
                  ·
                    rfl

theorem cell20_972764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_972764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972764 prefixEnd_972764 := by exact prefixLift 972764
  have htrace : WordTrace (prefixWord ++ tailWord_972764) baseStart_972764 baseEnd_972764 := by
    simpa [prefixWord, tailWord_972764, baseEnd_972764] using wordTrace_append hprefix tailTrace_972764
  have hstable : (prefixWord ++ tailWord_972764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972764).length < 2 ^ (prefixWord ++ tailWord_972764).sum := by decide
  have hdescent : baseEnd_972764 < baseStart_972764 := by decide
  rcases family_descends (prefixWord ++ tailWord_972764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972782 : List Nat := [4, 1, 2, 1, 3, 3, 2, 4]
def baseStart_972782 : Nat := 118140960795 + 972782 * 2 ^ 59
def prefixEnd_972782 : Nat := 4983230072969 + 3 ^ 40 * 972782 * 2
def baseEnd_972782 : Nat := 148001403864331324341115

theorem tailTrace_972782 : CollatzResearch.WordTrace tailWord_972782 prefixEnd_972782 148001403864331324341115 := by
  unfold tailWord_972782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435034295223053347974075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23653516241189617855861733 4435034295223053347974075)
  ·
    refine ⟨6652551442834580021961113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4435034295223053347974075 6652551442834580021961113)
    ·
      refine ⟨4989413582125935016470835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6652551442834580021961113 4989413582125935016470835)
      ·
        refine ⟨7484120373188902524706253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989413582125935016470835 7484120373188902524706253)
        ·
          refine ⟨2806545139945838446764845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7484120373188902524706253 2806545139945838446764845)
          ·
            refine ⟨1052454427479689417536817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2806545139945838446764845 1052454427479689417536817)
            ·
              refine ⟨789340820609767063152613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052454427479689417536817 789340820609767063152613)
              ·
                refine ⟨148001403864331324341115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789340820609767063152613 148001403864331324341115)
                ·
                  rfl

theorem cell20_972782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_972782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972782 prefixEnd_972782 := by exact prefixLift 972782
  have htrace : WordTrace (prefixWord ++ tailWord_972782) baseStart_972782 baseEnd_972782 := by
    simpa [prefixWord, tailWord_972782, baseEnd_972782] using wordTrace_append hprefix tailTrace_972782
  have hstable : (prefixWord ++ tailWord_972782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972782).length < 2 ^ (prefixWord ++ tailWord_972782).sum := by decide
  have hdescent : baseEnd_972782 < baseStart_972782 := by decide
  rcases family_descends (prefixWord ++ tailWord_972782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972793 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_972793 : Nat := 118140960795 + 972793 * 2 ^ 59
def prefixEnd_972793 : Nat := 4983230072969 + 3 ^ 40 * 972793 * 2
def baseEnd_972793 : Nat := 444009232292726823656633

theorem tailTrace_972793 : CollatzResearch.WordTrace tailWord_972793 prefixEnd_972793 444009232292726823656633 := by
  unfold tailWord_972793
  simp only [CollatzResearch.WordTrace]
  refine ⟨35480675564744575662443033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23653783709829717108295355 35480675564744575662443033)
  ·
    refine ⟨26610506673558431746832275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35480675564744575662443033 26610506673558431746832275)
    ·
      refine ⟨39915760010337647620248413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26610506673558431746832275 39915760010337647620248413)
      ·
        refine ⟨14968410003876617857593155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39915760010337647620248413 14968410003876617857593155)
        ·
          refine ⟨22452615005814926786389733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14968410003876617857593155 22452615005814926786389733)
          ·
            refine ⟨4209865313590298772448075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22452615005814926786389733 4209865313590298772448075)
            ·
              refine ⟨6314797970385448158672113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209865313590298772448075 6314797970385448158672113)
              ·
                refine ⟨4736098477789086119004085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6314797970385448158672113 4736098477789086119004085)
                ·
                  refine ⟨444009232292726823656633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4736098477789086119004085 444009232292726823656633)
                  ·
                    rfl

theorem cell20_972793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_972793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972793 prefixEnd_972793 := by exact prefixLift 972793
  have htrace : WordTrace (prefixWord ++ tailWord_972793) baseStart_972793 baseEnd_972793 := by
    simpa [prefixWord, tailWord_972793, baseEnd_972793] using wordTrace_append hprefix tailTrace_972793
  have hstable : (prefixWord ++ tailWord_972793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972793).length < 2 ^ (prefixWord ++ tailWord_972793).sum := by decide
  have hdescent : baseEnd_972793 < baseStart_972793 := by decide
  rcases family_descends (prefixWord ++ tailWord_972793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972823 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 3]
def baseStart_972823 : Nat := 118140960795 + 972823 * 2 ^ 59
def prefixEnd_972823 : Nat := 4983230072969 + 3 ^ 40 * 972823 * 2
def baseEnd_972823 : Nat := 444022925110180052656511

theorem tailTrace_972823 : CollatzResearch.WordTrace tailWord_972823 prefixEnd_972823 444022925110180052656511 := by
  unfold tailWord_972823
  simp only [CollatzResearch.WordTrace]
  refine ⟨35481769754635890786035123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23654513169757260524023415 35481769754635890786035123)
  ·
    refine ⟨53222654631953836179052685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35481769754635890786035123 53222654631953836179052685)
    ·
      refine ⟨19958495486982688567144757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53222654631953836179052685 19958495486982688567144757)
      ·
        refine ⟨1871108951904627053169821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19958495486982688567144757 1871108951904627053169821)
        ·
          refine ⟨701665856964235144938683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1871108951904627053169821 701665856964235144938683)
          ·
            refine ⟨1052498785446352717408025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701665856964235144938683 1052498785446352717408025)
            ·
              refine ⟨789374089084764538056019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052498785446352717408025 789374089084764538056019)
              ·
                refine ⟨1184061133627146807084029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789374089084764538056019 1184061133627146807084029)
                ·
                  refine ⟨444022925110180052656511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184061133627146807084029 444022925110180052656511)
                  ·
                    rfl

theorem cell20_972823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 3].length) (baseStart_972823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972823 prefixEnd_972823 := by exact prefixLift 972823
  have htrace : WordTrace (prefixWord ++ tailWord_972823) baseStart_972823 baseEnd_972823 := by
    simpa [prefixWord, tailWord_972823, baseEnd_972823] using wordTrace_append hprefix tailTrace_972823
  have hstable : (prefixWord ++ tailWord_972823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972823).length < 2 ^ (prefixWord ++ tailWord_972823).sum := by decide
  have hdescent : baseEnd_972823 < baseStart_972823 := by decide
  rcases family_descends (prefixWord ++ tailWord_972823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972824 : List Nat := [2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_972824 : Nat := 118140960795 + 972824 * 2 ^ 59
def prefixEnd_972824 : Nat := 4983230072969 + 3 ^ 40 * 972824 * 2
def baseEnd_972824 : Nat := 148007793845809497874391

theorem tailTrace_972824 : CollatzResearch.WordTrace tailWord_972824 prefixEnd_972824 148007793845809497874391 := by
  unfold tailWord_972824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17740903113816133978410763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23654537485088178637881017 17740903113816133978410763)
  ·
    refine ⟨26611354670724200967616145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17740903113816133978410763 26611354670724200967616145)
    ·
      refine ⟨19958516003043150725712109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26611354670724200967616145 19958516003043150725712109)
      ·
        refine ⟨7484443501141181522142041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19958516003043150725712109 7484443501141181522142041)
        ·
          refine ⟨5613332625855886141606531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7484443501141181522142041 5613332625855886141606531)
          ·
            refine ⟨8419998938783829212409797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5613332625855886141606531 8419998938783829212409797)
            ·
              refine ⟨1578749801021967977326837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8419998938783829212409797 1578749801021967977326837)
              ·
                refine ⟨148007793845809497874391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1578749801021967977326837 148007793845809497874391)
                ·
                  rfl

theorem cell20_972824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_972824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972824 prefixEnd_972824 := by exact prefixLift 972824
  have htrace : WordTrace (prefixWord ++ tailWord_972824) baseStart_972824 baseEnd_972824 := by
    simpa [prefixWord, tailWord_972824, baseEnd_972824] using wordTrace_append hprefix tailTrace_972824
  have hstable : (prefixWord ++ tailWord_972824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972824).length < 2 ^ (prefixWord ++ tailWord_972824).sum := by decide
  have hdescent : baseEnd_972824 < baseStart_972824 := by decide
  rcases family_descends (prefixWord ++ tailWord_972824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972862 : List Nat := [4, 2, 1, 3, 10]
def baseStart_972862 : Nat := 118140960795 + 972862 * 2 ^ 59
def prefixEnd_972862 : Nat := 4983230072969 + 3 ^ 40 * 972862 * 2
def baseEnd_972862 : Nat := 5481984268800854942671

theorem tailTrace_972862 : CollatzResearch.WordTrace tailWord_972862 prefixEnd_972862 5481984268800854942671 := by
  unfold tailWord_972862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435399025186825055838105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23655461467663066964469893 4435399025186825055838105)
  ·
    refine ⟨3326549268890118791878579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4435399025186825055838105 3326549268890118791878579)
    ·
      refine ⟨4989823903335178187817869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326549268890118791878579 4989823903335178187817869)
      ·
        refine ⟨1871183963750691820431701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4989823903335178187817869 1871183963750691820431701)
        ·
          refine ⟨5481984268800854942671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1871183963750691820431701 5481984268800854942671)
          ·
            rfl

theorem cell20_972862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 10].length) (baseStart_972862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972862 prefixEnd_972862 := by exact prefixLift 972862
  have htrace : WordTrace (prefixWord ++ tailWord_972862) baseStart_972862 baseEnd_972862 := by
    simpa [prefixWord, tailWord_972862, baseEnd_972862] using wordTrace_append hprefix tailTrace_972862
  have hstable : (prefixWord ++ tailWord_972862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972862).length < 2 ^ (prefixWord ++ tailWord_972862).sum := by decide
  have hdescent : baseEnd_972862 < baseStart_972862 := by decide
  rcases family_descends (prefixWord ++ tailWord_972862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972865 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_972865 : Nat := 118140960795 + 972865 * 2 ^ 59
def prefixEnd_972865 : Nat := 4983230072969 + 3 ^ 40 * 972865 * 2
def baseEnd_972865 : Nat := 444042095054614573256339

theorem tailTrace_972865 : CollatzResearch.WordTrace tailWord_972865 prefixEnd_972865 444042095054614573256339 := by
  unfold tailWord_972865
  simp only [CollatzResearch.WordTrace]
  refine ⟨35483301620483731959064049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23655534413655821306042699 35483301620483731959064049)
  ·
    refine ⟨26612476215362798969298037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35483301620483731959064049 26612476215362798969298037)
    ·
      refine ⟨2494919645190262403371691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26612476215362798969298037 2494919645190262403371691)
      ·
        refine ⟨3742379467785393605057537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494919645190262403371691 3742379467785393605057537)
        ·
          refine ⟨2806784600839045203793153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742379467785393605057537 2806784600839045203793153)
          ·
            refine ⟨2105088450629283902844865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2806784600839045203793153 2105088450629283902844865)
            ·
              refine ⟨1578816337971962927133649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105088450629283902844865 1578816337971962927133649)
              ·
                refine ⟨1184112253478972195350237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578816337971962927133649 1184112253478972195350237)
                ·
                  refine ⟨444042095054614573256339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184112253478972195350237 444042095054614573256339)
                  ·
                    rfl

theorem cell20_972865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_972865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972865 prefixEnd_972865 := by exact prefixLift 972865
  have htrace : WordTrace (prefixWord ++ tailWord_972865) baseStart_972865 baseEnd_972865 := by
    simpa [prefixWord, tailWord_972865, baseEnd_972865] using wordTrace_append hprefix tailTrace_972865
  have hstable : (prefixWord ++ tailWord_972865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972865).length < 2 ^ (prefixWord ++ tailWord_972865).sum := by decide
  have hdescent : baseEnd_972865 < baseStart_972865 := by decide
  rcases family_descends (prefixWord ++ tailWord_972865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972924 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_972924 : Nat := 118140960795 + 972924 * 2 ^ 59
def prefixEnd_972924 : Nat := 4983230072969 + 3 ^ 40 * 972924 * 2
def baseEnd_972924 : Nat := 444069024262272590289431

theorem tailTrace_972924 : CollatzResearch.WordTrace tailWord_972924 prefixEnd_972924 444069024262272590289431 := by
  unfold tailWord_972924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17742726763634992517730913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23656969018179990023641217 17742726763634992517730913)
  ·
    refine ⟨13307045072726244388298185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17742726763634992517730913 13307045072726244388298185)
    ·
      refine ⟨9980283804544683291223639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13307045072726244388298185 9980283804544683291223639)
      ·
        refine ⟨14970425706817024936835459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980283804544683291223639 14970425706817024936835459)
        ·
          refine ⟨22455638560225537405253189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14970425706817024936835459 22455638560225537405253189)
          ·
            refine ⟨4210432230042288263484973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22455638560225537405253189 4210432230042288263484973)
            ·
              refine ⟨1578912086265858098806865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4210432230042288263484973 1578912086265858098806865)
              ·
                refine ⟨1184184064699393574105149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578912086265858098806865 1184184064699393574105149)
                ·
                  refine ⟨444069024262272590289431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184184064699393574105149 444069024262272590289431)
                  ·
                    rfl

theorem cell20_972924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_972924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972924 prefixEnd_972924 := by exact prefixLift 972924
  have htrace : WordTrace (prefixWord ++ tailWord_972924) baseStart_972924 baseEnd_972924 := by
    simpa [prefixWord, tailWord_972924, baseEnd_972924] using wordTrace_append hprefix tailTrace_972924
  have hstable : (prefixWord ++ tailWord_972924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972924).length < 2 ^ (prefixWord ++ tailWord_972924).sum := by decide
  have hdescent : baseEnd_972924 < baseStart_972924 := by decide
  rcases family_descends (prefixWord ++ tailWord_972924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972931 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_972931 : Nat := 118140960795 + 972931 * 2 ^ 59
def prefixEnd_972931 : Nat := 4983230072969 + 3 ^ 40 * 972931 * 2
def baseEnd_972931 : Nat := 444072219253011677056069

theorem tailTrace_972931 : CollatzResearch.WordTrace tailWord_972931 prefixEnd_972931 444072219253011677056069 := by
  unfold tailWord_972931
  simp only [CollatzResearch.WordTrace]
  refine ⟨35485708838244625230966647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23657139225496416820644431 35485708838244625230966647)
  ·
    refine ⟨53228563257366937846449971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35485708838244625230966647 53228563257366937846449971)
    ·
      refine ⟨79842844886050406769674957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53228563257366937846449971 79842844886050406769674957)
      ·
        refine ⟨29941066832268902538628109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79842844886050406769674957 29941066832268902538628109)
        ·
          refine ⟨11227900062100838451985541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29941066832268902538628109 11227900062100838451985541)
          ·
            refine ⟨2105231261643907209747289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11227900062100838451985541 2105231261643907209747289)
            ·
              refine ⟨1578923446232930407310467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105231261643907209747289 1578923446232930407310467)
              ·
                refine ⟨2368385169349395610965701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578923446232930407310467 2368385169349395610965701)
                ·
                  refine ⟨444072219253011677056069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368385169349395610965701 444072219253011677056069)
                  ·
                    rfl

theorem cell20_972931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_972931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972931 prefixEnd_972931 := by exact prefixLift 972931
  have htrace : WordTrace (prefixWord ++ tailWord_972931) baseStart_972931 baseEnd_972931 := by
    simpa [prefixWord, tailWord_972931, baseEnd_972931] using wordTrace_append hprefix tailTrace_972931
  have hstable : (prefixWord ++ tailWord_972931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972931).length < 2 ^ (prefixWord ++ tailWord_972931).sum := by decide
  have hdescent : baseEnd_972931 < baseStart_972931 := by decide
  rcases family_descends (prefixWord ++ tailWord_972931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972962 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_972962 : Nat := 118140960795 + 972962 * 2 ^ 59
def prefixEnd_972962 : Nat := 4983230072969 + 3 ^ 40 * 972962 * 2
def baseEnd_972962 : Nat := 444086368497713347022609

theorem tailTrace_972962 : CollatzResearch.WordTrace tailWord_972962 prefixEnd_972962 444086368497713347022609 := by
  unfold tailWord_972962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8871709875283079381336285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23657893000754878350230093 8871709875283079381336285)
  ·
    refine ⟨3326891203231154768001107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8871709875283079381336285 3326891203231154768001107)
    ·
      refine ⟨4990336804846732152001661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326891203231154768001107 4990336804846732152001661)
      ·
        refine ⟨1871376301817524557000623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4990336804846732152001661 1871376301817524557000623)
        ·
          refine ⟨2807064452726286835500935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1871376301817524557000623 2807064452726286835500935)
          ·
            refine ⟨4210596679089430253251403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807064452726286835500935 4210596679089430253251403)
            ·
              refine ⟨6315895018634145379877105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210596679089430253251403 6315895018634145379877105)
              ·
                refine ⟨4736921263975609034907829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315895018634145379877105 4736921263975609034907829)
                ·
                  refine ⟨444086368497713347022609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4736921263975609034907829 444086368497713347022609)
                  ·
                    rfl

theorem cell20_972962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_972962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972962 prefixEnd_972962 := by exact prefixLift 972962
  have htrace : WordTrace (prefixWord ++ tailWord_972962) baseStart_972962 baseEnd_972962 := by
    simpa [prefixWord, tailWord_972962, baseEnd_972962] using wordTrace_append hprefix tailTrace_972962
  have hstable : (prefixWord ++ tailWord_972962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972962).length < 2 ^ (prefixWord ++ tailWord_972962).sum := by decide
  have hdescent : baseEnd_972962 < baseStart_972962 := by decide
  rcases family_descends (prefixWord ++ tailWord_972962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972983 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_972983 : Nat := 118140960795 + 972983 * 2 ^ 59
def prefixEnd_972983 : Nat := 4983230072969 + 3 ^ 40 * 972983 * 2
def baseEnd_972983 : Nat := 444095953469930607322523

theorem tailTrace_972983 : CollatzResearch.WordTrace tailWord_972983 prefixEnd_972983 444095953469930607322523 := by
  unfold tailWord_972983
  simp only [CollatzResearch.WordTrace]
  refine ⟨35487605434056238111859603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23658403622704158741239735 35487605434056238111859603)
  ·
    refine ⟨53231408151084357167789405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35487605434056238111859603 53231408151084357167789405)
    ·
      refine ⟨19961778056656633937921027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53231408151084357167789405 19961778056656633937921027)
      ·
        refine ⟨29942667084984950906881541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19961778056656633937921027 29942667084984950906881541)
        ·
          refine ⟨5614250078434678295040289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29942667084984950906881541 5614250078434678295040289)
          ·
            refine ⟨4210687558826008721280217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5614250078434678295040289 4210687558826008721280217)
            ·
              refine ⟨3158015669119506540960163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4210687558826008721280217 3158015669119506540960163)
              ·
                refine ⟨4737023503679259811440245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158015669119506540960163 4737023503679259811440245)
                ·
                  refine ⟨444095953469930607322523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4737023503679259811440245 444095953469930607322523)
                  ·
                    rfl

theorem cell20_972983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_972983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972983 prefixEnd_972983 := by exact prefixLift 972983
  have htrace : WordTrace (prefixWord ++ tailWord_972983) baseStart_972983 baseEnd_972983 := by
    simpa [prefixWord, tailWord_972983, baseEnd_972983] using wordTrace_append hprefix tailTrace_972983
  have hstable : (prefixWord ++ tailWord_972983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972983).length < 2 ^ (prefixWord ++ tailWord_972983).sum := by decide
  have hdescent : baseEnd_972983 < baseStart_972983 := by decide
  rcases family_descends (prefixWord ++ tailWord_972983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972996 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_972996 : Nat := 118140960795 + 972996 * 2 ^ 59
def prefixEnd_972996 : Nat := 4983230072969 + 3 ^ 40 * 972996 * 2
def baseEnd_972996 : Nat := 444101887024160339889137

theorem tailTrace_972996 : CollatzResearch.WordTrace tailWord_972996 prefixEnd_972996 444101887024160339889137 := by
  unfold tailWord_972996
  simp only [CollatzResearch.WordTrace]
  refine ⟨17744039791504570666041421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23658719722006094221388561 17744039791504570666041421)
  ·
    refine ⟨6654014921814213999765533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17744039791504570666041421 6654014921814213999765533)
    ·
      refine ⟨2495255595680330249912075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6654014921814213999765533 2495255595680330249912075)
      ·
        refine ⟨3742883393520495374868113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495255595680330249912075 3742883393520495374868113)
        ·
          refine ⟨2807162545140371531151085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3742883393520495374868113 2807162545140371531151085)
          ·
            refine ⟨1052685954427639324181657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2807162545140371531151085 1052685954427639324181657)
            ·
              refine ⟨789514465820729493136243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052685954427639324181657 789514465820729493136243)
              ·
                refine ⟨1184271698731094239704365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789514465820729493136243 1184271698731094239704365)
                ·
                  refine ⟨444101887024160339889137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184271698731094239704365 444101887024160339889137)
                  ·
                    rfl

theorem cell20_972996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_972996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972996 prefixEnd_972996 := by exact prefixLift 972996
  have htrace : WordTrace (prefixWord ++ tailWord_972996) baseStart_972996 baseEnd_972996 := by
    simpa [prefixWord, tailWord_972996, baseEnd_972996] using wordTrace_append hprefix tailTrace_972996
  have hstable : (prefixWord ++ tailWord_972996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972996).length < 2 ^ (prefixWord ++ tailWord_972996).sum := by decide
  have hdescent : baseEnd_972996 < baseStart_972996 := by decide
  rcases family_descends (prefixWord ++ tailWord_972996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972997 : List Nat := [1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_972997 : Nat := 118140960795 + 972997 * 2 ^ 59
def prefixEnd_972997 : Nat := 4983230072969 + 3 ^ 40 * 972997 * 2
def baseEnd_972997 : Nat := 148034114483802926951933

theorem tailTrace_972997 : CollatzResearch.WordTrace tailWord_972997 prefixEnd_972997 148034114483802926951933 := by
  unfold tailWord_972997
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488116056005518502869245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23658744037337012335246163 35488116056005518502869245)
  ·
    refine ⟨13308043521002069438575967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35488116056005518502869245 13308043521002069438575967)
    ·
      refine ⟨19962065281503104157863951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13308043521002069438575967 19962065281503104157863951)
      ·
        refine ⟨29943097922254656236795927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19962065281503104157863951 29943097922254656236795927)
        ·
          refine ⟨44914646883381984355193891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29943097922254656236795927 44914646883381984355193891)
          ·
            refine ⟨67371970325072976532790837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44914646883381984355193891 67371970325072976532790837)
            ·
              refine ⟨6316122217975591549949141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67371970325072976532790837 6316122217975591549949141)
              ·
                refine ⟨148034114483802926951933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6316122217975591549949141 148034114483802926951933)
                ·
                  rfl

theorem cell20_972997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_972997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_972997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_972997 prefixEnd_972997 := by exact prefixLift 972997
  have htrace : WordTrace (prefixWord ++ tailWord_972997) baseStart_972997 baseEnd_972997 := by
    simpa [prefixWord, tailWord_972997, baseEnd_972997] using wordTrace_append hprefix tailTrace_972997
  have hstable : (prefixWord ++ tailWord_972997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972997).length < 2 ^ (prefixWord ++ tailWord_972997).sum := by decide
  have hdescent : baseEnd_972997 < baseStart_972997 := by decide
  rcases family_descends (prefixWord ++ tailWord_972997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973037 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 2]
def baseStart_973037 : Nat := 118140960795 + 973037 * 2 ^ 59
def prefixEnd_973037 : Nat := 4983230072969 + 3 ^ 40 * 973037 * 2
def baseEnd_973037 : Nat := 444120600541346419522303

theorem tailTrace_973037 : CollatzResearch.WordTrace tailWord_973037 prefixEnd_973037 444120600541346419522303 := by
  unfold tailWord_973037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35489574975860605334325365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23659716650573736889550243 35489574975860605334325365)
  ·
    refine ⟨3327147653986931750093003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35489574975860605334325365 3327147653986931750093003)
    ·
      refine ⟨4990721480980397625139505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327147653986931750093003 4990721480980397625139505)
      ·
        refine ⟨3743041110735298218854629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4990721480980397625139505 3743041110735298218854629)
        ·
          refine ⟨701820208262868416035243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3743041110735298218854629 701820208262868416035243)
          ·
            refine ⟨1052730312394302624052865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701820208262868416035243 1052730312394302624052865)
            ·
              refine ⟨789547734295726968039649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052730312394302624052865 789547734295726968039649)
              ·
                refine ⟨592160800721795226029737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789547734295726968039649 592160800721795226029737)
                ·
                  refine ⟨444120600541346419522303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592160800721795226029737 444120600541346419522303)
                  ·
                    rfl

theorem cell20_973037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_973037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973037 prefixEnd_973037 := by exact prefixLift 973037
  have htrace : WordTrace (prefixWord ++ tailWord_973037) baseStart_973037 baseEnd_973037 := by
    simpa [prefixWord, tailWord_973037, baseEnd_973037] using wordTrace_append hprefix tailTrace_973037
  have hstable : (prefixWord ++ tailWord_973037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973037).length < 2 ^ (prefixWord ++ tailWord_973037).sum := by decide
  have hdescent : baseEnd_973037 < baseStart_973037 := by decide
  rcases family_descends (prefixWord ++ tailWord_973037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973052 : List Nat := [2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_973052 : Nat := 118140960795 + 973052 * 2 ^ 59
def prefixEnd_973052 : Nat := 4983230072969 + 3 ^ 40 * 973052 * 2
def baseEnd_973052 : Nat := 148042482316691011340747

theorem tailTrace_973052 : CollatzResearch.WordTrace tailWord_973052 prefixEnd_973052 148042482316691011340747 := by
  unfold tailWord_973052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17745061035403131448060705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23660081380537508597414273 17745061035403131448060705)
  ·
    refine ⟨13308795776552348586045529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17745061035403131448060705 13308795776552348586045529)
    ·
      refine ⟨9981596832414261439534147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13308795776552348586045529 9981596832414261439534147)
      ·
        refine ⟨14972395248621392159301221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9981596832414261439534147 14972395248621392159301221)
        ·
          refine ⟨2807324109116511029868979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14972395248621392159301221 2807324109116511029868979)
          ·
            refine ⟨4210986163674766544803469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807324109116511029868979 4210986163674766544803469)
            ·
              refine ⟨1579119811378037454301301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4210986163674766544803469 1579119811378037454301301)
              ·
                refine ⟨148042482316691011340747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579119811378037454301301 148042482316691011340747)
                ·
                  rfl

theorem cell20_973052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_973052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973052 prefixEnd_973052 := by exact prefixLift 973052
  have htrace : WordTrace (prefixWord ++ tailWord_973052) baseStart_973052 baseEnd_973052 := by
    simpa [prefixWord, tailWord_973052, baseEnd_973052] using wordTrace_append hprefix tailTrace_973052
  have hstable : (prefixWord ++ tailWord_973052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973052).length < 2 ^ (prefixWord ++ tailWord_973052).sum := by decide
  have hdescent : baseEnd_973052 < baseStart_973052 := by decide
  rcases family_descends (prefixWord ++ tailWord_973052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973059 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_973059 : Nat := 118140960795 + 973059 * 2 ^ 59
def prefixEnd_973059 : Nat := 4983230072969 + 3 ^ 40 * 973059 * 2
def baseEnd_973059 : Nat := 444130641940812120788879

theorem tailTrace_973059 : CollatzResearch.WordTrace tailWord_973059 prefixEnd_973059 444130641940812120788879 := by
  unfold tailWord_973059
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490377381780903091626231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23660251587853935394417487 35490377381780903091626231)
  ·
    refine ⟨53235566072671354637439347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35490377381780903091626231 53235566072671354637439347)
    ·
      refine ⟨79853349109007031956159021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53235566072671354637439347 79853349109007031956159021)
      ·
        refine ⟨29945005915877636983559633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79853349109007031956159021 29945005915877636983559633)
        ·
          refine ⟨22458754436908227737669725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29945005915877636983559633 22458754436908227737669725)
          ·
            refine ⟨8422032913840585401626147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22458754436908227737669725 8422032913840585401626147)
            ·
              refine ⟨12633049370760878102439221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422032913840585401626147 12633049370760878102439221)
              ·
                refine ⟨1184348378508832322103677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12633049370760878102439221 1184348378508832322103677)
                ·
                  refine ⟨444130641940812120788879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184348378508832322103677 444130641940812120788879)
                  ·
                    rfl

theorem cell20_973059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_973059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973059 prefixEnd_973059 := by exact prefixLift 973059
  have htrace : WordTrace (prefixWord ++ tailWord_973059) baseStart_973059 baseEnd_973059 := by
    simpa [prefixWord, tailWord_973059, baseEnd_973059] using wordTrace_append hprefix tailTrace_973059
  have hstable : (prefixWord ++ tailWord_973059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973059).length < 2 ^ (prefixWord ++ tailWord_973059).sum := by decide
  have hdescent : baseEnd_973059 < baseStart_973059 := by decide
  rcases family_descends (prefixWord ++ tailWord_973059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973066 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_973066 : Nat := 118140960795 + 973066 * 2 ^ 59
def prefixEnd_973066 : Nat := 4983230072969 + 3 ^ 40 * 973066 * 2
def baseEnd_973066 : Nat := 444133836931551207555517

theorem tailTrace_973066 : CollatzResearch.WordTrace tailWord_973066 prefixEnd_973066 444133836931551207555517 := by
  unfold tailWord_973066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872658173188885821782763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23660421795170362191420701 8872658173188885821782763)
  ·
    refine ⟨13308987259783328732674145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8872658173188885821782763 13308987259783328732674145)
    ·
      refine ⟨9981740444837496549505609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13308987259783328732674145 9981740444837496549505609)
      ·
        refine ⟨7486305333628122412129207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9981740444837496549505609 7486305333628122412129207)
        ·
          refine ⟨11229458000442183618193811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486305333628122412129207 11229458000442183618193811)
          ·
            refine ⟨16844187000663275427290717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229458000442183618193811 16844187000663275427290717)
            ·
              refine ⟨6316570125248728285234019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16844187000663275427290717 6316570125248728285234019)
              ·
                refine ⟨9474855187873092427851029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6316570125248728285234019 9474855187873092427851029)
                ·
                  refine ⟨444133836931551207555517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9474855187873092427851029 444133836931551207555517)
                  ·
                    rfl

theorem cell20_973066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_973066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973066 prefixEnd_973066 := by exact prefixLift 973066
  have htrace : WordTrace (prefixWord ++ tailWord_973066) baseStart_973066 baseEnd_973066 := by
    simpa [prefixWord, tailWord_973066, baseEnd_973066] using wordTrace_append hprefix tailTrace_973066
  have hstable : (prefixWord ++ tailWord_973066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973066).length < 2 ^ (prefixWord ++ tailWord_973066).sum := by decide
  have hdescent : baseEnd_973066 < baseStart_973066 := by decide
  rcases family_descends (prefixWord ++ tailWord_973066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973083 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 2]
def baseStart_973083 : Nat := 118140960795 + 973083 * 2 ^ 59
def prefixEnd_973083 : Nat := 4983230072969 + 3 ^ 40 * 973083 * 2
def baseEnd_973083 : Nat := 444141596194774703988781

theorem tailTrace_973083 : CollatzResearch.WordTrace tailWord_973083 prefixEnd_973083 444141596194774703988781 := by
  unfold tailWord_973083
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491252733693955190499903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23660835155795970126999935 35491252733693955190499903)
  ·
    refine ⟨53236879100540932785749855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35491252733693955190499903 53236879100540932785749855)
    ·
      refine ⟨79855318650811399178624783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53236879100540932785749855 79855318650811399178624783)
      ·
        refine ⟨119782977976217098767937175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79855318650811399178624783 119782977976217098767937175)
        ·
          refine ⟨179674466964325648151905763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119782977976217098767937175 179674466964325648151905763)
          ·
            refine ⟨269511700446488472227858645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179674466964325648151905763 269511700446488472227858645)
            ·
              refine ⟨6316680479214573567840437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 269511700446488472227858645 6316680479214573567840437)
              ·
                refine ⟨592188794926366271985041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6316680479214573567840437 592188794926366271985041)
                ·
                  refine ⟨444141596194774703988781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592188794926366271985041 444141596194774703988781)
                  ·
                    rfl

theorem cell20_973083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 2].length) (baseStart_973083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973083 prefixEnd_973083 := by exact prefixLift 973083
  have htrace : WordTrace (prefixWord ++ tailWord_973083) baseStart_973083 baseEnd_973083 := by
    simpa [prefixWord, tailWord_973083, baseEnd_973083] using wordTrace_append hprefix tailTrace_973083
  have hstable : (prefixWord ++ tailWord_973083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973083).length < 2 ^ (prefixWord ++ tailWord_973083).sum := by decide
  have hdescent : baseEnd_973083 < baseStart_973083 := by decide
  rcases family_descends (prefixWord ++ tailWord_973083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973090 : List Nat := [3, 3, 1, 1, 3, 2, 7]
def baseStart_973090 : Nat := 118140960795 + 973090 * 2 ^ 59
def prefixEnd_973090 : Nat := 4983230072969 + 3 ^ 40 * 973090 * 2
def baseEnd_973090 : Nat := 49349421242834865639491

theorem tailTrace_973090 : CollatzResearch.WordTrace tailWord_973090 prefixEnd_973090 49349421242834865639491 := by
  unfold tailWord_973090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872877011167148846501181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23661005363112396924003149 8872877011167148846501181)
  ·
    refine ⟨3327328879187680817437943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8872877011167148846501181 3327328879187680817437943)
    ·
      refine ⟨4990993318781521226156915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327328879187680817437943 4990993318781521226156915)
      ·
        refine ⟨7486489978172281839235373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990993318781521226156915 7486489978172281839235373)
        ·
          refine ⟨2807433741814605689713265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7486489978172281839235373 2807433741814605689713265)
          ·
            refine ⟨2105575306360954267284949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2807433741814605689713265 2105575306360954267284949)
            ·
              refine ⟨49349421242834865639491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2105575306360954267284949 49349421242834865639491)
              ·
                rfl

theorem cell20_973090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_973090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973090 prefixEnd_973090 := by exact prefixLift 973090
  have htrace : WordTrace (prefixWord ++ tailWord_973090) baseStart_973090 baseEnd_973090 := by
    simpa [prefixWord, tailWord_973090, baseEnd_973090] using wordTrace_append hprefix tailTrace_973090
  have hstable : (prefixWord ++ tailWord_973090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973090).length < 2 ^ (prefixWord ++ tailWord_973090).sum := by decide
  have hdescent : baseEnd_973090 < baseStart_973090 := by decide
  rcases family_descends (prefixWord ++ tailWord_973090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973093 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 3]
def baseStart_973093 : Nat := 118140960795 + 973093 * 2 ^ 59
def prefixEnd_973093 : Nat := 4983230072969 + 3 ^ 40 * 973093 * 2
def baseEnd_973093 : Nat := 444146160467259113655407

theorem tailTrace_973093 : CollatzResearch.WordTrace tailWord_973093 prefixEnd_973093 444146160467259113655407 := by
  unfold tailWord_973093
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491617463657726898363933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23661078309105151265575955 35491617463657726898363933)
  ·
    refine ⟨13309356548871647586886475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35491617463657726898363933 13309356548871647586886475)
    ·
      refine ⟨19964034823307471380329713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13309356548871647586886475 19964034823307471380329713)
      ·
        refine ⟨14973026117480603535247285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19964034823307471380329713 14973026117480603535247285)
        ·
          refine ⟨1403721198513806581429433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14973026117480603535247285 1403721198513806581429433)
          ·
            refine ⟨1052790898885354936072075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403721198513806581429433 1052790898885354936072075)
            ·
              refine ⟨1579186348328032404108113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052790898885354936072075 1579186348328032404108113)
              ·
                refine ⟨1184389761246024303081085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579186348328032404108113 1184389761246024303081085)
                ·
                  refine ⟨444146160467259113655407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184389761246024303081085 444146160467259113655407)
                  ·
                    rfl

theorem cell20_973093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_973093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973093 prefixEnd_973093 := by exact prefixLift 973093
  have htrace : WordTrace (prefixWord ++ tailWord_973093) baseStart_973093 baseEnd_973093 := by
    simpa [prefixWord, tailWord_973093, baseEnd_973093] using wordTrace_append hprefix tailTrace_973093
  have hstable : (prefixWord ++ tailWord_973093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973093).length < 2 ^ (prefixWord ++ tailWord_973093).sum := by decide
  have hdescent : baseEnd_973093 < baseStart_973093 := by decide
  rcases family_descends (prefixWord ++ tailWord_973093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973128 : List Nat := [2, 1, 3, 1, 1, 2, 6, 4]
def baseStart_973128 : Nat := 118140960795 + 973128 * 2 ^ 59
def prefixEnd_973128 : Nat := 4983230072969 + 3 ^ 40 * 973128 * 2
def baseEnd_973128 : Nat := 148054045140318182496199

theorem tailTrace_973128 : CollatzResearch.WordTrace tailWord_973128 prefixEnd_973128 148054045140318182496199 := by
  unfold tailWord_973128
  simp only [CollatzResearch.WordTrace]
  refine ⟨17746447009265463937944019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23661929345687285250592025 17746447009265463937944019)
  ·
    refine ⟨26619670513898195906916029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17746447009265463937944019 26619670513898195906916029)
    ·
      refine ⟨9982376442711823465093511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26619670513898195906916029 9982376442711823465093511)
      ·
        refine ⟨14973564664067735197640267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9982376442711823465093511 14973564664067735197640267)
        ·
          refine ⟨22460346996101602796460401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14973564664067735197640267 22460346996101602796460401)
          ·
            refine ⟨16845260247076202097345301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22460346996101602796460401 16845260247076202097345301)
            ·
              refine ⟨789621574081696973313061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16845260247076202097345301 789621574081696973313061)
              ·
                refine ⟨148054045140318182496199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789621574081696973313061 148054045140318182496199)
                ·
                  rfl

theorem cell20_973128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_973128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973128 prefixEnd_973128 := by exact prefixLift 973128
  have htrace : WordTrace (prefixWord ++ tailWord_973128) baseStart_973128 baseEnd_973128 := by
    simpa [prefixWord, tailWord_973128, baseEnd_973128] using wordTrace_append hprefix tailTrace_973128
  have hstable : (prefixWord ++ tailWord_973128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973128).length < 2 ^ (prefixWord ++ tailWord_973128).sum := by decide
  have hdescent : baseEnd_973128 < baseStart_973128 := by decide
  rcases family_descends (prefixWord ++ tailWord_973128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973138 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_973138 : Nat := 118140960795 + 973138 * 2 ^ 59
def prefixEnd_973138 : Nat := 4983230072969 + 3 ^ 40 * 973138 * 2
def baseEnd_973138 : Nat := 444166699693438957155223

theorem tailTrace_973138 : CollatzResearch.WordTrace tailWord_973138 prefixEnd_973138 444166699693438957155223 := by
  unfold tailWord_973138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873314687123674895938017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23662172498996466389168045 8873314687123674895938017)
  ·
    refine ⟨6654986015342756171953513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8873314687123674895938017 6654986015342756171953513)
    ·
      refine ⟨4991239511507067128965135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6654986015342756171953513 4991239511507067128965135)
      ·
        refine ⟨7486859267260600693447703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4991239511507067128965135 7486859267260600693447703)
        ·
          refine ⟨11230288900890901040171555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486859267260600693447703 11230288900890901040171555)
          ·
            refine ⟨16845433351336351560257333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11230288900890901040171555 16845433351336351560257333)
            ·
              refine ⟨1579259376687782958774125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16845433351336351560257333 1579259376687782958774125)
              ·
                refine ⟨592222266257918609540297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1579259376687782958774125 592222266257918609540297)
                ·
                  refine ⟨444166699693438957155223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592222266257918609540297 444166699693438957155223)
                  ·
                    rfl

theorem cell20_973138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_973138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973138 prefixEnd_973138 := by exact prefixLift 973138
  have htrace : WordTrace (prefixWord ++ tailWord_973138) baseStart_973138 baseEnd_973138 := by
    simpa [prefixWord, tailWord_973138, baseEnd_973138] using wordTrace_append hprefix tailTrace_973138
  have hstable : (prefixWord ++ tailWord_973138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973138).length < 2 ^ (prefixWord ++ tailWord_973138).sum := by decide
  have hdescent : baseEnd_973138 < baseStart_973138 := by decide
  rcases family_descends (prefixWord ++ tailWord_973138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973159 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_973159 : Nat := 118140960795 + 973159 * 2 ^ 59
def prefixEnd_973159 : Nat := 4983230072969 + 3 ^ 40 * 973159 * 2
def baseEnd_973159 : Nat := 444176284665656217455137

theorem tailTrace_973159 : CollatzResearch.WordTrace tailWord_973159 prefixEnd_973159 444176284665656217455137 := by
  unfold tailWord_973159
  simp only [CollatzResearch.WordTrace]
  refine ⟨35494024681418620170266531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23662683120945746780177687 35494024681418620170266531)
  ·
    refine ⟨53241037022127930255399797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35494024681418620170266531 53241037022127930255399797)
    ·
      refine ⟨4991347220824493461443731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53241037022127930255399797 4991347220824493461443731)
      ·
        refine ⟨7487020831236740192165597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4991347220824493461443731 7487020831236740192165597)
        ·
          refine ⟨2807632811713777572062099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7487020831236740192165597 2807632811713777572062099)
          ·
            refine ⟨4211449217570666358093149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807632811713777572062099 4211449217570666358093149)
            ·
              refine ⟨1579293456588999884284931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4211449217570666358093149 1579293456588999884284931)
              ·
                refine ⟨2368940184883499826427397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579293456588999884284931 2368940184883499826427397)
                ·
                  refine ⟨444176284665656217455137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368940184883499826427397 444176284665656217455137)
                  ·
                    rfl

theorem cell20_973159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_973159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973159 prefixEnd_973159 := by exact prefixLift 973159
  have htrace : WordTrace (prefixWord ++ tailWord_973159) baseStart_973159 baseEnd_973159 := by
    simpa [prefixWord, tailWord_973159, baseEnd_973159] using wordTrace_append hprefix tailTrace_973159
  have hstable : (prefixWord ++ tailWord_973159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973159).length < 2 ^ (prefixWord ++ tailWord_973159).sum := by decide
  have hdescent : baseEnd_973159 < baseStart_973159 := by decide
  rcases family_descends (prefixWord ++ tailWord_973159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973204 : List Nat := [2, 4, 2, 1, 3, 8]
def baseStart_973204 : Nat := 118140960795 + 973204 * 2 ^ 59
def prefixEnd_973204 : Nat := 4983230072969 + 3 ^ 40 * 973204 * 2
def baseEnd_973204 : Nat := 16451734218216150405739

theorem tailTrace_973204 : CollatzResearch.WordTrace tailWord_973204 prefixEnd_973204 16451734218216150405739 := by
  unfold tailWord_973204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747832983127796427827333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23663777310837061903769777 17747832983127796427827333)
  ·
    refine ⟨3327718684336461830217625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17747832983127796427827333 3327718684336461830217625)
    ·
      refine ⟨2495789013252346372663219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3327718684336461830217625 2495789013252346372663219)
      ·
        refine ⟨3743683519878519558994829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495789013252346372663219 3743683519878519558994829)
        ·
          refine ⟨1403881319954444834623061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3743683519878519558994829 1403881319954444834623061)
          ·
            refine ⟨16451734218216150405739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1403881319954444834623061 16451734218216150405739)
            ·
              rfl

theorem cell20_973204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 8].length) (baseStart_973204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973204 prefixEnd_973204 := by exact prefixLift 973204
  have htrace : WordTrace (prefixWord ++ tailWord_973204) baseStart_973204 baseEnd_973204 := by
    simpa [prefixWord, tailWord_973204, baseEnd_973204] using wordTrace_append hprefix tailTrace_973204
  have hstable : (prefixWord ++ tailWord_973204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973204).length < 2 ^ (prefixWord ++ tailWord_973204).sum := by decide
  have hdescent : baseEnd_973204 < baseStart_973204 := by decide
  rcases family_descends (prefixWord ++ tailWord_973204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973273 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 2]
def baseStart_973273 : Nat := 118140960795 + 973273 * 2 ^ 59
def prefixEnd_973273 : Nat := 4983230072969 + 3 ^ 40 * 973273 * 2
def baseEnd_973273 : Nat := 444228317371978487654671

theorem tailTrace_973273 : CollatzResearch.WordTrace tailWord_973273 prefixEnd_973273 444228317371978487654671 := by
  unfold tailWord_973273
  simp only [CollatzResearch.WordTrace]
  refine ⟨35498182603005617639916473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23665455068670411759944315 35498182603005617639916473)
  ·
    refine ⟨26623636952254213229937355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35498182603005617639916473 26623636952254213229937355)
    ·
      refine ⟨39935455428381319844906033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26623636952254213229937355 39935455428381319844906033)
      ·
        refine ⟨29951591571285989883679525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39935455428381319844906033 29951591571285989883679525)
        ·
          refine ⟨5615923419616123103189911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29951591571285989883679525 5615923419616123103189911)
          ·
            refine ⟨8423885129424184654784867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615923419616123103189911 8423885129424184654784867)
            ·
              refine ⟨12635827694136276982177301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423885129424184654784867 12635827694136276982177301)
              ·
                refine ⟨592304423162637983539561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12635827694136276982177301 592304423162637983539561)
                ·
                  refine ⟨444228317371978487654671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592304423162637983539561 444228317371978487654671)
                  ·
                    rfl

theorem cell20_973273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_973273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973273 prefixEnd_973273 := by exact prefixLift 973273
  have htrace : WordTrace (prefixWord ++ tailWord_973273) baseStart_973273 baseEnd_973273 := by
    simpa [prefixWord, tailWord_973273, baseEnd_973273] using wordTrace_append hprefix tailTrace_973273
  have hstable : (prefixWord ++ tailWord_973273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973273).length < 2 ^ (prefixWord ++ tailWord_973273).sum := by decide
  have hdescent : baseEnd_973273 < baseStart_973273 := by decide
  rcases family_descends (prefixWord ++ tailWord_973273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973283 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 3]
def baseStart_973283 : Nat := 118140960795 + 973283 * 2 ^ 59
def prefixEnd_973283 : Nat := 4983230072969 + 3 ^ 40 * 973283 * 2
def baseEnd_973283 : Nat := 444232881644462897321297

theorem tailTrace_973283 : CollatzResearch.WordTrace tailWord_973283 prefixEnd_973283 444232881644462897321297 := by
  unfold tailWord_973283
  simp only [CollatzResearch.WordTrace]
  refine ⟨35498547332969389347780503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23665698221979592898520335 35498547332969389347780503)
  ·
    refine ⟨53247820999454084021670755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35498547332969389347780503 53247820999454084021670755)
    ·
      refine ⟨79871731499181126032506133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53247820999454084021670755 79871731499181126032506133)
      ·
        refine ⟨3743987414024115282773725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79871731499181126032506133 3743987414024115282773725)
        ·
          refine ⟨1403995280259043231040147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3743987414024115282773725 1403995280259043231040147)
          ·
            refine ⟨2105992920388564846560221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403995280259043231040147 2105992920388564846560221)
            ·
              refine ⟨789747345145711817460083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2105992920388564846560221 789747345145711817460083)
              ·
                refine ⟨1184621017718567726190125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789747345145711817460083 1184621017718567726190125)
                ·
                  refine ⟨444232881644462897321297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184621017718567726190125 444232881644462897321297)
                  ·
                    rfl

theorem cell20_973283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_973283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973283 prefixEnd_973283 := by exact prefixLift 973283
  have htrace : WordTrace (prefixWord ++ tailWord_973283) baseStart_973283 baseEnd_973283 := by
    simpa [prefixWord, tailWord_973283, baseEnd_973283] using wordTrace_append hprefix tailTrace_973283
  have hstable : (prefixWord ++ tailWord_973283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973283).length < 2 ^ (prefixWord ++ tailWord_973283).sum := by decide
  have hdescent : baseEnd_973283 < baseStart_973283 := by decide
  rcases family_descends (prefixWord ++ tailWord_973283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973314 : List Nat := [3, 4, 1, 2, 3, 1, 6]
def baseStart_973314 : Nat := 118140960795 + 973314 * 2 ^ 59
def prefixEnd_973314 : Nat := 4983230072969 + 3 ^ 40 * 973314 * 2
def baseEnd_973314 : Nat := 49360781209907174143093

theorem tailTrace_973314 : CollatzResearch.WordTrace tailWord_973314 prefixEnd_973314 49360781209907174143093 := by
  unfold tailWord_973314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874919498964270410539749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23666451997238054428105997 8874919498964270410539749)
  ·
    refine ⟨1664047406055800701976203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8874919498964270410539749 1664047406055800701976203)
    ·
      refine ⟨2496071109083701052964305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664047406055800701976203 2496071109083701052964305)
      ·
        refine ⟨1872053331812775789723229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2496071109083701052964305 1872053331812775789723229)
        ·
          refine ⟨702019999429790921146211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1872053331812775789723229 702019999429790921146211)
          ·
            refine ⟨1053029999144686381719317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702019999429790921146211 1053029999144686381719317)
            ·
              refine ⟨49360781209907174143093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1053029999144686381719317 49360781209907174143093)
              ·
                rfl

theorem cell20_973314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 6].length) (baseStart_973314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973314 prefixEnd_973314 := by exact prefixLift 973314
  have htrace : WordTrace (prefixWord ++ tailWord_973314) baseStart_973314 baseEnd_973314 := by
    simpa [prefixWord, tailWord_973314, baseEnd_973314] using wordTrace_append hprefix tailTrace_973314
  have hstable : (prefixWord ++ tailWord_973314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973314).length < 2 ^ (prefixWord ++ tailWord_973314).sum := by decide
  have hdescent : baseEnd_973314 < baseStart_973314 := by decide
  rcases family_descends (prefixWord ++ tailWord_973314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973335 : List Nat := [1, 1, 3, 6, 1, 1, 2, 5]
def baseStart_973335 : Nat := 118140960795 + 973335 * 2 ^ 59
def prefixEnd_973335 : Nat := 4983230072969 + 3 ^ 40 * 973335 * 2
def baseEnd_973335 : Nat := 148085538620460609195917

theorem tailTrace_973335 : CollatzResearch.WordTrace tailWord_973335 prefixEnd_973335 148085538620460609195917 := by
  unfold tailWord_973335
  simp only [CollatzResearch.WordTrace]
  refine ⟨35500443928781002228673459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23666962619187334819115639 35500443928781002228673459)
  ·
    refine ⟨53250665893171503343010189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35500443928781002228673459 53250665893171503343010189)
    ·
      refine ⟨19968999709939313753628821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53250665893171503343010189 19968999709939313753628821)
      ·
        refine ⟨936046861403405332201351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19968999709939313753628821 936046861403405332201351)
        ·
          refine ⟨1404070292105107998302027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936046861403405332201351 1404070292105107998302027)
          ·
            refine ⟨2106105438157661997453041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404070292105107998302027 2106105438157661997453041)
            ·
              refine ⟨1579579078618246498089781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106105438157661997453041 1579579078618246498089781)
              ·
                refine ⟨148085538620460609195917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579579078618246498089781 148085538620460609195917)
                ·
                  rfl

theorem cell20_973335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_973335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973335 prefixEnd_973335 := by exact prefixLift 973335
  have htrace : WordTrace (prefixWord ++ tailWord_973335) baseStart_973335 baseEnd_973335 := by
    simpa [prefixWord, tailWord_973335, baseEnd_973335] using wordTrace_append hprefix tailTrace_973335
  have hstable : (prefixWord ++ tailWord_973335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973335).length < 2 ^ (prefixWord ++ tailWord_973335).sum := by decide
  have hdescent : baseEnd_973335 < baseStart_973335 := by decide
  rcases family_descends (prefixWord ++ tailWord_973335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973377 : List Nat := [1, 2, 5, 1, 1, 10]
def baseStart_973377 : Nat := 118140960795 + 973377 * 2 ^ 59
def prefixEnd_973377 : Nat := 4983230072969 + 3 ^ 40 * 973377 * 2
def baseEnd_973377 : Nat := 16454658733548753636577

theorem tailTrace_973377 : CollatzResearch.WordTrace tailWord_973377 prefixEnd_973377 16454658733548753636577 := by
  unfold tailWord_973377
  simp only [CollatzResearch.WordTrace]
  refine ⟨35501975794628843401702385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23667983863085895601134923 35501975794628843401702385)
  ·
    refine ⟨26626481845971632551276789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35501975794628843401702385 26626481845971632551276789)
    ·
      refine ⟨2496232673059840551682199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26626481845971632551276789 2496232673059840551682199)
      ·
        refine ⟨3744349009589760827523299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496232673059840551682199 3744349009589760827523299)
        ·
          refine ⟨5616523514384641241284949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744349009589760827523299 5616523514384641241284949)
          ·
            refine ⟨16454658733548753636577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5616523514384641241284949 16454658733548753636577)
            ·
              rfl

theorem cell20_973377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 10].length) (baseStart_973377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973377 prefixEnd_973377 := by exact prefixLift 973377
  have htrace : WordTrace (prefixWord ++ tailWord_973377) baseStart_973377 baseEnd_973377 := by
    simpa [prefixWord, tailWord_973377, baseEnd_973377] using wordTrace_append hprefix tailTrace_973377
  have hstable : (prefixWord ++ tailWord_973377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973377).length < 2 ^ (prefixWord ++ tailWord_973377).sum := by decide
  have hdescent : baseEnd_973377 < baseStart_973377 := by decide
  rcases family_descends (prefixWord ++ tailWord_973377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973383 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 2]
def baseStart_973383 : Nat := 118140960795 + 973383 * 2 ^ 59
def prefixEnd_973383 : Nat := 4983230072969 + 3 ^ 40 * 973383 * 2
def baseEnd_973383 : Nat := 444278524369306993987555

theorem tailTrace_973383 : CollatzResearch.WordTrace tailWord_973383 prefixEnd_973383 444278524369306993987555 := by
  unfold tailWord_973383
  simp only [CollatzResearch.WordTrace]
  refine ⟨35502194632607106426420803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23668129755071404284280535 35502194632607106426420803)
  ·
    refine ⟨53253291948910659639631205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35502194632607106426420803 53253291948910659639631205)
    ·
      refine ⟨9984992240420748682430851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53253291948910659639631205 9984992240420748682430851)
      ·
        refine ⟨14977488360631123023646277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984992240420748682430851 14977488360631123023646277)
        ·
          refine ⟨2808279067618335566933677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14977488360631123023646277 2808279067618335566933677)
          ·
            refine ⟨1053104650356875837600129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2808279067618335566933677 1053104650356875837600129)
            ·
              refine ⟨789828487767656878200097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053104650356875837600129 789828487767656878200097)
              ·
                refine ⟨592371365825742658650073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789828487767656878200097 592371365825742658650073)
                ·
                  refine ⟨444278524369306993987555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592371365825742658650073 444278524369306993987555)
                  ·
                    rfl

theorem cell20_973383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 2].length) (baseStart_973383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973383 prefixEnd_973383 := by exact prefixLift 973383
  have htrace : WordTrace (prefixWord ++ tailWord_973383) baseStart_973383 baseEnd_973383 := by
    simpa [prefixWord, tailWord_973383, baseEnd_973383] using wordTrace_append hprefix tailTrace_973383
  have hstable : (prefixWord ++ tailWord_973383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973383).length < 2 ^ (prefixWord ++ tailWord_973383).sum := by decide
  have hdescent : baseEnd_973383 < baseStart_973383 := by decide
  rcases family_descends (prefixWord ++ tailWord_973383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973384 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_973384 : Nat := 118140960795 + 973384 * 2 ^ 59
def prefixEnd_973384 : Nat := 4983230072969 + 3 ^ 40 * 973384 * 2
def baseEnd_973384 : Nat := 444278980796555434954217

theorem tailTrace_973384 : CollatzResearch.WordTrace tailWord_973384 prefixEnd_973384 444278980796555434954217 := by
  unfold tailWord_973384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17751115552801741798603603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23668154070402322398138137 17751115552801741798603603)
  ·
    refine ⟨26626673329202612697905405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17751115552801741798603603 26626673329202612697905405)
    ·
      refine ⟨9985002498450979761714527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26626673329202612697905405 9985002498450979761714527)
      ·
        refine ⟨14977503747676469642571791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9985002498450979761714527 14977503747676469642571791)
        ·
          refine ⟨22466255621514704463857687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14977503747676469642571791 22466255621514704463857687)
          ·
            refine ⟨33699383432272056695786531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22466255621514704463857687 33699383432272056695786531)
            ·
              refine ⟨50549075148408085043679797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33699383432272056695786531 50549075148408085043679797)
              ·
                refine ⟨4738975795163257972844981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50549075148408085043679797 4738975795163257972844981)
                ·
                  refine ⟨444278980796555434954217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4738975795163257972844981 444278980796555434954217)
                  ·
                    rfl

theorem cell20_973384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_973384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973384 prefixEnd_973384 := by exact prefixLift 973384
  have htrace : WordTrace (prefixWord ++ tailWord_973384) baseStart_973384 baseEnd_973384 := by
    simpa [prefixWord, tailWord_973384, baseEnd_973384] using wordTrace_append hprefix tailTrace_973384
  have hstable : (prefixWord ++ tailWord_973384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973384).length < 2 ^ (prefixWord ++ tailWord_973384).sum := by decide
  have hdescent : baseEnd_973384 < baseStart_973384 := by decide
  rcases family_descends (prefixWord ++ tailWord_973384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973466 : List Nat := [3, 1, 1, 6, 1, 2, 2, 4]
def baseStart_973466 : Nat := 118140960795 + 973466 * 2 ^ 59
def prefixEnd_973466 : Nat := 4983230072969 + 3 ^ 40 * 973466 * 2
def baseEnd_973466 : Nat := 148105469276975864740183

theorem tailTrace_973466 : CollatzResearch.WordTrace tailWord_973466 prefixEnd_973466 148105469276975864740183 := by
  unfold tailWord_973466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876305472826602900423063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23670147927537607734461501 8876305472826602900423063)
  ·
    refine ⟨13314458209239904350634595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8876305472826602900423063 13314458209239904350634595)
    ·
      refine ⟨19971687313859856525951893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13314458209239904350634595 19971687313859856525951893)
      ·
        refine ⟨936172842837180774653995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19971687313859856525951893 936172842837180774653995)
        ·
          refine ⟨1404259264255771161980993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936172842837180774653995 1404259264255771161980993)
          ·
            refine ⟨1053194448191828371485745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404259264255771161980993 1053194448191828371485745)
            ·
              refine ⟨789895836143871278614309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053194448191828371485745 789895836143871278614309)
              ·
                refine ⟨148105469276975864740183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789895836143871278614309 148105469276975864740183)
                ·
                  rfl

theorem cell20_973466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_973466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973466 prefixEnd_973466 := by exact prefixLift 973466
  have htrace : WordTrace (prefixWord ++ tailWord_973466) baseStart_973466 baseEnd_973466 := by
    simpa [prefixWord, tailWord_973466, baseEnd_973466] using wordTrace_append hprefix tailTrace_973466
  have hstable : (prefixWord ++ tailWord_973466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973466).length < 2 ^ (prefixWord ++ tailWord_973466).sum := by decide
  have hdescent : baseEnd_973466 < baseStart_973466 := by decide
  rcases family_descends (prefixWord ++ tailWord_973466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973470 : List Nat := [4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_973470 : Nat := 118140960795 + 973470 * 2 ^ 59
def prefixEnd_973470 : Nat := 4983230072969 + 3 ^ 40 * 973470 * 2
def baseEnd_973470 : Nat := 148106077846640452695733

theorem tailTrace_973470 : CollatzResearch.WordTrace tailWord_973470 prefixEnd_973470 148106077846640452695733 := by
  unfold tailWord_973470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4438170972911490035604733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23670245188861280189891909 4438170972911490035604733)
  ·
    refine ⟨1664314114841808763351775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4438170972911490035604733 1664314114841808763351775)
    ·
      refine ⟨2496471172262713145027663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664314114841808763351775 2496471172262713145027663)
      ·
        refine ⟨3744706758394069717541495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496471172262713145027663 3744706758394069717541495)
        ·
          refine ⟨5617060137591104576312243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744706758394069717541495 5617060137591104576312243)
          ·
            refine ⟨8425590206386656864468365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617060137591104576312243 8425590206386656864468365)
            ·
              refine ⟨3159596327394996324175637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8425590206386656864468365 3159596327394996324175637)
              ·
                refine ⟨148106077846640452695733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3159596327394996324175637 148106077846640452695733)
                ·
                  rfl

theorem cell20_973470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_973470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973470 prefixEnd_973470 := by exact prefixLift 973470
  have htrace : WordTrace (prefixWord ++ tailWord_973470) baseStart_973470 baseEnd_973470 := by
    simpa [prefixWord, tailWord_973470, baseEnd_973470] using wordTrace_append hprefix tailTrace_973470
  have hstable : (prefixWord ++ tailWord_973470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973470).length < 2 ^ (prefixWord ++ tailWord_973470).sum := by decide
  have hdescent : baseEnd_973470 < baseStart_973470 := by decide
  rcases family_descends (prefixWord ++ tailWord_973470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973491 : List Nat := [1, 1, 1, 2, 3, 6, 6]
def baseStart_973491 : Nat := 118140960795 + 973491 * 2 ^ 59
def prefixEnd_973491 : Nat := 4983230072969 + 3 ^ 40 * 973491 * 2
def baseEnd_973491 : Nat := 49369757612459846487457

theorem tailTrace_973491 : CollatzResearch.WordTrace tailWord_973491 prefixEnd_973491 49369757612459846487457 := by
  unfold tailWord_973491
  simp only [CollatzResearch.WordTrace]
  refine ⟨35506133716215840871352327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23670755810810560580901551 35506133716215840871352327)
  ·
    refine ⟨53259200574323761307028491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35506133716215840871352327 53259200574323761307028491)
    ·
      refine ⟨79888800861485641960542737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53259200574323761307028491 79888800861485641960542737)
      ·
        refine ⟨59916600646114231470407053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79888800861485641960542737 59916600646114231470407053)
        ·
          refine ⟨22468725242292836801402645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59916600646114231470407053 22468725242292836801402645)
          ·
            refine ⟨1053221495732476725065749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22468725242292836801402645 1053221495732476725065749)
            ·
              refine ⟨49369757612459846487457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1053221495732476725065749 49369757612459846487457)
              ·
                rfl

theorem cell20_973491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_973491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973491 prefixEnd_973491 := by exact prefixLift 973491
  have htrace : WordTrace (prefixWord ++ tailWord_973491) baseStart_973491 baseEnd_973491 := by
    simpa [prefixWord, tailWord_973491, baseEnd_973491] using wordTrace_append hprefix tailTrace_973491
  have hstable : (prefixWord ++ tailWord_973491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973491).length < 2 ^ (prefixWord ++ tailWord_973491).sum := by decide
  have hdescent : baseEnd_973491 < baseStart_973491 := by decide
  rcases family_descends (prefixWord ++ tailWord_973491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973498 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_973498 : Nat := 118140960795 + 973498 * 2 ^ 59
def prefixEnd_973498 : Nat := 4983230072969 + 3 ^ 40 * 973498 * 2
def baseEnd_973498 : Nat := 444331013502877705153751

theorem tailTrace_973498 : CollatzResearch.WordTrace tailWord_973498 prefixEnd_973498 444331013502877705153751 := by
  unfold tailWord_973498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876597256797620266714287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23670926018126987377904765 8876597256797620266714287)
  ·
    refine ⟨13314895885196430400071431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8876597256797620266714287 13314895885196430400071431)
    ·
      refine ⟨19972343827794645600107147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13314895885196430400071431 19972343827794645600107147)
      ·
        refine ⟨29958515741691968400160721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19972343827794645600107147 29958515741691968400160721)
        ·
          refine ⟨22468886806268976300120541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29958515741691968400160721 22468886806268976300120541)
          ·
            refine ⟨8425832552350866112545203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22468886806268976300120541 8425832552350866112545203)
            ·
              refine ⟨12638748828526299168817805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425832552350866112545203 12638748828526299168817805)
              ·
                refine ⟨4739530810697362188306677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12638748828526299168817805 4739530810697362188306677)
                ·
                  refine ⟨444331013502877705153751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4739530810697362188306677 444331013502877705153751)
                  ·
                    rfl

theorem cell20_973498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_973498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973498 prefixEnd_973498 := by exact prefixLift 973498
  have htrace : WordTrace (prefixWord ++ tailWord_973498) baseStart_973498 baseEnd_973498 := by
    simpa [prefixWord, tailWord_973498, baseEnd_973498] using wordTrace_append hprefix tailTrace_973498
  have hstable : (prefixWord ++ tailWord_973498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973498).length < 2 ^ (prefixWord ++ tailWord_973498).sum := by decide
  have hdescent : baseEnd_973498 < baseStart_973498 := by decide
  rcases family_descends (prefixWord ++ tailWord_973498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973501 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 4]
def baseStart_973501 : Nat := 118140960795 + 973501 * 2 ^ 59
def prefixEnd_973501 : Nat := 4983230072969 + 3 ^ 40 * 973501 * 2
def baseEnd_973501 : Nat := 444332382784623028053739

theorem tailTrace_973501 : CollatzResearch.WordTrace tailWord_973501 prefixEnd_973501 444332382784623028053739 := by
  unfold tailWord_973501
  simp only [CollatzResearch.WordTrace]
  refine ⟨35506498446179612579216357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23670998964119741719477571 35506498446179612579216357)
  ·
    refine ⟨6657468458658677358603067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35506498446179612579216357 6657468458658677358603067)
    ·
      refine ⟨9986202687988016037904601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6657468458658677358603067 9986202687988016037904601)
      ·
        refine ⟨7489652015991012028428451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9986202687988016037904601 7489652015991012028428451)
        ·
          refine ⟨11234478023986518042642677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489652015991012028428451 11234478023986518042642677)
          ·
            refine ⟨1053232314748736066497751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11234478023986518042642677 1053232314748736066497751)
            ·
              refine ⟨1579848472123104099746627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053232314748736066497751 1579848472123104099746627)
              ·
                refine ⟨2369772708184656149619941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1579848472123104099746627 2369772708184656149619941)
                ·
                  refine ⟨444332382784623028053739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2369772708184656149619941 444332382784623028053739)
                  ·
                    rfl

theorem cell20_973501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_973501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973501 prefixEnd_973501 := by exact prefixLift 973501
  have htrace : WordTrace (prefixWord ++ tailWord_973501) baseStart_973501 baseEnd_973501 := by
    simpa [prefixWord, tailWord_973501, baseEnd_973501] using wordTrace_append hprefix tailTrace_973501
  have hstable : (prefixWord ++ tailWord_973501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973501).length < 2 ^ (prefixWord ++ tailWord_973501).sum := by decide
  have hdescent : baseEnd_973501 < baseStart_973501 := by decide
  rcases family_descends (prefixWord ++ tailWord_973501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973508 : List Nat := [2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_973508 : Nat := 118140960795 + 973508 * 2 ^ 59
def prefixEnd_973508 : Nat := 4983230072969 + 3 ^ 40 * 973508 * 2
def baseEnd_973508 : Nat := 148111859258454038273459

theorem tailTrace_973508 : CollatzResearch.WordTrace tailWord_973508 prefixEnd_973508 148111859258454038273459 := by
  unfold tailWord_973508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17753376878577126387360589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23671169171436168516480785 17753376878577126387360589)
  ·
    refine ⟨6657516329466422395260221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17753376878577126387360589 6657516329466422395260221)
    ·
      refine ⟨2496568623549908398222583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6657516329466422395260221 2496568623549908398222583)
      ·
        refine ⟨3744852935324862597333875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496568623549908398222583 3744852935324862597333875)
        ·
          refine ⟨5617279402987293896000813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744852935324862597333875 5617279402987293896000813)
          ·
            refine ⟨2106479776120235211000305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5617279402987293896000813 2106479776120235211000305)
            ·
              refine ⟨1579859832090176408250229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106479776120235211000305 1579859832090176408250229)
              ·
                refine ⟨148111859258454038273459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579859832090176408250229 148111859258454038273459)
                ·
                  rfl

theorem cell20_973508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_973508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973508 prefixEnd_973508 := by exact prefixLift 973508
  have htrace : WordTrace (prefixWord ++ tailWord_973508) baseStart_973508 baseEnd_973508 := by
    simpa [prefixWord, tailWord_973508, baseEnd_973508] using wordTrace_append hprefix tailTrace_973508
  have hstable : (prefixWord ++ tailWord_973508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973508).length < 2 ^ (prefixWord ++ tailWord_973508).sum := by decide
  have hdescent : baseEnd_973508 < baseStart_973508 := by decide
  rcases family_descends (prefixWord ++ tailWord_973508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973553 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_973553 : Nat := 118140960795 + 973553 * 2 ^ 59
def prefixEnd_973553 : Nat := 4983230072969 + 3 ^ 40 * 973553 * 2
def baseEnd_973553 : Nat := 444356117001541958320193

theorem tailTrace_973553 : CollatzResearch.WordTrace tailWord_973553 prefixEnd_973553 444356117001541958320193 := by
  unfold tailWord_973553
  simp only [CollatzResearch.WordTrace]
  refine ⟨35508395041991225460109313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23672263361327483640072875 35508395041991225460109313)
  ·
    refine ⟨26631296281493419095081985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35508395041991225460109313 26631296281493419095081985)
    ·
      refine ⟨19973472211120064321311489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26631296281493419095081985 19973472211120064321311489)
      ·
        refine ⟨14980104158340048240983617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19973472211120064321311489 14980104158340048240983617)
        ·
          refine ⟨11235078118755036180737713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14980104158340048240983617 11235078118755036180737713)
          ·
            refine ⟨8426308589066277135553285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11235078118755036180737713 8426308589066277135553285)
            ·
              refine ⟨1579932860449926962916241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8426308589066277135553285 1579932860449926962916241)
              ·
                refine ⟨1184949645337445222187181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1579932860449926962916241 1184949645337445222187181)
                ·
                  refine ⟨444356117001541958320193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184949645337445222187181 444356117001541958320193)
                  ·
                    rfl

theorem cell20_973553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_973553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973553 prefixEnd_973553 := by exact prefixLift 973553
  have htrace : WordTrace (prefixWord ++ tailWord_973553) baseStart_973553 baseEnd_973553 := by
    simpa [prefixWord, tailWord_973553, baseEnd_973553] using wordTrace_append hprefix tailTrace_973553
  have hstable : (prefixWord ++ tailWord_973553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973553).length < 2 ^ (prefixWord ++ tailWord_973553).sum := by decide
  have hdescent : baseEnd_973553 < baseStart_973553 := by decide
  rcases family_descends (prefixWord ++ tailWord_973553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973570 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_973570 : Nat := 118140960795 + 973570 * 2 ^ 59
def prefixEnd_973570 : Nat := 4983230072969 + 3 ^ 40 * 973570 * 2
def baseEnd_973570 : Nat := 444363876264765454753457

theorem tailTrace_973570 : CollatzResearch.WordTrace tailWord_973570 prefixEnd_973570 444363876264765454753457 := by
  unfold tailWord_973570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877253770732409340869541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23672676721953091575652109 8877253770732409340869541)
  ·
    refine ⟨1664485082012326751413039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8877253770732409340869541 1664485082012326751413039)
    ·
      refine ⟨2496727623018490127119559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664485082012326751413039 2496727623018490127119559)
      ·
        refine ⟨3745091434527735190679339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496727623018490127119559 3745091434527735190679339)
        ·
          refine ⟨5617637151791602786019009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745091434527735190679339 5617637151791602786019009)
          ·
            refine ⟨4213227863843702089514257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617637151791602786019009 4213227863843702089514257)
            ·
              refine ⟨3159920897882776567135693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213227863843702089514257 3159920897882776567135693)
              ·
                refine ⟨1184970336706041212675885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3159920897882776567135693 1184970336706041212675885)
                ·
                  refine ⟨444363876264765454753457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1184970336706041212675885 444363876264765454753457)
                  ·
                    rfl

theorem cell20_973570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_973570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973570 prefixEnd_973570 := by exact prefixLift 973570
  have htrace : WordTrace (prefixWord ++ tailWord_973570) baseStart_973570 baseEnd_973570 := by
    simpa [prefixWord, tailWord_973570, baseEnd_973570] using wordTrace_append hprefix tailTrace_973570
  have hstable : (prefixWord ++ tailWord_973570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973570).length < 2 ^ (prefixWord ++ tailWord_973570).sum := by decide
  have hdescent : baseEnd_973570 < baseStart_973570 := by decide
  rcases family_descends (prefixWord ++ tailWord_973570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973612 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_973612 : Nat := 118140960795 + 973612 * 2 ^ 59
def prefixEnd_973612 : Nat := 4983230072969 + 3 ^ 40 * 973612 * 2
def baseEnd_973612 : Nat := 444383046209199975353285

theorem tailTrace_973612 : CollatzResearch.WordTrace tailWord_973612 prefixEnd_973612 444383046209199975353285 := by
  unfold tailWord_973612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17755273474388739268253545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23673697965851652357671393 17755273474388739268253545)
  ·
    refine ⟨13316455105791554451190159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17755273474388739268253545 13316455105791554451190159)
    ·
      refine ⟨19974682658687331676785239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13316455105791554451190159 19974682658687331676785239)
      ·
        refine ⟨29962023988030997515177859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19974682658687331676785239 29962023988030997515177859)
        ·
          refine ⟨44943035982046496272766789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29962023988030997515177859 44943035982046496272766789)
          ·
            refine ⟨8426819246633718051143773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44943035982046496272766789 8426819246633718051143773)
            ·
              refine ⟨3160057217487644269178915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8426819246633718051143773 3160057217487644269178915)
              ·
                refine ⟨4740085826231466403768373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160057217487644269178915 4740085826231466403768373)
                ·
                  refine ⟨444383046209199975353285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4740085826231466403768373 444383046209199975353285)
                  ·
                    rfl

theorem cell20_973612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_973612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973612 prefixEnd_973612 := by exact prefixLift 973612
  have htrace : WordTrace (prefixWord ++ tailWord_973612) baseStart_973612 baseEnd_973612 := by
    simpa [prefixWord, tailWord_973612, baseEnd_973612] using wordTrace_append hprefix tailTrace_973612
  have hstable : (prefixWord ++ tailWord_973612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973612).length < 2 ^ (prefixWord ++ tailWord_973612).sum := by decide
  have hdescent : baseEnd_973612 < baseStart_973612 := by decide
  rcases family_descends (prefixWord ++ tailWord_973612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973649 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 2]
def baseStart_973649 : Nat := 118140960795 + 973649 * 2 ^ 59
def prefixEnd_973649 : Nat := 4983230072969 + 3 ^ 40 * 973649 * 2
def baseEnd_973649 : Nat := 444399934017392291119801

theorem tailTrace_973649 : CollatzResearch.WordTrace tailWord_973649 prefixEnd_973649 444399934017392291119801 := by
  unfold tailWord_973649
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511896449643433855604001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23674597633095622570402667 35511896449643433855604001)
  ·
    refine ⟨26633922337232575391703001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35511896449643433855604001 26633922337232575391703001)
    ·
      refine ⟨19975441752924431543777251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26633922337232575391703001 19975441752924431543777251)
      ·
        refine ⟨29963162629386647315665877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19975441752924431543777251 29963162629386647315665877)
        ·
          refine ⟨702261624126249546460919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29963162629386647315665877 702261624126249546460919)
          ·
            refine ⟨1053392436189374319691379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702261624126249546460919 1053392436189374319691379)
            ·
              refine ⟨1580088654284061479537069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053392436189374319691379 1580088654284061479537069)
              ·
                refine ⟨592533245356523054826401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580088654284061479537069 592533245356523054826401)
                ·
                  refine ⟨444399934017392291119801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592533245356523054826401 444399934017392291119801)
                  ·
                    rfl

theorem cell20_973649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_973649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973649 prefixEnd_973649 := by exact prefixLift 973649
  have htrace : WordTrace (prefixWord ++ tailWord_973649) baseStart_973649 baseEnd_973649 := by
    simpa [prefixWord, tailWord_973649, baseEnd_973649] using wordTrace_append hprefix tailTrace_973649
  have hstable : (prefixWord ++ tailWord_973649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973649).length < 2 ^ (prefixWord ++ tailWord_973649).sum := by decide
  have hdescent : baseEnd_973649 < baseStart_973649 := by decide
  rcases family_descends (prefixWord ++ tailWord_973649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973650 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_973650 : Nat := 118140960795 + 973650 * 2 ^ 59
def prefixEnd_973650 : Nat := 4983230072969 + 3 ^ 40 * 973650 * 2
def baseEnd_973650 : Nat := 444400390444640732086463

theorem tailTrace_973650 : CollatzResearch.WordTrace tailWord_973650 prefixEnd_973650 444400390444640732086463 := by
  unfold tailWord_973650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877983230659952756597601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23674621948426540684260269 8877983230659952756597601)
  ·
    refine ⟨6658487422994964567448201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8877983230659952756597601 6658487422994964567448201)
    ·
      refine ⟨4993865567246223425586151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6658487422994964567448201 4993865567246223425586151)
      ·
        refine ⟨7490798350869335138379227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993865567246223425586151 7490798350869335138379227)
        ·
          refine ⟨11236197526304002707568841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490798350869335138379227 11236197526304002707568841)
          ·
            refine ⟨8427148144728002030676631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11236197526304002707568841 8427148144728002030676631)
            ·
              refine ⟨12640722217092003046014947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427148144728002030676631 12640722217092003046014947)
              ·
                refine ⟨18961083325638004569022421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12640722217092003046014947 18961083325638004569022421)
                ·
                  refine ⟨444400390444640732086463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18961083325638004569022421 444400390444640732086463)
                  ·
                    rfl

theorem cell20_973650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_973650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973650 prefixEnd_973650 := by exact prefixLift 973650
  have htrace : WordTrace (prefixWord ++ tailWord_973650) baseStart_973650 baseEnd_973650 := by
    simpa [prefixWord, tailWord_973650, baseEnd_973650] using wordTrace_append hprefix tailTrace_973650
  have hstable : (prefixWord ++ tailWord_973650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973650).length < 2 ^ (prefixWord ++ tailWord_973650).sum := by decide
  have hdescent : baseEnd_973650 < baseStart_973650 := by decide
  rcases family_descends (prefixWord ++ tailWord_973650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973660 : List Nat := [2, 2, 4, 2, 1, 3, 6]
def baseStart_973660 : Nat := 118140960795 + 973660 * 2 ^ 59
def prefixEnd_973660 : Nat := 4983230072969 + 3 ^ 40 * 973660 * 2
def baseEnd_973660 : Nat := 49378328301902793528121

theorem tailTrace_973660 : CollatzResearch.WordTrace tailWord_973660 prefixEnd_973660 49378328301902793528121 := by
  unfold tailWord_973660
  simp only [CollatzResearch.WordTrace]
  refine ⟨17756148826301791367127217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23674865101735721822836289 17756148826301791367127217)
  ·
    refine ⟨13317111619726343525345413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17756148826301791367127217 13317111619726343525345413)
    ·
      refine ⟨2496958428698689411002265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13317111619726343525345413 2496958428698689411002265)
      ·
        refine ⟨1872718821524017058251699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2496958428698689411002265 1872718821524017058251699)
        ·
          refine ⟨2809078232286025587377549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872718821524017058251699 2809078232286025587377549)
          ·
            refine ⟨1053404337107259595266581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2809078232286025587377549 1053404337107259595266581)
            ·
              refine ⟨49378328301902793528121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1053404337107259595266581 49378328301902793528121)
              ·
                rfl

theorem cell20_973660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 6].length) (baseStart_973660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973660 prefixEnd_973660 := by exact prefixLift 973660
  have htrace : WordTrace (prefixWord ++ tailWord_973660) baseStart_973660 baseEnd_973660 := by
    simpa [prefixWord, tailWord_973660, baseEnd_973660] using wordTrace_append hprefix tailTrace_973660
  have hstable : (prefixWord ++ tailWord_973660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973660).length < 2 ^ (prefixWord ++ tailWord_973660).sum := by decide
  have hdescent : baseEnd_973660 < baseStart_973660 := by decide
  rcases family_descends (prefixWord ++ tailWord_973660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973681 : List Nat := [1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_973681 : Nat := 118140960795 + 973681 * 2 ^ 59
def prefixEnd_973681 : Nat := 4983230072969 + 3 ^ 40 * 973681 * 2
def baseEnd_973681 : Nat := 148138179896447467351001

theorem tailTrace_973681 : CollatzResearch.WordTrace tailWord_973681 prefixEnd_973681 148138179896447467351001 := by
  unfold tailWord_973681
  simp only [CollatzResearch.WordTrace]
  refine ⟨35513063585527503320768897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23675375723685002213845931 35513063585527503320768897)
  ·
    refine ⟨26634797689145627490576673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35513063585527503320768897 26634797689145627490576673)
    ·
      refine ⟨19976098266859220617932505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26634797689145627490576673 19976098266859220617932505)
      ·
        refine ⟨14982073700144415463449379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19976098266859220617932505 14982073700144415463449379)
        ·
          refine ⟨22473110550216623195174069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14982073700144415463449379 22473110550216623195174069)
          ·
            refine ⟨2106854114082808424547569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22473110550216623195174069 2106854114082808424547569)
            ·
              refine ⟨1580140585562106318410677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106854114082808424547569 1580140585562106318410677)
              ·
                refine ⟨148138179896447467351001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1580140585562106318410677 148138179896447467351001)
                ·
                  rfl

theorem cell20_973681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_973681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973681 prefixEnd_973681 := by exact prefixLift 973681
  have htrace : WordTrace (prefixWord ++ tailWord_973681) baseStart_973681 baseEnd_973681 := by
    simpa [prefixWord, tailWord_973681, baseEnd_973681] using wordTrace_append hprefix tailTrace_973681
  have hstable : (prefixWord ++ tailWord_973681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973681).length < 2 ^ (prefixWord ++ tailWord_973681).sum := by decide
  have hdescent : baseEnd_973681 < baseStart_973681 := by decide
  rcases family_descends (prefixWord ++ tailWord_973681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973695 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_973695 : Nat := 118140960795 + 973695 * 2 ^ 59
def prefixEnd_973695 : Nat := 4983230072969 + 3 ^ 40 * 973695 * 2
def baseEnd_973695 : Nat := 444420929670820575586279

theorem tailTrace_973695 : CollatzResearch.WordTrace tailWord_973695 prefixEnd_973695 444420929670820575586279 := by
  unfold tailWord_973695
  simp only [CollatzResearch.WordTrace]
  refine ⟨35513574207476783711778539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23675716138317855807852359 35513574207476783711778539)
  ·
    refine ⟨53270361311215175567667809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35513574207476783711778539 53270361311215175567667809)
    ·
      refine ⟨39952770983411381675750857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53270361311215175567667809 39952770983411381675750857)
      ·
        refine ⟨29964578237558536256813143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39952770983411381675750857 29964578237558536256813143)
        ·
          refine ⟨44946867356337804385219715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29964578237558536256813143 44946867356337804385219715)
          ·
            refine ⟨67420301034506706577829573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44946867356337804385219715 67420301034506706577829573)
            ·
              refine ⟨12641306443970007483343045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67420301034506706577829573 12641306443970007483343045)
              ·
                refine ⟨2370244958244376403126821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12641306443970007483343045 2370244958244376403126821)
                ·
                  refine ⟨444420929670820575586279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370244958244376403126821 444420929670820575586279)
                  ·
                    rfl

theorem cell20_973695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_973695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973695 prefixEnd_973695 := by exact prefixLift 973695
  have htrace : WordTrace (prefixWord ++ tailWord_973695) baseStart_973695 baseEnd_973695 := by
    simpa [prefixWord, tailWord_973695, baseEnd_973695] using wordTrace_append hprefix tailTrace_973695
  have hstable : (prefixWord ++ tailWord_973695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973695).length < 2 ^ (prefixWord ++ tailWord_973695).sum := by decide
  have hdescent : baseEnd_973695 < baseStart_973695 := by decide
  rcases family_descends (prefixWord ++ tailWord_973695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973718 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_973718 : Nat := 118140960795 + 973718 * 2 ^ 59
def prefixEnd_973718 : Nat := 4983230072969 + 3 ^ 40 * 973718 * 2
def baseEnd_973718 : Nat := 444431427497534717819519

theorem tailTrace_973718 : CollatzResearch.WordTrace tailWord_973718 prefixEnd_973718 444431427497534717819519 := by
  unfold tailWord_973718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219650817899591164991613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23676275390928972426577205 2219650817899591164991613)
  ·
    refine ⟨832369056712346686871855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2219650817899591164991613 832369056712346686871855)
    ·
      refine ⟨1248553585068520030307783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832369056712346686871855 1248553585068520030307783)
      ·
        refine ⟨1872830377602780045461675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248553585068520030307783 1872830377602780045461675)
        ·
          refine ⟨2809245566404170068192513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872830377602780045461675 2809245566404170068192513)
          ·
            refine ⟨2106934174803127551144385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809245566404170068192513 2106934174803127551144385)
            ·
              refine ⟨1580200631102345663358289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106934174803127551144385 1580200631102345663358289)
              ·
                refine ⟨1185150473326759247518717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580200631102345663358289 1185150473326759247518717)
                ·
                  refine ⟨444431427497534717819519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185150473326759247518717 444431427497534717819519)
                  ·
                    rfl

theorem cell20_973718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_973718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973718 prefixEnd_973718 := by exact prefixLift 973718
  have htrace : WordTrace (prefixWord ++ tailWord_973718) baseStart_973718 baseEnd_973718 := by
    simpa [prefixWord, tailWord_973718, baseEnd_973718] using wordTrace_append hprefix tailTrace_973718
  have hstable : (prefixWord ++ tailWord_973718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973718).length < 2 ^ (prefixWord ++ tailWord_973718).sum := by decide
  have hdescent : baseEnd_973718 < baseStart_973718 := by decide
  rcases family_descends (prefixWord ++ tailWord_973718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973722 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_973722 : Nat := 118140960795 + 973722 * 2 ^ 59
def prefixEnd_973722 : Nat := 4983230072969 + 3 ^ 40 * 973722 * 2
def baseEnd_973722 : Nat := 444433253206528481686169

theorem tailTrace_973722 : CollatzResearch.WordTrace tailWord_973722 prefixEnd_973722 444433253206528481686169 := by
  unfold tailWord_973722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8878639744594741830752855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23676372652252644882007613 8878639744594741830752855)
  ·
    refine ⟨13317959616892112746129283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8878639744594741830752855 13317959616892112746129283)
    ·
      refine ⟨19976939425338169119193925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13317959616892112746129283 19976939425338169119193925)
      ·
        refine ⟨3745676142250906709848861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19976939425338169119193925 3745676142250906709848861)
        ·
          refine ⟨1404628553344090016193323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3745676142250906709848861 1404628553344090016193323)
          ·
            refine ⟨2106942830016135024289985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404628553344090016193323 2106942830016135024289985)
            ·
              refine ⟨1580207122512101268217489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106942830016135024289985 1580207122512101268217489)
              ·
                refine ⟨1185155341884075951163117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580207122512101268217489 1185155341884075951163117)
                ·
                  refine ⟨444433253206528481686169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185155341884075951163117 444433253206528481686169)
                  ·
                    rfl

theorem cell20_973722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_973722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973722 prefixEnd_973722 := by exact prefixLift 973722
  have htrace : WordTrace (prefixWord ++ tailWord_973722) baseStart_973722 baseEnd_973722 := by
    simpa [prefixWord, tailWord_973722, baseEnd_973722] using wordTrace_append hprefix tailTrace_973722
  have hstable : (prefixWord ++ tailWord_973722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973722).length < 2 ^ (prefixWord ++ tailWord_973722).sum := by decide
  have hdescent : baseEnd_973722 < baseStart_973722 := by decide
  rcases family_descends (prefixWord ++ tailWord_973722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
