import V185TrunkScan20Chunk124

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_759824 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_759824 : Nat := 118140960795 + 759824 * 2 ^ 59
def prefixEnd_759824 : Nat := 4983230072969 + 3 ^ 40 * 759824 * 2
def baseEnd_759824 : Nat := 346804377619502594493901

theorem tailTrace_759824 : CollatzResearch.WordTrace tailWord_759824 prefixEnd_759824 346804377619502594493901 := by
  unfold tailWord_759824
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856528999647445226491263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18475371999529926968655017 13856528999647445226491263)
  ·
    refine ⟨20784793499471167839736895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13856528999647445226491263 20784793499471167839736895)
    ·
      refine ⟨31177190249206751759605343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20784793499471167839736895 31177190249206751759605343)
      ·
        refine ⟨46765785373810127639408015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31177190249206751759605343 46765785373810127639408015)
        ·
          refine ⟨70148678060715191459112023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46765785373810127639408015 70148678060715191459112023)
          ·
            refine ⟨105223017091072787188668035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70148678060715191459112023 105223017091072787188668035)
            ·
              refine ⟨157834525636609180783002053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105223017091072787188668035 157834525636609180783002053)
              ·
                refine ⟨29593973556864221396812885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157834525636609180783002053 29593973556864221396812885)
                ·
                  refine ⟨346804377619502594493901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29593973556864221396812885 346804377619502594493901)
                  ·
                    rfl

theorem cell20_759824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_759824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759824 prefixEnd_759824 := by exact prefixLift 759824
  have htrace : WordTrace (prefixWord ++ tailWord_759824) baseStart_759824 baseEnd_759824 := by
    simpa [prefixWord, tailWord_759824, baseEnd_759824] using wordTrace_append hprefix tailTrace_759824
  have hstable : (prefixWord ++ tailWord_759824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759824).length < 2 ^ (prefixWord ++ tailWord_759824).sum := by decide
  have hdescent : baseEnd_759824 < baseStart_759824 := by decide
  rcases family_descends (prefixWord ++ tailWord_759824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759854 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_759854 : Nat := 118140960795 + 759854 * 2 ^ 59
def prefixEnd_759854 : Nat := 4983230072969 + 3 ^ 40 * 759854 * 2
def baseEnd_759854 : Nat := 346818070436955823493779

theorem tailTrace_759854 : CollatzResearch.WordTrace tailWord_759854 prefixEnd_759854 346818070436955823493779 := by
  unfold tailWord_759854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464269023648275697071827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18476101459457470384383077 3464269023648275697071827)
  ·
    refine ⟨5196403535472413545607741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3464269023648275697071827 5196403535472413545607741)
    ·
      refine ⟨1948651325802155079602903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5196403535472413545607741 1948651325802155079602903)
      ·
        refine ⟨2922976988703232619404355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948651325802155079602903 2922976988703232619404355)
        ·
          refine ⟨4384465483054848929106533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922976988703232619404355 4384465483054848929106533)
          ·
            refine ⟨822087278072784174207475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4384465483054848929106533 822087278072784174207475)
            ·
              refine ⟨1233130917109176261311213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822087278072784174207475 1233130917109176261311213)
              ·
                refine ⟨462424093915941097991705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1233130917109176261311213 462424093915941097991705)
                ·
                  refine ⟨346818070436955823493779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462424093915941097991705 346818070436955823493779)
                  ·
                    rfl

theorem cell20_759854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_759854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759854 prefixEnd_759854 := by exact prefixLift 759854
  have htrace : WordTrace (prefixWord ++ tailWord_759854) baseStart_759854 baseEnd_759854 := by
    simpa [prefixWord, tailWord_759854, baseEnd_759854] using wordTrace_append hprefix tailTrace_759854
  have hstable : (prefixWord ++ tailWord_759854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759854).length < 2 ^ (prefixWord ++ tailWord_759854).sum := by decide
  have hdescent : baseEnd_759854 < baseStart_759854 := by decide
  rcases family_descends (prefixWord ++ tailWord_759854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759865 : List Nat := [1, 2, 1, 5, 3, 2, 6]
def baseStart_759865 : Nat := 118140960795 + 759865 * 2 ^ 59
def prefixEnd_759865 : Nat := 4983230072969 + 3 ^ 40 * 759865 * 2
def baseEnd_759865 : Nat := 38535899015187630458563

theorem tailTrace_759865 : CollatzResearch.WordTrace tailWord_759865 prefixEnd_759865 38535899015187630458563 := by
  unfold tailWord_759865
  simp only [CollatzResearch.WordTrace]
  refine ⟨27714553392146354455225049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18476368928097569636816699 27714553392146354455225049)
  ·
    refine ⟨20785915044109765841418787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27714553392146354455225049 20785915044109765841418787)
    ·
      refine ⟨31178872566164648762128181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20785915044109765841418787 31178872566164648762128181)
      ·
        refine ⟨2923019303077935821449517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31178872566164648762128181 2923019303077935821449517)
        ·
          refine ⟨1096132238654225933043569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2923019303077935821449517 1096132238654225933043569)
          ·
            refine ⟨822099178990669449782677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096132238654225933043569 822099178990669449782677)
            ·
              refine ⟨38535899015187630458563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 822099178990669449782677 38535899015187630458563)
              ·
                rfl

theorem cell20_759865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_759865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759865 prefixEnd_759865 := by exact prefixLift 759865
  have htrace : WordTrace (prefixWord ++ tailWord_759865) baseStart_759865 baseEnd_759865 := by
    simpa [prefixWord, tailWord_759865, baseEnd_759865] using wordTrace_append hprefix tailTrace_759865
  have hstable : (prefixWord ++ tailWord_759865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759865).length < 2 ^ (prefixWord ++ tailWord_759865).sum := by decide
  have hdescent : baseEnd_759865 < baseStart_759865 := by decide
  rcases family_descends (prefixWord ++ tailWord_759865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759886 : List Nat := [4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_759886 : Nat := 118140960795 + 759886 * 2 ^ 59
def prefixEnd_759886 : Nat := 4983230072969 + 3 ^ 40 * 759886 * 2
def baseEnd_759886 : Nat := 115610892036301978142327

theorem tailTrace_759886 : CollatzResearch.WordTrace tailWord_759886 prefixEnd_759886 115610892036301978142327 := by
  unfold tailWord_759886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464414915633784380217439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18476879550046850027826341 3464414915633784380217439)
  ·
    refine ⟨5196622373450676570326159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3464414915633784380217439 5196622373450676570326159)
    ·
      refine ⟨7794933560176014855489239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196622373450676570326159 7794933560176014855489239)
      ·
        refine ⟨11692400340264022283233859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7794933560176014855489239 11692400340264022283233859)
        ·
          refine ⟨17538600510396033424850789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11692400340264022283233859 17538600510396033424850789)
          ·
            refine ⟨3288487595699256267159523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17538600510396033424850789 3288487595699256267159523)
            ·
              refine ⟨4932731393548884400739285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288487595699256267159523 4932731393548884400739285)
              ·
                refine ⟨115610892036301978142327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4932731393548884400739285 115610892036301978142327)
                ·
                  rfl

theorem cell20_759886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_759886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759886 prefixEnd_759886 := by exact prefixLift 759886
  have htrace : WordTrace (prefixWord ++ tailWord_759886) baseStart_759886 baseEnd_759886 := by
    simpa [prefixWord, tailWord_759886, baseEnd_759886] using wordTrace_append hprefix tailTrace_759886
  have hstable : (prefixWord ++ tailWord_759886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759886).length < 2 ^ (prefixWord ++ tailWord_759886).sum := by decide
  have hdescent : baseEnd_759886 < baseStart_759886 := by decide
  rcases family_descends (prefixWord ++ tailWord_759886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759941 : List Nat := [1, 3, 1, 1, 5, 3, 1, 5]
def baseStart_759941 : Nat := 118140960795 + 759941 * 2 ^ 59
def prefixEnd_759941 : Nat := 4983230072969 + 3 ^ 40 * 759941 * 2
def baseEnd_759941 : Nat := 115619259869190062531141

theorem tailTrace_759941 : CollatzResearch.WordTrace tailWord_759941 prefixEnd_759941 115619259869190062531141 := by
  unfold tailWord_759941
  simp only [CollatzResearch.WordTrace]
  refine ⟨27717325339871019434991677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18478216893247346289994451 27717325339871019434991677)
  ·
    refine ⟨10393997002451632288121879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27717325339871019434991677 10393997002451632288121879)
    ·
      refine ⟨15590995503677448432182819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10393997002451632288121879 15590995503677448432182819)
      ·
        refine ⟨23386493255516172648274229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15590995503677448432182819 23386493255516172648274229)
        ·
          refine ⟨2192483742704641185775709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23386493255516172648274229 2192483742704641185775709)
          ·
            refine ⟨822181403514240444665891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2192483742704641185775709 822181403514240444665891)
            ·
              refine ⟨1233272105271360666998837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822181403514240444665891 1233272105271360666998837)
              ·
                refine ⟨115619259869190062531141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1233272105271360666998837 115619259869190062531141)
                ·
                  rfl

theorem cell20_759941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_759941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759941 prefixEnd_759941 := by exact prefixLift 759941
  have htrace : WordTrace (prefixWord ++ tailWord_759941) baseStart_759941 baseEnd_759941 := by
    simpa [prefixWord, tailWord_759941, baseEnd_759941] using wordTrace_append hprefix tailTrace_759941
  have hstable : (prefixWord ++ tailWord_759941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759941).length < 2 ^ (prefixWord ++ tailWord_759941).sum := by decide
  have hdescent : baseEnd_759941 < baseStart_759941 := by decide
  rcases family_descends (prefixWord ++ tailWord_759941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759982 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_759982 : Nat := 118140960795 + 759982 * 2 ^ 59
def prefixEnd_759982 : Nat := 4983230072969 + 3 ^ 40 * 759982 * 2
def baseEnd_759982 : Nat := 346876493124756267226589

theorem tailTrace_759982 : CollatzResearch.WordTrace tailWord_759982 prefixEnd_759982 346876493124756267226589 := by
  unfold tailWord_759982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464852591590310429654275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18479213821814988958156133 3464852591590310429654275)
  ·
    refine ⟨5197278887385465644481413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3464852591590310429654275 5197278887385465644481413)
    ·
      refine ⟨974489791384774808340265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5197278887385465644481413 974489791384774808340265)
      ·
        refine ⟨730867343538581106255199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 974489791384774808340265 730867343538581106255199)
        ·
          refine ⟨1096301015307871659382799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730867343538581106255199 1096301015307871659382799)
          ·
            refine ⟨1644451522961807489074199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096301015307871659382799 1644451522961807489074199)
            ·
              refine ⟨2466677284442711233611299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644451522961807489074199 2466677284442711233611299)
              ·
                refine ⟨3700015926664066850416949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466677284442711233611299 3700015926664066850416949)
                ·
                  refine ⟨346876493124756267226589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3700015926664066850416949 346876493124756267226589)
                  ·
                    rfl

theorem cell20_759982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_759982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759982 prefixEnd_759982 := by exact prefixLift 759982
  have htrace : WordTrace (prefixWord ++ tailWord_759982) baseStart_759982 baseEnd_759982 := by
    simpa [prefixWord, tailWord_759982, baseEnd_759982] using wordTrace_append hprefix tailTrace_759982
  have hstable : (prefixWord ++ tailWord_759982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759982).length < 2 ^ (prefixWord ++ tailWord_759982).sum := by decide
  have hdescent : baseEnd_759982 < baseStart_759982 := by decide
  rcases family_descends (prefixWord ++ tailWord_759982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759989 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 4]
def baseStart_759989 : Nat := 118140960795 + 759989 * 2 ^ 59
def prefixEnd_759989 : Nat := 4983230072969 + 3 ^ 40 * 759989 * 2
def baseEnd_759989 : Nat := 346879688115495353993227

theorem tailTrace_759989 : CollatzResearch.WordTrace tailWord_759989 prefixEnd_759989 346879688115495353993227 := by
  unfold tailWord_759989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27719076043697123632739021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18479384029131415755159347 27719076043697123632739021)
  ·
    refine ⟨10394653516386421362277133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27719076043697123632739021 10394653516386421362277133)
    ·
      refine ⟨3897995068644908010853925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10394653516386421362277133 3897995068644908010853925)
      ·
        refine ⟨730874075370920252035111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3897995068644908010853925 730874075370920252035111)
        ·
          refine ⟨1096311113056380378052667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730874075370920252035111 1096311113056380378052667)
          ·
            refine ⟨1644466669584570567079001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096311113056380378052667 1644466669584570567079001)
            ·
              refine ⟨1233350002188427925309251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644466669584570567079001 1233350002188427925309251)
              ·
                refine ⟨1850025003282641887963877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233350002188427925309251 1850025003282641887963877)
                ·
                  refine ⟨346879688115495353993227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850025003282641887963877 346879688115495353993227)
                  ·
                    rfl

theorem cell20_759989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_759989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759989 prefixEnd_759989 := by exact prefixLift 759989
  have htrace : WordTrace (prefixWord ++ tailWord_759989) baseStart_759989 baseEnd_759989 := by
    simpa [prefixWord, tailWord_759989, baseEnd_759989] using wordTrace_append hprefix tailTrace_759989
  have hstable : (prefixWord ++ tailWord_759989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759989).length < 2 ^ (prefixWord ++ tailWord_759989).sum := by decide
  have hdescent : baseEnd_759989 < baseStart_759989 := by decide
  rcases family_descends (prefixWord ++ tailWord_759989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759993 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_759993 : Nat := 118140960795 + 759993 * 2 ^ 59
def prefixEnd_759993 : Nat := 4983230072969 + 3 ^ 40 * 759993 * 2
def baseEnd_759993 : Nat := 346881513824489117859877

theorem tailTrace_759993 : CollatzResearch.WordTrace tailWord_759993 prefixEnd_759993 346881513824489117859877 := by
  unfold tailWord_759993
  simp only [CollatzResearch.WordTrace]
  refine ⟨27719221935682632315884633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18479481290455088210589755 27719221935682632315884633)
  ·
    refine ⟨20789416451761974236913475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27719221935682632315884633 20789416451761974236913475)
    ·
      refine ⟨31184124677642961355370213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20789416451761974236913475 31184124677642961355370213)
      ·
        refine ⟨5847023377058055254131915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31184124677642961355370213 5847023377058055254131915)
        ·
          refine ⟨8770535065587082881197873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847023377058055254131915 8770535065587082881197873)
          ·
            refine ⟨6577901299190312160898405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8770535065587082881197873 6577901299190312160898405)
            ·
              refine ⟨1233356493598183530168451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6577901299190312160898405 1233356493598183530168451)
              ·
                refine ⟨1850034740397275295252677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233356493598183530168451 1850034740397275295252677)
                ·
                  refine ⟨346881513824489117859877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850034740397275295252677 346881513824489117859877)
                  ·
                    rfl

theorem cell20_759993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_759993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_759993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_759993 prefixEnd_759993 := by exact prefixLift 759993
  have htrace : WordTrace (prefixWord ++ tailWord_759993) baseStart_759993 baseEnd_759993 := by
    simpa [prefixWord, tailWord_759993, baseEnd_759993] using wordTrace_append hprefix tailTrace_759993
  have hstable : (prefixWord ++ tailWord_759993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759993).length < 2 ^ (prefixWord ++ tailWord_759993).sum := by decide
  have hdescent : baseEnd_759993 < baseStart_759993 := by decide
  rcases family_descends (prefixWord ++ tailWord_759993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760093 : List Nat := [1, 4, 2, 3, 3, 7]
def baseStart_760093 : Nat := 118140960795 + 760093 * 2 ^ 59
def prefixEnd_760093 : Nat := 4983230072969 + 3 ^ 40 * 760093 * 2
def baseEnd_760093 : Nat := 12849153946271600538005

theorem tailTrace_760093 : CollatzResearch.WordTrace tailWord_760093 prefixEnd_760093 12849153946271600538005 := by
  unfold tailWord_760093
  simp only [CollatzResearch.WordTrace]
  refine ⟨27722869235320349394524933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18481912823546899596349955 27722869235320349394524933)
  ·
    refine ⟨5198037981622565511473425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27722869235320349394524933 5198037981622565511473425)
    ·
      refine ⟨3898528486216924133605069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5198037981622565511473425 3898528486216924133605069)
      ·
        refine ⟨1461948182331346550101901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3898528486216924133605069 1461948182331346550101901)
        ·
          refine ⟨548230568374254956288213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1461948182331346550101901 548230568374254956288213)
          ·
            refine ⟨12849153946271600538005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 548230568374254956288213 12849153946271600538005)
            ·
              rfl

theorem cell20_760093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 7].length) (baseStart_760093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760093 prefixEnd_760093 := by exact prefixLift 760093
  have htrace : WordTrace (prefixWord ++ tailWord_760093) baseStart_760093 baseEnd_760093 := by
    simpa [prefixWord, tailWord_760093, baseEnd_760093] using wordTrace_append hprefix tailTrace_760093
  have hstable : (prefixWord ++ tailWord_760093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760093).length < 2 ^ (prefixWord ++ tailWord_760093).sum := by decide
  have hdescent : baseEnd_760093 < baseStart_760093 := by decide
  rcases family_descends (prefixWord ++ tailWord_760093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760100 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_760100 : Nat := 118140960795 + 760100 * 2 ^ 59
def prefixEnd_760100 : Nat := 4983230072969 + 3 ^ 40 * 760100 * 2
def baseEnd_760100 : Nat := 346930351540072301292773

theorem tailTrace_760100 : CollatzResearch.WordTrace tailWord_760100 prefixEnd_760100 346930351540072301292773 := by
  unfold tailWord_760100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13861562273147494795014877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18482083030863326393353169 13861562273147494795014877)
  ·
    refine ⟨5198085852430310548130579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13861562273147494795014877 5198085852430310548130579)
    ·
      refine ⟨7797128778645465822195869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5198085852430310548130579 7797128778645465822195869)
      ·
        refine ⟨2923923291992049683323451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7797128778645465822195869 2923923291992049683323451)
        ·
          refine ⟨4385884937988074524985177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923923291992049683323451 4385884937988074524985177)
          ·
            refine ⟨3289413703491055893738883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4385884937988074524985177 3289413703491055893738883)
            ·
              refine ⟨4934120555236583840608325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289413703491055893738883 4934120555236583840608325)
              ·
                refine ⟨925147604106859470114061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4934120555236583840608325 925147604106859470114061)
                ·
                  refine ⟨346930351540072301292773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925147604106859470114061 346930351540072301292773)
                  ·
                    rfl

theorem cell20_760100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_760100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760100 prefixEnd_760100 := by exact prefixLift 760100
  have htrace : WordTrace (prefixWord ++ tailWord_760100) baseStart_760100 baseEnd_760100 := by
    simpa [prefixWord, tailWord_760100, baseEnd_760100] using wordTrace_append hprefix tailTrace_760100
  have hstable : (prefixWord ++ tailWord_760100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760100).length < 2 ^ (prefixWord ++ tailWord_760100).sum := by decide
  have hdescent : baseEnd_760100 < baseStart_760100 := by decide
  rcases family_descends (prefixWord ++ tailWord_760100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760162 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_760162 : Nat := 118140960795 + 760162 * 2 ^ 59
def prefixEnd_760162 : Nat := 4983230072969 + 3 ^ 40 * 760162 * 2
def baseEnd_760162 : Nat := 346958650029475641225853

theorem tailTrace_760162 : CollatzResearch.WordTrace tailWord_760162 prefixEnd_760162 346958650029475641225853 := by
  unfold tailWord_760162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931346468017593544696685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18483590581380249452524493 6931346468017593544696685)
  ·
    refine ⟨2599254925506597579261257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6931346468017593544696685 2599254925506597579261257)
    ·
      refine ⟨1949441194129948184445943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2599254925506597579261257 1949441194129948184445943)
      ·
        refine ⟨2924161791194922276668915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949441194129948184445943 2924161791194922276668915)
        ·
          refine ⟨4386242686792383415003373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924161791194922276668915 4386242686792383415003373)
          ·
            refine ⟨1644841007547143780626265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4386242686792383415003373 1644841007547143780626265)
            ·
              refine ⟨1233630755660357835469699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644841007547143780626265 1233630755660357835469699)
              ·
                refine ⟨1850446133490536753204549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233630755660357835469699 1850446133490536753204549)
                ·
                  refine ⟨346958650029475641225853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850446133490536753204549 346958650029475641225853)
                  ·
                    rfl

theorem cell20_760162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_760162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760162 prefixEnd_760162 := by exact prefixLift 760162
  have htrace : WordTrace (prefixWord ++ tailWord_760162) baseStart_760162 baseEnd_760162 := by
    simpa [prefixWord, tailWord_760162, baseEnd_760162] using wordTrace_append hprefix tailTrace_760162
  have hstable : (prefixWord ++ tailWord_760162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760162).length < 2 ^ (prefixWord ++ tailWord_760162).sum := by decide
  have hdescent : baseEnd_760162 < baseStart_760162 := by decide
  rcases family_descends (prefixWord ++ tailWord_760162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760182 : List Nat := [5, 1, 1, 4, 2, 1, 2, 4]
def baseStart_760182 : Nat := 118140960795 + 760182 * 2 ^ 59
def prefixEnd_760182 : Nat := 4983230072969 + 3 ^ 40 * 760182 * 2
def baseEnd_760182 : Nat := 115655926191481486853035

theorem tailTrace_760182 : CollatzResearch.WordTrace tailWord_760182 prefixEnd_760182 115655926191481486853035 := by
  unfold tailWord_760182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732882208249869849657175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18484076887998611729676533 1732882208249869849657175)
  ·
    refine ⟨2599323312374804774485763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1732882208249869849657175 2599323312374804774485763)
    ·
      refine ⟨3898984968562207161728645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2599323312374804774485763 3898984968562207161728645)
      ·
        refine ⟨731059681605413842824121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3898984968562207161728645 731059681605413842824121)
        ·
          refine ⟨548294761204060382118091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731059681605413842824121 548294761204060382118091)
          ·
            refine ⟨822442141806090573177137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548294761204060382118091 822442141806090573177137)
            ·
              refine ⟨616831606354567929882853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822442141806090573177137 616831606354567929882853)
              ·
                refine ⟨115655926191481486853035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616831606354567929882853 115655926191481486853035)
                ·
                  rfl

theorem cell20_760182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_760182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760182 prefixEnd_760182 := by exact prefixLift 760182
  have htrace : WordTrace (prefixWord ++ tailWord_760182) baseStart_760182 baseEnd_760182 := by
    simpa [prefixWord, tailWord_760182, baseEnd_760182] using wordTrace_append hprefix tailTrace_760182
  have hstable : (prefixWord ++ tailWord_760182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760182).length < 2 ^ (prefixWord ++ tailWord_760182).sum := by decide
  have hdescent : baseEnd_760182 < baseStart_760182 := by decide
  rcases family_descends (prefixWord ++ tailWord_760182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760231 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 3]
def baseStart_760231 : Nat := 118140960795 + 760231 * 2 ^ 59
def prefixEnd_760231 : Nat := 4983230072969 + 3 ^ 40 * 760231 * 2
def baseEnd_760231 : Nat := 346990143509618067925571

theorem tailTrace_760231 : CollatzResearch.WordTrace tailWord_760231 prefixEnd_760231 346990143509618067925571 := by
  unfold tailWord_760231
  simp only [CollatzResearch.WordTrace]
  refine ⟨27727902508820398963048547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18485268339213599308699031 27727902508820398963048547)
  ·
    refine ⟨41591853763230598444572821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27727902508820398963048547 41591853763230598444572821)
    ·
      refine ⟨1949618145151434302089351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41591853763230598444572821 1949618145151434302089351)
      ·
        refine ⟨2924427217727151453134027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949618145151434302089351 2924427217727151453134027)
        ·
          refine ⟨4386640826590727179701041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924427217727151453134027 4386640826590727179701041)
          ·
            refine ⟨3289980619943045384775781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4386640826590727179701041 3289980619943045384775781)
            ·
              refine ⟨616871366239321009645459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3289980619943045384775781 616871366239321009645459)
              ·
                refine ⟨925307049358981514468189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616871366239321009645459 925307049358981514468189)
                ·
                  refine ⟨346990143509618067925571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925307049358981514468189 346990143509618067925571)
                  ·
                    rfl

theorem cell20_760231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_760231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760231 prefixEnd_760231 := by exact prefixLift 760231
  have htrace : WordTrace (prefixWord ++ tailWord_760231) baseStart_760231 baseEnd_760231 := by
    simpa [prefixWord, tailWord_760231, baseEnd_760231] using wordTrace_append hprefix tailTrace_760231
  have hstable : (prefixWord ++ tailWord_760231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760231).length < 2 ^ (prefixWord ++ tailWord_760231).sum := by decide
  have hdescent : baseEnd_760231 < baseStart_760231 := by decide
  rcases family_descends (prefixWord ++ tailWord_760231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760242 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_760242 : Nat := 118140960795 + 760242 * 2 ^ 59
def prefixEnd_760242 : Nat := 4983230072969 + 3 ^ 40 * 760242 * 2
def baseEnd_760242 : Nat := 346995164209350918558859

theorem tailTrace_760242 : CollatzResearch.WordTrace tailWord_760242 prefixEnd_760242 346995164209350918558859 := by
  unfold tailWord_760242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932075927945136960424745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18485535807853698561132653 6932075927945136960424745)
  ·
    refine ⟨5199056945958852720318559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6932075927945136960424745 5199056945958852720318559)
    ·
      refine ⟨7798585418938279080477839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5199056945958852720318559 7798585418938279080477839)
      ·
        refine ⟨11697878128407418620716759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7798585418938279080477839 11697878128407418620716759)
        ·
          refine ⟨17546817192611127931075139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11697878128407418620716759 17546817192611127931075139)
          ·
            refine ⟨26320225788916691896612709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17546817192611127931075139 26320225788916691896612709)
            ·
              refine ⟨4935042335421879730614883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26320225788916691896612709 4935042335421879730614883)
              ·
                refine ⟨7402563503132819595922325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935042335421879730614883 7402563503132819595922325)
                ·
                  refine ⟨346995164209350918558859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7402563503132819595922325 346995164209350918558859)
                  ·
                    rfl

theorem cell20_760242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_760242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760242 prefixEnd_760242 := by exact prefixLift 760242
  have htrace : WordTrace (prefixWord ++ tailWord_760242) baseStart_760242 baseEnd_760242 := by
    simpa [prefixWord, tailWord_760242, baseEnd_760242] using wordTrace_append hprefix tailTrace_760242
  have hstable : (prefixWord ++ tailWord_760242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760242).length < 2 ^ (prefixWord ++ tailWord_760242).sum := by decide
  have hdescent : baseEnd_760242 < baseStart_760242 := by decide
  rcases family_descends (prefixWord ++ tailWord_760242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760259 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 2]
def baseStart_760259 : Nat := 118140960795 + 760259 * 2 ^ 59
def prefixEnd_760259 : Nat := 4983230072969 + 3 ^ 40 * 760259 * 2
def baseEnd_760259 : Nat := 347002923472574414992123

theorem tailTrace_760259 : CollatzResearch.WordTrace tailWord_760259 prefixEnd_760259 347002923472574414992123 := by
  unfold tailWord_760259
  simp only [CollatzResearch.WordTrace]
  refine ⟨27728923752718959745067831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18485949168479306496711887 27728923752718959745067831)
  ·
    refine ⟨41593385629078439617601747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27728923752718959745067831 41593385629078439617601747)
    ·
      refine ⟨62390078443617659426402621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41593385629078439617601747 62390078443617659426402621)
      ·
        refine ⟨23396279416356622284900983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62390078443617659426402621 23396279416356622284900983)
        ·
          refine ⟨35094419124534933427351475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23396279416356622284900983 35094419124534933427351475)
          ·
            refine ⟨52641628686802400141027213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35094419124534933427351475 52641628686802400141027213)
            ·
              refine ⟨19740610757550900052885205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52641628686802400141027213 19740610757550900052885205)
              ·
                refine ⟨462670564630099219989497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19740610757550900052885205 462670564630099219989497)
                ·
                  refine ⟨347002923472574414992123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462670564630099219989497 347002923472574414992123)
                  ·
                    rfl

theorem cell20_760259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 2].length) (baseStart_760259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760259 prefixEnd_760259 := by exact prefixLift 760259
  have htrace : WordTrace (prefixWord ++ tailWord_760259) baseStart_760259 baseEnd_760259 := by
    simpa [prefixWord, tailWord_760259, baseEnd_760259] using wordTrace_append hprefix tailTrace_760259
  have hstable : (prefixWord ++ tailWord_760259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760259).length < 2 ^ (prefixWord ++ tailWord_760259).sum := by decide
  have hdescent : baseEnd_760259 < baseStart_760259 := by decide
  rcases family_descends (prefixWord ++ tailWord_760259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760280 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_760280 : Nat := 118140960795 + 760280 * 2 ^ 59
def prefixEnd_760280 : Nat := 4983230072969 + 3 ^ 40 * 760280 * 2
def baseEnd_760280 : Nat := 347012508444791675292037

theorem tailTrace_760280 : CollatzResearch.WordTrace tailWord_760280 prefixEnd_760280 347012508444791675292037 := by
  unfold tailWord_760280
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864844842821440165791147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18486459790428586887721529 13864844842821440165791147)
  ·
    refine ⟨20797267264232160248686721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13864844842821440165791147 20797267264232160248686721)
    ·
      refine ⟨15597950448174120186515041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20797267264232160248686721 15597950448174120186515041)
      ·
        refine ⟨11698462836130590139886281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15597950448174120186515041 11698462836130590139886281)
        ·
          refine ⟨8773847127097942604914711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11698462836130590139886281 8773847127097942604914711)
          ·
            refine ⟨13160770690646913907372067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8773847127097942604914711 13160770690646913907372067)
            ·
              refine ⟨19741156035970370861058101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160770690646913907372067 19741156035970370861058101)
              ·
                refine ⟨1850733378372222268224197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19741156035970370861058101 1850733378372222268224197)
                ·
                  refine ⟨347012508444791675292037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850733378372222268224197 347012508444791675292037)
                  ·
                    rfl

theorem cell20_760280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_760280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760280 prefixEnd_760280 := by exact prefixLift 760280
  have htrace : WordTrace (prefixWord ++ tailWord_760280) baseStart_760280 baseEnd_760280 := by
    simpa [prefixWord, tailWord_760280, baseEnd_760280] using wordTrace_append hprefix tailTrace_760280
  have hstable : (prefixWord ++ tailWord_760280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760280).length < 2 ^ (prefixWord ++ tailWord_760280).sum := by decide
  have hdescent : baseEnd_760280 < baseStart_760280 := by decide
  rcases family_descends (prefixWord ++ tailWord_760280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760304 : List Nat := [2, 1, 1, 1, 3, 3, 5, 4]
def baseStart_760304 : Nat := 118140960795 + 760304 * 2 ^ 59
def prefixEnd_760304 : Nat := 4983230072969 + 3 ^ 40 * 760304 * 2
def baseEnd_760304 : Nat := 115674487566251419497313

theorem tailTrace_760304 : CollatzResearch.WordTrace tailWord_760304 prefixEnd_760304 115674487566251419497313 := by
  unfold tailWord_760304
  simp only [CollatzResearch.WordTrace]
  refine ⟨13865282518777966215227983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18487043358370621620303977 13865282518777966215227983)
  ·
    refine ⟨20797923778166949322841975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13865282518777966215227983 20797923778166949322841975)
    ·
      refine ⟨31196885667250423984262963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20797923778166949322841975 31196885667250423984262963)
      ·
        refine ⟨46795328500875635976394445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31196885667250423984262963 46795328500875635976394445)
        ·
          refine ⟨17548248187828363491147917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46795328500875635976394445 17548248187828363491147917)
          ·
            refine ⟨6580593070435636309180469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17548248187828363491147917 6580593070435636309180469)
            ·
              refine ⟨616930600353340903985669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6580593070435636309180469 616930600353340903985669)
              ·
                refine ⟨115674487566251419497313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616930600353340903985669 115674487566251419497313)
                ·
                  rfl

theorem cell20_760304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_760304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760304 prefixEnd_760304 := by exact prefixLift 760304
  have htrace : WordTrace (prefixWord ++ tailWord_760304) baseStart_760304 baseEnd_760304 := by
    simpa [prefixWord, tailWord_760304, baseEnd_760304] using wordTrace_append hprefix tailTrace_760304
  have hstable : (prefixWord ++ tailWord_760304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760304).length < 2 ^ (prefixWord ++ tailWord_760304).sum := by decide
  have hdescent : baseEnd_760304 < baseStart_760304 := by decide
  rcases family_descends (prefixWord ++ tailWord_760304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760380 : List Nat := [2, 2, 2, 2, 3, 3, 6]
def baseStart_760380 : Nat := 118140960795 + 760380 * 2 ^ 59
def prefixEnd_760380 : Nat := 4983230072969 + 3 ^ 40 * 760380 * 2
def baseEnd_760380 : Nat := 38562016796626196884255

theorem tailTrace_760380 : CollatzResearch.WordTrace tailWord_760380 prefixEnd_760380 38562016796626196884255 := by
  unfold tailWord_760380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13866668492640298705111297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18488891323520398273481729 13866668492640298705111297)
  ·
    refine ⟨10400001369480224028833473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13866668492640298705111297 10400001369480224028833473)
    ·
      refine ⟨7800001027110168021625105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10400001369480224028833473 7800001027110168021625105)
      ·
        refine ⟨5850000770332626016218829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7800001027110168021625105 5850000770332626016218829)
        ·
          refine ⟨2193750288874734756082061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5850000770332626016218829 2193750288874734756082061)
          ·
            refine ⟨822656358328025533530773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2193750288874734756082061 822656358328025533530773)
            ·
              refine ⟨38562016796626196884255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 822656358328025533530773 38562016796626196884255)
              ·
                rfl

theorem cell20_760380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 6].length) (baseStart_760380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760380 prefixEnd_760380 := by exact prefixLift 760380
  have htrace : WordTrace (prefixWord ++ tailWord_760380) baseStart_760380 baseEnd_760380 := by
    simpa [prefixWord, tailWord_760380, baseEnd_760380] using wordTrace_append hprefix tailTrace_760380
  have hstable : (prefixWord ++ tailWord_760380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760380).length < 2 ^ (prefixWord ++ tailWord_760380).sum := by decide
  have hdescent : baseEnd_760380 < baseStart_760380 := by decide
  rcases family_descends (prefixWord ++ tailWord_760380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760397 : List Nat := [1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_760397 : Nat := 118140960795 + 760397 * 2 ^ 59
def prefixEnd_760397 : Nat := 4983230072969 + 3 ^ 40 * 760397 * 2
def baseEnd_760397 : Nat := 115688636810953089463853

theorem tailTrace_760397 : CollatzResearch.WordTrace tailWord_760397 prefixEnd_760397 115688636810953089463853 := by
  unfold tailWord_760397
  simp only [CollatzResearch.WordTrace]
  refine ⟨27733957026219009313591445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18489304684146006209060963 27733957026219009313591445)
  ·
    refine ⟨1300029235604016061574599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27733957026219009313591445 1300029235604016061574599)
    ·
      refine ⟨1950043853406024092361899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300029235604016061574599 1950043853406024092361899)
      ·
        refine ⟨2925065780109036138542849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950043853406024092361899 2925065780109036138542849)
        ·
          refine ⟨2193799335081777103907137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925065780109036138542849 2193799335081777103907137)
          ·
            refine ⟨1645349501311332827930353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2193799335081777103907137 1645349501311332827930353)
            ·
              refine ⟨1234012125983499620947765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645349501311332827930353 1234012125983499620947765)
              ·
                refine ⟨115688636810953089463853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1234012125983499620947765 115688636810953089463853)
                ·
                  rfl

theorem cell20_760397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_760397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760397 prefixEnd_760397 := by exact prefixLift 760397
  have htrace : WordTrace (prefixWord ++ tailWord_760397) baseStart_760397 baseEnd_760397 := by
    simpa [prefixWord, tailWord_760397, baseEnd_760397] using wordTrace_append hprefix tailTrace_760397
  have hstable : (prefixWord ++ tailWord_760397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760397).length < 2 ^ (prefixWord ++ tailWord_760397).sum := by decide
  have hdescent : baseEnd_760397 < baseStart_760397 := by decide
  rcases family_descends (prefixWord ++ tailWord_760397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760401 : List Nat := [1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_760401 : Nat := 118140960795 + 760401 * 2 ^ 59
def prefixEnd_760401 : Nat := 4983230072969 + 3 ^ 40 * 760401 * 2
def baseEnd_760401 : Nat := 115689245380617677419403

theorem tailTrace_760401 : CollatzResearch.WordTrace tailWord_760401 prefixEnd_760401 115689245380617677419403 := by
  unfold tailWord_760401
  simp only [CollatzResearch.WordTrace]
  refine ⟨27734102918204517996737057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18489401945469678664491371 27734102918204517996737057)
  ·
    refine ⟨20800577188653388497552793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27734102918204517996737057 20800577188653388497552793)
    ·
      refine ⟨15600432891490041373164595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20800577188653388497552793 15600432891490041373164595)
      ·
        refine ⟨23400649337235062059746893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600432891490041373164595 23400649337235062059746893)
        ·
          refine ⟨8775243501463148272405085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23400649337235062059746893 8775243501463148272405085)
          ·
            refine ⟨3290716313048680602151907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8775243501463148272405085 3290716313048680602151907)
            ·
              refine ⟨4936074469573020903227861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290716313048680602151907 4936074469573020903227861)
              ·
                refine ⟨115689245380617677419403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4936074469573020903227861 115689245380617677419403)
                ·
                  rfl

theorem cell20_760401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_760401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760401 prefixEnd_760401 := by exact prefixLift 760401
  have htrace : WordTrace (prefixWord ++ tailWord_760401) baseStart_760401 baseEnd_760401 := by
    simpa [prefixWord, tailWord_760401, baseEnd_760401] using wordTrace_append hprefix tailTrace_760401
  have hstable : (prefixWord ++ tailWord_760401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760401).length < 2 ^ (prefixWord ++ tailWord_760401).sum := by decide
  have hdescent : baseEnd_760401 < baseStart_760401 := by decide
  rcases family_descends (prefixWord ++ tailWord_760401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760404 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_760404 : Nat := 118140960795 + 760404 * 2 ^ 59
def prefixEnd_760404 : Nat := 4983230072969 + 3 ^ 40 * 760404 * 2
def baseEnd_760404 : Nat := 347069105423598355158197

theorem tailTrace_760404 : CollatzResearch.WordTrace tailWord_760404 prefixEnd_760404 347069105423598355158197 := by
  unfold tailWord_760404
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867106168596824754548133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18489474891462433006064177 13867106168596824754548133)
  ·
    refine ⟨2600082406611904641477775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13867106168596824754548133 2600082406611904641477775)
    ·
      refine ⟨3900123609917856962216663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600082406611904641477775 3900123609917856962216663)
      ·
        refine ⟨5850185414876785443324995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900123609917856962216663 5850185414876785443324995)
        ·
          refine ⟨8775278122315178164987493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850185414876785443324995 8775278122315178164987493)
          ·
            refine ⟨1645364647934095905935155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8775278122315178164987493 1645364647934095905935155)
            ·
              refine ⟨2468046971901143858902733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645364647934095905935155 2468046971901143858902733)
              ·
                refine ⟨925517614462928947088525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2468046971901143858902733 925517614462928947088525)
                ·
                  refine ⟨347069105423598355158197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925517614462928947088525 347069105423598355158197)
                  ·
                    rfl

theorem cell20_760404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_760404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760404 prefixEnd_760404 := by exact prefixLift 760404
  have htrace : WordTrace (prefixWord ++ tailWord_760404) baseStart_760404 baseEnd_760404 := by
    simpa [prefixWord, tailWord_760404, baseEnd_760404] using wordTrace_append hprefix tailTrace_760404
  have hstable : (prefixWord ++ tailWord_760404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760404).length < 2 ^ (prefixWord ++ tailWord_760404).sum := by decide
  have hdescent : baseEnd_760404 < baseStart_760404 := by decide
  rcases family_descends (prefixWord ++ tailWord_760404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760477 : List Nat := [1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_760477 : Nat := 118140960795 + 760477 * 2 ^ 59
def prefixEnd_760477 : Nat := 4983230072969 + 3 ^ 40 * 760477 * 2
def baseEnd_760477 : Nat := 115700808204244848574855

theorem tailTrace_760477 : CollatzResearch.WordTrace tailWord_760477 prefixEnd_760477 115700808204244848574855 := by
  unfold tailWord_760477
  simp only [CollatzResearch.WordTrace]
  refine ⟨27736874865929182976503685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18491249910619455317669123 27736874865929182976503685)
  ·
    refine ⟨5200664037361721808094441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27736874865929182976503685 5200664037361721808094441)
    ·
      refine ⟨3900498028021291356070831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5200664037361721808094441 3900498028021291356070831)
      ·
        refine ⟨5850747042031937034106247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900498028021291356070831 5850747042031937034106247)
        ·
          refine ⟨8776120563047905551159371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850747042031937034106247 8776120563047905551159371)
          ·
            refine ⟨13164180844571858326739057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776120563047905551159371 13164180844571858326739057)
            ·
              refine ⟨9873135633428893745054293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13164180844571858326739057 9873135633428893745054293)
              ·
                refine ⟨115700808204244848574855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9873135633428893745054293 115700808204244848574855)
                ·
                  rfl

theorem cell20_760477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_760477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760477 prefixEnd_760477 := by exact prefixLift 760477
  have htrace : WordTrace (prefixWord ++ tailWord_760477) baseStart_760477 baseEnd_760477 := by
    simpa [prefixWord, tailWord_760477, baseEnd_760477] using wordTrace_append hprefix tailTrace_760477
  have hstable : (prefixWord ++ tailWord_760477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760477).length < 2 ^ (prefixWord ++ tailWord_760477).sum := by decide
  have hdescent : baseEnd_760477 < baseStart_760477 := by decide
  rcases family_descends (prefixWord ++ tailWord_760477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760560 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_760560 : Nat := 118140960795 + 760560 * 2 ^ 59
def prefixEnd_760560 : Nat := 4983230072969 + 3 ^ 40 * 760560 * 2
def baseEnd_760560 : Nat := 347140308074355145957559

theorem tailTrace_760560 : CollatzResearch.WordTrace tailWord_760560 prefixEnd_760560 347140308074355145957559 := by
  unfold tailWord_760560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13869951062314244075887567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18493268083085658767850089 13869951062314244075887567)
  ·
    refine ⟨20804926593471366113831351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13869951062314244075887567 20804926593471366113831351)
    ·
      refine ⟨31207389890207049170747027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20804926593471366113831351 31207389890207049170747027)
      ·
        refine ⟨46811084835310573756120541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31207389890207049170747027 46811084835310573756120541)
        ·
          refine ⟨17554156813241465158545203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46811084835310573756120541 17554156813241465158545203)
          ·
            refine ⟨26331235219862197737817805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17554156813241465158545203 26331235219862197737817805)
            ·
              refine ⟨9874213207448324151681677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26331235219862197737817805 9874213207448324151681677)
              ·
                refine ⟨3702829952793121556880629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9874213207448324151681677 3702829952793121556880629)
                ·
                  refine ⟨347140308074355145957559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3702829952793121556880629 347140308074355145957559)
                  ·
                    rfl

theorem cell20_760560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_760560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760560 prefixEnd_760560 := by exact prefixLift 760560
  have htrace : WordTrace (prefixWord ++ tailWord_760560) baseStart_760560 baseEnd_760560 := by
    simpa [prefixWord, tailWord_760560, baseEnd_760560] using wordTrace_append hprefix tailTrace_760560
  have hstable : (prefixWord ++ tailWord_760560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760560).length < 2 ^ (prefixWord ++ tailWord_760560).sum := by decide
  have hdescent : baseEnd_760560 < baseStart_760560 := by decide
  rcases family_descends (prefixWord ++ tailWord_760560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760621 : List Nat := [1, 5, 3, 2, 2, 1, 1, 5]
def baseStart_760621 : Nat := 118140960795 + 760621 * 2 ^ 59
def prefixEnd_760621 : Nat := 4983230072969 + 3 ^ 40 * 760621 * 2
def baseEnd_760621 : Nat := 115722716712170014974659

theorem tailTrace_760621 : CollatzResearch.WordTrace tailWord_760621 prefixEnd_760621 115722716712170014974659 := by
  unfold tailWord_760621
  simp only [CollatzResearch.WordTrace]
  refine ⟨27742126977407495569745717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18494751318271663713163811 27742126977407495569745717)
  ·
    refine ⟨2600824404131952709663661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27742126977407495569745717 2600824404131952709663661)
    ·
      refine ⟨975309151549482266123873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2600824404131952709663661 975309151549482266123873)
      ·
        refine ⟨731481863662111699592905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975309151549482266123873 731481863662111699592905)
        ·
          refine ⟨548611397746583774694679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731481863662111699592905 548611397746583774694679)
          ·
            refine ⟨822917096619875662042019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548611397746583774694679 822917096619875662042019)
            ·
              refine ⟨1234375644929813493063029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822917096619875662042019 1234375644929813493063029)
              ·
                refine ⟨115722716712170014974659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1234375644929813493063029 115722716712170014974659)
                ·
                  rfl

theorem cell20_760621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].length) (baseStart_760621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760621 prefixEnd_760621 := by exact prefixLift 760621
  have htrace : WordTrace (prefixWord ++ tailWord_760621) baseStart_760621 baseEnd_760621 := by
    simpa [prefixWord, tailWord_760621, baseEnd_760621] using wordTrace_append hprefix tailTrace_760621
  have hstable : (prefixWord ++ tailWord_760621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760621).length < 2 ^ (prefixWord ++ tailWord_760621).sum := by decide
  have hdescent : baseEnd_760621 < baseStart_760621 := by decide
  rcases family_descends (prefixWord ++ tailWord_760621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760636 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_760636 : Nat := 118140960795 + 760636 * 2 ^ 59
def prefixEnd_760636 : Nat := 4983230072969 + 3 ^ 40 * 760636 * 2
def baseEnd_760636 : Nat := 347174996545236659423915

theorem tailTrace_760636 : CollatzResearch.WordTrace tailWord_760636 prefixEnd_760636 347174996545236659423915 := by
  unfold tailWord_760636
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871337036176576565770881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18495116048235435421027841 13871337036176576565770881)
  ·
    refine ⟨10403502777132432424328161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13871337036176576565770881 10403502777132432424328161)
    ·
      refine ⟨7802627082849324318246121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10403502777132432424328161 7802627082849324318246121)
      ·
        refine ⟨5851970312136993238684591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7802627082849324318246121 5851970312136993238684591)
        ·
          refine ⟨8777955468205489858026887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851970312136993238684591 8777955468205489858026887)
          ·
            refine ⟨13166933202308234787040331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8777955468205489858026887 13166933202308234787040331)
            ·
              refine ⟨19750399803462352180560497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13166933202308234787040331 19750399803462352180560497)
              ·
                refine ⟨14812799852596764135420373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19750399803462352180560497 14812799852596764135420373)
                ·
                  refine ⟨347174996545236659423915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14812799852596764135420373 347174996545236659423915)
                  ·
                    rfl

theorem cell20_760636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_760636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760636 prefixEnd_760636 := by exact prefixLift 760636
  have htrace : WordTrace (prefixWord ++ tailWord_760636) baseStart_760636 baseEnd_760636 := by
    simpa [prefixWord, tailWord_760636, baseEnd_760636] using wordTrace_append hprefix tailTrace_760636
  have hstable : (prefixWord ++ tailWord_760636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760636).length < 2 ^ (prefixWord ++ tailWord_760636).sum := by decide
  have hdescent : baseEnd_760636 < baseStart_760636 := by decide
  rcases family_descends (prefixWord ++ tailWord_760636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760677 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 2]
def baseStart_760677 : Nat := 118140960795 + 760677 * 2 ^ 59
def prefixEnd_760677 : Nat := 4983230072969 + 3 ^ 40 * 760677 * 2
def baseEnd_760677 : Nat := 347193710062422739057081

theorem tailTrace_760677 : CollatzResearch.WordTrace tailWord_760677 prefixEnd_760677 347193710062422739057081 := by
  unfold tailWord_760677
  simp only [CollatzResearch.WordTrace]
  refine ⟨27744169465204617133784285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496112976803078089189523 27744169465204617133784285)
  ·
    refine ⟨10404063549451731425169107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27744169465204617133784285 10404063549451731425169107)
    ·
      refine ⟨15606095324177597137753661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10404063549451731425169107 15606095324177597137753661)
      ·
        refine ⟨5852285746566598926657623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15606095324177597137753661 5852285746566598926657623)
        ·
          refine ⟨8778428619849898389986435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852285746566598926657623 8778428619849898389986435)
          ·
            refine ⟨13167642929774847584979653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778428619849898389986435 13167642929774847584979653)
            ·
              refine ⟨2468933049332783922183685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13167642929774847584979653 2468933049332783922183685)
              ·
                refine ⟨462924946749896985409441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2468933049332783922183685 462924946749896985409441)
                ·
                  refine ⟨347193710062422739057081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462924946749896985409441 347193710062422739057081)
                  ·
                    rfl

theorem cell20_760677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_760677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760677 prefixEnd_760677 := by exact prefixLift 760677
  have htrace : WordTrace (prefixWord ++ tailWord_760677) baseStart_760677 baseEnd_760677 := by
    simpa [prefixWord, tailWord_760677, baseEnd_760677] using wordTrace_append hprefix tailTrace_760677
  have hstable : (prefixWord ++ tailWord_760677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760677).length < 2 ^ (prefixWord ++ tailWord_760677).sum := by decide
  have hdescent : baseEnd_760677 < baseStart_760677 := by decide
  rcases family_descends (prefixWord ++ tailWord_760677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760715 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 2]
def baseStart_760715 : Nat := 118140960795 + 760715 * 2 ^ 59
def prefixEnd_760715 : Nat := 4983230072969 + 3 ^ 40 * 760715 * 2
def baseEnd_760715 : Nat := 347211054297863495790259

theorem tailTrace_760715 : CollatzResearch.WordTrace tailWord_760715 prefixEnd_760715 347211054297863495790259 := by
  unfold tailWord_760715
  simp only [CollatzResearch.WordTrace]
  refine ⟨27745555439066949623667599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18497036959377966415778399 27745555439066949623667599)
  ·
    refine ⟨41618333158600424435501399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27745555439066949623667599 41618333158600424435501399)
    ·
      refine ⟨62427499737900636653252099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41618333158600424435501399 62427499737900636653252099)
      ·
        refine ⟨93641249606850954979878149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62427499737900636653252099 93641249606850954979878149)
        ·
          refine ⟨17557734301284554058727153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93641249606850954979878149 17557734301284554058727153)
          ·
            refine ⟨13168300725963415544045365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17557734301284554058727153 13168300725963415544045365)
            ·
              refine ⟨1234528193059070207254253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13168300725963415544045365 1234528193059070207254253)
              ·
                refine ⟨462948072397151327720345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1234528193059070207254253 462948072397151327720345)
                ·
                  refine ⟨347211054297863495790259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462948072397151327720345 347211054297863495790259)
                  ·
                    rfl

theorem cell20_760715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 2].length) (baseStart_760715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760715 prefixEnd_760715 := by exact prefixLift 760715
  have htrace : WordTrace (prefixWord ++ tailWord_760715) baseStart_760715 baseEnd_760715 := by
    simpa [prefixWord, tailWord_760715, baseEnd_760715] using wordTrace_append hprefix tailTrace_760715
  have hstable : (prefixWord ++ tailWord_760715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760715).length < 2 ^ (prefixWord ++ tailWord_760715).sum := by decide
  have hdescent : baseEnd_760715 < baseStart_760715 := by decide
  rcases family_descends (prefixWord ++ tailWord_760715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760732 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_760732 : Nat := 118140960795 + 760732 * 2 ^ 59
def prefixEnd_760732 : Nat := 4983230072969 + 3 ^ 40 * 760732 * 2
def baseEnd_760732 : Nat := 347218813561086992223523

theorem tailTrace_760732 : CollatzResearch.WordTrace tailWord_760732 prefixEnd_760732 347218813561086992223523 := by
  unfold tailWord_760732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873087740002680763518225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18497450320003574351357633 13873087740002680763518225)
  ·
    refine ⟨10404815805002010572638669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13873087740002680763518225 10404815805002010572638669)
    ·
      refine ⟨3901805926875753964739501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10404815805002010572638669 3901805926875753964739501)
      ·
        refine ⟨1463177222578407736777313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3901805926875753964739501 1463177222578407736777313)
        ·
          refine ⟨1097382916933805802582985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463177222578407736777313 1097382916933805802582985)
          ·
            refine ⟨823037187700354351937239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097382916933805802582985 823037187700354351937239)
            ·
              refine ⟨1234555781550531527905859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823037187700354351937239 1234555781550531527905859)
              ·
                refine ⟨1851833672325797291858789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234555781550531527905859 1851833672325797291858789)
                ·
                  refine ⟨347218813561086992223523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851833672325797291858789 347218813561086992223523)
                  ·
                    rfl

theorem cell20_760732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_760732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760732 prefixEnd_760732 := by exact prefixLift 760732
  have htrace : WordTrace (prefixWord ++ tailWord_760732) baseStart_760732 baseEnd_760732 := by
    simpa [prefixWord, tailWord_760732, baseEnd_760732] using wordTrace_append hprefix tailTrace_760732
  have hstable : (prefixWord ++ tailWord_760732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760732).length < 2 ^ (prefixWord ++ tailWord_760732).sum := by decide
  have hdescent : baseEnd_760732 < baseStart_760732 := by decide
  rcases family_descends (prefixWord ++ tailWord_760732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760736 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_760736 : Nat := 118140960795 + 760736 * 2 ^ 59
def prefixEnd_760736 : Nat := 4983230072969 + 3 ^ 40 * 760736 * 2
def baseEnd_760736 : Nat := 347220639270080756090173

theorem tailTrace_760736 : CollatzResearch.WordTrace tailWord_760736 prefixEnd_760736 347220639270080756090173 := by
  unfold tailWord_760736
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873160685995435105091031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18497547581327246806788041 13873160685995435105091031)
  ·
    refine ⟨20809741028993152657636547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13873160685995435105091031 20809741028993152657636547)
    ·
      refine ⟨31214611543489728986454821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20809741028993152657636547 31214611543489728986454821)
      ·
        refine ⟨5852739664404324184960279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31214611543489728986454821 5852739664404324184960279)
        ·
          refine ⟨8779109496606486277440419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852739664404324184960279 8779109496606486277440419)
          ·
            refine ⟨13168664244909729416160629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779109496606486277440419 13168664244909729416160629)
            ·
              refine ⟨1234562272960287132765059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13168664244909729416160629 1234562272960287132765059)
              ·
                refine ⟨1851843409440430699147589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234562272960287132765059 1851843409440430699147589)
                ·
                  refine ⟨347220639270080756090173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851843409440430699147589 347220639270080756090173)
                  ·
                    rfl

theorem cell20_760736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_760736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760736 prefixEnd_760736 := by exact prefixLift 760736
  have htrace : WordTrace (prefixWord ++ tailWord_760736) baseStart_760736 baseEnd_760736 := by
    simpa [prefixWord, tailWord_760736, baseEnd_760736] using wordTrace_append hprefix tailTrace_760736
  have hstable : (prefixWord ++ tailWord_760736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760736).length < 2 ^ (prefixWord ++ tailWord_760736).sum := by decide
  have hdescent : baseEnd_760736 < baseStart_760736 := by decide
  rcases family_descends (prefixWord ++ tailWord_760736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760843 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 3]
def baseStart_760843 : Nat := 118140960795 + 760843 * 2 ^ 59
def prefixEnd_760843 : Nat := 4983230072969 + 3 ^ 40 * 760843 * 2
def baseEnd_760843 : Nat := 347269476985663939523069

theorem tailTrace_760843 : CollatzResearch.WordTrace tailWord_760843 prefixEnd_760843 347269476985663939523069 := by
  unfold tailWord_760843
  simp only [CollatzResearch.WordTrace]
  refine ⟨27750223982603227484327183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18500149321735484989551455 27750223982603227484327183)
  ·
    refine ⟨41625335973904841226490775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27750223982603227484327183 41625335973904841226490775)
    ·
      refine ⟨62438003960857261839736163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41625335973904841226490775 62438003960857261839736163)
      ·
        refine ⟨93657005941285892759604245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62438003960857261839736163 93657005941285892759604245)
        ·
          refine ⟨4390172153497776223106449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93657005941285892759604245 4390172153497776223106449)
          ·
            refine ⟨3292629115123332167329837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4390172153497776223106449 3292629115123332167329837)
            ·
              refine ⟨1234735918171249562748689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3292629115123332167329837 1234735918171249562748689)
              ·
                refine ⟨926051938628437172061517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234735918171249562748689 926051938628437172061517)
                ·
                  refine ⟨347269476985663939523069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926051938628437172061517 347269476985663939523069)
                  ·
                    rfl

theorem cell20_760843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_760843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760843 prefixEnd_760843 := by exact prefixLift 760843
  have htrace : WordTrace (prefixWord ++ tailWord_760843) baseStart_760843 baseEnd_760843 := by
    simpa [prefixWord, tailWord_760843, baseEnd_760843] using wordTrace_append hprefix tailTrace_760843
  have hstable : (prefixWord ++ tailWord_760843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760843).length < 2 ^ (prefixWord ++ tailWord_760843).sum := by decide
  have hdescent : baseEnd_760843 < baseStart_760843 := by decide
  rcases family_descends (prefixWord ++ tailWord_760843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760874 : List Nat := [3, 1, 4, 1, 3, 1, 1, 6]
def baseStart_760874 : Nat := 118140960795 + 760874 * 2 ^ 59
def prefixEnd_760874 : Nat := 4983230072969 + 3 ^ 40 * 760874 * 2
def baseEnd_760874 : Nat := 115761208743455203163203

theorem tailTrace_760874 : CollatzResearch.WordTrace tailWord_760874 prefixEnd_760874 115761208743455203163203 := by
  unfold tailWord_760874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937838661372729944676419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18500903096993946519137117 6937838661372729944676419)
  ·
    refine ⟨10406757992059094917014629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937838661372729944676419 10406757992059094917014629)
    ·
      refine ⟨1951267123511080296940243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10406757992059094917014629 1951267123511080296940243)
      ·
        refine ⟨2926900685266620445410365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951267123511080296940243 2926900685266620445410365)
        ·
          refine ⟨1097587756974982667028887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2926900685266620445410365 1097587756974982667028887)
          ·
            refine ⟨1646381635462474000543331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097587756974982667028887 1646381635462474000543331)
            ·
              refine ⟨2469572453193711000814997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646381635462474000543331 2469572453193711000814997)
              ·
                refine ⟨115761208743455203163203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2469572453193711000814997 115761208743455203163203)
                ·
                  rfl

theorem cell20_760874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_760874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760874 prefixEnd_760874 := by exact prefixLift 760874
  have htrace : WordTrace (prefixWord ++ tailWord_760874) baseStart_760874 baseEnd_760874 := by
    simpa [prefixWord, tailWord_760874, baseEnd_760874] using wordTrace_append hprefix tailTrace_760874
  have hstable : (prefixWord ++ tailWord_760874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760874).length < 2 ^ (prefixWord ++ tailWord_760874).sum := by decide
  have hdescent : baseEnd_760874 < baseStart_760874 := by decide
  rcases family_descends (prefixWord ++ tailWord_760874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760957 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_760957 : Nat := 118140960795 + 760957 * 2 ^ 59
def prefixEnd_760957 : Nat := 4983230072969 + 3 ^ 40 * 760957 * 2
def baseEnd_760957 : Nat := 347321509691986209722603

theorem tailTrace_760957 : CollatzResearch.WordTrace tailWord_760957 prefixEnd_760957 347321509691986209722603 := by
  unfold tailWord_760957
  simp only [CollatzResearch.WordTrace]
  refine ⟨27754381904190224953977125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18502921269460149969318083 27754381904190224953977125)
  ·
    refine ⟨5203946607035667178870711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27754381904190224953977125 5203946607035667178870711)
    ·
      refine ⟨7805919910553500768306067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5203946607035667178870711 7805919910553500768306067)
      ·
        refine ⟨11708879865830251152459101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805919910553500768306067 11708879865830251152459101)
        ·
          refine ⟨4390829949686344182172163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11708879865830251152459101 4390829949686344182172163)
          ·
            refine ⟨6586244924529516273258245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390829949686344182172163 6586244924529516273258245)
            ·
              refine ⟨1234920923349284301235921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6586244924529516273258245 1234920923349284301235921)
              ·
                refine ⟨926190692511963225926941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234920923349284301235921 926190692511963225926941)
                ·
                  refine ⟨347321509691986209722603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926190692511963225926941 347321509691986209722603)
                  ·
                    rfl

theorem cell20_760957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_760957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760957 prefixEnd_760957 := by exact prefixLift 760957
  have htrace : WordTrace (prefixWord ++ tailWord_760957) baseStart_760957 baseEnd_760957 := by
    simpa [prefixWord, tailWord_760957, baseEnd_760957] using wordTrace_append hprefix tailTrace_760957
  have hstable : (prefixWord ++ tailWord_760957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760957).length < 2 ^ (prefixWord ++ tailWord_760957).sum := by decide
  have hdescent : baseEnd_760957 < baseStart_760957 := by decide
  rcases family_descends (prefixWord ++ tailWord_760957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760988 : List Nat := [2, 2, 3, 2, 1, 3, 3, 4]
def baseStart_760988 : Nat := 118140960795 + 760988 * 2 ^ 59
def prefixEnd_760988 : Nat := 4983230072969 + 3 ^ 40 * 760988 * 2
def baseEnd_760988 : Nat := 115778552978895959896381

theorem tailTrace_760988 : CollatzResearch.WordTrace tailWord_760988 prefixEnd_760988 115778552978895959896381 := by
  unfold tailWord_760988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13877756283538958624177809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18503675044718611498903745 13877756283538958624177809)
  ·
    refine ⟨10408317212654218968133357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13877756283538958624177809 10408317212654218968133357)
    ·
      refine ⟨3903118954745332113050009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10408317212654218968133357 3903118954745332113050009)
      ·
        refine ⟨2927339216058999084787507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3903118954745332113050009 2927339216058999084787507)
        ·
          refine ⟨4391008824088498627181261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927339216058999084787507 4391008824088498627181261)
          ·
            refine ⟨1646628309033186985192973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4391008824088498627181261 1646628309033186985192973)
            ·
              refine ⟨617485615887445119447365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646628309033186985192973 617485615887445119447365)
              ·
                refine ⟨115778552978895959896381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617485615887445119447365 115778552978895959896381)
                ·
                  rfl

theorem cell20_760988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_760988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_760988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_760988 prefixEnd_760988 := by exact prefixLift 760988
  have htrace : WordTrace (prefixWord ++ tailWord_760988) baseStart_760988 baseEnd_760988 := by
    simpa [prefixWord, tailWord_760988, baseEnd_760988] using wordTrace_append hprefix tailTrace_760988
  have hstable : (prefixWord ++ tailWord_760988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760988).length < 2 ^ (prefixWord ++ tailWord_760988).sum := by decide
  have hdescent : baseEnd_760988 < baseStart_760988 := by decide
  rcases family_descends (prefixWord ++ tailWord_760988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761009 : List Nat := [1, 2, 2, 5, 1, 2, 7]
def baseStart_761009 : Nat := 118140960795 + 761009 * 2 ^ 59
def prefixEnd_761009 : Nat := 4983230072969 + 3 ^ 40 * 761009 * 2
def baseEnd_761009 : Nat := 38593915989878348887673

theorem tailTrace_761009 : CollatzResearch.WordTrace tailWord_761009 prefixEnd_761009 38593915989878348887673 := by
  unfold tailWord_761009
  simp only [CollatzResearch.WordTrace]
  refine ⟨27756278500001837834870081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18504185666667891889913387 27756278500001837834870081)
  ·
    refine ⟨20817208875001378376152561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27756278500001837834870081 20817208875001378376152561)
    ·
      refine ⟨15612906656251033782114421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20817208875001378376152561 15612906656251033782114421)
      ·
        refine ⟨1463709999023534417073227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15612906656251033782114421 1463709999023534417073227)
        ·
          refine ⟨2195564998535301625609841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463709999023534417073227 2195564998535301625609841)
          ·
            refine ⟨1646673748901476219207381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195564998535301625609841 1646673748901476219207381)
            ·
              refine ⟨38593915989878348887673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1646673748901476219207381 38593915989878348887673)
              ·
                rfl

theorem cell20_761009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_761009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761009 prefixEnd_761009 := by exact prefixLift 761009
  have htrace : WordTrace (prefixWord ++ tailWord_761009) baseStart_761009 baseEnd_761009 := by
    simpa [prefixWord, tailWord_761009, baseEnd_761009] using wordTrace_append hprefix tailTrace_761009
  have hstable : (prefixWord ++ tailWord_761009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761009).length < 2 ^ (prefixWord ++ tailWord_761009).sum := by decide
  have hdescent : baseEnd_761009 < baseStart_761009 := by decide
  rcases family_descends (prefixWord ++ tailWord_761009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761016 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_761016 : Nat := 118140960795 + 761016 * 2 ^ 59
def prefixEnd_761016 : Nat := 4983230072969 + 3 ^ 40 * 761016 * 2
def baseEnd_761016 : Nat := 347348438899644226755695

theorem tailTrace_761016 : CollatzResearch.WordTrace tailWord_761016 prefixEnd_761016 347348438899644226755695 := by
  unfold tailWord_761016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878266905488239015187451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18504355873984318686916601 13878266905488239015187451)
  ·
    refine ⟨20817400358232358522781177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13878266905488239015187451 20817400358232358522781177)
    ·
      refine ⟨15613050268674268892085883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20817400358232358522781177 15613050268674268892085883)
      ·
        refine ⟨23419575403011403338128825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15613050268674268892085883 23419575403011403338128825)
        ·
          refine ⟨17564681552258552503596619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23419575403011403338128825 17564681552258552503596619)
          ·
            refine ⟨26347022328387828755394929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17564681552258552503596619 26347022328387828755394929)
            ·
              refine ⟨19760266746290871566546197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26347022328387828755394929 19760266746290871566546197)
              ·
                refine ⟨926262503732384604681853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19760266746290871566546197 926262503732384604681853)
                ·
                  refine ⟨347348438899644226755695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926262503732384604681853 347348438899644226755695)
                  ·
                    rfl

theorem cell20_761016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_761016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761016 prefixEnd_761016 := by exact prefixLift 761016
  have htrace : WordTrace (prefixWord ++ tailWord_761016) baseStart_761016 baseEnd_761016 := by
    simpa [prefixWord, tailWord_761016, baseEnd_761016] using wordTrace_append hprefix tailTrace_761016
  have hstable : (prefixWord ++ tailWord_761016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761016).length < 2 ^ (prefixWord ++ tailWord_761016).sum := by decide
  have hdescent : baseEnd_761016 < baseStart_761016 := by decide
  rcases family_descends (prefixWord ++ tailWord_761016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761023 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_761023 : Nat := 118140960795 + 761023 * 2 ^ 59
def prefixEnd_761023 : Nat := 4983230072969 + 3 ^ 40 * 761023 * 2
def baseEnd_761023 : Nat := 347351633890383313522333

theorem tailTrace_761023 : CollatzResearch.WordTrace tailWord_761023 prefixEnd_761023 347351633890383313522333 := by
  unfold tailWord_761023
  simp only [CollatzResearch.WordTrace]
  refine ⟨27756789121951118225879723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18504526081300745483919815 27756789121951118225879723)
  ·
    refine ⟨41635183682926677338819585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27756789121951118225879723 41635183682926677338819585)
    ·
      refine ⟨31226387762195008004114689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41635183682926677338819585 31226387762195008004114689)
      ·
        refine ⟨23419790821646256003086017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31226387762195008004114689 23419790821646256003086017)
        ·
          refine ⟨17564843116234692002314513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23419790821646256003086017 17564843116234692002314513)
          ·
            refine ⟨13173632337176019001735885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17564843116234692002314513 13173632337176019001735885)
            ·
              refine ⟨4940112126441007125650957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13173632337176019001735885 4940112126441007125650957)
              ·
                refine ⟨1852542047415377672119109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4940112126441007125650957 1852542047415377672119109)
                ·
                  refine ⟨347351633890383313522333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852542047415377672119109 347351633890383313522333)
                  ·
                    rfl

theorem cell20_761023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_761023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761023 prefixEnd_761023 := by exact prefixLift 761023
  have htrace : WordTrace (prefixWord ++ tailWord_761023) baseStart_761023 baseEnd_761023 := by
    simpa [prefixWord, tailWord_761023, baseEnd_761023] using wordTrace_append hprefix tailTrace_761023
  have hstable : (prefixWord ++ tailWord_761023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761023).length < 2 ^ (prefixWord ++ tailWord_761023).sum := by decide
  have hdescent : baseEnd_761023 < baseStart_761023 := by decide
  rcases family_descends (prefixWord ++ tailWord_761023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761047 : List Nat := [1, 1, 3, 2, 1, 2, 6, 4]
def baseStart_761047 : Nat := 118140960795 + 761047 * 2 ^ 59
def prefixEnd_761047 : Nat := 4983230072969 + 3 ^ 40 * 761047 * 2
def baseEnd_761047 : Nat := 115787529381448632240745

theorem tailTrace_761047 : CollatzResearch.WordTrace tailWord_761047 prefixEnd_761047 115787529381448632240745 := by
  unfold tailWord_761047
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757664473864170324753395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18505109649242780216502263 27757664473864170324753395)
  ·
    refine ⟨41636496710796255487130093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27757664473864170324753395 41636496710796255487130093)
    ·
      refine ⟨15613686266548595807673785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41636496710796255487130093 15613686266548595807673785)
      ·
        refine ⟨11710264699911446855755339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15613686266548595807673785 11710264699911446855755339)
        ·
          refine ⟨17565397049867170283633009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710264699911446855755339 17565397049867170283633009)
          ·
            refine ⟨13174047787400377712724757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17565397049867170283633009 13174047787400377712724757)
            ·
              refine ⟨617533490034392705283973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13174047787400377712724757 617533490034392705283973)
              ·
                refine ⟨115787529381448632240745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617533490034392705283973 115787529381448632240745)
                ·
                  rfl

theorem cell20_761047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_761047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761047 prefixEnd_761047 := by exact prefixLift 761047
  have htrace : WordTrace (prefixWord ++ tailWord_761047) baseStart_761047 baseEnd_761047 := by
    simpa [prefixWord, tailWord_761047, baseEnd_761047] using wordTrace_append hprefix tailTrace_761047
  have hstable : (prefixWord ++ tailWord_761047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761047).length < 2 ^ (prefixWord ++ tailWord_761047).sum := by decide
  have hdescent : baseEnd_761047 < baseStart_761047 := by decide
  rcases family_descends (prefixWord ++ tailWord_761047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761053 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 2]
def baseStart_761053 : Nat := 118140960795 + 761053 * 2 ^ 59
def prefixEnd_761053 : Nat := 4983230072969 + 3 ^ 40 * 761053 * 2
def baseEnd_761053 : Nat := 347365326707836542522211

theorem tailTrace_761053 : CollatzResearch.WordTrace tailWord_761053 prefixEnd_761053 347365326707836542522211 := by
  unfold tailWord_761053
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757883311842433349471813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18505255541228288899647875 27757883311842433349471813)
  ·
    refine ⟨5204603120970456253025965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27757883311842433349471813 5204603120970456253025965)
    ·
      refine ⟨1951726170363921094884737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5204603120970456253025965 1951726170363921094884737)
      ·
        refine ⟨1463794627772940821163553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1951726170363921094884737 1463794627772940821163553)
        ·
          refine ⟨1097845970829705615872665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463794627772940821163553 1097845970829705615872665)
          ·
            refine ⟨823384478122279211904499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097845970829705615872665 823384478122279211904499)
            ·
              refine ⟨1235076717183418817856749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823384478122279211904499 1235076717183418817856749)
              ·
                refine ⟨463153768943782056696281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1235076717183418817856749 463153768943782056696281)
                ·
                  refine ⟨347365326707836542522211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463153768943782056696281 347365326707836542522211)
                  ·
                    rfl

theorem cell20_761053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_761053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761053 prefixEnd_761053 := by exact prefixLift 761053
  have htrace : WordTrace (prefixWord ++ tailWord_761053) baseStart_761053 baseEnd_761053 := by
    simpa [prefixWord, tailWord_761053, baseEnd_761053] using wordTrace_append hprefix tailTrace_761053
  have hstable : (prefixWord ++ tailWord_761053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761053).length < 2 ^ (prefixWord ++ tailWord_761053).sum := by decide
  have hdescent : baseEnd_761053 < baseStart_761053 := by decide
  rcases family_descends (prefixWord ++ tailWord_761053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761057 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 2]
def baseStart_761057 : Nat := 118140960795 + 761057 * 2 ^ 59
def prefixEnd_761057 : Nat := 4983230072969 + 3 ^ 40 * 761057 * 2
def baseEnd_761057 : Nat := 347367152416830306388861

theorem tailTrace_761057 : CollatzResearch.WordTrace tailWord_761057 prefixEnd_761057 347367152416830306388861 := by
  unfold tailWord_761057
  simp only [CollatzResearch.WordTrace]
  refine ⟨27758029203827942032617425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18505352802551961355078283 27758029203827942032617425)
  ·
    refine ⟨20818521902870956524463069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27758029203827942032617425 20818521902870956524463069)
    ·
      refine ⟨7806945713576608696673651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20818521902870956524463069 7806945713576608696673651)
      ·
        refine ⟨11710418570364913045010477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7806945713576608696673651 11710418570364913045010477)
        ·
          refine ⟨4391406963886842391878929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11710418570364913045010477 4391406963886842391878929)
          ·
            refine ⟨3293555222915131793909197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4391406963886842391878929 3293555222915131793909197)
            ·
              refine ⟨1235083208593174422715949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3293555222915131793909197 1235083208593174422715949)
              ·
                refine ⟨463156203222440408518481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1235083208593174422715949 463156203222440408518481)
                ·
                  refine ⟨347367152416830306388861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463156203222440408518481 347367152416830306388861)
                  ·
                    rfl

theorem cell20_761057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_761057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761057 prefixEnd_761057 := by exact prefixLift 761057
  have htrace : WordTrace (prefixWord ++ tailWord_761057) baseStart_761057 baseEnd_761057 := by
    simpa [prefixWord, tailWord_761057, baseEnd_761057] using wordTrace_append hprefix tailTrace_761057
  have hstable : (prefixWord ++ tailWord_761057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761057).length < 2 ^ (prefixWord ++ tailWord_761057).sum := by decide
  have hdescent : baseEnd_761057 < baseStart_761057 := by decide
  rcases family_descends (prefixWord ++ tailWord_761057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761068 : List Nat := [2, 2, 1, 1, 2, 4, 8]
def baseStart_761068 : Nat := 118140960795 + 761068 * 2 ^ 59
def prefixEnd_761068 : Nat := 4983230072969 + 3 ^ 40 * 761068 * 2
def baseEnd_761068 : Nat := 38596908124062573002461

theorem tailTrace_761068 : CollatzResearch.WordTrace tailWord_761068 prefixEnd_761068 38596908124062573002461 := by
  unfold tailWord_761068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13879215203394045455633929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18505620271192060607511905 13879215203394045455633929)
  ·
    refine ⟨10409411402545534091725447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13879215203394045455633929 10409411402545534091725447)
    ·
      refine ⟨15614117103818301137588171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10409411402545534091725447 15614117103818301137588171)
      ·
        refine ⟨23421175655727451706382257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15614117103818301137588171 23421175655727451706382257)
        ·
          refine ⟨17565881741795588779786693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23421175655727451706382257 17565881741795588779786693)
          ·
            refine ⟨3293602826586672896210005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17565881741795588779786693 3293602826586672896210005)
            ·
              refine ⟨38596908124062573002461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3293602826586672896210005 38596908124062573002461)
              ·
                rfl

theorem cell20_761068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_761068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761068 prefixEnd_761068 := by exact prefixLift 761068
  have htrace : WordTrace (prefixWord ++ tailWord_761068) baseStart_761068 baseEnd_761068 := by
    simpa [prefixWord, tailWord_761068, baseEnd_761068] using wordTrace_append hprefix tailTrace_761068
  have hstable : (prefixWord ++ tailWord_761068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761068).length < 2 ^ (prefixWord ++ tailWord_761068).sum := by decide
  have hdescent : baseEnd_761068 < baseStart_761068 := by decide
  rcases family_descends (prefixWord ++ tailWord_761068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761074 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_761074 : Nat := 118140960795 + 761074 * 2 ^ 59
def prefixEnd_761074 : Nat := 4983230072969 + 3 ^ 40 * 761074 * 2
def baseEnd_761074 : Nat := 347374911680053802822125

theorem tailTrace_761074 : CollatzResearch.WordTrace tailWord_761074 prefixEnd_761074 347374911680053802822125 := by
  unfold tailWord_761074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939662311191588483996569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18505766163177569290657517 6939662311191588483996569)
  ·
    refine ⟨5204746733393691362997427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6939662311191588483996569 5204746733393691362997427)
    ·
      refine ⟨7807120100090537044496141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5204746733393691362997427 7807120100090537044496141)
      ·
        refine ⟨2927670037533951391686053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7807120100090537044496141 2927670037533951391686053)
        ·
          refine ⟨548938132037615885941135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2927670037533951391686053 548938132037615885941135)
          ·
            refine ⟨823407198056423828911703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548938132037615885941135 823407198056423828911703)
            ·
              refine ⟨1235110797084635743367555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823407198056423828911703 1235110797084635743367555)
              ·
                refine ⟨1852666195626953615051333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235110797084635743367555 1852666195626953615051333)
                ·
                  refine ⟨347374911680053802822125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852666195626953615051333 347374911680053802822125)
                  ·
                    rfl

theorem cell20_761074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_761074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761074 prefixEnd_761074 := by exact prefixLift 761074
  have htrace : WordTrace (prefixWord ++ tailWord_761074) baseStart_761074 baseEnd_761074 := by
    simpa [prefixWord, tailWord_761074, baseEnd_761074] using wordTrace_append hprefix tailTrace_761074
  have hstable : (prefixWord ++ tailWord_761074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761074).length < 2 ^ (prefixWord ++ tailWord_761074).sum := by decide
  have hdescent : baseEnd_761074 < baseStart_761074 := by decide
  rcases family_descends (prefixWord ++ tailWord_761074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761174 : List Nat := [5, 2, 3, 1, 1, 1, 7]
def baseStart_761174 : Nat := 118140960795 + 761174 * 2 ^ 59
def prefixEnd_761174 : Nat := 4983230072969 + 3 ^ 40 * 761174 * 2
def baseEnd_761174 : Nat := 38602283822766433276487

theorem tailTrace_761174 : CollatzResearch.WordTrace tailWord_761174 prefixEnd_761174 38602283822766433276487 := by
  unfold tailWord_761174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735143534025254438414161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18508197696269380676417717 1735143534025254438414161)
  ·
    refine ⟨1301357650518940828810621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1735143534025254438414161 1301357650518940828810621)
    ·
      refine ⟨488009118944602810803983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1301357650518940828810621 488009118944602810803983)
      ·
        refine ⟨732013678416904216205975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488009118944602810803983 732013678416904216205975)
        ·
          refine ⟨1098020517625356324308963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732013678416904216205975 1098020517625356324308963)
          ·
            refine ⟨1647030776438034486463445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098020517625356324308963 1647030776438034486463445)
            ·
              refine ⟨38602283822766433276487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1647030776438034486463445 38602283822766433276487)
              ·
                rfl

theorem cell20_761174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 7].length) (baseStart_761174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761174 prefixEnd_761174 := by exact prefixLift 761174
  have htrace : WordTrace (prefixWord ++ tailWord_761174) baseStart_761174 baseEnd_761174 := by
    simpa [prefixWord, tailWord_761174, baseEnd_761174] using wordTrace_append hprefix tailTrace_761174
  have hstable : (prefixWord ++ tailWord_761174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761174).length < 2 ^ (prefixWord ++ tailWord_761174).sum := by decide
  have hdescent : baseEnd_761174 < baseStart_761174 := by decide
  rcases family_descends (prefixWord ++ tailWord_761174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761181 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 5]
def baseStart_761181 : Nat := 118140960795 + 761181 * 2 ^ 59
def prefixEnd_761181 : Nat := 4983230072969 + 3 ^ 40 * 761181 * 2
def baseEnd_761181 : Nat := 347423749395636986255021

theorem tailTrace_761181 : CollatzResearch.WordTrace tailWord_761181 prefixEnd_761181 347423749395636986255021 := by
  unfold tailWord_761181
  simp only [CollatzResearch.WordTrace]
  refine ⟨27762551855378711210131397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18508367903585807473420931 27762551855378711210131397)
  ·
    refine ⟨5205478472883508351899637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27762551855378711210131397 5205478472883508351899637)
    ·
      refine ⟨488013606832828907990591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5205478472883508351899637 488013606832828907990591)
      ·
        refine ⟨732020410249243361985887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488013606832828907990591 732020410249243361985887)
        ·
          refine ⟨1098030615373865042978831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732020410249243361985887 1098030615373865042978831)
          ·
            refine ⟨1647045923060797564468247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098030615373865042978831 1647045923060797564468247)
            ·
              refine ⟨2470568884591196346702371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647045923060797564468247 2470568884591196346702371)
              ·
                refine ⟨3705853326886794520053557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470568884591196346702371 3705853326886794520053557)
                ·
                  refine ⟨347423749395636986255021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3705853326886794520053557 347423749395636986255021)
                  ·
                    rfl

theorem cell20_761181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_761181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761181 prefixEnd_761181 := by exact prefixLift 761181
  have htrace : WordTrace (prefixWord ++ tailWord_761181) baseStart_761181 baseEnd_761181 := by
    simpa [prefixWord, tailWord_761181, baseEnd_761181] using wordTrace_append hprefix tailTrace_761181
  have hstable : (prefixWord ++ tailWord_761181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761181).length < 2 ^ (prefixWord ++ tailWord_761181).sum := by decide
  have hdescent : baseEnd_761181 < baseStart_761181 := by decide
  rcases family_descends (prefixWord ++ tailWord_761181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761213 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_761213 : Nat := 118140960795 + 761213 * 2 ^ 59
def prefixEnd_761213 : Nat := 4983230072969 + 3 ^ 40 * 761213 * 2
def baseEnd_761213 : Nat := 347438355067587097188223

theorem tailTrace_761213 : CollatzResearch.WordTrace tailWord_761213 prefixEnd_761213 347438355067587097188223 := by
  unfold tailWord_761213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27763718991262780675296293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18509145994175187116864195 27763718991262780675296293)
  ·
    refine ⟨5205697310861771376618055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27763718991262780675296293 5205697310861771376618055)
    ·
      refine ⟨7808545966292657064927083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5205697310861771376618055 7808545966292657064927083)
      ·
        refine ⟨11712818949438985597390625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7808545966292657064927083 11712818949438985597390625)
        ·
          refine ⟨8784614212079239198042969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11712818949438985597390625 8784614212079239198042969)
          ·
            refine ⟨6588460659059429398532227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8784614212079239198042969 6588460659059429398532227)
            ·
              refine ⟨9882690988589144097798341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588460659059429398532227 9882690988589144097798341)
              ·
                refine ⟨1853004560360464518337189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9882690988589144097798341 1853004560360464518337189)
                ·
                  refine ⟨347438355067587097188223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853004560360464518337189 347438355067587097188223)
                  ·
                    rfl

theorem cell20_761213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_761213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761213 prefixEnd_761213 := by exact prefixLift 761213
  have htrace : WordTrace (prefixWord ++ tailWord_761213) baseStart_761213 baseEnd_761213 := by
    simpa [prefixWord, tailWord_761213, baseEnd_761213] using wordTrace_append hprefix tailTrace_761213
  have hstable : (prefixWord ++ tailWord_761213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761213).length < 2 ^ (prefixWord ++ tailWord_761213).sum := by decide
  have hdescent : baseEnd_761213 < baseStart_761213 := by decide
  rcases family_descends (prefixWord ++ tailWord_761213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761227 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_761227 : Nat := 118140960795 + 761227 * 2 ^ 59
def prefixEnd_761227 : Nat := 4983230072969 + 3 ^ 40 * 761227 * 2
def baseEnd_761227 : Nat := 347444745049065270721499

theorem tailTrace_761227 : CollatzResearch.WordTrace tailWord_761227 prefixEnd_761227 347444745049065270721499 := by
  unfold tailWord_761227
  simp only [CollatzResearch.WordTrace]
  refine ⟨27764229613212061066305935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18509486408808040710870623 27764229613212061066305935)
  ·
    refine ⟨41646344419818091599458903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27764229613212061066305935 41646344419818091599458903)
    ·
      refine ⟨62469516629727137399188355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41646344419818091599458903 62469516629727137399188355)
      ·
        refine ⟨93704274944590706098782533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62469516629727137399188355 93704274944590706098782533)
        ·
          refine ⟨17569551552110757393521725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93704274944590706098782533 17569551552110757393521725)
          ·
            refine ⟨6588581832041534022570647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17569551552110757393521725 6588581832041534022570647)
            ·
              refine ⟨9882872748062301033855971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588581832041534022570647 9882872748062301033855971)
              ·
                refine ⟨14824309122093451550783957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9882872748062301033855971 14824309122093451550783957)
                ·
                  refine ⟨347444745049065270721499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14824309122093451550783957 347444745049065270721499)
                  ·
                    rfl

theorem cell20_761227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_761227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761227 prefixEnd_761227 := by exact prefixLift 761227
  have htrace : WordTrace (prefixWord ++ tailWord_761227) baseStart_761227 baseEnd_761227 := by
    simpa [prefixWord, tailWord_761227, baseEnd_761227] using wordTrace_append hprefix tailTrace_761227
  have hstable : (prefixWord ++ tailWord_761227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761227).length < 2 ^ (prefixWord ++ tailWord_761227).sum := by decide
  have hdescent : baseEnd_761227 < baseStart_761227 := by decide
  rcases family_descends (prefixWord ++ tailWord_761227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761302 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_761302 : Nat := 118140960795 + 761302 * 2 ^ 59
def prefixEnd_761302 : Nat := 4983230072969 + 3 ^ 40 * 761302 * 2
def baseEnd_761302 : Nat := 347478977092698343221193

theorem tailTrace_761302 : CollatzResearch.WordTrace tailWord_761302 prefixEnd_761302 347478977092698343221193 := by
  unfold tailWord_761302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735435317996271804705385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18511310058626899250190773 1735435317996271804705385)
  ·
    refine ⟨1301576488497203853529039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1735435317996271804705385 1301576488497203853529039)
    ·
      refine ⟨1952364732745805780293559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301576488497203853529039 1952364732745805780293559)
      ·
        refine ⟨2928547099118708670440339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952364732745805780293559 2928547099118708670440339)
        ·
          refine ⟨4392820648678063005660509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928547099118708670440339 4392820648678063005660509)
          ·
            refine ⟨1647307743254273627122691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4392820648678063005660509 1647307743254273627122691)
            ·
              refine ⟨2470961614881410440684037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647307743254273627122691 2470961614881410440684037)
              ·
                refine ⟨463305302790264457628257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2470961614881410440684037 463305302790264457628257)
                ·
                  refine ⟨347478977092698343221193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463305302790264457628257 347478977092698343221193)
                  ·
                    rfl

theorem cell20_761302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_761302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761302 prefixEnd_761302 := by exact prefixLift 761302
  have htrace : WordTrace (prefixWord ++ tailWord_761302) baseStart_761302 baseEnd_761302 := by
    simpa [prefixWord, tailWord_761302, baseEnd_761302] using wordTrace_append hprefix tailTrace_761302
  have hstable : (prefixWord ++ tailWord_761302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761302).length < 2 ^ (prefixWord ++ tailWord_761302).sum := by decide
  have hdescent : baseEnd_761302 < baseStart_761302 := by decide
  rcases family_descends (prefixWord ++ tailWord_761302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761303 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_761303 : Nat := 118140960795 + 761303 * 2 ^ 59
def prefixEnd_761303 : Nat := 4983230072969 + 3 ^ 40 * 761303 * 2
def baseEnd_761303 : Nat := 347479433519946784187855

theorem tailTrace_761303 : CollatzResearch.WordTrace tailWord_761303 prefixEnd_761303 347479433519946784187855 := by
  unfold tailWord_761303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27767001560936726046072563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18511334373957817364048375 27767001560936726046072563)
  ·
    refine ⟨41650502341405089069108845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27767001560936726046072563 41650502341405089069108845)
    ·
      refine ⟨15618938378026908400915817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41650502341405089069108845 15618938378026908400915817)
      ·
        refine ⟨11714203783520181300686863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15618938378026908400915817 11714203783520181300686863)
        ·
          refine ⟨17571305675280271951030295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11714203783520181300686863 17571305675280271951030295)
          ·
            refine ⟨26356958512920407926545443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17571305675280271951030295 26356958512920407926545443)
            ·
              refine ⟨39535437769380611889818165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26356958512920407926545443 39535437769380611889818165)
              ·
                refine ⟨3706447290879432364670453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39535437769380611889818165 3706447290879432364670453)
                ·
                  refine ⟨347479433519946784187855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3706447290879432364670453 347479433519946784187855)
                  ·
                    rfl

theorem cell20_761303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_761303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761303 prefixEnd_761303 := by exact prefixLift 761303
  have htrace : WordTrace (prefixWord ++ tailWord_761303) baseStart_761303 baseEnd_761303 := by
    simpa [prefixWord, tailWord_761303, baseEnd_761303] using wordTrace_append hprefix tailTrace_761303
  have hstable : (prefixWord ++ tailWord_761303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761303).length < 2 ^ (prefixWord ++ tailWord_761303).sum := by decide
  have hdescent : baseEnd_761303 < baseStart_761303 := by decide
  rcases family_descends (prefixWord ++ tailWord_761303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761313 : List Nat := [1, 2, 3, 1, 2, 5, 1, 5]
def baseStart_761313 : Nat := 118140960795 + 761313 * 2 ^ 59
def prefixEnd_761313 : Nat := 4983230072969 + 3 ^ 40 * 761313 * 2
def baseEnd_761313 : Nat := 115827999264143731284827

theorem tailTrace_761313 : CollatzResearch.WordTrace tailWord_761313 prefixEnd_761313 115827999264143731284827 := by
  unfold tailWord_761313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27767366290900497753936593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18511577527266998502624395 27767366290900497753936593)
  ·
    refine ⟨20825524718175373315452445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27767366290900497753936593 20825524718175373315452445)
    ·
      refine ⟨7809571769315764993294667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20825524718175373315452445 7809571769315764993294667)
      ·
        refine ⟨11714357653973647489942001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7809571769315764993294667 11714357653973647489942001)
        ·
          refine ⟨8785768240480235617456501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11714357653973647489942001 8785768240480235617456501)
          ·
            refine ⟨823665772545022089136547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8785768240480235617456501 823665772545022089136547)
            ·
              refine ⟨1235498658817533133704821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823665772545022089136547 1235498658817533133704821)
              ·
                refine ⟨115827999264143731284827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1235498658817533133704821 115827999264143731284827)
                ·
                  rfl

theorem cell20_761313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_761313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761313 prefixEnd_761313 := by exact prefixLift 761313
  have htrace : WordTrace (prefixWord ++ tailWord_761313) baseStart_761313 baseEnd_761313 := by
    simpa [prefixWord, tailWord_761313, baseEnd_761313] using wordTrace_append hprefix tailTrace_761313
  have hstable : (prefixWord ++ tailWord_761313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761313).length < 2 ^ (prefixWord ++ tailWord_761313).sum := by decide
  have hdescent : baseEnd_761313 < baseStart_761313 := by decide
  rcases family_descends (prefixWord ++ tailWord_761313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761320 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_761320 : Nat := 118140960795 + 761320 * 2 ^ 59
def prefixEnd_761320 : Nat := 4983230072969 + 3 ^ 40 * 761320 * 2
def baseEnd_761320 : Nat := 347487192783170280621119

theorem tailTrace_761320 : CollatzResearch.WordTrace tailWord_761320 prefixEnd_761320 347487192783170280621119 := by
  unfold tailWord_761320
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883810800937568974720707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18511747734583425299627609 13883810800937568974720707)
  ·
    refine ⟨20825716201406353462081061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13883810800937568974720707 20825716201406353462081061)
    ·
      refine ⟨3904821787763691274140199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20825716201406353462081061 3904821787763691274140199)
      ·
        refine ⟨5857232681645536911210299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904821787763691274140199 5857232681645536911210299)
        ·
          refine ⟨8785849022468305366815449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857232681645536911210299 8785849022468305366815449)
          ·
            refine ⟨6589386766851229025111587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8785849022468305366815449 6589386766851229025111587)
            ·
              refine ⟨9884080150276843537667381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589386766851229025111587 9884080150276843537667381)
              ·
                refine ⟨926632514088454081656317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9884080150276843537667381 926632514088454081656317)
                ·
                  refine ⟨347487192783170280621119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926632514088454081656317 347487192783170280621119)
                  ·
                    rfl

theorem cell20_761320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_761320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761320 prefixEnd_761320 := by exact prefixLift 761320
  have htrace : WordTrace (prefixWord ++ tailWord_761320) baseStart_761320 baseEnd_761320 := by
    simpa [prefixWord, tailWord_761320, baseEnd_761320] using wordTrace_append hprefix tailTrace_761320
  have hstable : (prefixWord ++ tailWord_761320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761320).length < 2 ^ (prefixWord ++ tailWord_761320).sum := by decide
  have hdescent : baseEnd_761320 < baseStart_761320 := by decide
  rcases family_descends (prefixWord ++ tailWord_761320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761330 : List Nat := [3, 2, 1, 4, 1, 2, 3, 4]
def baseStart_761330 : Nat := 118140960795 + 761330 * 2 ^ 59
def prefixEnd_761330 : Nat := 4983230072969 + 3 ^ 40 * 761330 * 2
def baseEnd_761330 : Nat := 115830585685218230095915

theorem tailTrace_761330 : CollatzResearch.WordTrace tailWord_761330 prefixEnd_761330 115830585685218230095915 := by
  unfold tailWord_761330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941996582959727414326361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18511990887892606438203629 6941996582959727414326361)
  ·
    refine ⟨5206497437219795560744771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6941996582959727414326361 5206497437219795560744771)
    ·
      refine ⟨7809746155829693341117157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206497437219795560744771 7809746155829693341117157)
      ·
        refine ⟨1464327404218067501459467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7809746155829693341117157 1464327404218067501459467)
        ·
          refine ⟨2196491106327101252189201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464327404218067501459467 2196491106327101252189201)
          ·
            refine ⟨1647368329745325939141901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196491106327101252189201 1647368329745325939141901)
            ·
              refine ⟨617763123654497227178213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1647368329745325939141901 617763123654497227178213)
              ·
                refine ⟨115830585685218230095915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 617763123654497227178213 115830585685218230095915)
                ·
                  rfl

theorem cell20_761330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_761330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761330 prefixEnd_761330 := by exact prefixLift 761330
  have htrace : WordTrace (prefixWord ++ tailWord_761330) baseStart_761330 baseEnd_761330 := by
    simpa [prefixWord, tailWord_761330, baseEnd_761330] using wordTrace_append hprefix tailTrace_761330
  have hstable : (prefixWord ++ tailWord_761330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761330).length < 2 ^ (prefixWord ++ tailWord_761330).sum := by decide
  have hdescent : baseEnd_761330 < baseStart_761330 := by decide
  rcases family_descends (prefixWord ++ tailWord_761330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761365 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_761365 : Nat := 118140960795 + 761365 * 2 ^ 59
def prefixEnd_761365 : Nat := 4983230072969 + 3 ^ 40 * 761365 * 2
def baseEnd_761365 : Nat := 347507732009350124120935

theorem tailTrace_761365 : CollatzResearch.WordTrace tailWord_761365 prefixEnd_761365 347507732009350124120935 := by
  unfold tailWord_761365
  simp only [CollatzResearch.WordTrace]
  refine ⟨27769262886712110634829549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18512841924474740423219699 27769262886712110634829549)
  ·
    refine ⟨10413473582517041488061081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27769262886712110634829549 10413473582517041488061081)
    ·
      refine ⟨7810105186887781116045811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10413473582517041488061081 7810105186887781116045811)
      ·
        refine ⟨11715157780331671674068717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810105186887781116045811 11715157780331671674068717)
        ·
          refine ⟨4393184167624376877775769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11715157780331671674068717 4393184167624376877775769)
          ·
            refine ⟨3294888125718282658331827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4393184167624376877775769 3294888125718282658331827)
            ·
              refine ⟨4942332188577423987497741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294888125718282658331827 4942332188577423987497741)
              ·
                refine ⟨1853374570716533995311653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4942332188577423987497741 1853374570716533995311653)
                ·
                  refine ⟨347507732009350124120935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853374570716533995311653 347507732009350124120935)
                  ·
                    rfl

theorem cell20_761365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_761365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761365 prefixEnd_761365 := by exact prefixLift 761365
  have htrace : WordTrace (prefixWord ++ tailWord_761365) baseStart_761365 baseEnd_761365 := by
    simpa [prefixWord, tailWord_761365, baseEnd_761365] using wordTrace_append hprefix tailTrace_761365
  have hstable : (prefixWord ++ tailWord_761365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761365).length < 2 ^ (prefixWord ++ tailWord_761365).sum := by decide
  have hdescent : baseEnd_761365 < baseStart_761365 := by decide
  rcases family_descends (prefixWord ++ tailWord_761365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761372 : List Nat := [2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_761372 : Nat := 118140960795 + 761372 * 2 ^ 59
def prefixEnd_761372 : Nat := 4983230072969 + 3 ^ 40 * 761372 * 2
def baseEnd_761372 : Nat := 115836975666696403629191

theorem tailTrace_761372 : CollatzResearch.WordTrace tailWord_761372 prefixEnd_761372 115836975666696403629191 := by
  unfold tailWord_761372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13884759098843375415167185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18513012131791167220222913 13884759098843375415167185)
  ·
    refine ⟨10413569324132531561375389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13884759098843375415167185 10413569324132531561375389)
    ·
      refine ⟨3905088496549699335515771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10413569324132531561375389 3905088496549699335515771)
      ·
        refine ⟨5857632744824549003273657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905088496549699335515771 5857632744824549003273657)
        ·
          refine ⟨4393224558618411752455243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857632744824549003273657 4393224558618411752455243)
          ·
            refine ⟨6589836837927617628682865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393224558618411752455243 6589836837927617628682865)
            ·
              refine ⟨4942377628445713221512149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6589836837927617628682865 4942377628445713221512149)
              ·
                refine ⟨115836975666696403629191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4942377628445713221512149 115836975666696403629191)
                ·
                  rfl

theorem cell20_761372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_761372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761372 prefixEnd_761372 := by exact prefixLift 761372
  have htrace : WordTrace (prefixWord ++ tailWord_761372) baseStart_761372 baseEnd_761372 := by
    simpa [prefixWord, tailWord_761372, baseEnd_761372] using wordTrace_append hprefix tailTrace_761372
  have hstable : (prefixWord ++ tailWord_761372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761372).length < 2 ^ (prefixWord ++ tailWord_761372).sum := by decide
  have hdescent : baseEnd_761372 < baseStart_761372 := by decide
  rcases family_descends (prefixWord ++ tailWord_761372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761399 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 2]
def baseStart_761399 : Nat := 118140960795 + 761399 * 2 ^ 59
def prefixEnd_761399 : Nat := 4983230072969 + 3 ^ 40 * 761399 * 2
def baseEnd_761399 : Nat := 347523250535797116987463

theorem tailTrace_761399 : CollatzResearch.WordTrace tailWord_761399 prefixEnd_761399 347523250535797116987463 := by
  unfold tailWord_761399
  simp only [CollatzResearch.WordTrace]
  refine ⟨27770502968588934441567251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18513668645725956294378167 27770502968588934441567251)
  ·
    refine ⟨41655754452883401662350877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27770502968588934441567251 41655754452883401662350877)
    ·
      refine ⟨15620907919831275623381579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41655754452883401662350877 15620907919831275623381579)
      ·
        refine ⟨23431361879746913435072369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15620907919831275623381579 23431361879746913435072369)
        ·
          refine ⟨17573521409810185076304277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23431361879746913435072369 17573521409810185076304277)
          ·
            refine ⟨823758816084852425451763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17573521409810185076304277 823758816084852425451763)
            ·
              refine ⟨1235638224127278638177645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823758816084852425451763 1235638224127278638177645)
              ·
                refine ⟨463364334047729489316617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1235638224127278638177645 463364334047729489316617)
                ·
                  refine ⟨347523250535797116987463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463364334047729489316617 347523250535797116987463)
                  ·
                    rfl

theorem cell20_761399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 2].length) (baseStart_761399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761399 prefixEnd_761399 := by exact prefixLift 761399
  have htrace : WordTrace (prefixWord ++ tailWord_761399) baseStart_761399 baseEnd_761399 := by
    simpa [prefixWord, tailWord_761399, baseEnd_761399] using wordTrace_append hprefix tailTrace_761399
  have hstable : (prefixWord ++ tailWord_761399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761399).length < 2 ^ (prefixWord ++ tailWord_761399).sum := by decide
  have hdescent : baseEnd_761399 < baseStart_761399 := by decide
  rcases family_descends (prefixWord ++ tailWord_761399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761420 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_761420 : Nat := 118140960795 + 761420 * 2 ^ 59
def prefixEnd_761420 : Nat := 4983230072969 + 3 ^ 40 * 761420 * 2
def baseEnd_761420 : Nat := 347532835508014377287377

theorem tailTrace_761420 : CollatzResearch.WordTrace tailWord_761420 prefixEnd_761420 347532835508014377287377 := by
  unfold tailWord_761420
  simp only [CollatzResearch.WordTrace]
  refine ⟨13885634450756427514040857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18514179267675236685387809 13885634450756427514040857)
  ·
    refine ⟨10414225838067320635530643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13885634450756427514040857 10414225838067320635530643)
    ·
      refine ⟨15621338757100980953295965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10414225838067320635530643 15621338757100980953295965)
      ·
        refine ⟨5858002033912867857485987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15621338757100980953295965 5858002033912867857485987)
        ·
          refine ⟨8787003050869301786228981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5858002033912867857485987 8787003050869301786228981)
          ·
            refine ⟨823781536018997042458967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8787003050869301786228981 823781536018997042458967)
            ·
              refine ⟨1235672304028495563688451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823781536018997042458967 1235672304028495563688451)
              ·
                refine ⟨1853508456042743345532677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235672304028495563688451 1853508456042743345532677)
                ·
                  refine ⟨347532835508014377287377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853508456042743345532677 347532835508014377287377)
                  ·
                    rfl

theorem cell20_761420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_761420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761420 prefixEnd_761420 := by exact prefixLift 761420
  have htrace : WordTrace (prefixWord ++ tailWord_761420) baseStart_761420 baseEnd_761420 := by
    simpa [prefixWord, tailWord_761420, baseEnd_761420] using wordTrace_append hprefix tailTrace_761420
  have hstable : (prefixWord ++ tailWord_761420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761420).length < 2 ^ (prefixWord ++ tailWord_761420).sum := by decide
  have hdescent : baseEnd_761420 < baseStart_761420 := by decide
  rcases family_descends (prefixWord ++ tailWord_761420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761472 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_761472 : Nat := 118140960795 + 761472 * 2 ^ 59
def prefixEnd_761472 : Nat := 4983230072969 + 3 ^ 40 * 761472 * 2
def baseEnd_761472 : Nat := 347556569724933307553831

theorem tailTrace_761472 : CollatzResearch.WordTrace tailWord_761472 prefixEnd_761472 347556569724933307553831 := by
  unfold tailWord_761472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886582748662233954487335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18515443664882978605983113 13886582748662233954487335)
  ·
    refine ⟨20829874122993350931731003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13886582748662233954487335 20829874122993350931731003)
    ·
      refine ⟨31244811184490026397596505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20829874122993350931731003 31244811184490026397596505)
      ·
        refine ⟨23433608388367519798197379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31244811184490026397596505 23433608388367519798197379)
        ·
          refine ⟨35150412582551279697296069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23433608388367519798197379 35150412582551279697296069)
          ·
            refine ⟨6590702359228364943243013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35150412582551279697296069 6590702359228364943243013)
            ·
              refine ⟨1235756692355318426858065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6590702359228364943243013 1235756692355318426858065)
              ·
                refine ⟨926817519266488820143549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235756692355318426858065 926817519266488820143549)
                ·
                  refine ⟨347556569724933307553831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926817519266488820143549 347556569724933307553831)
                  ·
                    rfl

theorem cell20_761472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_761472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761472 prefixEnd_761472 := by exact prefixLift 761472
  have htrace : WordTrace (prefixWord ++ tailWord_761472) baseStart_761472 baseEnd_761472 := by
    simpa [prefixWord, tailWord_761472, baseEnd_761472] using wordTrace_append hprefix tailTrace_761472
  have hstable : (prefixWord ++ tailWord_761472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761472).length < 2 ^ (prefixWord ++ tailWord_761472).sum := by decide
  have hdescent : baseEnd_761472 < baseStart_761472 := by decide
  rcases family_descends (prefixWord ++ tailWord_761472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761517 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_761517 : Nat := 118140960795 + 761517 * 2 ^ 59
def prefixEnd_761517 : Nat := 4983230072969 + 3 ^ 40 * 761517 * 2
def baseEnd_761517 : Nat := 347577108951113151053647

theorem tailTrace_761517 : CollatzResearch.WordTrace tailWord_761517 prefixEnd_761517 347577108951113151053647 := by
  unfold tailWord_761517
  simp only [CollatzResearch.WordTrace]
  refine ⟨27774806782161440594362805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18516537854774293729575203 27774806782161440594362805)
  ·
    refine ⟨2603888135827635055721513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27774806782161440594362805 2603888135827635055721513)
    ·
      refine ⟨1952916101870726291791135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2603888135827635055721513 1952916101870726291791135)
      ·
        refine ⟨2929374152806089437686703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952916101870726291791135 2929374152806089437686703)
        ·
          refine ⟨4394061229209134156530055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929374152806089437686703 4394061229209134156530055)
          ·
            refine ⟨6591091843813701234795083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394061229209134156530055 6591091843813701234795083)
            ·
              refine ⟨9886637765720551852192625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591091843813701234795083 9886637765720551852192625)
              ·
                refine ⟨7414978324290413889144469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9886637765720551852192625 7414978324290413889144469)
                ·
                  refine ⟨347577108951113151053647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7414978324290413889144469 347577108951113151053647)
                  ·
                    rfl

theorem cell20_761517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_761517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761517 prefixEnd_761517 := by exact prefixLift 761517
  have htrace : WordTrace (prefixWord ++ tailWord_761517) baseStart_761517 baseEnd_761517 := by
    simpa [prefixWord, tailWord_761517, baseEnd_761517] using wordTrace_append hprefix tailTrace_761517
  have hstable : (prefixWord ++ tailWord_761517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761517).length < 2 ^ (prefixWord ++ tailWord_761517).sum := by decide
  have hdescent : baseEnd_761517 < baseStart_761517 := by decide
  rcases family_descends (prefixWord ++ tailWord_761517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761527 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 3]
def baseStart_761527 : Nat := 118140960795 + 761527 * 2 ^ 59
def prefixEnd_761527 : Nat := 4983230072969 + 3 ^ 40 * 761527 * 2
def baseEnd_761527 : Nat := 347581673223597560720273

theorem tailTrace_761527 : CollatzResearch.WordTrace tailWord_761527 prefixEnd_761527 347581673223597560720273 := by
  unfold tailWord_761527
  simp only [CollatzResearch.WordTrace]
  refine ⟨27775171512125212302226835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18516781008083474868151223 27775171512125212302226835)
  ·
    refine ⟨41662757268187818453340253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27775171512125212302226835 41662757268187818453340253)
    ·
      refine ⟨15623533975570431920002595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41662757268187818453340253 15623533975570431920002595)
      ·
        refine ⟨23435300963355647880003893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15623533975570431920002595 23435300963355647880003893)
        ·
          refine ⟨2197059465314591988750365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23435300963355647880003893 2197059465314591988750365)
          ·
            refine ⟨823897299492971995781387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2197059465314591988750365 823897299492971995781387)
            ·
              refine ⟨1235845949239457993672081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823897299492971995781387 1235845949239457993672081)
              ·
                refine ⟨926884461929593495254061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235845949239457993672081 926884461929593495254061)
                ·
                  refine ⟨347581673223597560720273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926884461929593495254061 347581673223597560720273)
                  ·
                    rfl

theorem cell20_761527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_761527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761527 prefixEnd_761527 := by exact prefixLift 761527
  have htrace : WordTrace (prefixWord ++ tailWord_761527) baseStart_761527 baseEnd_761527 := by
    simpa [prefixWord, tailWord_761527, baseEnd_761527] using wordTrace_append hprefix tailTrace_761527
  have hstable : (prefixWord ++ tailWord_761527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761527).length < 2 ^ (prefixWord ++ tailWord_761527).sum := by decide
  have hdescent : baseEnd_761527 < baseStart_761527 := by decide
  rcases family_descends (prefixWord ++ tailWord_761527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761534 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_761534 : Nat := 118140960795 + 761534 * 2 ^ 59
def prefixEnd_761534 : Nat := 4983230072969 + 3 ^ 40 * 761534 * 2
def baseEnd_761534 : Nat := 347584868214336647486911

theorem tailTrace_761534 : CollatzResearch.WordTrace tailWord_761534 prefixEnd_761534 347584868214336647486911 := by
  unfold tailWord_761534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471928352887481562216457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18516951215399901665154437 3471928352887481562216457)
  ·
    refine ⟨2603946264665611171662343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3471928352887481562216457 2603946264665611171662343)
    ·
      refine ⟨3905919396998416757493515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603946264665611171662343 3905919396998416757493515)
      ·
        refine ⟨5858879095497625136240273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905919396998416757493515 5858879095497625136240273)
        ·
          refine ⟨4394159321623218852180205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5858879095497625136240273 4394159321623218852180205)
          ·
            refine ⟨1647809745608707069567577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4394159321623218852180205 1647809745608707069567577)
            ·
              refine ⟨1235857309206530302175683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647809745608707069567577 1235857309206530302175683)
              ·
                refine ⟨1853785963809795453263525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235857309206530302175683 1853785963809795453263525)
                ·
                  refine ⟨347584868214336647486911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853785963809795453263525 347584868214336647486911)
                  ·
                    rfl

theorem cell20_761534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_761534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761534 prefixEnd_761534 := by exact prefixLift 761534
  have htrace : WordTrace (prefixWord ++ tailWord_761534) baseStart_761534 baseEnd_761534 := by
    simpa [prefixWord, tailWord_761534, baseEnd_761534] using wordTrace_append hprefix tailTrace_761534
  have hstable : (prefixWord ++ tailWord_761534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761534).length < 2 ^ (prefixWord ++ tailWord_761534).sum := by decide
  have hdescent : baseEnd_761534 < baseStart_761534 := by decide
  rcases family_descends (prefixWord ++ tailWord_761534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761562 : List Nat := [3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_761562 : Nat := 118140960795 + 761562 * 2 ^ 59
def prefixEnd_761562 : Nat := 4983230072969 + 3 ^ 40 * 761562 * 2
def baseEnd_761562 : Nat := 115865882725764331517821

theorem tailTrace_761562 : CollatzResearch.WordTrace tailWord_761562 prefixEnd_761562 115865882725764331517821 := by
  unfold tailWord_761562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944112016749603319937735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18517632044665608853167293 6944112016749603319937735)
  ·
    refine ⟨10416168025124404979906603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944112016749603319937735 10416168025124404979906603)
    ·
      refine ⟨15624252037686607469859905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10416168025124404979906603 15624252037686607469859905)
      ·
        refine ⟨11718189028264955602394929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15624252037686607469859905 11718189028264955602394929)
        ·
          refine ⟨8788641771198716701796197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11718189028264955602394929 8788641771198716701796197)
          ·
            refine ⟨1647870332099759381586787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8788641771198716701796197 1647870332099759381586787)
            ·
              refine ⟨2471805498149639072380181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647870332099759381586787 2471805498149639072380181)
              ·
                refine ⟨115865882725764331517821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2471805498149639072380181 115865882725764331517821)
                ·
                  rfl

theorem cell20_761562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_761562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761562 prefixEnd_761562 := by exact prefixLift 761562
  have htrace : WordTrace (prefixWord ++ tailWord_761562) baseStart_761562 baseEnd_761562 := by
    simpa [prefixWord, tailWord_761562, baseEnd_761562] using wordTrace_append hprefix tailTrace_761562
  have hstable : (prefixWord ++ tailWord_761562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761562).length < 2 ^ (prefixWord ++ tailWord_761562).sum := by decide
  have hdescent : baseEnd_761562 < baseStart_761562 := by decide
  rcases family_descends (prefixWord ++ tailWord_761562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761586 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_761586 : Nat := 118140960795 + 761586 * 2 ^ 59
def prefixEnd_761586 : Nat := 4983230072969 + 3 ^ 40 * 761586 * 2
def baseEnd_761586 : Nat := 347608602431255577753365

theorem tailTrace_761586 : CollatzResearch.WordTrace tailWord_761586 prefixEnd_761586 347608602431255577753365 := by
  unfold tailWord_761586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944330854727866344656153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18518215612607643585749741 6944330854727866344656153)
  ·
    refine ⟨5208248141045899758492115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6944330854727866344656153 5208248141045899758492115)
    ·
      refine ⟨7812372211568849637738173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208248141045899758492115 7812372211568849637738173)
      ·
        refine ⟨2929639579338318614151815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7812372211568849637738173 2929639579338318614151815)
        ·
          refine ⟨4394459369007477921227723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929639579338318614151815 4394459369007477921227723)
          ·
            refine ⟨6591689053511216881841585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394459369007477921227723 6591689053511216881841585)
            ·
              refine ⟨4943766790133412661381189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591689053511216881841585 4943766790133412661381189)
              ·
                refine ⟨926956273150014874008973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4943766790133412661381189 926956273150014874008973)
                ·
                  refine ⟨347608602431255577753365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926956273150014874008973 347608602431255577753365)
                  ·
                    rfl

theorem cell20_761586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_761586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761586 prefixEnd_761586 := by exact prefixLift 761586
  have htrace : WordTrace (prefixWord ++ tailWord_761586) baseStart_761586 baseEnd_761586 := by
    simpa [prefixWord, tailWord_761586, baseEnd_761586] using wordTrace_append hprefix tailTrace_761586
  have hstable : (prefixWord ++ tailWord_761586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761586).length < 2 ^ (prefixWord ++ tailWord_761586).sum := by decide
  have hdescent : baseEnd_761586 < baseStart_761586 := by decide
  rcases family_descends (prefixWord ++ tailWord_761586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761690 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_761690 : Nat := 118140960795 + 761690 * 2 ^ 59
def prefixEnd_761690 : Nat := 4983230072969 + 3 ^ 40 * 761690 * 2
def baseEnd_761690 : Nat := 347656070865093438286273

theorem tailTrace_761690 : CollatzResearch.WordTrace tailWord_761690 prefixEnd_761690 347656070865093438286273 := by
  unfold tailWord_761690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945279152633672785102631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18520744407023127426940349 6945279152633672785102631)
  ·
    refine ⟨10417918728950509177653947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945279152633672785102631 10417918728950509177653947)
    ·
      refine ⟨15626878093425763766480921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417918728950509177653947 15626878093425763766480921)
      ·
        refine ⟨11720158570069322824860691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15626878093425763766480921 11720158570069322824860691)
        ·
          refine ⟨17580237855103984237291037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11720158570069322824860691 17580237855103984237291037)
          ·
            refine ⟨6592589195663994088984139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17580237855103984237291037 6592589195663994088984139)
            ·
              refine ⟨9888883793495991133476209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6592589195663994088984139 9888883793495991133476209)
              ·
                refine ⟨7416662845121993350107157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9888883793495991133476209 7416662845121993350107157)
                ·
                  refine ⟨347656070865093438286273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7416662845121993350107157 347656070865093438286273)
                  ·
                    rfl

theorem cell20_761690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_761690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761690 prefixEnd_761690 := by exact prefixLift 761690
  have htrace : WordTrace (prefixWord ++ tailWord_761690) baseStart_761690 baseEnd_761690 := by
    simpa [prefixWord, tailWord_761690, baseEnd_761690] using wordTrace_append hprefix tailTrace_761690
  have hstable : (prefixWord ++ tailWord_761690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761690).length < 2 ^ (prefixWord ++ tailWord_761690).sum := by decide
  have hdescent : baseEnd_761690 < baseStart_761690 := by decide
  rcases family_descends (prefixWord ++ tailWord_761690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761697 : List Nat := [1, 2, 3, 1, 1, 1, 11]
def baseStart_761697 : Nat := 118140960795 + 761697 * 2 ^ 59
def prefixEnd_761697 : Nat := 4983230072969 + 3 ^ 40 * 761697 * 2
def baseEnd_761697 : Nat := 38628807317314725005879

theorem tailTrace_761697 : CollatzResearch.WordTrace tailWord_761697 prefixEnd_761697 38628807317314725005879 := by
  unfold tailWord_761697
  simp only [CollatzResearch.WordTrace]
  refine ⟨27781371921509331335915345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18520914614339554223943563 27781371921509331335915345)
  ·
    refine ⟨20836028941131998501936509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27781371921509331335915345 20836028941131998501936509)
    ·
      refine ⟨7813510852924499438226191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20836028941131998501936509 7813510852924499438226191)
      ·
        refine ⟨11720266279386749157339287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813510852924499438226191 11720266279386749157339287)
        ·
          refine ⟨17580399419080123736008931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11720266279386749157339287 17580399419080123736008931)
          ·
            refine ⟨26370599128620185604013397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17580399419080123736008931 26370599128620185604013397)
            ·
              refine ⟨38628807317314725005879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26370599128620185604013397 38628807317314725005879)
              ·
                rfl

theorem cell20_761697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_761697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761697 prefixEnd_761697 := by exact prefixLift 761697
  have htrace : WordTrace (prefixWord ++ tailWord_761697) baseStart_761697 baseEnd_761697 := by
    simpa [prefixWord, tailWord_761697, baseEnd_761697] using wordTrace_append hprefix tailTrace_761697
  have hstable : (prefixWord ++ tailWord_761697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761697).length < 2 ^ (prefixWord ++ tailWord_761697).sum := by decide
  have hdescent : baseEnd_761697 < baseStart_761697 := by decide
  rcases family_descends (prefixWord ++ tailWord_761697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761700 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_761700 : Nat := 118140960795 + 761700 * 2 ^ 59
def prefixEnd_761700 : Nat := 4983230072969 + 3 ^ 40 * 761700 * 2
def baseEnd_761700 : Nat := 347660635137577847952899

theorem tailTrace_761700 : CollatzResearch.WordTrace tailWord_761700 prefixEnd_761700 347660635137577847952899 := by
  unfold tailWord_761700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13890740670249231424137277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18520987560332308565516369 13890740670249231424137277)
  ·
    refine ⟨5209027751343461784051479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13890740670249231424137277 5209027751343461784051479)
    ·
      refine ⟨7813541627015192676077219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5209027751343461784051479 7813541627015192676077219)
      ·
        refine ⟨11720312440522789014115829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813541627015192676077219 11720312440522789014115829)
        ·
          refine ⟨1098779291299011470073359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11720312440522789014115829 1098779291299011470073359)
          ·
            refine ⟨1648168936948517205110039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098779291299011470073359 1648168936948517205110039)
            ·
              refine ⟨2472253405422775807665059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648168936948517205110039 2472253405422775807665059)
              ·
                refine ⟨3708380108134163711497589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472253405422775807665059 3708380108134163711497589)
                ·
                  refine ⟨347660635137577847952899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3708380108134163711497589 347660635137577847952899)
                  ·
                    rfl

theorem cell20_761700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_761700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761700 prefixEnd_761700 := by exact prefixLift 761700
  have htrace : WordTrace (prefixWord ++ tailWord_761700) baseStart_761700 baseEnd_761700 := by
    simpa [prefixWord, tailWord_761700, baseEnd_761700] using wordTrace_append hprefix tailTrace_761700
  have hstable : (prefixWord ++ tailWord_761700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761700).length < 2 ^ (prefixWord ++ tailWord_761700).sum := by decide
  have hdescent : baseEnd_761700 < baseStart_761700 := by decide
  rcases family_descends (prefixWord ++ tailWord_761700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761717 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 3]
def baseStart_761717 : Nat := 118140960795 + 761717 * 2 ^ 59
def prefixEnd_761717 : Nat := 4983230072969 + 3 ^ 40 * 761717 * 2
def baseEnd_761717 : Nat := 347668394400801344386163

theorem tailTrace_761717 : CollatzResearch.WordTrace tailWord_761717 prefixEnd_761717 347668394400801344386163 := by
  unfold tailWord_761717
  simp only [CollatzResearch.WordTrace]
  refine ⟨27782101381436874751643405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18521400920957916501095603 27782101381436874751643405)
  ·
    refine ⟨10418288018038828031866277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27782101381436874751643405 10418288018038828031866277)
    ·
      refine ⟨1953429003382280255974927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10418288018038828031866277 1953429003382280255974927)
      ·
        refine ⟨2930143505073420383962391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953429003382280255974927 2930143505073420383962391)
        ·
          refine ⟨4395215257610130575943587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930143505073420383962391 4395215257610130575943587)
          ·
            refine ⟨6592822886415195863915381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395215257610130575943587 6592822886415195863915381)
            ·
              refine ⟨618077145601424612242067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6592822886415195863915381 618077145601424612242067)
              ·
                refine ⟨927115718402136918363101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618077145601424612242067 927115718402136918363101)
                ·
                  refine ⟨347668394400801344386163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927115718402136918363101 347668394400801344386163)
                  ·
                    rfl

theorem cell20_761717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_761717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761717 prefixEnd_761717 := by exact prefixLift 761717
  have htrace : WordTrace (prefixWord ++ tailWord_761717) baseStart_761717 baseEnd_761717 := by
    simpa [prefixWord, tailWord_761717, baseEnd_761717] using wordTrace_append hprefix tailTrace_761717
  have hstable : (prefixWord ++ tailWord_761717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761717).length < 2 ^ (prefixWord ++ tailWord_761717).sum := by decide
  have hdescent : baseEnd_761717 < baseStart_761717 := by decide
  rcases family_descends (prefixWord ++ tailWord_761717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761728 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_761728 : Nat := 118140960795 + 761728 * 2 ^ 59
def prefixEnd_761728 : Nat := 4983230072969 + 3 ^ 40 * 761728 * 2
def baseEnd_761728 : Nat := 347673415100534195019451

theorem tailTrace_761728 : CollatzResearch.WordTrace tailWord_761728 prefixEnd_761728 347673415100534195019451 := by
  unfold tailWord_761728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891251292198511815146919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18521668389598015753529225 13891251292198511815146919)
  ·
    refine ⟨20836876938297767722720379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13891251292198511815146919 20836876938297767722720379)
    ·
      refine ⟨31255315407446651584080569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20836876938297767722720379 31255315407446651584080569)
      ·
        refine ⟨23441486555584988688060427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31255315407446651584080569 23441486555584988688060427)
        ·
          refine ⟨35162229833377483032090641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23441486555584988688060427 35162229833377483032090641)
          ·
            refine ⟨26371672375033112274067981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35162229833377483032090641 26371672375033112274067981)
            ·
              refine ⟨9889377140637417102775493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26371672375033112274067981 9889377140637417102775493)
              ·
                refine ⟨1854258213869515706770405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9889377140637417102775493 1854258213869515706770405)
                ·
                  refine ⟨347673415100534195019451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854258213869515706770405 347673415100534195019451)
                  ·
                    rfl

theorem cell20_761728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_761728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761728 prefixEnd_761728 := by exact prefixLift 761728
  have htrace : WordTrace (prefixWord ++ tailWord_761728) baseStart_761728 baseEnd_761728 := by
    simpa [prefixWord, tailWord_761728, baseEnd_761728] using wordTrace_append hprefix tailTrace_761728
  have hstable : (prefixWord ++ tailWord_761728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761728).length < 2 ^ (prefixWord ++ tailWord_761728).sum := by decide
  have hdescent : baseEnd_761728 < baseStart_761728 := by decide
  rcases family_descends (prefixWord ++ tailWord_761728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761731 : List Nat := [1, 1, 1, 3, 4, 4, 2, 4]
def baseStart_761731 : Nat := 118140960795 + 761731 * 2 ^ 59
def prefixEnd_761731 : Nat := 4983230072969 + 3 ^ 40 * 761731 * 2
def baseEnd_761731 : Nat := 115891594794093172639813

theorem tailTrace_761731 : CollatzResearch.WordTrace tailWord_761731 prefixEnd_761731 115891594794093172639813 := by
  unfold tailWord_761731
  simp only [CollatzResearch.WordTrace]
  refine ⟨27782612003386155142653047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18521741335590770095102031 27782612003386155142653047)
  ·
    refine ⟨41673918005079232713979571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27782612003386155142653047 41673918005079232713979571)
    ·
      refine ⟨62510877007618849070969357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41673918005079232713979571 62510877007618849070969357)
      ·
        refine ⟨23441578877857068401613509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62510877007618849070969357 23441578877857068401613509)
        ·
          refine ⟨4395296039598200325302533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23441578877857068401613509 4395296039598200325302533)
          ·
            refine ⟨824118007424662560994225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4395296039598200325302533 824118007424662560994225)
            ·
              refine ⟨618088505568496920745669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824118007424662560994225 618088505568496920745669)
              ·
                refine ⟨115891594794093172639813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618088505568496920745669 115891594794093172639813)
                ·
                  rfl

theorem cell20_761731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_761731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761731 prefixEnd_761731 := by exact prefixLift 761731
  have htrace : WordTrace (prefixWord ++ tailWord_761731) baseStart_761731 baseEnd_761731 := by
    simpa [prefixWord, tailWord_761731, baseEnd_761731] using wordTrace_append hprefix tailTrace_761731
  have hstable : (prefixWord ++ tailWord_761731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761731).length < 2 ^ (prefixWord ++ tailWord_761731).sum := by decide
  have hdescent : baseEnd_761731 < baseStart_761731 := by decide
  rcases family_descends (prefixWord ++ tailWord_761731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761758 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_761758 : Nat := 118140960795 + 761758 * 2 ^ 59
def prefixEnd_761758 : Nat := 4983230072969 + 3 ^ 40 * 761758 * 2
def baseEnd_761758 : Nat := 347687107917987424019329

theorem tailTrace_761758 : CollatzResearch.WordTrace tailWord_761758 prefixEnd_761758 347687107917987424019329 := by
  unfold tailWord_761758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472949596786042344235741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18522397849525559169257285 3472949596786042344235741)
  ·
    refine ⟨1302356098794765879088403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3472949596786042344235741 1302356098794765879088403)
    ·
      refine ⟨1953534148192148818632605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302356098794765879088403 1953534148192148818632605)
      ·
        refine ⟨732575305572055806987227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1953534148192148818632605 732575305572055806987227)
        ·
          refine ⟨1098862958358083710480841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732575305572055806987227 1098862958358083710480841)
          ·
            refine ⟨824147218768562782860631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098862958358083710480841 824147218768562782860631)
            ·
              refine ⟨1236220828152844174290947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824147218768562782860631 1236220828152844174290947)
              ·
                refine ⟨1854331242229266261436421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236220828152844174290947 1854331242229266261436421)
                ·
                  refine ⟨347687107917987424019329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854331242229266261436421 347687107917987424019329)
                  ·
                    rfl

theorem cell20_761758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_761758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761758 prefixEnd_761758 := by exact prefixLift 761758
  have htrace : WordTrace (prefixWord ++ tailWord_761758) baseStart_761758 baseEnd_761758 := by
    simpa [prefixWord, tailWord_761758, baseEnd_761758] using wordTrace_append hprefix tailTrace_761758
  have hstable : (prefixWord ++ tailWord_761758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761758).length < 2 ^ (prefixWord ++ tailWord_761758).sum := by decide
  have hdescent : baseEnd_761758 < baseStart_761758 := by decide
  rcases family_descends (prefixWord ++ tailWord_761758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761768 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 3]
def baseStart_761768 : Nat := 118140960795 + 761768 * 2 ^ 59
def prefixEnd_761768 : Nat := 4983230072969 + 3 ^ 40 * 761768 * 2
def baseEnd_761768 : Nat := 347691672190471833685955

theorem tailTrace_761768 : CollatzResearch.WordTrace tailWord_761768 prefixEnd_761768 347691672190471833685955 := by
  unfold tailWord_761768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891980752126055230874979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18522641002834740307833305 13891980752126055230874979)
  ·
    refine ⟨20837971128189082846312469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13891980752126055230874979 20837971128189082846312469)
    ·
      refine ⟨976779896633863258420897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20837971128189082846312469 976779896633863258420897)
      ·
        refine ⟨732584922475397443815673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 976779896633863258420897 732584922475397443815673)
        ·
          refine ⟨549438691856548082861755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732584922475397443815673 549438691856548082861755)
          ·
            refine ⟨824158037784822124292633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549438691856548082861755 824158037784822124292633)
            ·
              refine ⟨618118528338616593219475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824158037784822124292633 618118528338616593219475)
              ·
                refine ⟨927177792507924889829213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618118528338616593219475 927177792507924889829213)
                ·
                  refine ⟨347691672190471833685955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927177792507924889829213 347691672190471833685955)
                  ·
                    rfl

theorem cell20_761768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_761768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761768 prefixEnd_761768 := by exact prefixLift 761768
  have htrace : WordTrace (prefixWord ++ tailWord_761768) baseStart_761768 baseEnd_761768 := by
    simpa [prefixWord, tailWord_761768, baseEnd_761768] using wordTrace_append hprefix tailTrace_761768
  have hstable : (prefixWord ++ tailWord_761768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761768).length < 2 ^ (prefixWord ++ tailWord_761768).sum := by decide
  have hdescent : baseEnd_761768 < baseStart_761768 := by decide
  rcases family_descends (prefixWord ++ tailWord_761768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761790 : List Nat := [4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_761790 : Nat := 118140960795 + 761790 * 2 ^ 59
def prefixEnd_761790 : Nat := 4983230072969 + 3 ^ 40 * 761790 * 2
def baseEnd_761790 : Nat := 115900571196645844984177

theorem tailTrace_761790 : CollatzResearch.WordTrace tailWord_761790 prefixEnd_761790 115900571196645844984177 := by
  unfold tailWord_761790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473095488771551027381353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18523175940114938812700549 3473095488771551027381353)
  ·
    refine ⟨2604821616578663270536015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3473095488771551027381353 2604821616578663270536015)
    ·
      refine ⟨3907232424867994905804023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604821616578663270536015 3907232424867994905804023)
      ·
        refine ⟨5860848637301992358706035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907232424867994905804023 5860848637301992358706035)
        ·
          refine ⟨8791272955952988538059053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860848637301992358706035 8791272955952988538059053)
          ·
            refine ⟨3296727358482370701772145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8791272955952988538059053 3296727358482370701772145)
            ·
              refine ⟨2472545518861778026329109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296727358482370701772145 2472545518861778026329109)
              ·
                refine ⟨115900571196645844984177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2472545518861778026329109 115900571196645844984177)
                ·
                  rfl

theorem cell20_761790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_761790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761790 prefixEnd_761790 := by exact prefixLift 761790
  have htrace : WordTrace (prefixWord ++ tailWord_761790) baseStart_761790 baseEnd_761790 := by
    simpa [prefixWord, tailWord_761790, baseEnd_761790] using wordTrace_append hprefix tailTrace_761790
  have hstable : (prefixWord ++ tailWord_761790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761790).length < 2 ^ (prefixWord ++ tailWord_761790).sum := by decide
  have hdescent : baseEnd_761790 < baseStart_761790 := by decide
  rcases family_descends (prefixWord ++ tailWord_761790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761820 : List Nat := [2, 2, 6, 1, 2, 1, 1, 5]
def baseStart_761820 : Nat := 118140960795 + 761820 * 2 ^ 59
def prefixEnd_761820 : Nat := 4983230072969 + 3 ^ 40 * 761820 * 2
def baseEnd_761820 : Nat := 115905135469130254650803

theorem tailTrace_761820 : CollatzResearch.WordTrace tailWord_761820 prefixEnd_761820 115905135469130254650803 := by
  unfold tailWord_761820
  simp only [CollatzResearch.WordTrace]
  refine ⟨13892929050031861671321457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18523905400042482228428609 13892929050031861671321457)
  ·
    refine ⟨10419696787523896253491093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13892929050031861671321457 10419696787523896253491093)
    ·
      refine ⟨488423286915182636882395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10419696787523896253491093 488423286915182636882395)
      ·
        refine ⟨732634930372773955323593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488423286915182636882395 732634930372773955323593)
        ·
          refine ⟨549476197779580466492695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732634930372773955323593 549476197779580466492695)
          ·
            refine ⟨824214296669370699739043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549476197779580466492695 824214296669370699739043)
            ·
              refine ⟨1236321445004056049608565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824214296669370699739043 1236321445004056049608565)
              ·
                refine ⟨115905135469130254650803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1236321445004056049608565 115905135469130254650803)
                ·
                  rfl

theorem cell20_761820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_761820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761820 prefixEnd_761820 := by exact prefixLift 761820
  have htrace : WordTrace (prefixWord ++ tailWord_761820) baseStart_761820 baseEnd_761820 := by
    simpa [prefixWord, tailWord_761820, baseEnd_761820] using wordTrace_append hprefix tailTrace_761820
  have hstable : (prefixWord ++ tailWord_761820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761820).length < 2 ^ (prefixWord ++ tailWord_761820).sum := by decide
  have hdescent : baseEnd_761820 < baseStart_761820 := by decide
  rcases family_descends (prefixWord ++ tailWord_761820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761866 : List Nat := [3, 1, 2, 2, 4, 1, 7]
def baseStart_761866 : Nat := 118140960795 + 761866 * 2 ^ 59
def prefixEnd_761866 : Nat := 4983230072969 + 3 ^ 40 * 761866 * 2
def baseEnd_761866 : Nat := 38637378006757672046543

theorem tailTrace_761866 : CollatzResearch.WordTrace tailWord_761866 prefixEnd_761866 38637378006757672046543 := by
  unfold tailWord_761866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946883964474268299704363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18525023905264715465878301 6946883964474268299704363)
  ·
    refine ⟨10420325946711402449556545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6946883964474268299704363 10420325946711402449556545)
    ·
      refine ⟨7815244460033551837167409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10420325946711402449556545 7815244460033551837167409)
      ·
        refine ⟨5861433345025163877875557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7815244460033551837167409 5861433345025163877875557)
        ·
          refine ⟨1099018752192218227101667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5861433345025163877875557 1099018752192218227101667)
          ·
            refine ⟨1648528128288327340652501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099018752192218227101667 1648528128288327340652501)
            ·
              refine ⟨38637378006757672046543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1648528128288327340652501 38637378006757672046543)
              ·
                rfl

theorem cell20_761866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 7].length) (baseStart_761866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761866 prefixEnd_761866 := by exact prefixLift 761866
  have htrace : WordTrace (prefixWord ++ tailWord_761866) baseStart_761866 baseEnd_761866 := by
    simpa [prefixWord, tailWord_761866, baseEnd_761866] using wordTrace_append hprefix tailTrace_761866
  have hstable : (prefixWord ++ tailWord_761866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761866).length < 2 ^ (prefixWord ++ tailWord_761866).sum := by decide
  have hdescent : baseEnd_761866 < baseStart_761866 := by decide
  rcases family_descends (prefixWord ++ tailWord_761866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761887 : List Nat := [1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_761887 : Nat := 118140960795 + 761887 * 2 ^ 59
def prefixEnd_761887 : Nat := 4983230072969 + 3 ^ 40 * 761887 * 2
def baseEnd_761887 : Nat := 115915329011012102906267

theorem tailTrace_761887 : CollatzResearch.WordTrace tailWord_761887 prefixEnd_761887 115915329011012102906267 := by
  unfold tailWord_761887
  simp only [CollatzResearch.WordTrace]
  refine ⟨27788301790820993785331915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18525534527213995856887943 27788301790820993785331915)
  ·
    refine ⟨41682452686231490677997873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27788301790820993785331915 41682452686231490677997873)
    ·
      refine ⟨31261839514673618008498405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41682452686231490677997873 31261839514673618008498405)
      ·
        refine ⟨5861594909001303376593451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31261839514673618008498405 5861594909001303376593451)
        ·
          refine ⟨8792392363501955064890177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861594909001303376593451 8792392363501955064890177)
          ·
            refine ⟨6594294272626466298667633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8792392363501955064890177 6594294272626466298667633)
            ·
              refine ⟨4945720704469849724000725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594294272626466298667633 4945720704469849724000725)
              ·
                refine ⟨115915329011012102906267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4945720704469849724000725 115915329011012102906267)
                ·
                  rfl

theorem cell20_761887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_761887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761887 prefixEnd_761887 := by exact prefixLift 761887
  have htrace : WordTrace (prefixWord ++ tailWord_761887) baseStart_761887 baseEnd_761887 := by
    simpa [prefixWord, tailWord_761887, baseEnd_761887] using wordTrace_append hprefix tailTrace_761887
  have hstable : (prefixWord ++ tailWord_761887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761887).length < 2 ^ (prefixWord ++ tailWord_761887).sum := by decide
  have hdescent : baseEnd_761887 < baseStart_761887 := by decide
  rcases family_descends (prefixWord ++ tailWord_761887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761904 : List Nat := [2, 1, 1, 1, 2, 5, 4, 4]
def baseStart_761904 : Nat := 118140960795 + 761904 * 2 ^ 59
def prefixEnd_761904 : Nat := 4983230072969 + 3 ^ 40 * 761904 * 2
def baseEnd_761904 : Nat := 115917915432086601717355

theorem tailTrace_761904 : CollatzResearch.WordTrace tailWord_761904 prefixEnd_761904 115917915432086601717355 := by
  unfold tailWord_761904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894460915879702844350383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18525947887839603792467177 13894460915879702844350383)
  ·
    refine ⟨20841691373819554266525575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894460915879702844350383 20841691373819554266525575)
    ·
      refine ⟨31262537060729331399788363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20841691373819554266525575 31262537060729331399788363)
      ·
        refine ⟨46893805591093997099682545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31262537060729331399788363 46893805591093997099682545)
        ·
          refine ⟨35170354193320497824761909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46893805591093997099682545 35170354193320497824761909)
          ·
            refine ⟨3297220705623796671071429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35170354193320497824761909 3297220705623796671071429)
            ·
              refine ⟨618228882304461875825893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3297220705623796671071429 618228882304461875825893)
              ·
                refine ⟨115917915432086601717355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618228882304461875825893 115917915432086601717355)
                ·
                  rfl

theorem cell20_761904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_761904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761904 prefixEnd_761904 := by exact prefixLift 761904
  have htrace : WordTrace (prefixWord ++ tailWord_761904) baseStart_761904 baseEnd_761904 := by
    simpa [prefixWord, tailWord_761904, baseEnd_761904] using wordTrace_append hprefix tailTrace_761904
  have hstable : (prefixWord ++ tailWord_761904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761904).length < 2 ^ (prefixWord ++ tailWord_761904).sum := by decide
  have hdescent : baseEnd_761904 < baseStart_761904 := by decide
  rcases family_descends (prefixWord ++ tailWord_761904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761956 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_761956 : Nat := 118140960795 + 761956 * 2 ^ 59
def prefixEnd_761956 : Nat := 4983230072969 + 3 ^ 40 * 761956 * 2
def baseEnd_761956 : Nat := 347777480513178735418519

theorem tailTrace_761956 : CollatzResearch.WordTrace tailWord_761956 prefixEnd_761956 347777480513178735418519 := by
  unfold tailWord_761956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13895409213785509284796861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18527212285047345713062481 13895409213785509284796861)
  ·
    refine ⟨5210778455169565981798823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13895409213785509284796861 5210778455169565981798823)
    ·
      refine ⟨7816167682754348972698235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5210778455169565981798823 7816167682754348972698235)
      ·
        refine ⟨11724251524131523459047353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7816167682754348972698235 11724251524131523459047353)
        ·
          refine ⟨8793188643098642594285515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11724251524131523459047353 8793188643098642594285515)
          ·
            refine ⟨13189782964647963891428273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8793188643098642594285515 13189782964647963891428273)
            ·
              refine ⟨9892337223485972918571205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13189782964647963891428273 9892337223485972918571205)
              ·
                refine ⟨1854813229403619922232101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9892337223485972918571205 1854813229403619922232101)
                ·
                  refine ⟨347777480513178735418519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854813229403619922232101 347777480513178735418519)
                  ·
                    rfl

theorem cell20_761956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_761956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761956 prefixEnd_761956 := by exact prefixLift 761956
  have htrace : WordTrace (prefixWord ++ tailWord_761956) baseStart_761956 baseEnd_761956 := by
    simpa [prefixWord, tailWord_761956, baseEnd_761956] using wordTrace_append hprefix tailTrace_761956
  have hstable : (prefixWord ++ tailWord_761956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761956).length < 2 ^ (prefixWord ++ tailWord_761956).sum := by decide
  have hdescent : baseEnd_761956 < baseStart_761956 := by decide
  rcases family_descends (prefixWord ++ tailWord_761956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761987 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_761987 : Nat := 118140960795 + 761987 * 2 ^ 59
def prefixEnd_761987 : Nat := 4983230072969 + 3 ^ 40 * 761987 * 2
def baseEnd_761987 : Nat := 347791629757880405385059

theorem tailTrace_761987 : CollatzResearch.WordTrace tailWord_761987 prefixEnd_761987 347791629757880405385059 := by
  unfold tailWord_761987
  simp only [CollatzResearch.WordTrace]
  refine ⟨27791949090458710863972215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18527966060305807242648143 27791949090458710863972215)
  ·
    refine ⟨41687923635688066295958323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27791949090458710863972215 41687923635688066295958323)
    ·
      refine ⟨62531885453532099443937485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41687923635688066295958323 62531885453532099443937485)
      ·
        refine ⟨23449457045074537291476557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62531885453532099443937485 23449457045074537291476557)
        ·
          refine ⟨8793546391902951484303709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23449457045074537291476557 8793546391902951484303709)
          ·
            refine ⟨3297579896963606806613891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8793546391902951484303709 3297579896963606806613891)
            ·
              refine ⟨4946369845445410209920837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297579896963606806613891 4946369845445410209920837)
              ·
                refine ⟨927444346021014414360157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4946369845445410209920837 927444346021014414360157)
                ·
                  refine ⟨347791629757880405385059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927444346021014414360157 347791629757880405385059)
                  ·
                    rfl

theorem cell20_761987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_761987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_761987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_761987 prefixEnd_761987 := by exact prefixLift 761987
  have htrace : WordTrace (prefixWord ++ tailWord_761987) baseStart_761987 baseEnd_761987 := by
    simpa [prefixWord, tailWord_761987, baseEnd_761987] using wordTrace_append hprefix tailTrace_761987
  have hstable : (prefixWord ++ tailWord_761987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761987).length < 2 ^ (prefixWord ++ tailWord_761987).sum := by decide
  have hdescent : baseEnd_761987 < baseStart_761987 := by decide
  rcases family_descends (prefixWord ++ tailWord_761987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762014 : List Nat := [4, 3, 1, 1, 3, 1, 3, 4]
def baseStart_762014 : Nat := 118140960795 + 762014 * 2 ^ 59
def prefixEnd_762014 : Nat := 4983230072969 + 3 ^ 40 * 762014 * 2
def baseEnd_762014 : Nat := 115934651097862770494983

theorem tailTrace_762014 : CollatzResearch.WordTrace tailWord_762014 prefixEnd_762014 115934651097862770494983 := by
  unfold tailWord_762014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474116732670111809400637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18528622574240596316803397 3474116732670111809400637)
  ·
    refine ⟨1302793774751291928525239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3474116732670111809400637 1302793774751291928525239)
    ·
      refine ⟨1954190662126937892787859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302793774751291928525239 1954190662126937892787859)
      ·
        refine ⟨2931285993190406839181789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954190662126937892787859 2931285993190406839181789)
        ·
          refine ⟨1099232247446402564693171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2931285993190406839181789 1099232247446402564693171)
          ·
            refine ⟨1648848371169603847039757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099232247446402564693171 1648848371169603847039757)
            ·
              refine ⟨618318139188601442639909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1648848371169603847039757 618318139188601442639909)
              ·
                refine ⟨115934651097862770494983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618318139188601442639909 115934651097862770494983)
                ·
                  rfl

theorem cell20_762014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_762014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762014 prefixEnd_762014 := by exact prefixLift 762014
  have htrace : WordTrace (prefixWord ++ tailWord_762014) baseStart_762014 baseEnd_762014 := by
    simpa [prefixWord, tailWord_762014, baseEnd_762014] using wordTrace_append hprefix tailTrace_762014
  have hstable : (prefixWord ++ tailWord_762014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762014).length < 2 ^ (prefixWord ++ tailWord_762014).sum := by decide
  have hdescent : baseEnd_762014 < baseStart_762014 := by decide
  rcases family_descends (prefixWord ++ tailWord_762014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762039 : List Nat := [1, 1, 3, 1, 4, 3, 7]
def baseStart_762039 : Nat := 118140960795 + 762039 * 2 ^ 59
def prefixEnd_762039 : Nat := 4983230072969 + 3 ^ 40 * 762039 * 2
def baseEnd_762039 : Nat := 38646151552755481739057

theorem tailTrace_762039 : CollatzResearch.WordTrace tailWord_762039 prefixEnd_762039 38646151552755481739057 := by
  unfold tailWord_762039
  simp only [CollatzResearch.WordTrace]
  refine ⟨27793845686270323744865171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18529230457513549163243447 27793845686270323744865171)
  ·
    refine ⟨41690768529405485617297757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27793845686270323744865171 41690768529405485617297757)
    ·
      refine ⟨15634038198527057106486659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41690768529405485617297757 15634038198527057106486659)
      ·
        refine ⟨23451057297790585659729989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15634038198527057106486659 23451057297790585659729989)
        ·
          refine ⟨4397073243335734811199373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23451057297790585659729989 4397073243335734811199373)
          ·
            refine ⟨1648902466250900554199765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4397073243335734811199373 1648902466250900554199765)
            ·
              refine ⟨38646151552755481739057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1648902466250900554199765 38646151552755481739057)
              ·
                rfl

theorem cell20_762039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_762039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762039 prefixEnd_762039 := by exact prefixLift 762039
  have htrace : WordTrace (prefixWord ++ tailWord_762039) baseStart_762039 baseEnd_762039 := by
    simpa [prefixWord, tailWord_762039, baseEnd_762039] using wordTrace_append hprefix tailTrace_762039
  have hstable : (prefixWord ++ tailWord_762039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762039).length < 2 ^ (prefixWord ++ tailWord_762039).sum := by decide
  have hdescent : baseEnd_762039 < baseStart_762039 := by decide
  rcases family_descends (prefixWord ++ tailWord_762039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762114 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_762114 : Nat := 118140960795 + 762114 * 2 ^ 59
def prefixEnd_762114 : Nat := 4983230072969 + 3 ^ 40 * 762114 * 2
def baseEnd_762114 : Nat := 347849596018432408151207

theorem tailTrace_762114 : CollatzResearch.WordTrace tailWord_762114 prefixEnd_762114 347849596018432408151207 := by
  unfold tailWord_762114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949145290249652888461349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18531054107332407702563597 6949145290249652888461349)
  ·
    refine ⟨1302964741921809916586503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6949145290249652888461349 1302964741921809916586503)
    ·
      refine ⟨1954447112882714874879755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302964741921809916586503 1954447112882714874879755)
      ·
        refine ⟨2931670669324072312319633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954447112882714874879755 2931670669324072312319633)
        ·
          refine ⟨2198753001993054234239725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2931670669324072312319633 2198753001993054234239725)
          ·
            refine ⟨824532375747395337839897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2198753001993054234239725 824532375747395337839897)
            ·
              refine ⟨618399281810546503379923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824532375747395337839897 618399281810546503379923)
              ·
                refine ⟨927598922715819755069885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618399281810546503379923 927598922715819755069885)
                ·
                  refine ⟨347849596018432408151207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927598922715819755069885 347849596018432408151207)
                  ·
                    rfl

theorem cell20_762114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_762114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762114 prefixEnd_762114 := by exact prefixLift 762114
  have htrace : WordTrace (prefixWord ++ tailWord_762114) baseStart_762114 baseEnd_762114 := by
    simpa [prefixWord, tailWord_762114, baseEnd_762114] using wordTrace_append hprefix tailTrace_762114
  have hstable : (prefixWord ++ tailWord_762114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762114).length < 2 ^ (prefixWord ++ tailWord_762114).sum := by decide
  have hdescent : baseEnd_762114 < baseStart_762114 := by decide
  rcases family_descends (prefixWord ++ tailWord_762114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762115 : List Nat := [1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_762115 : Nat := 118140960795 + 762115 * 2 ^ 59
def prefixEnd_762115 : Nat := 4983230072969 + 3 ^ 40 * 762115 * 2
def baseEnd_762115 : Nat := 115950017481893616372623

theorem tailTrace_762115 : CollatzResearch.WordTrace tailWord_762115 prefixEnd_762115 115950017481893616372623 := by
  unfold tailWord_762115
  simp only [CollatzResearch.WordTrace]
  refine ⟨27796617633994988724631799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18531078422663325816421199 27796617633994988724631799)
  ·
    refine ⟨41694926450992483086947699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27796617633994988724631799 41694926450992483086947699)
    ·
      refine ⟨62542389676488724630421549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41694926450992483086947699 62542389676488724630421549)
      ·
        refine ⟨23453396128683271736408081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62542389676488724630421549 23453396128683271736408081)
        ·
          refine ⟨17590047096512453802306061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23453396128683271736408081 17590047096512453802306061)
          ·
            refine ⟨6596267661192170175864773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17590047096512453802306061 6596267661192170175864773)
            ·
              refine ⟨1236800186473531907974645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6596267661192170175864773 1236800186473531907974645)
              ·
                refine ⟨115950017481893616372623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1236800186473531907974645 115950017481893616372623)
                ·
                  rfl

theorem cell20_762115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_762115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762115 prefixEnd_762115 := by exact prefixLift 762115
  have htrace : WordTrace (prefixWord ++ tailWord_762115) baseStart_762115 baseEnd_762115 := by
    simpa [prefixWord, tailWord_762115, baseEnd_762115] using wordTrace_append hprefix tailTrace_762115
  have hstable : (prefixWord ++ tailWord_762115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762115).length < 2 ^ (prefixWord ++ tailWord_762115).sum := by decide
  have hdescent : baseEnd_762115 < baseStart_762115 := by decide
  rcases family_descends (prefixWord ++ tailWord_762115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762163 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 2]
def baseStart_762163 : Nat := 118140960795 + 762163 * 2 ^ 59
def prefixEnd_762163 : Nat := 4983230072969 + 3 ^ 40 * 762163 * 2
def baseEnd_762163 : Nat := 347871960953606015517673

theorem tailTrace_762163 : CollatzResearch.WordTrace tailWord_762163 prefixEnd_762163 347871960953606015517673 := by
  unfold tailWord_762163
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798368337821092922379143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18532245558547395281586095 27798368337821092922379143)
  ·
    refine ⟨41697552506731639383568715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27798368337821092922379143 41697552506731639383568715)
    ·
      refine ⟨62546328760097459075353073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41697552506731639383568715 62546328760097459075353073)
      ·
        refine ⟨46909746570073094306514805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62546328760097459075353073 46909746570073094306514805)
        ·
          refine ⟨4397788740944352591235763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46909746570073094306514805 4397788740944352591235763)
          ·
            refine ⟨6596683111416528886853645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397788740944352591235763 6596683111416528886853645)
            ·
              refine ⟨2473756166781198332570117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6596683111416528886853645 2473756166781198332570117)
              ·
                refine ⟨463829281271474687356897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2473756166781198332570117 463829281271474687356897)
                ·
                  refine ⟨347871960953606015517673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463829281271474687356897 347871960953606015517673)
                  ·
                    rfl

theorem cell20_762163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 2].length) (baseStart_762163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762163 prefixEnd_762163 := by exact prefixLift 762163
  have htrace : WordTrace (prefixWord ++ tailWord_762163) baseStart_762163 baseEnd_762163 := by
    simpa [prefixWord, tailWord_762163, baseEnd_762163] using wordTrace_append hprefix tailTrace_762163
  have hstable : (prefixWord ++ tailWord_762163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762163).length < 2 ^ (prefixWord ++ tailWord_762163).sum := by decide
  have hdescent : baseEnd_762163 < baseStart_762163 := by decide
  rcases family_descends (prefixWord ++ tailWord_762163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762167 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_762167 : Nat := 118140960795 + 762167 * 2 ^ 59
def prefixEnd_762167 : Nat := 4983230072969 + 3 ^ 40 * 762167 * 2
def baseEnd_762167 : Nat := 347873786662599779384323

theorem tailTrace_762167 : CollatzResearch.WordTrace tailWord_762167 prefixEnd_762167 347873786662599779384323 := by
  unfold tailWord_762167
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798514229806601605524755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18532342819871067737016503 27798514229806601605524755)
  ·
    refine ⟨41697771344709902408287133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27798514229806601605524755 41697771344709902408287133)
    ·
      refine ⟨15636664254266213403107675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41697771344709902408287133 15636664254266213403107675)
      ·
        refine ⟨23454996381399320104661513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15636664254266213403107675 23454996381399320104661513)
        ·
          refine ⟨17591247286049490078496135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23454996381399320104661513 17591247286049490078496135)
          ·
            refine ⟨26386870929074235117744203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17591247286049490078496135 26386870929074235117744203)
            ·
              refine ⟨39580306393611352676616305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26386870929074235117744203 39580306393611352676616305)
              ·
                refine ⟨29685229795208514507462229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39580306393611352676616305 29685229795208514507462229)
                ·
                  refine ⟨347873786662599779384323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29685229795208514507462229 347873786662599779384323)
                  ·
                    rfl

theorem cell20_762167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_762167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762167 prefixEnd_762167 := by exact prefixLift 762167
  have htrace : WordTrace (prefixWord ++ tailWord_762167) baseStart_762167 baseEnd_762167 := by
    simpa [prefixWord, tailWord_762167, baseEnd_762167] using wordTrace_append hprefix tailTrace_762167
  have hstable : (prefixWord ++ tailWord_762167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762167).length < 2 ^ (prefixWord ++ tailWord_762167).sum := by decide
  have hdescent : baseEnd_762167 < baseStart_762167 := by decide
  rcases family_descends (prefixWord ++ tailWord_762167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762170 : List Nat := [3, 1, 1, 1, 4, 4, 1, 5]
def baseStart_762170 : Nat := 118140960795 + 762170 * 2 ^ 59
def prefixEnd_762170 : Nat := 4983230072969 + 3 ^ 40 * 762170 * 2
def baseEnd_762170 : Nat := 115958385314781700761437

theorem tailTrace_762170 : CollatzResearch.WordTrace tailWord_762170 prefixEnd_762170 115958385314781700761437 := by
  unfold tailWord_762170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949655912198933279470991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18532415765863822078589309 6949655912198933279470991)
  ·
    refine ⟨10424483868298399919206487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6949655912198933279470991 10424483868298399919206487)
    ·
      refine ⟨15636725802447599878809731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10424483868298399919206487 15636725802447599878809731)
      ·
        refine ⟨23455088703671399818214597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15636725802447599878809731 23455088703671399818214597)
        ·
          refine ⟨4397829131938387465915237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23455088703671399818214597 4397829131938387465915237)
          ·
            refine ⟨824592962238447649859107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4397829131938387465915237 824592962238447649859107)
            ·
              refine ⟨1236889443357671474788661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824592962238447649859107 1236889443357671474788661)
              ·
                refine ⟨115958385314781700761437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1236889443357671474788661 115958385314781700761437)
                ·
                  rfl

theorem cell20_762170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_762170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762170 prefixEnd_762170 := by exact prefixLift 762170
  have htrace : WordTrace (prefixWord ++ tailWord_762170) baseStart_762170 baseEnd_762170 := by
    simpa [prefixWord, tailWord_762170, baseEnd_762170] using wordTrace_append hprefix tailTrace_762170
  have hstable : (prefixWord ++ tailWord_762170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762170).length < 2 ^ (prefixWord ++ tailWord_762170).sum := by decide
  have hdescent : baseEnd_762170 < baseStart_762170 := by decide
  rcases family_descends (prefixWord ++ tailWord_762170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762180 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_762180 : Nat := 118140960795 + 762180 * 2 ^ 59
def prefixEnd_762180 : Nat := 4983230072969 + 3 ^ 40 * 762180 * 2
def baseEnd_762180 : Nat := 347879720216829511950937

theorem tailTrace_762180 : CollatzResearch.WordTrace tailWord_762180 prefixEnd_762180 347879720216829511950937 := by
  unfold tailWord_762180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13899494189379752412873997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18532658919173003217165329 13899494189379752412873997)
  ·
    refine ⟨5212310321017407154827749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13899494189379752412873997 5212310321017407154827749)
    ·
      refine ⟨977308185190763841530203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5212310321017407154827749 977308185190763841530203)
      ·
        refine ⟨1465962277786145762295305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977308185190763841530203 1465962277786145762295305)
        ·
          refine ⟨1099471708339609321721479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1465962277786145762295305 1099471708339609321721479)
          ·
            refine ⟨1649207562509413982582219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099471708339609321721479 1649207562509413982582219)
            ·
              refine ⟨2473811343764120973873329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649207562509413982582219 2473811343764120973873329)
              ·
                refine ⟨1855358507823090730404997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473811343764120973873329 1855358507823090730404997)
                ·
                  refine ⟨347879720216829511950937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855358507823090730404997 347879720216829511950937)
                  ·
                    rfl

theorem cell20_762180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_762180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762180 prefixEnd_762180 := by exact prefixLift 762180
  have htrace : WordTrace (prefixWord ++ tailWord_762180) baseStart_762180 baseEnd_762180 := by
    simpa [prefixWord, tailWord_762180, baseEnd_762180] using wordTrace_append hprefix tailTrace_762180
  have hstable : (prefixWord ++ tailWord_762180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762180).length < 2 ^ (prefixWord ++ tailWord_762180).sum := by decide
  have hdescent : baseEnd_762180 < baseStart_762180 := by decide
  rcases family_descends (prefixWord ++ tailWord_762180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762215 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_762215 : Nat := 118140960795 + 762215 * 2 ^ 59
def prefixEnd_762215 : Nat := 4983230072969 + 3 ^ 40 * 762215 * 2
def baseEnd_762215 : Nat := 347895695170524945784127

theorem tailTrace_762215 : CollatzResearch.WordTrace tailWord_762215 prefixEnd_762215 347895695170524945784127 := by
  unfold tailWord_762215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27800264933632705803272099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18533509955755137202181399 27800264933632705803272099)
  ·
    refine ⟨41700397400449058704908149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27800264933632705803272099 41700397400449058704908149)
    ·
      refine ⟨3909412256292099253585139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41700397400449058704908149 3909412256292099253585139)
      ·
        refine ⟨5864118384438148880377709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909412256292099253585139 5864118384438148880377709)
        ·
          refine ⟨2199044394164305830141641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5864118384438148880377709 2199044394164305830141641)
          ·
            refine ⟨1649283295623229372606231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2199044394164305830141641 1649283295623229372606231)
            ·
              refine ⟨2473924943434844058909347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649283295623229372606231 2473924943434844058909347)
              ·
                refine ⟨3710887415152266088364021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473924943434844058909347 3710887415152266088364021)
                ·
                  refine ⟨347895695170524945784127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3710887415152266088364021 347895695170524945784127)
                  ·
                    rfl

theorem cell20_762215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_762215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762215 prefixEnd_762215 := by exact prefixLift 762215
  have htrace : WordTrace (prefixWord ++ tailWord_762215) baseStart_762215 baseEnd_762215 := by
    simpa [prefixWord, tailWord_762215, baseEnd_762215] using wordTrace_append hprefix tailTrace_762215
  have hstable : (prefixWord ++ tailWord_762215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762215).length < 2 ^ (prefixWord ++ tailWord_762215).sum := by decide
  have hdescent : baseEnd_762215 < baseStart_762215 := by decide
  rcases family_descends (prefixWord ++ tailWord_762215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762218 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_762218 : Nat := 118140960795 + 762218 * 2 ^ 59
def prefixEnd_762218 : Nat := 4983230072969 + 3 ^ 40 * 762218 * 2
def baseEnd_762218 : Nat := 347897064452270268684115

theorem tailTrace_762218 : CollatzResearch.WordTrace tailWord_762218 prefixEnd_762218 347897064452270268684115 := by
  unfold tailWord_762218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950093588155459328907827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18533582901747891543754205 6950093588155459328907827)
  ·
    refine ⟨10425140382233188993361741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6950093588155459328907827 10425140382233188993361741)
    ·
      refine ⟨3909427643337445872510653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10425140382233188993361741 3909427643337445872510653)
      ·
        refine ⟨1466035366251542202191495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3909427643337445872510653 1466035366251542202191495)
        ·
          refine ⟨2199053049377313303287243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466035366251542202191495 2199053049377313303287243)
          ·
            refine ⟨3298579574065969954930865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199053049377313303287243 3298579574065969954930865)
            ·
              refine ⟨2473934680549477466198149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3298579574065969954930865 2473934680549477466198149)
              ·
                refine ⟨463862752603027024912153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2473934680549477466198149 463862752603027024912153)
                ·
                  refine ⟨347897064452270268684115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463862752603027024912153 347897064452270268684115)
                  ·
                    rfl

theorem cell20_762218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_762218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762218 prefixEnd_762218 := by exact prefixLift 762218
  have htrace : WordTrace (prefixWord ++ tailWord_762218) baseStart_762218 baseEnd_762218 := by
    simpa [prefixWord, tailWord_762218, baseEnd_762218] using wordTrace_append hprefix tailTrace_762218
  have hstable : (prefixWord ++ tailWord_762218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762218).length < 2 ^ (prefixWord ++ tailWord_762218).sum := by decide
  have hdescent : baseEnd_762218 < baseStart_762218 := by decide
  rcases family_descends (prefixWord ++ tailWord_762218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762270 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_762270 : Nat := 118140960795 + 762270 * 2 ^ 59
def prefixEnd_762270 : Nat := 4983230072969 + 3 ^ 40 * 762270 * 2
def baseEnd_762270 : Nat := 347920798669189198950569

theorem tailTrace_762270 : CollatzResearch.WordTrace tailWord_762270 prefixEnd_762270 347920798669189198950569 := by
  unfold tailWord_762270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475283868554181274565533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18534847298955633464349509 3475283868554181274565533)
  ·
    refine ⟨1303231450707817977962075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3475283868554181274565533 1303231450707817977962075)
    ·
      refine ⟨1954847176061726966943113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303231450707817977962075 1954847176061726966943113)
      ·
        refine ⟨1466135382046295225207335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1954847176061726966943113 1466135382046295225207335)
        ·
          refine ⟨2199203073069442837811003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466135382046295225207335 2199203073069442837811003)
          ·
            refine ⟨3298804609604164256716505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199203073069442837811003 3298804609604164256716505)
            ·
              refine ⟨2474103457203123192537379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3298804609604164256716505 2474103457203123192537379)
              ·
                refine ⟨3711155185804684788806069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474103457203123192537379 3711155185804684788806069)
                ·
                  refine ⟨347920798669189198950569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3711155185804684788806069 347920798669189198950569)
                  ·
                    rfl

theorem cell20_762270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_762270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762270 prefixEnd_762270 := by exact prefixLift 762270
  have htrace : WordTrace (prefixWord ++ tailWord_762270) baseStart_762270 baseEnd_762270 := by
    simpa [prefixWord, tailWord_762270, baseEnd_762270] using wordTrace_append hprefix tailTrace_762270
  have hstable : (prefixWord ++ tailWord_762270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762270).length < 2 ^ (prefixWord ++ tailWord_762270).sum := by decide
  have hdescent : baseEnd_762270 < baseStart_762270 := by decide
  rcases family_descends (prefixWord ++ tailWord_762270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762273 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 4]
def baseStart_762273 : Nat := 118140960795 + 762273 * 2 ^ 59
def prefixEnd_762273 : Nat := 4983230072969 + 3 ^ 40 * 762273 * 2
def baseEnd_762273 : Nat := 347922167950934521850557

theorem tailTrace_762273 : CollatzResearch.WordTrace tailWord_762273 prefixEnd_762273 347922167950934521850557 := by
  unfold tailWord_762273
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802380367422581708883473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18534920244948387805922315 27802380367422581708883473)
  ·
    refine ⟨20851785275566936281662605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27802380367422581708883473 20851785275566936281662605)
    ·
      refine ⟨7819419478337601105623477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20851785275566936281662605 7819419478337601105623477)
      ·
        refine ⟨733070576094150103652201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7819419478337601105623477 733070576094150103652201)
        ·
          refine ⟨549802932070612577739151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733070576094150103652201 549802932070612577739151)
          ·
            refine ⟨824704398105918866608727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549802932070612577739151 824704398105918866608727)
            ·
              refine ⟨1237056597158878299913091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824704398105918866608727 1237056597158878299913091)
              ·
                refine ⟨1855584895738317449869637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237056597158878299913091 1855584895738317449869637)
                ·
                  refine ⟨347922167950934521850557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855584895738317449869637 347922167950934521850557)
                  ·
                    rfl

theorem cell20_762273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_762273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762273 prefixEnd_762273 := by exact prefixLift 762273
  have htrace : WordTrace (prefixWord ++ tailWord_762273) baseStart_762273 baseEnd_762273 := by
    simpa [prefixWord, tailWord_762273, baseEnd_762273] using wordTrace_append hprefix tailTrace_762273
  have hstable : (prefixWord ++ tailWord_762273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762273).length < 2 ^ (prefixWord ++ tailWord_762273).sum := by decide
  have hdescent : baseEnd_762273 < baseStart_762273 := by decide
  rcases family_descends (prefixWord ++ tailWord_762273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762322 : List Nat := [3, 2, 2, 4, 1, 8]
def baseStart_762322 : Nat := 118140960795 + 762322 * 2 ^ 59
def prefixEnd_762322 : Nat := 4983230072969 + 3 ^ 40 * 762322 * 2
def baseEnd_762322 : Nat := 12886834551337338119149

theorem tailTrace_762322 : CollatzResearch.WordTrace tailWord_762322 prefixEnd_762322 12886834551337338119149 := by
  unfold tailWord_762322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951041886061265769354305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18536111696163375384944813 6951041886061265769354305)
  ·
    refine ⟨5213281414545949327015729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6951041886061265769354305 5213281414545949327015729)
    ·
      refine ⟨3909961060909461995261797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5213281414545949327015729 3909961060909461995261797)
      ·
        refine ⟨733117698920524124111587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3909961060909461995261797 733117698920524124111587)
        ·
          refine ⟨1099676548380786186167381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733117698920524124111587 1099676548380786186167381)
          ·
            refine ⟨12886834551337338119149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1099676548380786186167381 12886834551337338119149)
            ·
              rfl

theorem cell20_762322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 8].length) (baseStart_762322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762322 prefixEnd_762322 := by exact prefixLift 762322
  have htrace : WordTrace (prefixWord ++ tailWord_762322) baseStart_762322 baseEnd_762322 := by
    simpa [prefixWord, tailWord_762322, baseEnd_762322] using wordTrace_append hprefix tailTrace_762322
  have hstable : (prefixWord ++ tailWord_762322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762322).length < 2 ^ (prefixWord ++ tailWord_762322).sum := by decide
  have hdescent : baseEnd_762322 < baseStart_762322 := by decide
  rcases family_descends (prefixWord ++ tailWord_762322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762329 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_762329 : Nat := 118140960795 + 762329 * 2 ^ 59
def prefixEnd_762329 : Nat := 4983230072969 + 3 ^ 40 * 762329 * 2
def baseEnd_762329 : Nat := 347947727876847215983661

theorem tailTrace_762329 : CollatzResearch.WordTrace tailWord_762329 prefixEnd_762329 347947727876847215983661 := by
  unfold tailWord_762329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27804422855219703272922041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18536281903479802181948027 27804422855219703272922041)
  ·
    refine ⟨20853317141414777454691531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27804422855219703272922041 20853317141414777454691531)
    ·
      refine ⟨31279975712122166182037297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20853317141414777454691531 31279975712122166182037297)
      ·
        refine ⟨23459981784091624636527973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31279975712122166182037297 23459981784091624636527973)
        ·
          refine ⟨4398746584517179619348995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23459981784091624636527973 4398746584517179619348995)
          ·
            refine ⟨6598119876775769429023493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398746584517179619348995 6598119876775769429023493)
            ·
              refine ⟨1237147476895456767941905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6598119876775769429023493 1237147476895456767941905)
              ·
                refine ⟨927860607671592575956429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237147476895456767941905 927860607671592575956429)
                ·
                  refine ⟨347947727876847215983661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927860607671592575956429 347947727876847215983661)
                  ·
                    rfl

theorem cell20_762329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_762329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762329 prefixEnd_762329 := by exact prefixLift 762329
  have htrace : WordTrace (prefixWord ++ tailWord_762329) baseStart_762329 baseEnd_762329 := by
    simpa [prefixWord, tailWord_762329, baseEnd_762329] using wordTrace_append hprefix tailTrace_762329
  have hstable : (prefixWord ++ tailWord_762329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762329).length < 2 ^ (prefixWord ++ tailWord_762329).sum := by decide
  have hdescent : baseEnd_762329 < baseStart_762329 := by decide
  rcases family_descends (prefixWord ++ tailWord_762329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762339 : List Nat := [1, 1, 1, 6, 4, 1, 1, 5]
def baseStart_762339 : Nat := 118140960795 + 762339 * 2 ^ 59
def prefixEnd_762339 : Nat := 4983230072969 + 3 ^ 40 * 762339 * 2
def baseEnd_762339 : Nat := 115984097383110541883429

theorem tailTrace_762339 : CollatzResearch.WordTrace tailWord_762339 prefixEnd_762339 115984097383110541883429 := by
  unfold tailWord_762339
  simp only [CollatzResearch.WordTrace]
  refine ⟨27804787585183474980786071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18536525056788983320524047 27804787585183474980786071)
  ·
    refine ⟨41707181377775212471179107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27804787585183474980786071 41707181377775212471179107)
    ·
      refine ⟨62560772066662818706768661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41707181377775212471179107 62560772066662818706768661)
      ·
        refine ⟨2932536190624819626879781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62560772066662818706768661 2932536190624819626879781)
        ·
          refine ⟨549850535742153680039959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2932536190624819626879781 549850535742153680039959)
          ·
            refine ⟨824775803613230520059939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549850535742153680039959 824775803613230520059939)
            ·
              refine ⟨1237163705419845780089909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824775803613230520059939 1237163705419845780089909)
              ·
                refine ⟨115984097383110541883429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1237163705419845780089909 115984097383110541883429)
                ·
                  rfl

theorem cell20_762339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].length) (baseStart_762339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762339 prefixEnd_762339 := by exact prefixLift 762339
  have htrace : WordTrace (prefixWord ++ tailWord_762339) baseStart_762339 baseEnd_762339 := by
    simpa [prefixWord, tailWord_762339, baseEnd_762339] using wordTrace_append hprefix tailTrace_762339
  have hstable : (prefixWord ++ tailWord_762339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762339).length < 2 ^ (prefixWord ++ tailWord_762339).sum := by decide
  have hdescent : baseEnd_762339 < baseStart_762339 := by decide
  rcases family_descends (prefixWord ++ tailWord_762339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762426 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_762426 : Nat := 118140960795 + 762426 * 2 ^ 59
def prefixEnd_762426 : Nat := 4983230072969 + 3 ^ 40 * 762426 * 2
def baseEnd_762426 : Nat := 347992001319945989749931

theorem tailTrace_762426 : CollatzResearch.WordTrace tailWord_762426 prefixEnd_762426 347992001319945989749931 := by
  unfold tailWord_762426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951990183967072209800783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18538640490578859226135421 6951990183967072209800783)
  ·
    refine ⟨10427985275950608314701175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6951990183967072209800783 10427985275950608314701175)
    ·
      refine ⟨15641977913925912472051763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427985275950608314701175 15641977913925912472051763)
      ·
        refine ⟨23462966870888868708077645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15641977913925912472051763 23462966870888868708077645)
        ·
          refine ⟨8798612576583325765529117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23462966870888868708077645 8798612576583325765529117)
          ·
            refine ⟨3299479716218747162073419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8798612576583325765529117 3299479716218747162073419)
            ·
              refine ⟨4949219574328120743110129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299479716218747162073419 4949219574328120743110129)
              ·
                refine ⟨3711914680746090557332597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949219574328120743110129 3711914680746090557332597)
                ·
                  refine ⟨347992001319945989749931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3711914680746090557332597 347992001319945989749931)
                  ·
                    rfl

theorem cell20_762426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_762426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762426 prefixEnd_762426 := by exact prefixLift 762426
  have htrace : WordTrace (prefixWord ++ tailWord_762426) baseStart_762426 baseEnd_762426 := by
    simpa [prefixWord, tailWord_762426, baseEnd_762426] using wordTrace_append hprefix tailTrace_762426
  have hstable : (prefixWord ++ tailWord_762426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762426).length < 2 ^ (prefixWord ++ tailWord_762426).sum := by decide
  have hdescent : baseEnd_762426 < baseStart_762426 := by decide
  rcases family_descends (prefixWord ++ tailWord_762426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762460 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_762460 : Nat := 118140960795 + 762460 * 2 ^ 59
def prefixEnd_762460 : Nat := 4983230072969 + 3 ^ 40 * 762460 * 2
def baseEnd_762460 : Nat := 348007519846392982616459

theorem tailTrace_762460 : CollatzResearch.WordTrace tailWord_762460 prefixEnd_762460 348007519846392982616459 := by
  unfold tailWord_762460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13904600408872556322970417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18539467211830075097293889 13904600408872556322970417)
  ·
    refine ⟨10428450306654417242227813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13904600408872556322970417 10428450306654417242227813)
    ·
      refine ⟨1955334432497703232917715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10428450306654417242227813 1955334432497703232917715)
      ·
        refine ⟨2933001648746554849376573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955334432497703232917715 2933001648746554849376573)
        ·
          refine ⟨1099875618279958068516215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2933001648746554849376573 1099875618279958068516215)
          ·
            refine ⟨1649813427419937102774323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099875618279958068516215 1649813427419937102774323)
            ·
              refine ⟨2474720141129905654161485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649813427419937102774323 2474720141129905654161485)
              ·
                refine ⟨928020052923714620310557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2474720141129905654161485 928020052923714620310557)
                ·
                  refine ⟨348007519846392982616459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928020052923714620310557 348007519846392982616459)
                  ·
                    rfl

theorem cell20_762460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_762460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762460 prefixEnd_762460 := by exact prefixLift 762460
  have htrace : WordTrace (prefixWord ++ tailWord_762460) baseStart_762460 baseEnd_762460 := by
    simpa [prefixWord, tailWord_762460, baseEnd_762460] using wordTrace_append hprefix tailTrace_762460
  have hstable : (prefixWord ++ tailWord_762460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762460).length < 2 ^ (prefixWord ++ tailWord_762460).sum := by decide
  have hdescent : baseEnd_762460 < baseStart_762460 := by decide
  rcases family_descends (prefixWord ++ tailWord_762460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762471 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_762471 : Nat := 118140960795 + 762471 * 2 ^ 59
def prefixEnd_762471 : Nat := 4983230072969 + 3 ^ 40 * 762471 * 2
def baseEnd_762471 : Nat := 348012540546125833249747

theorem tailTrace_762471 : CollatzResearch.WordTrace tailWord_762471 prefixEnd_762471 348012540546125833249747 := by
  unfold tailWord_762471
  simp only [CollatzResearch.WordTrace]
  refine ⟨27809602020705261524591267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18539734680470174349727511 27809602020705261524591267)
  ·
    refine ⟨41714403031057892286886901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27809602020705261524591267 41714403031057892286886901)
    ·
      refine ⟨3910725284161677401895647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41714403031057892286886901 3910725284161677401895647)
      ·
        refine ⟨5866087926242516102843471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3910725284161677401895647 5866087926242516102843471)
        ·
          refine ⟨8799131889363774154265207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866087926242516102843471 8799131889363774154265207)
          ·
            refine ⟨13198697834045661231397811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799131889363774154265207 13198697834045661231397811)
            ·
              refine ⟨19798046751068491847096717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13198697834045661231397811 19798046751068491847096717)
              ·
                refine ⟨7424267531650684442661269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19798046751068491847096717 7424267531650684442661269)
                ·
                  refine ⟨348012540546125833249747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7424267531650684442661269 348012540546125833249747)
                  ·
                    rfl

theorem cell20_762471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_762471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762471 prefixEnd_762471 := by exact prefixLift 762471
  have htrace : WordTrace (prefixWord ++ tailWord_762471) baseStart_762471 baseEnd_762471 := by
    simpa [prefixWord, tailWord_762471, baseEnd_762471] using wordTrace_append hprefix tailTrace_762471
  have hstable : (prefixWord ++ tailWord_762471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762471).length < 2 ^ (prefixWord ++ tailWord_762471).sum := by decide
  have hdescent : baseEnd_762471 < baseStart_762471 := by decide
  rcases family_descends (prefixWord ++ tailWord_762471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762543 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 2]
def baseStart_762543 : Nat := 118140960795 + 762543 * 2 ^ 59
def prefixEnd_762543 : Nat := 4983230072969 + 3 ^ 40 * 762543 * 2
def baseEnd_762543 : Nat := 348045403308013582849453

theorem tailTrace_762543 : CollatzResearch.WordTrace tailWord_762543 prefixEnd_762543 348045403308013582849453 := by
  unfold tailWord_762543
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812228076444417821212283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18541485384296278547474855 27812228076444417821212283)
  ·
    refine ⟨41718342114666626731818425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27812228076444417821212283 41718342114666626731818425)
    ·
      refine ⟨31288756585999970048863819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41718342114666626731818425 31288756585999970048863819)
      ·
        refine ⟨46933134878999955073295729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31288756585999970048863819 46933134878999955073295729)
        ·
          refine ⟨35199851159249966304971797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46933134878999955073295729 35199851159249966304971797)
          ·
            refine ⟨1649993023089842170545553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35199851159249966304971797 1649993023089842170545553)
            ·
              refine ⟨1237494767317381627909165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649993023089842170545553 1237494767317381627909165)
              ·
                refine ⟨464060537744018110465937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1237494767317381627909165 464060537744018110465937)
                ·
                  refine ⟨348045403308013582849453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464060537744018110465937 348045403308013582849453)
                  ·
                    rfl

theorem cell20_762543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 2].length) (baseStart_762543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762543 prefixEnd_762543 := by exact prefixLift 762543
  have htrace : WordTrace (prefixWord ++ tailWord_762543) baseStart_762543 baseEnd_762543 := by
    simpa [prefixWord, tailWord_762543, baseEnd_762543] using wordTrace_append hprefix tailTrace_762543
  have hstable : (prefixWord ++ tailWord_762543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762543).length < 2 ^ (prefixWord ++ tailWord_762543).sum := by decide
  have hdescent : baseEnd_762543 < baseStart_762543 := by decide
  rcases family_descends (prefixWord ++ tailWord_762543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762554 : List Nat := [3, 1, 1, 1, 2, 3, 9]
def baseStart_762554 : Nat := 118140960795 + 762554 * 2 ^ 59
def prefixEnd_762554 : Nat := 4983230072969 + 3 ^ 40 * 762554 * 2
def baseEnd_762554 : Nat := 38672269334194048164749

theorem tailTrace_762554 : CollatzResearch.WordTrace tailWord_762554 prefixEnd_762554 38672269334194048164749 := by
  unfold tailWord_762554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953157319851141674965679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18541752852936377799908477 6953157319851141674965679)
  ·
    refine ⟨10429735979776712512448519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6953157319851141674965679 10429735979776712512448519)
    ·
      refine ⟨15644603969665068768672779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10429735979776712512448519 15644603969665068768672779)
      ·
        refine ⟨23466905954497603153009169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15644603969665068768672779 23466905954497603153009169)
        ·
          refine ⟨17600179465873202364756877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23466905954497603153009169 17600179465873202364756877)
          ·
            refine ⟨6600067299702450886783829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17600179465873202364756877 6600067299702450886783829)
            ·
              refine ⟨38672269334194048164749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6600067299702450886783829 38672269334194048164749)
              ·
                rfl

theorem cell20_762554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_762554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762554 prefixEnd_762554 := by exact prefixLift 762554
  have htrace : WordTrace (prefixWord ++ tailWord_762554) baseStart_762554 baseEnd_762554 := by
    simpa [prefixWord, tailWord_762554, baseEnd_762554] using wordTrace_append hprefix tailTrace_762554
  have hstable : (prefixWord ++ tailWord_762554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762554).length < 2 ^ (prefixWord ++ tailWord_762554).sum := by decide
  have hdescent : baseEnd_762554 < baseStart_762554 := by decide
  rcases family_descends (prefixWord ++ tailWord_762554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762557 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_762557 : Nat := 118140960795 + 762557 * 2 ^ 59
def prefixEnd_762557 : Nat := 4983230072969 + 3 ^ 40 * 762557 * 2
def baseEnd_762557 : Nat := 348051793289491756382729

theorem tailTrace_762557 : CollatzResearch.WordTrace tailWord_762557 prefixEnd_762557 348051793289491756382729 := by
  unfold tailWord_762557
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812738698393698212221925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18541825798929132141481283 27812738698393698212221925)
  ·
    refine ⟨5214888505948818414791611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27812738698393698212221925 5214888505948818414791611)
    ·
      refine ⟨7822332758923227622187417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5214888505948818414791611 7822332758923227622187417)
      ·
        refine ⟨5866749569192420716640563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7822332758923227622187417 5866749569192420716640563)
        ·
          refine ⟨8800124353788631074960845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866749569192420716640563 8800124353788631074960845)
          ·
            refine ⟨3300046632670736653110317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8800124353788631074960845 3300046632670736653110317)
            ·
              refine ⟨1237517487251526244916369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3300046632670736653110317 1237517487251526244916369)
              ·
                refine ⟨928138115438644683687277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237517487251526244916369 928138115438644683687277)
                ·
                  refine ⟨348051793289491756382729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928138115438644683687277 348051793289491756382729)
                  ·
                    rfl

theorem cell20_762557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_762557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762557 prefixEnd_762557 := by exact prefixLift 762557
  have htrace : WordTrace (prefixWord ++ tailWord_762557) baseStart_762557 baseEnd_762557 := by
    simpa [prefixWord, tailWord_762557, baseEnd_762557] using wordTrace_append hprefix tailTrace_762557
  have hstable : (prefixWord ++ tailWord_762557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762557).length < 2 ^ (prefixWord ++ tailWord_762557).sum := by decide
  have hdescent : baseEnd_762557 < baseStart_762557 := by decide
  rcases family_descends (prefixWord ++ tailWord_762557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762564 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_762564 : Nat := 118140960795 + 762564 * 2 ^ 59
def prefixEnd_762564 : Nat := 4983230072969 + 3 ^ 40 * 762564 * 2
def baseEnd_762564 : Nat := 348054988280230843149367

theorem tailTrace_762564 : CollatzResearch.WordTrace tailWord_762564 prefixEnd_762564 348054988280230843149367 := by
  unfold tailWord_762564
  simp only [CollatzResearch.WordTrace]
  refine ⟨13906497004684169203863373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18541996006245558938484497 13906497004684169203863373)
  ·
    refine ⟨5214936376756563451448765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13906497004684169203863373 5214936376756563451448765)
    ·
      refine ⟨1955601141283711294293287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5214936376756563451448765 1955601141283711294293287)
      ·
        refine ⟨2933401711925566941439931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955601141283711294293287 2933401711925566941439931)
        ·
          refine ⟨4400102567888350412159897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933401711925566941439931 4400102567888350412159897)
          ·
            refine ⟨3300076925916262809119923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4400102567888350412159897 3300076925916262809119923)
            ·
              refine ⟨4950115388874394213679885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300076925916262809119923 4950115388874394213679885)
              ·
                refine ⟨1856293270827897830129957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4950115388874394213679885 1856293270827897830129957)
                ·
                  refine ⟨348054988280230843149367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856293270827897830129957 348054988280230843149367)
                  ·
                    rfl

theorem cell20_762564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_762564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762564 prefixEnd_762564 := by exact prefixLift 762564
  have htrace : WordTrace (prefixWord ++ tailWord_762564) baseStart_762564 baseEnd_762564 := by
    simpa [prefixWord, tailWord_762564, baseEnd_762564] using wordTrace_append hprefix tailTrace_762564
  have hstable : (prefixWord ++ tailWord_762564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762564).length < 2 ^ (prefixWord ++ tailWord_762564).sum := by decide
  have hdescent : baseEnd_762564 < baseStart_762564 := by decide
  rcases family_descends (prefixWord ++ tailWord_762564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762574 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_762574 : Nat := 118140960795 + 762574 * 2 ^ 59
def prefixEnd_762574 : Nat := 4983230072969 + 3 ^ 40 * 762574 * 2
def baseEnd_762574 : Nat := 348059552552715252815993

theorem tailTrace_762574 : CollatzResearch.WordTrace tailWord_762574 prefixEnd_762574 348059552552715252815993 := by
  unfold tailWord_762574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476669842416513764448847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18542239159554740077060517 3476669842416513764448847)
  ·
    refine ⟨5215004763624770646673271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3476669842416513764448847 5215004763624770646673271)
    ·
      refine ⟨7822507145437155970009907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5215004763624770646673271 7822507145437155970009907)
      ·
        refine ⟨11733760718155733955014861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7822507145437155970009907 11733760718155733955014861)
        ·
          refine ⟨4400160269308400233130573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11733760718155733955014861 4400160269308400233130573)
          ·
            refine ⟨1650060100990650087423965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4400160269308400233130573 1650060100990650087423965)
            ·
              refine ⟨618772537871493782783987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1650060100990650087423965 618772537871493782783987)
              ·
                refine ⟨928158806807240674175981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618772537871493782783987 928158806807240674175981)
                ·
                  refine ⟨348059552552715252815993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928158806807240674175981 348059552552715252815993)
                  ·
                    rfl

theorem cell20_762574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_762574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762574 prefixEnd_762574 := by exact prefixLift 762574
  have htrace : WordTrace (prefixWord ++ tailWord_762574) baseStart_762574 baseEnd_762574 := by
    simpa [prefixWord, tailWord_762574, baseEnd_762574] using wordTrace_append hprefix tailTrace_762574
  have hstable : (prefixWord ++ tailWord_762574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762574).length < 2 ^ (prefixWord ++ tailWord_762574).sum := by decide
  have hdescent : baseEnd_762574 < baseStart_762574 := by decide
  rcases family_descends (prefixWord ++ tailWord_762574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762585 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_762585 : Nat := 118140960795 + 762585 * 2 ^ 59
def prefixEnd_762585 : Nat := 4983230072969 + 3 ^ 40 * 762585 * 2
def baseEnd_762585 : Nat := 348064573252448103449281

theorem tailTrace_762585 : CollatzResearch.WordTrace tailWord_762585 prefixEnd_762585 348064573252448103449281 := by
  unfold tailWord_762585
  simp only [CollatzResearch.WordTrace]
  refine ⟨27813759942292258994241209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18542506628194839329494139 27813759942292258994241209)
  ·
    refine ⟨20860319956719194245680907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27813759942292258994241209 20860319956719194245680907)
    ·
      refine ⟨31290479935078791368521361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20860319956719194245680907 31290479935078791368521361)
      ·
        refine ⟨23467859951309093526391021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31290479935078791368521361 23467859951309093526391021)
        ·
          refine ⟨8800447481740910072396633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23467859951309093526391021 8800447481740910072396633)
          ·
            refine ⟨6600335611305682554297475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8800447481740910072396633 6600335611305682554297475)
            ·
              refine ⟨9900503416958523831446213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600335611305682554297475 9900503416958523831446213)
              ·
                refine ⟨1856344390679723218396165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9900503416958523831446213 1856344390679723218396165)
                ·
                  refine ⟨348064573252448103449281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856344390679723218396165 348064573252448103449281)
                  ·
                    rfl

theorem cell20_762585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_762585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762585 prefixEnd_762585 := by exact prefixLift 762585
  have htrace : WordTrace (prefixWord ++ tailWord_762585) baseStart_762585 baseEnd_762585 := by
    simpa [prefixWord, tailWord_762585, baseEnd_762585] using wordTrace_append hprefix tailTrace_762585
  have hstable : (prefixWord ++ tailWord_762585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762585).length < 2 ^ (prefixWord ++ tailWord_762585).sum := by decide
  have hdescent : baseEnd_762585 < baseStart_762585 := by decide
  rcases family_descends (prefixWord ++ tailWord_762585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762588 : List Nat := [2, 2, 5, 1, 1, 2, 1, 6]
def baseStart_762588 : Nat := 118140960795 + 762588 * 2 ^ 59
def prefixEnd_762588 : Nat := 4983230072969 + 3 ^ 40 * 762588 * 2
def baseEnd_762588 : Nat := 116021980844731142116423

theorem tailTrace_762588 : CollatzResearch.WordTrace tailWord_762588 prefixEnd_762588 116021980844731142116423 := by
  unfold tailWord_762588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13906934680640695253300209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18542579574187593671066945 13906934680640695253300209)
  ·
    refine ⟨10430201010480521439975157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13906934680640695253300209 10430201010480521439975157)
    ·
      refine ⟨977831344732548884997671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10430201010480521439975157 977831344732548884997671)
      ·
        refine ⟨1466747017098823327496507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977831344732548884997671 1466747017098823327496507)
        ·
          refine ⟨2200120525648234991244761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466747017098823327496507 2200120525648234991244761)
          ·
            refine ⟨1650090394236176243433571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200120525648234991244761 1650090394236176243433571)
            ·
              refine ⟨2475135591354264365150357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650090394236176243433571 2475135591354264365150357)
              ·
                refine ⟨116021980844731142116423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2475135591354264365150357 116021980844731142116423)
                ·
                  rfl

theorem cell20_762588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_762588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762588 prefixEnd_762588 := by exact prefixLift 762588
  have htrace : WordTrace (prefixWord ++ tailWord_762588) baseStart_762588 baseEnd_762588 := by
    simpa [prefixWord, tailWord_762588, baseEnd_762588] using wordTrace_append hprefix tailTrace_762588
  have hstable : (prefixWord ++ tailWord_762588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762588).length < 2 ^ (prefixWord ++ tailWord_762588).sum := by decide
  have hdescent : baseEnd_762588 < baseStart_762588 := by decide
  rcases family_descends (prefixWord ++ tailWord_762588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762616 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_762616 : Nat := 118140960795 + 762616 * 2 ^ 59
def prefixEnd_762616 : Nat := 4983230072969 + 3 ^ 40 * 762616 * 2
def baseEnd_762616 : Nat := 348078722497149773415821

theorem tailTrace_762616 : CollatzResearch.WordTrace tailWord_762616 prefixEnd_762616 348078722497149773415821 := by
  unfold tailWord_762616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13907445302589975644309851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18543260403453300859079801 13907445302589975644309851)
  ·
    refine ⟨20861167953884963466464777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13907445302589975644309851 20861167953884963466464777)
    ·
      refine ⟨15645875965413722599848583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20861167953884963466464777 15645875965413722599848583)
      ·
        refine ⟨23468813948120583899772875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15645875965413722599848583 23468813948120583899772875)
        ·
          refine ⟨35203220922180875849659313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23468813948120583899772875 35203220922180875849659313)
          ·
            refine ⟨26402415691635656887244485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35203220922180875849659313 26402415691635656887244485)
            ·
              refine ⟨4950452942181685666358341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26402415691635656887244485 4950452942181685666358341)
              ·
                refine ⟨928209926659066062442189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4950452942181685666358341 928209926659066062442189)
                ·
                  refine ⟨348078722497149773415821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928209926659066062442189 348078722497149773415821)
                  ·
                    rfl

theorem cell20_762616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_762616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762616 prefixEnd_762616 := by exact prefixLift 762616
  have htrace : WordTrace (prefixWord ++ tailWord_762616) baseStart_762616 baseEnd_762616 := by
    simpa [prefixWord, tailWord_762616, baseEnd_762616] using wordTrace_append hprefix tailTrace_762616
  have hstable : (prefixWord ++ tailWord_762616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762616).length < 2 ^ (prefixWord ++ tailWord_762616).sum := by decide
  have hdescent : baseEnd_762616 < baseStart_762616 := by decide
  rcases family_descends (prefixWord ++ tailWord_762616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762626 : List Nat := [3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_762626 : Nat := 118140960795 + 762626 * 2 ^ 59
def prefixEnd_762626 : Nat := 4983230072969 + 3 ^ 40 * 762626 * 2
def baseEnd_762626 : Nat := 116027762256544727694149

theorem tailTrace_762626 : CollatzResearch.WordTrace tailWord_762626 prefixEnd_762626 116027762256544727694149 := by
  unfold tailWord_762626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953813833785930749120933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18543503556762481997655821 6953813833785930749120933)
  ·
    refine ⟨1303840093834862015460175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6953813833785930749120933 1303840093834862015460175)
    ·
      refine ⟨1955760140752293023190263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303840093834862015460175 1955760140752293023190263)
      ·
        refine ⟨2933640211128439534785395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955760140752293023190263 2933640211128439534785395)
        ·
          refine ⟨4400460316692659302178093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933640211128439534785395 4400460316692659302178093)
          ·
            refine ⟨1650172618759747238316785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4400460316692659302178093 1650172618759747238316785)
            ·
              refine ⟨1237629464069810428737589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650172618759747238316785 1237629464069810428737589)
              ·
                refine ⟨116027762256544727694149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1237629464069810428737589 116027762256544727694149)
                ·
                  rfl

theorem cell20_762626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_762626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762626 prefixEnd_762626 := by exact prefixLift 762626
  have htrace : WordTrace (prefixWord ++ tailWord_762626) baseStart_762626 baseEnd_762626 := by
    simpa [prefixWord, tailWord_762626, baseEnd_762626] using wordTrace_append hprefix tailTrace_762626
  have hstable : (prefixWord ++ tailWord_762626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762626).length < 2 ^ (prefixWord ++ tailWord_762626).sum := by decide
  have hdescent : baseEnd_762626 < baseStart_762626 := by decide
  rcases family_descends (prefixWord ++ tailWord_762626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762633 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 3]
def baseStart_762633 : Nat := 118140960795 + 762633 * 2 ^ 59
def prefixEnd_762633 : Nat := 4983230072969 + 3 ^ 40 * 762633 * 2
def baseEnd_762633 : Nat := 348086481760373269849085

theorem tailTrace_762633 : CollatzResearch.WordTrace tailWord_762633 prefixEnd_762633 348086481760373269849085 := by
  unfold tailWord_762633
  simp only [CollatzResearch.WordTrace]
  refine ⟨27815510646118363191988553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18543673764078908794659035 27815510646118363191988553)
  ·
    refine ⟨20861632984588772393991415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27815510646118363191988553 20861632984588772393991415)
    ·
      refine ⟨31292449476883158590987123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20861632984588772393991415 31292449476883158590987123)
      ·
        refine ⟨46938674215324737886480685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31292449476883158590987123 46938674215324737886480685)
        ·
          refine ⟨17602002830746776707430257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46938674215324737886480685 17602002830746776707430257)
          ·
            refine ⟨13201502123060082530572693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17602002830746776707430257 13201502123060082530572693)
            ·
              refine ⟨618820412018441368620595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13201502123060082530572693 618820412018441368620595)
              ·
                refine ⟨928230618027662052930893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618820412018441368620595 928230618027662052930893)
                ·
                  refine ⟨348086481760373269849085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928230618027662052930893 348086481760373269849085)
                  ·
                    rfl

theorem cell20_762633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_762633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762633 prefixEnd_762633 := by exact prefixLift 762633
  have htrace : WordTrace (prefixWord ++ tailWord_762633) baseStart_762633 baseEnd_762633 := by
    simpa [prefixWord, tailWord_762633, baseEnd_762633] using wordTrace_append hprefix tailTrace_762633
  have hstable : (prefixWord ++ tailWord_762633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762633).length < 2 ^ (prefixWord ++ tailWord_762633).sum := by decide
  have hdescent : baseEnd_762633 < baseStart_762633 := by decide
  rcases family_descends (prefixWord ++ tailWord_762633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762737 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_762737 : Nat := 118140960795 + 762737 * 2 ^ 59
def prefixEnd_762737 : Nat := 4983230072969 + 3 ^ 40 * 762737 * 2
def baseEnd_762737 : Nat := 348133950194211130381993

theorem tailTrace_762737 : CollatzResearch.WordTrace tailWord_762737 prefixEnd_762737 348133950194211130381993 := by
  unfold tailWord_762737
  simp only [CollatzResearch.WordTrace]
  refine ⟨27819303837741588953774465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18546202558494392635849643 27819303837741588953774465)
  ·
    refine ⟨20864477878306191715330849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27819303837741588953774465 20864477878306191715330849)
    ·
      refine ⟨15648358408729643786498137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20864477878306191715330849 15648358408729643786498137)
      ·
        refine ⟨11736268806547232839873603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15648358408729643786498137 11736268806547232839873603)
        ·
          refine ⟨17604403209820849259810405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736268806547232839873603 17604403209820849259810405)
          ·
            refine ⟨3300825601841409236214451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17604403209820849259810405 3300825601841409236214451)
            ·
              refine ⟨4951238402762113854321677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300825601841409236214451 4951238402762113854321677)
              ·
                refine ⟨1856714401035792695370629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4951238402762113854321677 1856714401035792695370629)
                ·
                  refine ⟨348133950194211130381993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856714401035792695370629 348133950194211130381993)
                  ·
                    rfl

theorem cell20_762737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_762737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762737 prefixEnd_762737 := by exact prefixLift 762737
  have htrace : WordTrace (prefixWord ++ tailWord_762737) baseStart_762737 baseEnd_762737 := by
    simpa [prefixWord, tailWord_762737, baseEnd_762737] using wordTrace_append hprefix tailTrace_762737
  have hstable : (prefixWord ++ tailWord_762737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762737).length < 2 ^ (prefixWord ++ tailWord_762737).sum := by decide
  have hdescent : baseEnd_762737 < baseStart_762737 := by decide
  rcases family_descends (prefixWord ++ tailWord_762737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762761 : List Nat := [1, 2, 1, 1, 5, 2, 4, 4]
def baseStart_762761 : Nat := 118140960795 + 762761 * 2 ^ 59
def prefixEnd_762761 : Nat := 4983230072969 + 3 ^ 40 * 762761 * 2
def baseEnd_762761 : Nat := 116048301482724571193965

theorem tailTrace_762761 : CollatzResearch.WordTrace tailWord_762761 prefixEnd_762761 116048301482724571193965 := by
  unfold tailWord_762761
  simp only [CollatzResearch.WordTrace]
  refine ⟨27820179189654641052648137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18546786126436427368432091 27820179189654641052648137)
  ·
    refine ⟨20865134392240980789486103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27820179189654641052648137 20865134392240980789486103)
    ·
      refine ⟨31297701588361471184229155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20865134392240980789486103 31297701588361471184229155)
      ·
        refine ⟨46946552382542206776343733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31297701588361471184229155 46946552382542206776343733)
        ·
          refine ⟨4401239285863331885282225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46946552382542206776343733 4401239285863331885282225)
          ·
            refine ⟨3300929464397498913961669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4401239285863331885282225 3300929464397498913961669)
            ·
              refine ⟨618924274574531046367813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3300929464397498913961669 618924274574531046367813)
              ·
                refine ⟨116048301482724571193965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618924274574531046367813 116048301482724571193965)
                ·
                  rfl

theorem cell20_762761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_762761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762761 prefixEnd_762761 := by exact prefixLift 762761
  have htrace : WordTrace (prefixWord ++ tailWord_762761) baseStart_762761 baseEnd_762761 := by
    simpa [prefixWord, tailWord_762761, baseEnd_762761] using wordTrace_append hprefix tailTrace_762761
  have hstable : (prefixWord ++ tailWord_762761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762761).length < 2 ^ (prefixWord ++ tailWord_762761).sum := by decide
  have hdescent : baseEnd_762761 < baseStart_762761 := by decide
  rcases family_descends (prefixWord ++ tailWord_762761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762778 : List Nat := [3, 1, 1, 4, 4, 1, 6]
def baseStart_762778 : Nat := 118140960795 + 762778 * 2 ^ 59
def prefixEnd_762778 : Nat := 4983230072969 + 3 ^ 40 * 762778 * 2
def baseEnd_762778 : Nat := 38683629301266356668351

theorem tailTrace_762778 : CollatzResearch.WordTrace tailWord_762778 prefixEnd_762778 38683629301266356668351 := by
  unfold tailWord_762778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6955199807648263239004247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18547199487062035304011325 6955199807648263239004247)
  ·
    refine ⟨10432799711472394858506371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6955199807648263239004247 10432799711472394858506371)
    ·
      refine ⟨15649199567208592287759557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10432799711472394858506371 15649199567208592287759557)
      ·
        refine ⟨2934224918851611053954917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15649199567208592287759557 2934224918851611053954917)
        ·
          refine ⟨550167172284677072616547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2934224918851611053954917 550167172284677072616547)
          ·
            refine ⟨825250758427015608924821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550167172284677072616547 825250758427015608924821)
            ·
              refine ⟨38683629301266356668351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 825250758427015608924821 38683629301266356668351)
              ·
                rfl

theorem cell20_762778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 6].length) (baseStart_762778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762778 prefixEnd_762778 := by exact prefixLift 762778
  have htrace : WordTrace (prefixWord ++ tailWord_762778) baseStart_762778 baseEnd_762778 := by
    simpa [prefixWord, tailWord_762778, baseEnd_762778] using wordTrace_append hprefix tailTrace_762778
  have hstable : (prefixWord ++ tailWord_762778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762778).length < 2 ^ (prefixWord ++ tailWord_762778).sum := by decide
  have hdescent : baseEnd_762778 < baseStart_762778 := by decide
  rcases family_descends (prefixWord ++ tailWord_762778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762837 : List Nat := [1, 3, 2, 3, 4, 7]
def baseStart_762837 : Nat := 118140960795 + 762837 * 2 ^ 59
def prefixEnd_762837 : Nat := 4983230072969 + 3 ^ 40 * 762837 * 2
def baseEnd_762837 : Nat := 12895540478483526927713

theorem tailTrace_762837 : CollatzResearch.WordTrace tailWord_762837 prefixEnd_762837 12895540478483526927713 := by
  unfold tailWord_762837
  simp only [CollatzResearch.WordTrace]
  refine ⟨27822951137379306032414765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18548634091586204021609843 27822951137379306032414765)
  ·
    refine ⟨10433606676517239762155537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27822951137379306032414765 10433606676517239762155537)
    ·
      refine ⟨7825205007387929821616653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10433606676517239762155537 7825205007387929821616653)
      ·
        refine ⟨2934451877770473683106245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7825205007387929821616653 2934451877770473683106245)
        ·
          refine ⟨550209727081963815582421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2934451877770473683106245 550209727081963815582421)
          ·
            refine ⟨12895540478483526927713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 550209727081963815582421 12895540478483526927713)
            ·
              rfl

theorem cell20_762837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 7].length) (baseStart_762837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762837 prefixEnd_762837 := by exact prefixLift 762837
  have htrace : WordTrace (prefixWord ++ tailWord_762837) baseStart_762837 baseEnd_762837 := by
    simpa [prefixWord, tailWord_762837, baseEnd_762837] using wordTrace_append hprefix tailTrace_762837
  have hstable : (prefixWord ++ tailWord_762837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762837).length < 2 ^ (prefixWord ++ tailWord_762837).sum := by decide
  have hdescent : baseEnd_762837 < baseStart_762837 := by decide
  rcases family_descends (prefixWord ++ tailWord_762837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762847 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 2]
def baseStart_762847 : Nat := 118140960795 + 762847 * 2 ^ 59
def prefixEnd_762847 : Nat := 4983230072969 + 3 ^ 40 * 762847 * 2
def baseEnd_762847 : Nat := 348184157191539636714877

theorem tailTrace_762847 : CollatzResearch.WordTrace tailWord_762847 prefixEnd_762847 348184157191539636714877 := by
  unfold tailWord_762847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27823315867343077740278795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18548877244895385160185863 27823315867343077740278795)
  ·
    refine ⟨41734973801014616610418193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27823315867343077740278795 41734973801014616610418193)
    ·
      refine ⟨31301230350760962457813645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41734973801014616610418193 31301230350760962457813645)
      ·
        refine ⟨11737961381535360921680117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31301230350760962457813645 11737961381535360921680117)
        ·
          refine ⟨1100433879518940086407511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11737961381535360921680117 1100433879518940086407511)
          ·
            refine ⟨1650650819278410129611267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100433879518940086407511 1650650819278410129611267)
            ·
              refine ⟨2475976228917615194416901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650650819278410129611267 2475976228917615194416901)
              ·
                refine ⟨464245542922052848953169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2475976228917615194416901 464245542922052848953169)
                ·
                  refine ⟨348184157191539636714877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464245542922052848953169 348184157191539636714877)
                  ·
                    rfl

theorem cell20_762847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 2].length) (baseStart_762847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762847 prefixEnd_762847 := by exact prefixLift 762847
  have htrace : WordTrace (prefixWord ++ tailWord_762847) baseStart_762847 baseEnd_762847 := by
    simpa [prefixWord, tailWord_762847, baseEnd_762847] using wordTrace_append hprefix tailTrace_762847
  have hstable : (prefixWord ++ tailWord_762847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762847).length < 2 ^ (prefixWord ++ tailWord_762847).sum := by decide
  have hdescent : baseEnd_762847 < baseStart_762847 := by decide
  rcases family_descends (prefixWord ++ tailWord_762847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762851 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_762851 : Nat := 118140960795 + 762851 * 2 ^ 59
def prefixEnd_762851 : Nat := 4983230072969 + 3 ^ 40 * 762851 * 2
def baseEnd_762851 : Nat := 348185982900533400581527

theorem tailTrace_762851 : CollatzResearch.WordTrace tailWord_762851 prefixEnd_762851 348185982900533400581527 := by
  unfold tailWord_762851
  simp only [CollatzResearch.WordTrace]
  refine ⟨27823461759328586423424407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18548974506219057615616271 27823461759328586423424407)
  ·
    refine ⟨41735192638992879635136611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27823461759328586423424407 41735192638992879635136611)
    ·
      refine ⟨62602788958489319452704917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41735192638992879635136611 62602788958489319452704917)
      ·
        refine ⟨2934505732429186849345543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62602788958489319452704917 2934505732429186849345543)
        ·
          refine ⟨4401758598643780274018315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934505732429186849345543 4401758598643780274018315)
          ·
            refine ⟨6602637897965670411027473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401758598643780274018315 6602637897965670411027473)
            ·
              refine ⟨4951978423474252808270605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6602637897965670411027473 4951978423474252808270605)
              ·
                refine ⟨1856991908802844803101477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4951978423474252808270605 1856991908802844803101477)
                ·
                  refine ⟨348185982900533400581527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856991908802844803101477 348185982900533400581527)
                  ·
                    rfl

theorem cell20_762851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_762851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762851 prefixEnd_762851 := by exact prefixLift 762851
  have htrace : WordTrace (prefixWord ++ tailWord_762851) baseStart_762851 baseEnd_762851 := by
    simpa [prefixWord, tailWord_762851, baseEnd_762851] using wordTrace_append hprefix tailTrace_762851
  have hstable : (prefixWord ++ tailWord_762851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762851).length < 2 ^ (prefixWord ++ tailWord_762851).sum := by decide
  have hdescent : baseEnd_762851 < baseStart_762851 := by decide
  rcases family_descends (prefixWord ++ tailWord_762851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762906 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_762906 : Nat := 118140960795 + 762906 * 2 ^ 59
def prefixEnd_762906 : Nat := 4983230072969 + 3 ^ 40 * 762906 * 2
def baseEnd_762906 : Nat := 348211086399197653747969

theorem tailTrace_762906 : CollatzResearch.WordTrace tailWord_762906 prefixEnd_762906 348211086399197653747969 := by
  unfold tailWord_762906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956366943532332704169143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18550311849419553877784381 6956366943532332704169143)
  ·
    refine ⟨10434550415298499056253715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6956366943532332704169143 10434550415298499056253715)
    ·
      refine ⟨15651825622947748584380573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10434550415298499056253715 15651825622947748584380573)
      ·
        refine ⟨5869434608605405719142715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15651825622947748584380573 5869434608605405719142715)
        ·
          refine ⟨8804151912908108578714073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869434608605405719142715 8804151912908108578714073)
          ·
            refine ⟨6603113934681081434035555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804151912908108578714073 6603113934681081434035555)
            ·
              refine ⟨9904670902021622151053333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603113934681081434035555 9904670902021622151053333)
              ·
                refine ⟨464281448532263538330625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9904670902021622151053333 464281448532263538330625)
                ·
                  refine ⟨348211086399197653747969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464281448532263538330625 348211086399197653747969)
                  ·
                    rfl

theorem cell20_762906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_762906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762906 prefixEnd_762906 := by exact prefixLift 762906
  have htrace : WordTrace (prefixWord ++ tailWord_762906) baseStart_762906 baseEnd_762906 := by
    simpa [prefixWord, tailWord_762906, baseEnd_762906] using wordTrace_append hprefix tailTrace_762906
  have hstable : (prefixWord ++ tailWord_762906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762906).length < 2 ^ (prefixWord ++ tailWord_762906).sum := by decide
  have hdescent : baseEnd_762906 < baseStart_762906 := by decide
  rcases family_descends (prefixWord ++ tailWord_762906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762916 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_762916 : Nat := 118140960795 + 762916 * 2 ^ 59
def prefixEnd_762916 : Nat := 4983230072969 + 3 ^ 40 * 762916 * 2
def baseEnd_762916 : Nat := 348215650671682063414595

theorem tailTrace_762916 : CollatzResearch.WordTrace tailWord_762916 prefixEnd_762916 348215650671682063414595 := by
  unfold tailWord_762916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13912916252046551262270301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18550555002728735016360401 13912916252046551262270301)
  ·
    refine ⟨5217343594517456723351363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13912916252046551262270301 5217343594517456723351363)
    ·
      refine ⟨7826015391776185085027045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217343594517456723351363 7826015391776185085027045)
      ·
        refine ⟨1467377885958034703442571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7826015391776185085027045 1467377885958034703442571)
        ·
          refine ⟨2201066828937052055163857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467377885958034703442571 2201066828937052055163857)
          ·
            refine ⟨1650800121702789041372893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201066828937052055163857 1650800121702789041372893)
            ·
              refine ⟨619050045638545890514835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1650800121702789041372893 619050045638545890514835)
              ·
                refine ⟨928575068457818835772253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619050045638545890514835 928575068457818835772253)
                ·
                  refine ⟨348215650671682063414595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928575068457818835772253 348215650671682063414595)
                  ·
                    rfl

theorem cell20_762916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_762916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762916 prefixEnd_762916 := by exact prefixLift 762916
  have htrace : WordTrace (prefixWord ++ tailWord_762916) baseStart_762916 baseEnd_762916 := by
    simpa [prefixWord, tailWord_762916, baseEnd_762916] using wordTrace_append hprefix tailTrace_762916
  have hstable : (prefixWord ++ tailWord_762916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762916).length < 2 ^ (prefixWord ++ tailWord_762916).sum := by decide
  have hdescent : baseEnd_762916 < baseStart_762916 := by decide
  rcases family_descends (prefixWord ++ tailWord_762916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_762958 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_762958 : Nat := 118140960795 + 762958 * 2 ^ 59
def prefixEnd_762958 : Nat := 4983230072969 + 3 ^ 40 * 762958 * 2
def baseEnd_762958 : Nat := 348234820616116584014423

theorem tailTrace_762958 : CollatzResearch.WordTrace tailWord_762958 prefixEnd_762958 348234820616116584014423 := by
  unfold tailWord_762958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478420546242617962196191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18551576246627295798379685 3478420546242617962196191)
  ·
    refine ⟨5217630819363926943294287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3478420546242617962196191 5217630819363926943294287)
    ·
      refine ⟨7826446229045890414941431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217630819363926943294287 7826446229045890414941431)
      ·
        refine ⟨11739669343568835622412147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7826446229045890414941431 11739669343568835622412147)
        ·
          refine ⟨17609504015353253433618221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11739669343568835622412147 17609504015353253433618221)
          ·
            refine ⟨6603564005757470037606833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17609504015353253433618221 6603564005757470037606833)
            ·
              refine ⟨4952673004318102528205125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603564005757470037606833 4952673004318102528205125)
              ·
                refine ⟨928626188309644224038461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4952673004318102528205125 928626188309644224038461)
                ·
                  refine ⟨348234820616116584014423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928626188309644224038461 348234820616116584014423)
                  ·
                    rfl

theorem cell20_762958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_762958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_762958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_762958 prefixEnd_762958 := by exact prefixLift 762958
  have htrace : WordTrace (prefixWord ++ tailWord_762958) baseStart_762958 baseEnd_762958 := by
    simpa [prefixWord, tailWord_762958, baseEnd_762958] using wordTrace_append hprefix tailTrace_762958
  have hstable : (prefixWord ++ tailWord_762958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_762958).length < 2 ^ (prefixWord ++ tailWord_762958).sum := by decide
  have hdescent : baseEnd_762958 < baseStart_762958 := by decide
  rcases family_descends (prefixWord ++ tailWord_762958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763006 : List Nat := [4, 2, 4, 1, 9]
def baseStart_763006 : Nat := 118140960795 + 763006 * 2 ^ 59
def prefixEnd_763006 : Nat := 4983230072969 + 3 ^ 40 * 763006 * 2
def baseEnd_763006 : Nat := 4299465791654836424867

theorem tailTrace_763006 : CollatzResearch.WordTrace tailWord_763006 prefixEnd_763006 4299465791654836424867 := by
  unfold tailWord_763006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478639384220880986914609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18552743382511365263544581 3478639384220880986914609)
  ·
    refine ⟨2608979538165660740185957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3478639384220880986914609 2608979538165660740185957)
    ·
      refine ⟨489183663406061388784867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2608979538165660740185957 489183663406061388784867)
      ·
        refine ⟨733775495109092083177301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489183663406061388784867 733775495109092083177301)
        ·
          refine ⟨4299465791654836424867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 733775495109092083177301 4299465791654836424867)
          ·
            rfl

theorem cell20_763006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 9].length) (baseStart_763006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763006 prefixEnd_763006 := by exact prefixLift 763006
  have htrace : WordTrace (prefixWord ++ tailWord_763006) baseStart_763006 baseEnd_763006 := by
    simpa [prefixWord, tailWord_763006, baseEnd_763006] using wordTrace_append hprefix tailTrace_763006
  have hstable : (prefixWord ++ tailWord_763006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763006).length < 2 ^ (prefixWord ++ tailWord_763006).sum := by decide
  have hdescent : baseEnd_763006 < baseStart_763006 := by decide
  rcases family_descends (prefixWord ++ tailWord_763006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763013 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_763013 : Nat := 118140960795 + 763013 * 2 ^ 59
def prefixEnd_763013 : Nat := 4983230072969 + 3 ^ 40 * 763013 * 2
def baseEnd_763013 : Nat := 348259924114780837180865

theorem tailTrace_763013 : CollatzResearch.WordTrace tailWord_763013 prefixEnd_763013 348259924114780837180865 := by
  unfold tailWord_763013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27829370384741688090821693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18552913589827792060547795 27829370384741688090821693)
  ·
    refine ⟨10436013894278133034058135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27829370384741688090821693 10436013894278133034058135)
    ·
      refine ⟨15654020841417199551087203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10436013894278133034058135 15654020841417199551087203)
      ·
        refine ⟨23481031262125799326630805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15654020841417199551087203 23481031262125799326630805)
        ·
          refine ⟨1100673340412146843435819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23481031262125799326630805 1100673340412146843435819)
          ·
            refine ⟨1651010010618220265153729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100673340412146843435819 1651010010618220265153729)
            ·
              refine ⟨1238257507963665198865297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651010010618220265153729 1238257507963665198865297)
              ·
                refine ⟨928693130972748899148973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238257507963665198865297 928693130972748899148973)
                ·
                  refine ⟨348259924114780837180865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928693130972748899148973 348259924114780837180865)
                  ·
                    rfl

theorem cell20_763013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_763013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763013 prefixEnd_763013 := by exact prefixLift 763013
  have htrace : WordTrace (prefixWord ++ tailWord_763013) baseStart_763013 baseEnd_763013 := by
    simpa [prefixWord, tailWord_763013, baseEnd_763013] using wordTrace_append hprefix tailTrace_763013
  have hstable : (prefixWord ++ tailWord_763013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763013).length < 2 ^ (prefixWord ++ tailWord_763013).sum := by decide
  have hdescent : baseEnd_763013 < baseStart_763013 := by decide
  rcases family_descends (prefixWord ++ tailWord_763013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763041 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_763041 : Nat := 118140960795 + 763041 * 2 ^ 59
def prefixEnd_763041 : Nat := 4983230072969 + 3 ^ 40 * 763041 * 2
def baseEnd_763041 : Nat := 348272704077737184247417

theorem tailTrace_763041 : CollatzResearch.WordTrace tailWord_763041 prefixEnd_763041 348272704077737184247417 := by
  unfold tailWord_763041
  simp only [CollatzResearch.WordTrace]
  refine ⟨27830391628640248872840977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18553594419093499248560651 27830391628640248872840977)
  ·
    refine ⟨20872793721480186654630733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27830391628640248872840977 20872793721480186654630733)
    ·
      refine ⟨7827297645555069995486525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20872793721480186654630733 7827297645555069995486525)
      ·
        refine ⟨2935236617083151248307447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7827297645555069995486525 2935236617083151248307447)
        ·
          refine ⟨4402854925624726872461171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935236617083151248307447 4402854925624726872461171)
          ·
            refine ⟨6604282388437090308691757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402854925624726872461171 6604282388437090308691757)
            ·
              refine ⟨2476605895663908865759409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6604282388437090308691757 2476605895663908865759409)
              ·
                refine ⟨1857454421747931649319557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2476605895663908865759409 1857454421747931649319557)
                ·
                  refine ⟨348272704077737184247417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857454421747931649319557 348272704077737184247417)
                  ·
                    rfl

theorem cell20_763041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_763041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763041 prefixEnd_763041 := by exact prefixLift 763041
  have htrace : WordTrace (prefixWord ++ tailWord_763041) baseStart_763041 baseEnd_763041 := by
    simpa [prefixWord, tailWord_763041, baseEnd_763041] using wordTrace_append hprefix tailTrace_763041
  have hstable : (prefixWord ++ tailWord_763041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763041).length < 2 ^ (prefixWord ++ tailWord_763041).sum := by decide
  have hdescent : baseEnd_763041 < baseStart_763041 := by decide
  rcases family_descends (prefixWord ++ tailWord_763041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763058 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_763058 : Nat := 118140960795 + 763058 * 2 ^ 59
def prefixEnd_763058 : Nat := 4983230072969 + 3 ^ 40 * 763058 * 2
def baseEnd_763058 : Nat := 348280463340960680680681

theorem tailTrace_763058 : CollatzResearch.WordTrace tailWord_763058 prefixEnd_763058 348280463340960680680681 := by
  unfold tailWord_763058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957752917394665194052457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18554007779719107184139885 6957752917394665194052457)
  ·
    refine ⟨5218314688045998895539343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6957752917394665194052457 5218314688045998895539343)
    ·
      refine ⟨7827472032068998343309015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218314688045998895539343 7827472032068998343309015)
      ·
        refine ⟨11741208048103497514963523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827472032068998343309015 11741208048103497514963523)
        ·
          refine ⟨17611812072155246272445285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11741208048103497514963523 17611812072155246272445285)
          ·
            refine ⟨3302214763529108676083491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17611812072155246272445285 3302214763529108676083491)
            ·
              refine ⟨4953322145293663014125237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302214763529108676083491 4953322145293663014125237)
              ·
                refine ⟨464373951121280907574241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4953322145293663014125237 464373951121280907574241)
                ·
                  refine ⟨348280463340960680680681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464373951121280907574241 348280463340960680680681)
                  ·
                    rfl

theorem cell20_763058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_763058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763058 prefixEnd_763058 := by exact prefixLift 763058
  have htrace : WordTrace (prefixWord ++ tailWord_763058) baseStart_763058 baseEnd_763058 := by
    simpa [prefixWord, tailWord_763058, baseEnd_763058] using wordTrace_append hprefix tailTrace_763058
  have hstable : (prefixWord ++ tailWord_763058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763058).length < 2 ^ (prefixWord ++ tailWord_763058).sum := by decide
  have hdescent : baseEnd_763058 < baseStart_763058 := by decide
  rcases family_descends (prefixWord ++ tailWord_763058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763072 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_763072 : Nat := 118140960795 + 763072 * 2 ^ 59
def prefixEnd_763072 : Nat := 4983230072969 + 3 ^ 40 * 763072 * 2
def baseEnd_763072 : Nat := 348286853322438854213957

theorem tailTrace_763072 : CollatzResearch.WordTrace tailWord_763072 prefixEnd_763072 348286853322438854213957 := by
  unfold tailWord_763072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13915761145763970583609735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18554348194351960778146313 13915761145763970583609735)
  ·
    refine ⟨20873641718645955875414603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13915761145763970583609735 20873641718645955875414603)
    ·
      refine ⟨31310462577968933813121905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20873641718645955875414603 31310462577968933813121905)
      ·
        refine ⟨23482846933476700359841429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31310462577968933813121905 23482846933476700359841429)
        ·
          refine ⟨1100758450006720329367567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23482846933476700359841429 1100758450006720329367567)
          ·
            refine ⟨1651137675010080494051351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100758450006720329367567 1651137675010080494051351)
            ·
              refine ⟨2476706512515120741077027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651137675010080494051351 2476706512515120741077027)
              ·
                refine ⟨3715059768772681111615541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476706512515120741077027 3715059768772681111615541)
                ·
                  refine ⟨348286853322438854213957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3715059768772681111615541 348286853322438854213957)
                  ·
                    rfl

theorem cell20_763072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_763072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763072 prefixEnd_763072 := by exact prefixLift 763072
  have htrace : WordTrace (prefixWord ++ tailWord_763072) baseStart_763072 baseEnd_763072 := by
    simpa [prefixWord, tailWord_763072, baseEnd_763072] using wordTrace_append hprefix tailTrace_763072
  have hstable : (prefixWord ++ tailWord_763072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763072).length < 2 ^ (prefixWord ++ tailWord_763072).sum := by decide
  have hdescent : baseEnd_763072 < baseStart_763072 := by decide
  rcases family_descends (prefixWord ++ tailWord_763072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763134 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_763134 : Nat := 118140960795 + 763134 * 2 ^ 59
def prefixEnd_763134 : Nat := 4983230072969 + 3 ^ 40 * 763134 * 2
def baseEnd_763134 : Nat := 348315151811842194147037

theorem tailTrace_763134 : CollatzResearch.WordTrace tailWord_763134 prefixEnd_763134 348315151811842194147037 := by
  unfold tailWord_763134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479222952162915719497057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18555855744868883837317637 3479222952162915719497057)
  ·
    refine ⟨2609417214122186789622793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3479222952162915719497057 2609417214122186789622793)
    ·
      refine ⟨1957062910591640092217095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2609417214122186789622793 1957062910591640092217095)
      ·
        refine ⟨2935594365887460138325643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957062910591640092217095 2935594365887460138325643)
        ·
          refine ⟨4403391548831190207488465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935594365887460138325643 4403391548831190207488465)
          ·
            refine ⟨3302543661623392655616349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403391548831190207488465 3302543661623392655616349)
            ·
              refine ⟨1238453873108772245856131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302543661623392655616349 1238453873108772245856131)
              ·
                refine ⟨1857680809663158368784197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238453873108772245856131 1857680809663158368784197)
                ·
                  refine ⟨348315151811842194147037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857680809663158368784197 348315151811842194147037)
                  ·
                    rfl

theorem cell20_763134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_763134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763134 prefixEnd_763134 := by exact prefixLift 763134
  have htrace : WordTrace (prefixWord ++ tailWord_763134) baseStart_763134 baseEnd_763134 := by
    simpa [prefixWord, tailWord_763134, baseEnd_763134] using wordTrace_append hprefix tailTrace_763134
  have hstable : (prefixWord ++ tailWord_763134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763134).length < 2 ^ (prefixWord ++ tailWord_763134).sum := by decide
  have hdescent : baseEnd_763134 < baseStart_763134 := by decide
  rcases family_descends (prefixWord ++ tailWord_763134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763144 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_763144 : Nat := 118140960795 + 763144 * 2 ^ 59
def prefixEnd_763144 : Nat := 4983230072969 + 3 ^ 40 * 763144 * 2
def baseEnd_763144 : Nat := 348319716084326603813663

theorem tailTrace_763144 : CollatzResearch.WordTrace tailWord_763144 prefixEnd_763144 348319716084326603813663 := by
  unfold tailWord_763144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917074173633548731920243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18556098898178064975893657 13917074173633548731920243)
  ·
    refine ⟨20875611260450323097880365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13917074173633548731920243 20875611260450323097880365)
    ·
      refine ⟨7828354222668871161705137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20875611260450323097880365 7828354222668871161705137)
      ·
        refine ⟨5871265667001653371278853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7828354222668871161705137 5871265667001653371278853)
        ·
          refine ⟨1100862312562810007114785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5871265667001653371278853 1100862312562810007114785)
          ·
            refine ⟨825646734422107505336089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100862312562810007114785 825646734422107505336089)
            ·
              refine ⟨619235050816580629002067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825646734422107505336089 619235050816580629002067)
              ·
                refine ⟨928852576224870943503101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619235050816580629002067 928852576224870943503101)
                ·
                  refine ⟨348319716084326603813663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928852576224870943503101 348319716084326603813663)
                  ·
                    rfl

theorem cell20_763144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_763144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763144 prefixEnd_763144 := by exact prefixLift 763144
  have htrace : WordTrace (prefixWord ++ tailWord_763144) baseStart_763144 baseEnd_763144 := by
    simpa [prefixWord, tailWord_763144, baseEnd_763144] using wordTrace_append hprefix tailTrace_763144
  have hstable : (prefixWord ++ tailWord_763144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763144).length < 2 ^ (prefixWord ++ tailWord_763144).sum := by decide
  have hdescent : baseEnd_763144 < baseStart_763144 := by decide
  rcases family_descends (prefixWord ++ tailWord_763144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763148 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_763148 : Nat := 118140960795 + 763148 * 2 ^ 59
def prefixEnd_763148 : Nat := 4983230072969 + 3 ^ 40 * 763148 * 2
def baseEnd_763148 : Nat := 348321541793320367680313

theorem tailTrace_763148 : CollatzResearch.WordTrace tailWord_763148 prefixEnd_763148 348321541793320367680313 := by
  unfold tailWord_763148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917147119626303073493049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18556196159501737431324065 13917147119626303073493049)
  ·
    refine ⟨10437860339719727305119787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13917147119626303073493049 10437860339719727305119787)
    ·
      refine ⟨15656790509579590957679681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10437860339719727305119787 15656790509579590957679681)
      ·
        refine ⟨11742592882184693218259761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15656790509579590957679681 11742592882184693218259761)
        ·
          refine ⟨8806944661638519913694821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11742592882184693218259761 8806944661638519913694821)
          ·
            refine ⟨1651302124057222483817779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8806944661638519913694821 1651302124057222483817779)
            ·
              refine ⟨2476953186085833725726669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651302124057222483817779 2476953186085833725726669)
              ·
                refine ⟨928857444782187647147501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2476953186085833725726669 928857444782187647147501)
                ·
                  refine ⟨348321541793320367680313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928857444782187647147501 348321541793320367680313)
                  ·
                    rfl

theorem cell20_763148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_763148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763148 prefixEnd_763148 := by exact prefixLift 763148
  have htrace : WordTrace (prefixWord ++ tailWord_763148) baseStart_763148 baseEnd_763148 := by
    simpa [prefixWord, tailWord_763148, baseEnd_763148] using wordTrace_append hprefix tailTrace_763148
  have hstable : (prefixWord ++ tailWord_763148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763148).length < 2 ^ (prefixWord ++ tailWord_763148).sum := by decide
  have hdescent : baseEnd_763148 < baseStart_763148 := by decide
  rcases family_descends (prefixWord ++ tailWord_763148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763162 : List Nat := [3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_763162 : Nat := 118140960795 + 763162 * 2 ^ 59
def prefixEnd_763162 : Nat := 4983230072969 + 3 ^ 40 * 763162 * 2
def baseEnd_763162 : Nat := 116109310591599513737863

theorem tailTrace_763162 : CollatzResearch.WordTrace tailWord_763162 prefixEnd_763162 116109310591599513737863 := by
  unfold tailWord_763162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958701215300471634498935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18556536574134591025330493 6958701215300471634498935)
  ·
    refine ⟨10438051822950707451748403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6958701215300471634498935 10438051822950707451748403)
    ·
      refine ⟨15657077734426061177622605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10438051822950707451748403 15657077734426061177622605)
      ·
        refine ⟨5871404150409772941608477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15657077734426061177622605 5871404150409772941608477)
        ·
          refine ⟨2201776556403664853103179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5871404150409772941608477 2201776556403664853103179)
          ·
            refine ⟨3302664834605497279654769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201776556403664853103179 3302664834605497279654769)
            ·
              refine ⟨2476998625954122959741077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3302664834605497279654769 2476998625954122959741077)
              ·
                refine ⟨116109310591599513737863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2476998625954122959741077 116109310591599513737863)
                ·
                  rfl

theorem cell20_763162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_763162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763162 prefixEnd_763162 := by exact prefixLift 763162
  have htrace : WordTrace (prefixWord ++ tailWord_763162) baseStart_763162 baseEnd_763162 := by
    simpa [prefixWord, tailWord_763162, baseEnd_763162] using wordTrace_append hprefix tailTrace_763162
  have hstable : (prefixWord ++ tailWord_763162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763162).length < 2 ^ (prefixWord ++ tailWord_763162).sum := by decide
  have hdescent : baseEnd_763162 < baseStart_763162 := by decide
  rcases family_descends (prefixWord ++ tailWord_763162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763172 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 2]
def baseStart_763172 : Nat := 118140960795 + 763172 * 2 ^ 59
def prefixEnd_763172 : Nat := 4983230072969 + 3 ^ 40 * 763172 * 2
def baseEnd_763172 : Nat := 348332496047282950880215

theorem tailTrace_763172 : CollatzResearch.WordTrace tailWord_763172 prefixEnd_763172 348332496047282950880215 := by
  unfold tailWord_763172
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917584795582829122929885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18556779727443772163906513 13917584795582829122929885)
  ·
    refine ⟨5219094298343560921098707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13917584795582829122929885 5219094298343560921098707)
    ·
      refine ⟨7828641447515341381648061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219094298343560921098707 7828641447515341381648061)
      ·
        refine ⟨2935740542818253018118023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7828641447515341381648061 2935740542818253018118023)
        ·
          refine ⟨4403610814227379527177035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935740542818253018118023 4403610814227379527177035)
          ·
            refine ⟨6605416221341069290765553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403610814227379527177035 6605416221341069290765553)
            ·
              refine ⟨4954062166005801968074165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6605416221341069290765553 4954062166005801968074165)
              ·
                refine ⟨464443328063043934506953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4954062166005801968074165 464443328063043934506953)
                ·
                  refine ⟨348332496047282950880215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464443328063043934506953 348332496047282950880215)
                  ·
                    rfl

theorem cell20_763172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_763172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763172 prefixEnd_763172 := by exact prefixLift 763172
  have htrace : WordTrace (prefixWord ++ tailWord_763172) baseStart_763172 baseEnd_763172 := by
    simpa [prefixWord, tailWord_763172, baseEnd_763172] using wordTrace_append hprefix tailTrace_763172
  have hstable : (prefixWord ++ tailWord_763172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763172).length < 2 ^ (prefixWord ++ tailWord_763172).sum := by decide
  have hdescent : baseEnd_763172 < baseStart_763172 := by decide
  rcases family_descends (prefixWord ++ tailWord_763172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763186 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_763186 : Nat := 118140960795 + 763186 * 2 ^ 59
def prefixEnd_763186 : Nat := 4983230072969 + 3 ^ 40 * 763186 * 2
def baseEnd_763186 : Nat := 348338886028761124413491

theorem tailTrace_763186 : CollatzResearch.WordTrace tailWord_763186 prefixEnd_763186 348338886028761124413491 := by
  unfold tailWord_763186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958920053278734659217353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18557120142076625757912941 6958920053278734659217353)
  ·
    refine ⟨5219190039959050994413015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6958920053278734659217353 5219190039959050994413015)
    ·
      refine ⟨7828785059938576491619523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219190039959050994413015 7828785059938576491619523)
      ·
        refine ⟨11743177589907864737429285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7828785059938576491619523 11743177589907864737429285)
        ·
          refine ⟨2201845798107724638267991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11743177589907864737429285 2201845798107724638267991)
          ·
            refine ⟨3302768697161586957401987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201845798107724638267991 3302768697161586957401987)
            ·
              refine ⟨4954153045742380436102981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302768697161586957401987 4954153045742380436102981)
              ·
                refine ⟨928903696076696331769309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4954153045742380436102981 928903696076696331769309)
                ·
                  refine ⟨348338886028761124413491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928903696076696331769309 348338886028761124413491)
                  ·
                    rfl

theorem cell20_763186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_763186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763186 prefixEnd_763186 := by exact prefixLift 763186
  have htrace : WordTrace (prefixWord ++ tailWord_763186) baseStart_763186 baseEnd_763186 := by
    simpa [prefixWord, tailWord_763186, baseEnd_763186] using wordTrace_append hprefix tailTrace_763186
  have hstable : (prefixWord ++ tailWord_763186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763186).length < 2 ^ (prefixWord ++ tailWord_763186).sum := by decide
  have hdescent : baseEnd_763186 < baseStart_763186 := by decide
  rcases family_descends (prefixWord ++ tailWord_763186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763189 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 2]
def baseStart_763189 : Nat := 118140960795 + 763189 * 2 ^ 59
def prefixEnd_763189 : Nat := 4983230072969 + 3 ^ 40 * 763189 * 2
def baseEnd_763189 : Nat := 348340255310506447313479

theorem tailTrace_763189 : CollatzResearch.WordTrace tailWord_763189 prefixEnd_763189 348340255310506447313479 := by
  unfold tailWord_763189
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835789632104070149228621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18557193088069380099485747 27835789632104070149228621)
  ·
    refine ⟨10438421112039026305960733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27835789632104070149228621 10438421112039026305960733)
    ·
      refine ⟨3914407917014634864735275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10438421112039026305960733 3914407917014634864735275)
      ·
        refine ⟨5871611875521952297102913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914407917014634864735275 5871611875521952297102913)
        ·
          refine ⟨4403708906641464222827185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5871611875521952297102913 4403708906641464222827185)
          ·
            refine ⟨3302781679981098167120389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403708906641464222827185 3302781679981098167120389)
            ·
              refine ⟨619271564996455906335073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3302781679981098167120389 619271564996455906335073)
              ·
                refine ⟨464453673747341929751305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619271564996455906335073 464453673747341929751305)
                ·
                  refine ⟨348340255310506447313479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464453673747341929751305 348340255310506447313479)
                  ·
                    rfl

theorem cell20_763189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_763189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763189 prefixEnd_763189 := by exact prefixLift 763189
  have htrace : WordTrace (prefixWord ++ tailWord_763189) baseStart_763189 baseEnd_763189 := by
    simpa [prefixWord, tailWord_763189, baseEnd_763189] using wordTrace_append hprefix tailTrace_763189
  have hstable : (prefixWord ++ tailWord_763189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763189).length < 2 ^ (prefixWord ++ tailWord_763189).sum := by decide
  have hdescent : baseEnd_763189 < baseStart_763189 := by decide
  rcases family_descends (prefixWord ++ tailWord_763189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763206 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_763206 : Nat := 118140960795 + 763206 * 2 ^ 59
def prefixEnd_763206 : Nat := 4983230072969 + 3 ^ 40 * 763206 * 2
def baseEnd_763206 : Nat := 348348014573729943746743

theorem tailTrace_763206 : CollatzResearch.WordTrace tailWord_763206 prefixEnd_763206 348348014573729943746743 := by
  unfold tailWord_763206
  simp only [CollatzResearch.WordTrace]
  refine ⟨869887802282577564143671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18557606448694988035064981 869887802282577564143671)
  ·
    refine ⟨1304831703423866346215507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 869887802282577564143671 1304831703423866346215507)
    ·
      refine ⟨1957247555135799519323261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304831703423866346215507 1957247555135799519323261)
      ·
        refine ⟨733967833175924819746223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1957247555135799519323261 733967833175924819746223)
        ·
          refine ⟨1100951749763887229619335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733967833175924819746223 1100951749763887229619335)
          ·
            refine ⟨1651427624645830844429003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100951749763887229619335 1651427624645830844429003)
            ·
              refine ⟨2477141436968746266643505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651427624645830844429003 2477141436968746266643505)
              ·
                refine ⟨1857856077726559699982629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477141436968746266643505 1857856077726559699982629)
                ·
                  refine ⟨348348014573729943746743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857856077726559699982629 348348014573729943746743)
                  ·
                    rfl

theorem cell20_763206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_763206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763206 prefixEnd_763206 := by exact prefixLift 763206
  have htrace : WordTrace (prefixWord ++ tailWord_763206) baseStart_763206 baseEnd_763206 := by
    simpa [prefixWord, tailWord_763206, baseEnd_763206] using wordTrace_append hprefix tailTrace_763206
  have hstable : (prefixWord ++ tailWord_763206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763206).length < 2 ^ (prefixWord ++ tailWord_763206).sum := by decide
  have hdescent : baseEnd_763206 < baseStart_763206 := by decide
  rcases family_descends (prefixWord ++ tailWord_763206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763213 : List Nat := [1, 6, 1, 3, 1, 1, 3, 4]
def baseStart_763213 : Nat := 118140960795 + 763213 * 2 ^ 59
def prefixEnd_763213 : Nat := 4983230072969 + 3 ^ 40 * 763213 * 2
def baseEnd_763213 : Nat := 116117069854823010171127

theorem tailTrace_763213 : CollatzResearch.WordTrace tailWord_763213 prefixEnd_763213 116117069854823010171127 := by
  unfold tailWord_763213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836664984017122248102293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18557776656011414832068195 27836664984017122248102293)
  ·
    refine ⟨1304843671125802605379795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27836664984017122248102293 1304843671125802605379795)
    ·
      refine ⟨1957265506688703908069693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304843671125802605379795 1957265506688703908069693)
      ·
        refine ⟨733974565008263965526135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1957265506688703908069693 733974565008263965526135)
        ·
          refine ⟨1100961847512395948289203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733974565008263965526135 1100961847512395948289203)
          ·
            refine ⟨1651442771268593922433805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100961847512395948289203 1651442771268593922433805)
            ·
              refine ⟨619291039225722720912677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1651442771268593922433805 619291039225722720912677)
              ·
                refine ⟨116117069854823010171127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619291039225722720912677 116117069854823010171127)
                ·
                  rfl

theorem cell20_763213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_763213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763213 prefixEnd_763213 := by exact prefixLift 763213
  have htrace : WordTrace (prefixWord ++ tailWord_763213) baseStart_763213 baseEnd_763213 := by
    simpa [prefixWord, tailWord_763213, baseEnd_763213] using wordTrace_append hprefix tailTrace_763213
  have hstable : (prefixWord ++ tailWord_763213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763213).length < 2 ^ (prefixWord ++ tailWord_763213).sum := by decide
  have hdescent : baseEnd_763213 < baseStart_763213 := by decide
  rcases family_descends (prefixWord ++ tailWord_763213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763259 : List Nat := [1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_763259 : Nat := 118140960795 + 763259 * 2 ^ 59
def prefixEnd_763259 : Nat := 4983230072969 + 3 ^ 40 * 763259 * 2
def baseEnd_763259 : Nat := 116124068405965771659953

theorem tailTrace_763259 : CollatzResearch.WordTrace tailWord_763259 prefixEnd_763259 116124068405965771659953 := by
  unfold tailWord_763259
  simp only [CollatzResearch.WordTrace]
  refine ⟨27838342741850472104276831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18558895161233648069517887 27838342741850472104276831)
  ·
    refine ⟨41757514112775708156415247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27838342741850472104276831 41757514112775708156415247)
    ·
      refine ⟨62636271169163562234622871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41757514112775708156415247 62636271169163562234622871)
      ·
        refine ⟨93954406753745343351934307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62636271169163562234622871 93954406753745343351934307)
        ·
          refine ⟨140931610130618015027901461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93954406753745343351934307 140931610130618015027901461)
          ·
            refine ⟨6606169224872719454432881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140931610130618015027901461 6606169224872719454432881)
            ·
              refine ⟨4954626918654539590824661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6606169224872719454432881 4954626918654539590824661)
              ·
                refine ⟨116124068405965771659953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4954626918654539590824661 116124068405965771659953)
                ·
                  rfl

theorem cell20_763259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_763259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763259 prefixEnd_763259 := by exact prefixLift 763259
  have htrace : WordTrace (prefixWord ++ tailWord_763259) baseStart_763259 baseEnd_763259 := by
    simpa [prefixWord, tailWord_763259, baseEnd_763259] using wordTrace_append hprefix tailTrace_763259
  have hstable : (prefixWord ++ tailWord_763259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763259).length < 2 ^ (prefixWord ++ tailWord_763259).sum := by decide
  have hdescent : baseEnd_763259 < baseStart_763259 := by decide
  rcases family_descends (prefixWord ++ tailWord_763259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763303 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 2]
def baseStart_763303 : Nat := 118140960795 + 763303 * 2 ^ 59
def prefixEnd_763303 : Nat := 4983230072969 + 3 ^ 40 * 763303 * 2
def baseEnd_763303 : Nat := 348392288016828717513013

theorem tailTrace_763303 : CollatzResearch.WordTrace tailWord_763303 prefixEnd_763303 348392288016828717513013 := by
  unfold tailWord_763303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27839947553691067618878563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18559965035794045079252375 27839947553691067618878563)
  ·
    refine ⟨41759921330536601428317845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27839947553691067618878563 41759921330536601428317845)
    ·
      refine ⟨1957496312368903191952399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41759921330536601428317845 1957496312368903191952399)
      ·
        refine ⟨2936244468553354787928599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957496312368903191952399 2936244468553354787928599)
        ·
          refine ⟨4404366702830032181892899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936244468553354787928599 4404366702830032181892899)
          ·
            refine ⟨6606550054245048272839349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404366702830032181892899 6606550054245048272839349)
            ·
              refine ⟨619364067585473275578689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6606550054245048272839349 619364067585473275578689)
              ·
                refine ⟨464523050689104956684017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619364067585473275578689 464523050689104956684017)
                ·
                  refine ⟨348392288016828717513013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464523050689104956684017 348392288016828717513013)
                  ·
                    rfl

theorem cell20_763303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 2].length) (baseStart_763303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763303 prefixEnd_763303 := by exact prefixLift 763303
  have htrace : WordTrace (prefixWord ++ tailWord_763303) baseStart_763303 baseEnd_763303 := by
    simpa [prefixWord, tailWord_763303, baseEnd_763303] using wordTrace_append hprefix tailTrace_763303
  have hstable : (prefixWord ++ tailWord_763303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763303).length < 2 ^ (prefixWord ++ tailWord_763303).sum := by decide
  have hdescent : baseEnd_763303 < baseStart_763303 := by decide
  rcases family_descends (prefixWord ++ tailWord_763303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763317 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 3]
def baseStart_763317 : Nat := 118140960795 + 763317 * 2 ^ 59
def prefixEnd_763317 : Nat := 4983230072969 + 3 ^ 40 * 763317 * 2
def baseEnd_763317 : Nat := 348398677998306891046289

theorem tailTrace_763317 : CollatzResearch.WordTrace tailWord_763317 prefixEnd_763317 348398677998306891046289 := by
  unfold tailWord_763317
  simp only [CollatzResearch.WordTrace]
  refine ⟨27840458175640348009888205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18560305450426898673258803 27840458175640348009888205)
  ·
    refine ⟨10440171815865130503708077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27840458175640348009888205 10440171815865130503708077)
    ·
      refine ⟨3915064430949423938890529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10440171815865130503708077 3915064430949423938890529)
      ·
        refine ⟨2936298323212067954167897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3915064430949423938890529 2936298323212067954167897)
        ·
          refine ⟨2202223742409050965625923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936298323212067954167897 2202223742409050965625923)
          ·
            refine ⟨3303335613613576448438885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202223742409050965625923 3303335613613576448438885)
            ·
              refine ⟨619375427552545584082291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3303335613613576448438885 619375427552545584082291)
              ·
                refine ⟨929063141328818376123437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619375427552545584082291 929063141328818376123437)
                ·
                  refine ⟨348398677998306891046289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929063141328818376123437 348398677998306891046289)
                  ·
                    rfl

theorem cell20_763317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_763317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763317 prefixEnd_763317 := by exact prefixLift 763317
  have htrace : WordTrace (prefixWord ++ tailWord_763317) baseStart_763317 baseEnd_763317 := by
    simpa [prefixWord, tailWord_763317, baseEnd_763317] using wordTrace_append hprefix tailTrace_763317
  have hstable : (prefixWord ++ tailWord_763317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763317).length < 2 ^ (prefixWord ++ tailWord_763317).sum := by decide
  have hdescent : baseEnd_763317 < baseStart_763317 := by decide
  rcases family_descends (prefixWord ++ tailWord_763317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763328 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_763328 : Nat := 118140960795 + 763328 * 2 ^ 59
def prefixEnd_763328 : Nat := 4983230072969 + 3 ^ 40 * 763328 * 2
def baseEnd_763328 : Nat := 348403698698039741679577

theorem tailTrace_763328 : CollatzResearch.WordTrace tailWord_763328 prefixEnd_763328 348403698698039741679577 := by
  unfold tailWord_763328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13920429689300248444269319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18560572919066997925692425 13920429689300248444269319)
  ·
    refine ⟨20880644533950372666403979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13920429689300248444269319 20880644533950372666403979)
    ·
      refine ⟨31320966800925558999605969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20880644533950372666403979 31320966800925558999605969)
      ·
        refine ⟨23490725100694169249704477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31320966800925558999605969 23490725100694169249704477)
        ·
          refine ⟨8809021912760313468639179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23490725100694169249704477 8809021912760313468639179)
          ·
            refine ⟨13213532869140470202958769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8809021912760313468639179 13213532869140470202958769)
            ·
              refine ⟨9910149651855352652219077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13213532869140470202958769 9910149651855352652219077)
              ·
                refine ⟨1858153059722878622291077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9910149651855352652219077 1858153059722878622291077)
                ·
                  refine ⟨348403698698039741679577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858153059722878622291077 348403698698039741679577)
                  ·
                    rfl

theorem cell20_763328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_763328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763328 prefixEnd_763328 := by exact prefixLift 763328
  have htrace : WordTrace (prefixWord ++ tailWord_763328) baseStart_763328 baseEnd_763328 := by
    simpa [prefixWord, tailWord_763328, baseEnd_763328] using wordTrace_append hprefix tailTrace_763328
  have hstable : (prefixWord ++ tailWord_763328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763328).length < 2 ^ (prefixWord ++ tailWord_763328).sum := by decide
  have hdescent : baseEnd_763328 < baseStart_763328 := by decide
  rcases family_descends (prefixWord ++ tailWord_763328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763335 : List Nat := [1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_763335 : Nat := 118140960795 + 763335 * 2 ^ 59
def prefixEnd_763335 : Nat := 4983230072969 + 3 ^ 40 * 763335 * 2
def baseEnd_763335 : Nat := 116135631229592942815405

theorem tailTrace_763335 : CollatzResearch.WordTrace tailWord_763335 prefixEnd_763335 116135631229592942815405 := by
  unfold tailWord_763335
  simp only [CollatzResearch.WordTrace]
  refine ⟨27841114689575137084043459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18560743126383424722695639 27841114689575137084043459)
  ·
    refine ⟨41761672034362705626065189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27841114689575137084043459 41761672034362705626065189)
    ·
      refine ⟨7830313506443007304887223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41761672034362705626065189 7830313506443007304887223)
      ·
        refine ⟨11745470259664510957330835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830313506443007304887223 11745470259664510957330835)
        ·
          refine ⟨17618205389496766435996253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11745470259664510957330835 17618205389496766435996253)
          ·
            refine ⟨6606827021061287413498595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17618205389496766435996253 6606827021061287413498595)
            ·
              refine ⟨9910240531591931120247893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606827021061287413498595 9910240531591931120247893)
              ·
                refine ⟨116135631229592942815405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9910240531591931120247893 116135631229592942815405)
                ·
                  rfl

theorem cell20_763335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_763335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763335 prefixEnd_763335 := by exact prefixLift 763335
  have htrace : WordTrace (prefixWord ++ tailWord_763335) baseStart_763335 baseEnd_763335 := by
    simpa [prefixWord, tailWord_763335, baseEnd_763335] using wordTrace_append hprefix tailTrace_763335
  have hstable : (prefixWord ++ tailWord_763335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763335).length < 2 ^ (prefixWord ++ tailWord_763335).sum := by decide
  have hdescent : baseEnd_763335 < baseStart_763335 := by decide
  rcases family_descends (prefixWord ++ tailWord_763335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763411 : List Nat := [1, 1, 1, 2, 1, 7, 7]
def baseStart_763411 : Nat := 118140960795 + 763411 * 2 ^ 59
def prefixEnd_763411 : Nat := 4983230072969 + 3 ^ 40 * 763411 * 2
def baseEnd_763411 : Nat := 38715731351073371323619

theorem tailTrace_763411 : CollatzResearch.WordTrace tailWord_763411 prefixEnd_763411 38715731351073371323619 := by
  unfold tailWord_763411
  simp only [CollatzResearch.WordTrace]
  refine ⟨27843886637299802063810087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18562591091533201375873391 27843886637299802063810087)
  ·
    refine ⟨41765829955949703095715131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27843886637299802063810087 41765829955949703095715131)
    ·
      refine ⟨62648744933924554643572697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41765829955949703095715131 62648744933924554643572697)
      ·
        refine ⟨46986558700443415982679523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62648744933924554643572697 46986558700443415982679523)
        ·
          refine ⟨70479838050665123974019285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46986558700443415982679523 70479838050665123974019285)
          ·
            refine ⟨1651871204312463843141077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70479838050665123974019285 1651871204312463843141077)
            ·
              refine ⟨38715731351073371323619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1651871204312463843141077 38715731351073371323619)
              ·
                rfl

theorem cell20_763411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_763411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763411 prefixEnd_763411 := by exact prefixLift 763411
  have htrace : WordTrace (prefixWord ++ tailWord_763411) baseStart_763411 baseEnd_763411 := by
    simpa [prefixWord, tailWord_763411, baseEnd_763411] using wordTrace_append hprefix tailTrace_763411
  have hstable : (prefixWord ++ tailWord_763411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763411).length < 2 ^ (prefixWord ++ tailWord_763411).sum := by decide
  have hdescent : baseEnd_763411 < baseStart_763411 := by decide
  rcases family_descends (prefixWord ++ tailWord_763411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763421 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_763421 : Nat := 118140960795 + 763421 * 2 ^ 59
def prefixEnd_763421 : Nat := 4983230072969 + 3 ^ 40 * 763421 * 2
def baseEnd_763421 : Nat := 348446146432144751579197

theorem tailTrace_763421 : CollatzResearch.WordTrace tailWord_763421 prefixEnd_763421 348446146432144751579197 := by
  unfold tailWord_763421
  simp only [CollatzResearch.WordTrace]
  refine ⟨27844251367263573771674117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18562834244842382514449411 27844251367263573771674117)
  ·
    refine ⟨5220797131361920082188897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27844251367263573771674117 5220797131361920082188897)
    ·
      refine ⟨3915597848521440061641673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5220797131361920082188897 3915597848521440061641673)
      ·
        refine ⟨2936698386391080046231255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3915597848521440061641673 2936698386391080046231255)
        ·
          refine ⟨4405047579586620069346883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936698386391080046231255 4405047579586620069346883)
          ·
            refine ⟨6607571369379930104020325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4405047579586620069346883 6607571369379930104020325)
            ·
              refine ⟨1238919631758736894503811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6607571369379930104020325 1238919631758736894503811)
              ·
                refine ⟨1858379447638105341755717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238919631758736894503811 1858379447638105341755717)
                ·
                  refine ⟨348446146432144751579197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858379447638105341755717 348446146432144751579197)
                  ·
                    rfl

theorem cell20_763421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_763421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763421 prefixEnd_763421 := by exact prefixLift 763421
  have htrace : WordTrace (prefixWord ++ tailWord_763421) baseStart_763421 baseEnd_763421 := by
    simpa [prefixWord, tailWord_763421, baseEnd_763421] using wordTrace_append hprefix tailTrace_763421
  have hstable : (prefixWord ++ tailWord_763421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763421).length < 2 ^ (prefixWord ++ tailWord_763421).sum := by decide
  have hdescent : baseEnd_763421 < baseStart_763421 := by decide
  rcases family_descends (prefixWord ++ tailWord_763421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763445 : List Nat := [1, 3, 3, 1, 1, 5, 2, 4]
def baseStart_763445 : Nat := 118140960795 + 763445 * 2 ^ 59
def prefixEnd_763445 : Nat := 4983230072969 + 3 ^ 40 * 763445 * 2
def baseEnd_763445 : Nat := 116152366895369111593033

theorem tailTrace_763445 : CollatzResearch.WordTrace tailWord_763445 prefixEnd_763445 116152366895369111593033 := by
  unfold tailWord_763445
  simp only [CollatzResearch.WordTrace]
  refine ⟨27845126719176625870547789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18563417812784417247031859 27845126719176625870547789)
  ·
    refine ⟨10441922519691234701455421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27845126719176625870547789 10441922519691234701455421)
    ·
      refine ⟨3915720944884213013045783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10441922519691234701455421 3915720944884213013045783)
      ·
        refine ⟨5873581417326319519568675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915720944884213013045783 5873581417326319519568675)
        ·
          refine ⟨8810372125989479279353013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873581417326319519568675 8810372125989479279353013)
          ·
            refine ⟨825972386811513682439345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8810372125989479279353013 825972386811513682439345)
            ·
              refine ⟨619479290108635261829509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825972386811513682439345 619479290108635261829509)
              ·
                refine ⟨116152366895369111593033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619479290108635261829509 116152366895369111593033)
                ·
                  rfl

theorem cell20_763445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_763445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763445 prefixEnd_763445 := by exact prefixLift 763445
  have htrace : WordTrace (prefixWord ++ tailWord_763445) baseStart_763445 baseEnd_763445 := by
    simpa [prefixWord, tailWord_763445, baseEnd_763445] using wordTrace_append hprefix tailTrace_763445
  have hstable : (prefixWord ++ tailWord_763445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763445).length < 2 ^ (prefixWord ++ tailWord_763445).sum := by decide
  have hdescent : baseEnd_763445 < baseStart_763445 := by decide
  rcases family_descends (prefixWord ++ tailWord_763445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763462 : List Nat := [6, 1, 1, 1, 3, 2, 6]
def baseStart_763462 : Nat := 118140960795 + 763462 * 2 ^ 59
def prefixEnd_763462 : Nat := 4983230072969 + 3 ^ 40 * 763462 * 2
def baseEnd_763462 : Nat := 38718317772147870134707

theorem tailTrace_763462 : CollatzResearch.WordTrace tailWord_763462 prefixEnd_763462 38718317772147870134707 := by
  unfold tailWord_763462
  simp only [CollatzResearch.WordTrace]
  refine ⟨870179586253594930434895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18563831173410025182611093 870179586253594930434895)
  ·
    refine ⟨1305269379380392395652343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870179586253594930434895 1305269379380392395652343)
    ·
      refine ⟨1957904069070588593478515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305269379380392395652343 1957904069070588593478515)
      ·
        refine ⟨2936856103605882890217773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957904069070588593478515 2936856103605882890217773)
        ·
          refine ⟨1101321038852206083831665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2936856103605882890217773 1101321038852206083831665)
          ·
            refine ⟨825990779139154562873749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101321038852206083831665 825990779139154562873749)
            ·
              refine ⟨38718317772147870134707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 825990779139154562873749 38718317772147870134707)
              ·
                rfl

theorem cell20_763462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 6].length) (baseStart_763462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763462 prefixEnd_763462 := by exact prefixLift 763462
  have htrace : WordTrace (prefixWord ++ tailWord_763462) baseStart_763462 baseEnd_763462 := by
    simpa [prefixWord, tailWord_763462, baseEnd_763462] using wordTrace_append hprefix tailTrace_763462
  have hstable : (prefixWord ++ tailWord_763462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763462).length < 2 ^ (prefixWord ++ tailWord_763462).sum := by decide
  have hdescent : baseEnd_763462 < baseStart_763462 := by decide
  rcases family_descends (prefixWord ++ tailWord_763462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763473 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_763473 : Nat := 118140960795 + 763473 * 2 ^ 59
def prefixEnd_763473 : Nat := 4983230072969 + 3 ^ 40 * 763473 * 2
def baseEnd_763473 : Nat := 348469880649063681845651

theorem tailTrace_763473 : CollatzResearch.WordTrace tailWord_763473 prefixEnd_763473 348469880649063681845651 := by
  unfold tailWord_763473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27846147963075186652567073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18564098642050124435044715 27846147963075186652567073)
  ·
    refine ⟨20884610972306389989425305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27846147963075186652567073 20884610972306389989425305)
    ·
      refine ⟨15663458229229792492068979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20884610972306389989425305 15663458229229792492068979)
      ·
        refine ⟨23495187343844688738103469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15663458229229792492068979 23495187343844688738103469)
        ·
          refine ⟨8810695253941758276788801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23495187343844688738103469 8810695253941758276788801)
          ·
            refine ⟨6608021440456318707591601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8810695253941758276788801 6608021440456318707591601)
            ·
              refine ⟨4956016080342239030693701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6608021440456318707591601 4956016080342239030693701)
              ·
                refine ⟨929253015064169818255069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4956016080342239030693701 929253015064169818255069)
                ·
                  refine ⟨348469880649063681845651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929253015064169818255069 348469880649063681845651)
                  ·
                    rfl

theorem cell20_763473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_763473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763473 prefixEnd_763473 := by exact prefixLift 763473
  have htrace : WordTrace (prefixWord ++ tailWord_763473) baseStart_763473 baseEnd_763473 := by
    simpa [prefixWord, tailWord_763473, baseEnd_763473] using wordTrace_append hprefix tailTrace_763473
  have hstable : (prefixWord ++ tailWord_763473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763473).length < 2 ^ (prefixWord ++ tailWord_763473).sum := by decide
  have hdescent : baseEnd_763473 < baseStart_763473 := by decide
  rcases family_descends (prefixWord ++ tailWord_763473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763538 : List Nat := [3, 2, 3, 1, 4, 1, 1, 5]
def baseStart_763538 : Nat := 118140960795 + 763538 * 2 ^ 59
def prefixEnd_763538 : Nat := 4983230072969 + 3 ^ 40 * 763538 * 2
def baseEnd_763538 : Nat := 116166516140070781559573

theorem tailTrace_763538 : CollatzResearch.WordTrace tailWord_763538 prefixEnd_763538 116166516140070781559573 := by
  unfold tailWord_763538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962129676959925688420817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18565679138559801835788845 6962129676959925688420817)
  ·
    refine ⟨5221597257719944266315613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6962129676959925688420817 5221597257719944266315613)
    ·
      refine ⟨1958098971644979099868355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5221597257719944266315613 1958098971644979099868355)
      ·
        refine ⟨2937148457467468649802533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958098971644979099868355 2937148457467468649802533)
        ·
          refine ⟨550715335775150371837975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2937148457467468649802533 550715335775150371837975)
          ·
            refine ⟨826073003662725557756963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550715335775150371837975 826073003662725557756963)
            ·
              refine ⟨1239109505494088336635445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826073003662725557756963 1239109505494088336635445)
              ·
                refine ⟨116166516140070781559573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1239109505494088336635445 116166516140070781559573)
                ·
                  rfl

theorem cell20_763538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_763538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763538 prefixEnd_763538 := by exact prefixLift 763538
  have htrace : WordTrace (prefixWord ++ tailWord_763538) baseStart_763538 baseEnd_763538 := by
    simpa [prefixWord, tailWord_763538, baseEnd_763538] using wordTrace_append hprefix tailTrace_763538
  have hstable : (prefixWord ++ tailWord_763538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763538).length < 2 ^ (prefixWord ++ tailWord_763538).sum := by decide
  have hdescent : baseEnd_763538 < baseStart_763538 := by decide
  rcases family_descends (prefixWord ++ tailWord_763538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763556 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_763556 : Nat := 118140960795 + 763556 * 2 ^ 59
def prefixEnd_763556 : Nat := 4983230072969 + 3 ^ 40 * 763556 * 2
def baseEnd_763556 : Nat := 348507764110684282078645

theorem tailTrace_763556 : CollatzResearch.WordTrace tailWord_763556 prefixEnd_763556 348507764110684282078645 := by
  unfold tailWord_763556
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924587610887245913919261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18566116814516327885225681 13924587610887245913919261)
  ·
    refine ⟨5221720354082717217719723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13924587610887245913919261 5221720354082717217719723)
    ·
      refine ⟨7832580531124075826579585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5221720354082717217719723 7832580531124075826579585)
      ·
        refine ⟨5874435398343056869934689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7832580531124075826579585 5874435398343056869934689)
        ·
          refine ⟨4405826548757292652451017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5874435398343056869934689 4405826548757292652451017)
          ·
            refine ⟨3304369911567969489338263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4405826548757292652451017 3304369911567969489338263)
            ·
              refine ⟨4956554867351954234007395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304369911567969489338263 4956554867351954234007395)
              ·
                refine ⟨7434832301027931351011093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956554867351954234007395 7434832301027931351011093)
                ·
                  refine ⟨348507764110684282078645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7434832301027931351011093 348507764110684282078645)
                  ·
                    rfl

theorem cell20_763556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_763556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763556 prefixEnd_763556 := by exact prefixLift 763556
  have htrace : WordTrace (prefixWord ++ tailWord_763556) baseStart_763556 baseEnd_763556 := by
    simpa [prefixWord, tailWord_763556, baseEnd_763556] using wordTrace_append hprefix tailTrace_763556
  have hstable : (prefixWord ++ tailWord_763556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763556).length < 2 ^ (prefixWord ++ tailWord_763556).sum := by decide
  have hdescent : baseEnd_763556 < baseStart_763556 := by decide
  rcases family_descends (prefixWord ++ tailWord_763556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763586 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_763586 : Nat := 118140960795 + 763586 * 2 ^ 59
def prefixEnd_763586 : Nat := 4983230072969 + 3 ^ 40 * 763586 * 2
def baseEnd_763586 : Nat := 348521456928137511078523

theorem tailTrace_763586 : CollatzResearch.WordTrace tailWord_763586 prefixEnd_763586 348521456928137511078523 := by
  unfold tailWord_763586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962567352916451737857653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18566846274443871300953741 6962567352916451737857653)
  ·
    refine ⟨652740689335917350424155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6962567352916451737857653 652740689335917350424155)
    ·
      refine ⟨979111034003876025636233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652740689335917350424155 979111034003876025636233)
      ·
        refine ⟨734333275502907019227175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 979111034003876025636233 734333275502907019227175)
        ·
          refine ⟨1101499913254360528840763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734333275502907019227175 1101499913254360528840763)
          ·
            refine ⟨1652249869881540793261145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101499913254360528840763 1652249869881540793261145)
            ·
              refine ⟨1239187402411155594945859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652249869881540793261145 1239187402411155594945859)
              ·
                refine ⟨1858781103616733392418789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239187402411155594945859 1858781103616733392418789)
                ·
                  refine ⟨348521456928137511078523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858781103616733392418789 348521456928137511078523)
                  ·
                    rfl

theorem cell20_763586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_763586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763586 prefixEnd_763586 := by exact prefixLift 763586
  have htrace : WordTrace (prefixWord ++ tailWord_763586) baseStart_763586 baseEnd_763586 := by
    simpa [prefixWord, tailWord_763586, baseEnd_763586] using wordTrace_append hprefix tailTrace_763586
  have hstable : (prefixWord ++ tailWord_763586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763586).length < 2 ^ (prefixWord ++ tailWord_763586).sum := by decide
  have hdescent : baseEnd_763586 < baseStart_763586 := by decide
  rcases family_descends (prefixWord ++ tailWord_763586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763649 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 2]
def baseStart_763649 : Nat := 118140960795 + 763649 * 2 ^ 59
def prefixEnd_763649 : Nat := 4983230072969 + 3 ^ 40 * 763649 * 2
def baseEnd_763649 : Nat := 348550211844789291978265

theorem tailTrace_763649 : CollatzResearch.WordTrace tailWord_763649 prefixEnd_763649 348550211844789291978265 := by
  unfold tailWord_763649
  simp only [CollatzResearch.WordTrace]
  refine ⟨27852567210437568710974001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18568378140291712473982667 27852567210437568710974001)
  ·
    refine ⟨20889425407828176533230501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27852567210437568710974001 20889425407828176533230501)
    ·
      refine ⟨3916767263967783099980719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20889425407828176533230501 3916767263967783099980719)
      ·
        refine ⟨5875150895951674649971079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3916767263967783099980719 5875150895951674649971079)
        ·
          refine ⟨8812726343927511974956619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875150895951674649971079 8812726343927511974956619)
          ·
            refine ⟨13219089515891267962434929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8812726343927511974956619 13219089515891267962434929)
            ·
              refine ⟨9914317136918450971826197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13219089515891267962434929 9914317136918450971826197)
              ·
                refine ⟨464733615793052389304353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9914317136918450971826197 464733615793052389304353)
                ·
                  refine ⟨348550211844789291978265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464733615793052389304353 348550211844789291978265)
                  ·
                    rfl

theorem cell20_763649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_763649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763649 prefixEnd_763649 := by exact prefixLift 763649
  have htrace : WordTrace (prefixWord ++ tailWord_763649) baseStart_763649 baseEnd_763649 := by
    simpa [prefixWord, tailWord_763649, baseEnd_763649] using wordTrace_append hprefix tailTrace_763649
  have hstable : (prefixWord ++ tailWord_763649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763649).length < 2 ^ (prefixWord ++ tailWord_763649).sum := by decide
  have hdescent : baseEnd_763649 < baseStart_763649 := by decide
  rcases family_descends (prefixWord ++ tailWord_763649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763694 : List Nat := [4, 1, 3, 2, 2, 8]
def baseStart_763694 : Nat := 118140960795 + 763694 * 2 ^ 59
def prefixEnd_763694 : Nat := 4983230072969 + 3 ^ 40 * 763694 * 2
def baseEnd_763694 : Nat := 12910027817443301314003

theorem tailTrace_763694 : CollatzResearch.WordTrace tailWord_763694 prefixEnd_763694 12910027817443301314003 := by
  unfold tailWord_763694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481776061909317674545267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18569472330183027597574757 3481776061909317674545267)
  ·
    refine ⟨5222664092863976511817901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481776061909317674545267 5222664092863976511817901)
    ·
      refine ⟨1958499034823991191931713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5222664092863976511817901 1958499034823991191931713)
      ·
        refine ⟨1468874276117993393948785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1958499034823991191931713 1468874276117993393948785)
        ·
          refine ⟨1101655707088495045461589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1468874276117993393948785 1101655707088495045461589)
          ·
            refine ⟨12910027817443301314003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1101655707088495045461589 12910027817443301314003)
            ·
              rfl

theorem cell20_763694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 8].length) (baseStart_763694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763694 prefixEnd_763694 := by exact prefixLift 763694
  have htrace : WordTrace (prefixWord ++ tailWord_763694) baseStart_763694 baseEnd_763694 := by
    simpa [prefixWord, tailWord_763694, baseEnd_763694] using wordTrace_append hprefix tailTrace_763694
  have hstable : (prefixWord ++ tailWord_763694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763694).length < 2 ^ (prefixWord ++ tailWord_763694).sum := by decide
  have hdescent : baseEnd_763694 < baseStart_763694 := by decide
  rcases family_descends (prefixWord ++ tailWord_763694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763700 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 2]
def baseStart_763700 : Nat := 118140960795 + 763700 * 2 ^ 59
def prefixEnd_763700 : Nat := 4983230072969 + 3 ^ 40 * 763700 * 2
def baseEnd_763700 : Nat := 348573489634459781278057

theorem tailTrace_763700 : CollatzResearch.WordTrace tailWord_763700 prefixEnd_763700 348573489634459781278057 := by
  unfold tailWord_763700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13927213666626402210540277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18569618222168536280720369 13927213666626402210540277)
  ·
    refine ⟨1305676281246225207238151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13927213666626402210540277 1305676281246225207238151)
    ·
      refine ⟨1958514421869337810857227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305676281246225207238151 1958514421869337810857227)
      ·
        refine ⟨2937771632804006716285841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958514421869337810857227 2937771632804006716285841)
        ·
          refine ⟨2203328724603005037214381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2937771632804006716285841 2203328724603005037214381)
          ·
            refine ⟨826248271726126888955393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2203328724603005037214381 826248271726126888955393)
            ·
              refine ⟨619686203794595166716545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826248271726126888955393 619686203794595166716545)
              ·
                refine ⟨464764652845946375037409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619686203794595166716545 464764652845946375037409)
                ·
                  refine ⟨348573489634459781278057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464764652845946375037409 348573489634459781278057)
                  ·
                    rfl

theorem cell20_763700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_763700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763700 prefixEnd_763700 := by exact prefixLift 763700
  have htrace : WordTrace (prefixWord ++ tailWord_763700) baseStart_763700 baseEnd_763700 := by
    simpa [prefixWord, tailWord_763700, baseEnd_763700] using wordTrace_append hprefix tailTrace_763700
  have hstable : (prefixWord ++ tailWord_763700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763700).length < 2 ^ (prefixWord ++ tailWord_763700).sum := by decide
  have hdescent : baseEnd_763700 < baseStart_763700 := by decide
  rcases family_descends (prefixWord ++ tailWord_763700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763704 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 2]
def baseStart_763704 : Nat := 118140960795 + 763704 * 2 ^ 59
def prefixEnd_763704 : Nat := 4983230072969 + 3 ^ 40 * 763704 * 2
def baseEnd_763704 : Nat := 348575315343453545144707

theorem tailTrace_763704 : CollatzResearch.WordTrace tailWord_763704 prefixEnd_763704 348575315343453545144707 := by
  unfold tailWord_763704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13927286612619156552113083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18569715483492208736150777 13927286612619156552113083)
  ·
    refine ⟨20890929918928734828169625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13927286612619156552113083 20890929918928734828169625)
    ·
      refine ⟨15668197439196551121127219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20890929918928734828169625 15668197439196551121127219)
      ·
        refine ⟨23502296158794826681690829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15668197439196551121127219 23502296158794826681690829)
        ·
          refine ⟨8813361059548060005634061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23502296158794826681690829 8813361059548060005634061)
          ·
            refine ⟨3305010397330522502112773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8813361059548060005634061 3305010397330522502112773)
            ·
              refine ⟨619689449499472969146145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3305010397330522502112773 619689449499472969146145)
              ·
                refine ⟨464767087124604726859609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619689449499472969146145 464767087124604726859609)
                ·
                  refine ⟨348575315343453545144707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464767087124604726859609 348575315343453545144707)
                  ·
                    rfl

theorem cell20_763704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_763704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763704 prefixEnd_763704 := by exact prefixLift 763704
  have htrace : WordTrace (prefixWord ++ tailWord_763704) baseStart_763704 baseEnd_763704 := by
    simpa [prefixWord, tailWord_763704, baseEnd_763704] using wordTrace_append hprefix tailTrace_763704
  have hstable : (prefixWord ++ tailWord_763704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763704).length < 2 ^ (prefixWord ++ tailWord_763704).sum := by decide
  have hdescent : baseEnd_763704 < baseStart_763704 := by decide
  rcases family_descends (prefixWord ++ tailWord_763704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763711 : List Nat := [1, 1, 2, 2, 7, 1, 1, 5]
def baseStart_763711 : Nat := 118140960795 + 763711 * 2 ^ 59
def prefixEnd_763711 : Nat := 4983230072969 + 3 ^ 40 * 763711 * 2
def baseEnd_763711 : Nat := 116192836778064210637115

theorem tailTrace_763711 : CollatzResearch.WordTrace tailWord_763711 prefixEnd_763711 116192836778064210637115 := by
  unfold tailWord_763711
  simp only [CollatzResearch.WordTrace]
  refine ⟨27854828536212953299730987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18569885690808635533153991 27854828536212953299730987)
  ·
    refine ⟨41782242804319429949596481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27854828536212953299730987 41782242804319429949596481)
    ·
      refine ⟨31336682103239572462197361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41782242804319429949596481 31336682103239572462197361)
      ·
        refine ⟨23502511577429679346648021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31336682103239572462197361 23502511577429679346648021)
        ·
          refine ⟨550840115096008109687063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 23502511577429679346648021 550840115096008109687063)
          ·
            refine ⟨826260172644012164530595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550840115096008109687063 826260172644012164530595)
            ·
              refine ⟨1239390258966018246795893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826260172644012164530595 1239390258966018246795893)
              ·
                refine ⟨116192836778064210637115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1239390258966018246795893 116192836778064210637115)
                ·
                  rfl

theorem cell20_763711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].length) (baseStart_763711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763711 prefixEnd_763711 := by exact prefixLift 763711
  have htrace : WordTrace (prefixWord ++ tailWord_763711) baseStart_763711 baseEnd_763711 := by
    simpa [prefixWord, tailWord_763711, baseEnd_763711] using wordTrace_append hprefix tailTrace_763711
  have hstable : (prefixWord ++ tailWord_763711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763711).length < 2 ^ (prefixWord ++ tailWord_763711).sum := by decide
  have hdescent : baseEnd_763711 < baseStart_763711 := by decide
  rcases family_descends (prefixWord ++ tailWord_763711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763715 : List Nat := [1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_763715 : Nat := 118140960795 + 763715 * 2 ^ 59
def prefixEnd_763715 : Nat := 4983230072969 + 3 ^ 40 * 763715 * 2
def baseEnd_763715 : Nat := 116193445347728798592665

theorem tailTrace_763715 : CollatzResearch.WordTrace tailWord_763715 prefixEnd_763715 116193445347728798592665 := by
  unfold tailWord_763715
  simp only [CollatzResearch.WordTrace]
  refine ⟨27854974428198461982876599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18569982952132307988584399 27854974428198461982876599)
  ·
    refine ⟨41782461642297692974314899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27854974428198461982876599 41782461642297692974314899)
    ·
      refine ⟨62673692463446539461472349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41782461642297692974314899 62673692463446539461472349)
      ·
        refine ⟨23502634673792452298052131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62673692463446539461472349 23502634673792452298052131)
        ·
          refine ⟨35253952010688678447078197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23502634673792452298052131 35253952010688678447078197)
          ·
            refine ⟨3305058001002063604413581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35253952010688678447078197 3305058001002063604413581)
            ·
              refine ⟨1239396750375773851655093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3305058001002063604413581 1239396750375773851655093)
              ·
                refine ⟨116193445347728798592665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1239396750375773851655093 116193445347728798592665)
                ·
                  rfl

theorem cell20_763715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_763715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763715 prefixEnd_763715 := by exact prefixLift 763715
  have htrace : WordTrace (prefixWord ++ tailWord_763715) baseStart_763715 baseEnd_763715 := by
    simpa [prefixWord, tailWord_763715, baseEnd_763715] using wordTrace_append hprefix tailTrace_763715
  have hstable : (prefixWord ++ tailWord_763715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763715).length < 2 ^ (prefixWord ++ tailWord_763715).sum := by decide
  have hdescent : baseEnd_763715 < baseStart_763715 := by decide
  rcases family_descends (prefixWord ++ tailWord_763715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763725 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_763725 : Nat := 118140960795 + 763725 * 2 ^ 59
def prefixEnd_763725 : Nat := 4983230072969 + 3 ^ 40 * 763725 * 2
def baseEnd_763725 : Nat := 348584900315670805444621

theorem tailTrace_763725 : CollatzResearch.WordTrace tailWord_763725 prefixEnd_763725 348584900315670805444621 := by
  unfold tailWord_763725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855339158162233690740629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18570226105441489127160419 27855339158162233690740629)
  ·
    refine ⟨1305719023038854704253467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27855339158162233690740629 1305719023038854704253467)
    ·
      refine ⟨1958578534558282056380201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305719023038854704253467 1958578534558282056380201)
      ·
        refine ⟨1468933900918711542285151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1958578534558282056380201 1468933900918711542285151)
        ·
          refine ⟨2203400851378067313427727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468933900918711542285151 2203400851378067313427727)
          ·
            refine ⟨3305101277067100970141591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203400851378067313427727 3305101277067100970141591)
            ·
              refine ⟨4957651915600651455212387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305101277067100970141591 4957651915600651455212387)
              ·
                refine ⟨7436477873400977182818581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957651915600651455212387 7436477873400977182818581)
                ·
                  refine ⟨348584900315670805444621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7436477873400977182818581 348584900315670805444621)
                  ·
                    rfl

theorem cell20_763725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_763725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763725 prefixEnd_763725 := by exact prefixLift 763725
  have htrace : WordTrace (prefixWord ++ tailWord_763725) baseStart_763725 baseEnd_763725 := by
    simpa [prefixWord, tailWord_763725, baseEnd_763725] using wordTrace_append hprefix tailTrace_763725
  have hstable : (prefixWord ++ tailWord_763725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763725).length < 2 ^ (prefixWord ++ tailWord_763725).sum := by decide
  have hdescent : baseEnd_763725 < baseStart_763725 := by decide
  rcases family_descends (prefixWord ++ tailWord_763725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763756 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_763756 : Nat := 118140960795 + 763756 * 2 ^ 59
def prefixEnd_763756 : Nat := 4983230072969 + 3 ^ 40 * 763756 * 2
def baseEnd_763756 : Nat := 348599049560372475411161

theorem tailTrace_763756 : CollatzResearch.WordTrace tailWord_763756 prefixEnd_763756 348599049560372475411161 := by
  unfold tailWord_763756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928234910524962992559561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18570979880699950656746081 13928234910524962992559561)
  ·
    refine ⟨10446176182893722244419671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13928234910524962992559561 10446176182893722244419671)
    ·
      refine ⟨15669264274340583366629507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10446176182893722244419671 15669264274340583366629507)
      ·
        refine ⟨23503896411510875049944261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15669264274340583366629507 23503896411510875049944261)
        ·
          refine ⟨4406980577158289071864549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23503896411510875049944261 4406980577158289071864549)
          ·
            refine ⟨826308858217179200974603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4406980577158289071864549 826308858217179200974603)
            ·
              refine ⟨1239463287325768801461905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826308858217179200974603 1239463287325768801461905)
              ·
                refine ⟨929597465494326601096429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239463287325768801461905 929597465494326601096429)
                ·
                  refine ⟨348599049560372475411161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929597465494326601096429 348599049560372475411161)
                  ·
                    rfl

theorem cell20_763756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_763756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763756 prefixEnd_763756 := by exact prefixLift 763756
  have htrace : WordTrace (prefixWord ++ tailWord_763756) baseStart_763756 baseEnd_763756 := by
    simpa [prefixWord, tailWord_763756, baseEnd_763756] using wordTrace_append hprefix tailTrace_763756
  have hstable : (prefixWord ++ tailWord_763756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763756).length < 2 ^ (prefixWord ++ tailWord_763756).sum := by decide
  have hdescent : baseEnd_763756 < baseStart_763756 := by decide
  rcases family_descends (prefixWord ++ tailWord_763756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763801 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 2]
def baseStart_763801 : Nat := 118140960795 + 763801 * 2 ^ 59
def prefixEnd_763801 : Nat := 4983230072969 + 3 ^ 40 * 763801 * 2
def baseEnd_763801 : Nat := 348619588786552318910977

theorem tailTrace_763801 : CollatzResearch.WordTrace tailWord_763801 prefixEnd_763801 348619588786552318910977 := by
  unfold tailWord_763801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27858111105886898670507257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18572074070591265780338171 27858111105886898670507257)
  ·
    refine ⟨20893583329415174002880443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27858111105886898670507257 20893583329415174002880443)
    ·
      refine ⟨31340374994122761004320665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20893583329415174002880443 31340374994122761004320665)
      ·
        refine ⟨23505281245592070753240499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31340374994122761004320665 23505281245592070753240499)
        ·
          refine ⟨35257921868388106129860749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23505281245592070753240499 35257921868388106129860749)
          ·
            refine ⟨13221720700645539798697781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35257921868388106129860749 13221720700645539798697781)
            ·
              refine ⟨1239536315685519356127917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13221720700645539798697781 1239536315685519356127917)
              ·
                refine ⟨464826118382069758547969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1239536315685519356127917 464826118382069758547969)
                ·
                  refine ⟨348619588786552318910977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464826118382069758547969 348619588786552318910977)
                  ·
                    rfl

theorem cell20_763801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_763801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763801 prefixEnd_763801 := by exact prefixLift 763801
  have htrace : WordTrace (prefixWord ++ tailWord_763801) baseStart_763801 baseEnd_763801 := by
    simpa [prefixWord, tailWord_763801, baseEnd_763801] using wordTrace_append hprefix tailTrace_763801
  have hstable : (prefixWord ++ tailWord_763801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763801).length < 2 ^ (prefixWord ++ tailWord_763801).sum := by decide
  have hdescent : baseEnd_763801 < baseStart_763801 := by decide
  rcases family_descends (prefixWord ++ tailWord_763801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763815 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_763815 : Nat := 118140960795 + 763815 * 2 ^ 59
def prefixEnd_763815 : Nat := 4983230072969 + 3 ^ 40 * 763815 * 2
def baseEnd_763815 : Nat := 348625978768030492444253

theorem tailTrace_763815 : CollatzResearch.WordTrace tailWord_763815 prefixEnd_763815 348625978768030492444253 := by
  unfold tailWord_763815
  simp only [CollatzResearch.WordTrace]
  refine ⟨27858621727836179061516899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18572414485224119374344599 27858621727836179061516899)
  ·
    refine ⟨41787932591754268592275349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27858621727836179061516899 41787932591754268592275349)
    ·
      refine ⟨1958809340238481340262907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41787932591754268592275349 1958809340238481340262907)
      ·
        refine ⟨2938214010357722010394361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958809340238481340262907 2938214010357722010394361)
        ·
          refine ⟨2203660507768291507795771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938214010357722010394361 2203660507768291507795771)
          ·
            refine ⟨3305490761652437261693657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203660507768291507795771 3305490761652437261693657)
            ·
              refine ⟨2479118071239327946270243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305490761652437261693657 2479118071239327946270243)
              ·
                refine ⟨3718677106858991919405365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479118071239327946270243 3718677106858991919405365)
                ·
                  refine ⟨348625978768030492444253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3718677106858991919405365 348625978768030492444253)
                  ·
                    rfl

theorem cell20_763815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_763815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763815 prefixEnd_763815 := by exact prefixLift 763815
  have htrace : WordTrace (prefixWord ++ tailWord_763815) baseStart_763815 baseEnd_763815 := by
    simpa [prefixWord, tailWord_763815, baseEnd_763815] using wordTrace_append hprefix tailTrace_763815
  have hstable : (prefixWord ++ tailWord_763815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763815).length < 2 ^ (prefixWord ++ tailWord_763815).sum := by decide
  have hdescent : baseEnd_763815 < baseStart_763815 := by decide
  rcases family_descends (prefixWord ++ tailWord_763815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763829 : List Nat := [1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_763829 : Nat := 118140960795 + 763829 * 2 ^ 59
def prefixEnd_763829 : Nat := 4983230072969 + 3 ^ 40 * 763829 * 2
def baseEnd_763829 : Nat := 116210789583169555325843

theorem tailTrace_763829 : CollatzResearch.WordTrace tailWord_763829 prefixEnd_763829 116210789583169555325843 := by
  unfold tailWord_763829
  simp only [CollatzResearch.WordTrace]
  refine ⟨27859132349785459452526541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18572754899856972968351027 27859132349785459452526541)
  ·
    refine ⟨10447174631169547294697453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27859132349785459452526541 10447174631169547294697453)
    ·
      refine ⟨3917690486688580235511545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10447174631169547294697453 3917690486688580235511545)
      ·
        refine ⟨2938267865016435176633659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917690486688580235511545 2938267865016435176633659)
        ·
          refine ⟨4407401797524652764950489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938267865016435176633659 4407401797524652764950489)
          ·
            refine ⟨3305551348143489573712867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407401797524652764950489 3305551348143489573712867)
            ·
              refine ⟨4958327022215234360569301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305551348143489573712867 4958327022215234360569301)
              ·
                refine ⟨116210789583169555325843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4958327022215234360569301 116210789583169555325843)
                ·
                  rfl

theorem cell20_763829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_763829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763829 prefixEnd_763829 := by exact prefixLift 763829
  have htrace : WordTrace (prefixWord ++ tailWord_763829) baseStart_763829 baseEnd_763829 := by
    simpa [prefixWord, tailWord_763829, baseEnd_763829] using wordTrace_append hprefix tailTrace_763829
  have hstable : (prefixWord ++ tailWord_763829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763829).length < 2 ^ (prefixWord ++ tailWord_763829).sum := by decide
  have hdescent : baseEnd_763829 < baseStart_763829 := by decide
  rcases family_descends (prefixWord ++ tailWord_763829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763912 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_763912 : Nat := 118140960795 + 763912 * 2 ^ 59
def prefixEnd_763912 : Nat := 4983230072969 + 3 ^ 40 * 763912 * 2
def baseEnd_763912 : Nat := 348670252211129266210523

theorem tailTrace_763912 : CollatzResearch.WordTrace tailWord_763912 prefixEnd_763912 348670252211129266210523 := by
  unfold tailWord_763912
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931079804242382313898995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18574773072323176418531993 13931079804242382313898995)
  ·
    refine ⟨20896619706363573470848493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13931079804242382313898995 20896619706363573470848493)
    ·
      refine ⟨7836232389886340051568185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20896619706363573470848493 7836232389886340051568185)
      ·
        refine ⟨5877174292414755038676139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7836232389886340051568185 5877174292414755038676139)
        ·
          refine ⟨8815761438622132558014209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877174292414755038676139 8815761438622132558014209)
          ·
            refine ⟨6611821078966599418510657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8815761438622132558014209 6611821078966599418510657)
            ·
              refine ⟨4958865809224949563882993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6611821078966599418510657 4958865809224949563882993)
              ·
                refine ⟨3719149356918712172912245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958865809224949563882993 3719149356918712172912245)
                ·
                  refine ⟨348670252211129266210523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3719149356918712172912245 348670252211129266210523)
                  ·
                    rfl

theorem cell20_763912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_763912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763912 prefixEnd_763912 := by exact prefixLift 763912
  have htrace : WordTrace (prefixWord ++ tailWord_763912) baseStart_763912 baseEnd_763912 := by
    simpa [prefixWord, tailWord_763912, baseEnd_763912] using wordTrace_append hprefix tailTrace_763912
  have hstable : (prefixWord ++ tailWord_763912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763912).length < 2 ^ (prefixWord ++ tailWord_763912).sum := by decide
  have hdescent : baseEnd_763912 < baseStart_763912 := by decide
  rcases family_descends (prefixWord ++ tailWord_763912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763915 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 2]
def baseStart_763915 : Nat := 118140960795 + 763915 * 2 ^ 59
def prefixEnd_763915 : Nat := 4983230072969 + 3 ^ 40 * 763915 * 2
def baseEnd_763915 : Nat := 348671621492874589110511

theorem tailTrace_763915 : CollatzResearch.WordTrace tailWord_763915 prefixEnd_763915 348671621492874589110511 := by
  unfold tailWord_763915
  simp only [CollatzResearch.WordTrace]
  refine ⟨27862269027473896140157199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18574846018315930760104799 27862269027473896140157199)
  ·
    refine ⟨41793403541210844210235799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27862269027473896140157199 41793403541210844210235799)
    ·
      refine ⟨62690105311816266315353699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41793403541210844210235799 62690105311816266315353699)
      ·
        refine ⟨94035157967724399473030549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62690105311816266315353699 94035157967724399473030549)
        ·
          refine ⟨4407898029737081225298307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94035157967724399473030549 4407898029737081225298307)
          ·
            refine ⟨6611847044605621837947461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407898029737081225298307 6611847044605621837947461)
            ·
              refine ⟨1239721320863554094615149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6611847044605621837947461 1239721320863554094615149)
              ·
                refine ⟨464895495323832785480681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1239721320863554094615149 464895495323832785480681)
                ·
                  refine ⟨348671621492874589110511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464895495323832785480681 348671621492874589110511)
                  ·
                    rfl

theorem cell20_763915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 2].length) (baseStart_763915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763915 prefixEnd_763915 := by exact prefixLift 763915
  have htrace : WordTrace (prefixWord ++ tailWord_763915) baseStart_763915 baseEnd_763915 := by
    simpa [prefixWord, tailWord_763915, baseEnd_763915] using wordTrace_append hprefix tailTrace_763915
  have hstable : (prefixWord ++ tailWord_763915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763915).length < 2 ^ (prefixWord ++ tailWord_763915).sum := by decide
  have hdescent : baseEnd_763915 < baseStart_763915 := by decide
  rcases family_descends (prefixWord ++ tailWord_763915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763925 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 3]
def baseStart_763925 : Nat := 118140960795 + 763925 * 2 ^ 59
def prefixEnd_763925 : Nat := 4983230072969 + 3 ^ 40 * 763925 * 2
def baseEnd_763925 : Nat := 348676185765358998777137

theorem tailTrace_763925 : CollatzResearch.WordTrace tailWord_763925 prefixEnd_763925 348676185765358998777137 := by
  unfold tailWord_763925
  simp only [CollatzResearch.WordTrace]
  refine ⟨27862633757437667848021229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18575089171625111898680819 27862633757437667848021229)
  ·
    refine ⟨10448487659039125443007961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27862633757437667848021229 10448487659039125443007961)
    ·
      refine ⟨7836365744279344082255971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10448487659039125443007961 7836365744279344082255971)
      ·
        refine ⟨11754548616419016123383957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7836365744279344082255971 11754548616419016123383957)
        ·
          refine ⟨550994466394641380783623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11754548616419016123383957 550994466394641380783623)
          ·
            refine ⟨826491699591962071175435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550994466394641380783623 826491699591962071175435)
            ·
              refine ⟨1239737549387943106763153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826491699591962071175435 1239737549387943106763153)
              ·
                refine ⟨929803162040957330072365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239737549387943106763153 929803162040957330072365)
                ·
                  refine ⟨348676185765358998777137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929803162040957330072365 348676185765358998777137)
                  ·
                    rfl

theorem cell20_763925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_763925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763925 prefixEnd_763925 := by exact prefixLift 763925
  have htrace : WordTrace (prefixWord ++ tailWord_763925) baseStart_763925 baseEnd_763925 := by
    simpa [prefixWord, tailWord_763925, baseEnd_763925] using wordTrace_append hprefix tailTrace_763925
  have hstable : (prefixWord ++ tailWord_763925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763925).length < 2 ^ (prefixWord ++ tailWord_763925).sum := by decide
  have hdescent : baseEnd_763925 < baseStart_763925 := by decide
  rcases family_descends (prefixWord ++ tailWord_763925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763956 : List Nat := [2, 5, 1, 2, 2, 2, 2, 4]
def baseStart_763956 : Nat := 118140960795 + 763956 * 2 ^ 59
def prefixEnd_763956 : Nat := 4983230072969 + 3 ^ 40 * 763956 * 2
def baseEnd_763956 : Nat := 116230111670020222914559

theorem tailTrace_763956 : CollatzResearch.WordTrace tailWord_763956 prefixEnd_763956 116230111670020222914559 := by
  unfold tailWord_763956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931882210162680071199861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18575842946883573428266481 13931882210162680071199861)
  ·
    refine ⟨1306113957202751256674987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13931882210162680071199861 1306113957202751256674987)
    ·
      refine ⟨1959170935804126885012481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306113957202751256674987 1959170935804126885012481)
      ·
        refine ⟨1469378201853095163759361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959170935804126885012481 1469378201853095163759361)
        ·
          refine ⟨1102033651389821372819521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1469378201853095163759361 1102033651389821372819521)
          ·
            refine ⟨826525238542366029614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102033651389821372819521 826525238542366029614641)
            ·
              refine ⟨619893928906774522210981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826525238542366029614641 619893928906774522210981)
              ·
                refine ⟨116230111670020222914559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619893928906774522210981 116230111670020222914559)
                ·
                  rfl

theorem cell20_763956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_763956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763956 prefixEnd_763956 := by exact prefixLift 763956
  have htrace : WordTrace (prefixWord ++ tailWord_763956) baseStart_763956 baseEnd_763956 := by
    simpa [prefixWord, tailWord_763956, baseEnd_763956] using wordTrace_append hprefix tailTrace_763956
  have hstable : (prefixWord ++ tailWord_763956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763956).length < 2 ^ (prefixWord ++ tailWord_763956).sum := by decide
  have hdescent : baseEnd_763956 < baseStart_763956 := by decide
  rcases family_descends (prefixWord ++ tailWord_763956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763966 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_763966 : Nat := 118140960795 + 763966 * 2 ^ 59
def prefixEnd_763966 : Nat := 4983230072969 + 3 ^ 40 * 763966 * 2
def baseEnd_763966 : Nat := 348694899282545078410303

theorem tailTrace_763966 : CollatzResearch.WordTrace tailWord_763966 prefixEnd_763966 348694899282545078410303 := by
  unfold tailWord_763966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483016143786141481282969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18576086100192754566842501 3483016143786141481282969)
  ·
    refine ⟨2612262107839606110962227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3483016143786141481282969 2612262107839606110962227)
    ·
      refine ⟨3918393161759409166443341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2612262107839606110962227 3918393161759409166443341)
      ·
        refine ⟨1469397435659778437416253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3918393161759409166443341 1469397435659778437416253)
        ·
          refine ⟨551024038372416914031095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1469397435659778437416253 551024038372416914031095)
          ·
            refine ⟨826536057558625371046643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551024038372416914031095 826536057558625371046643)
            ·
              refine ⟨1239804086337938056569965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826536057558625371046643 1239804086337938056569965)
              ·
                refine ⟨464926532376726771213737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1239804086337938056569965 464926532376726771213737)
                ·
                  refine ⟨348694899282545078410303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464926532376726771213737 348694899282545078410303)
                  ·
                    rfl

theorem cell20_763966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_763966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_763966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_763966 prefixEnd_763966 := by exact prefixLift 763966
  have htrace : WordTrace (prefixWord ++ tailWord_763966) baseStart_763966 baseEnd_763966 := by
    simpa [prefixWord, tailWord_763966, baseEnd_763966] using wordTrace_append hprefix tailTrace_763966
  have hstable : (prefixWord ++ tailWord_763966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763966).length < 2 ^ (prefixWord ++ tailWord_763966).sum := by decide
  have hdescent : baseEnd_763966 < baseStart_763966 := by decide
  rcases family_descends (prefixWord ++ tailWord_763966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764005 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_764005 : Nat := 118140960795 + 764005 * 2 ^ 59
def prefixEnd_764005 : Nat := 4983230072969 + 3 ^ 40 * 764005 * 2
def baseEnd_764005 : Nat := 348712699945234276110143

theorem tailTrace_764005 : CollatzResearch.WordTrace tailWord_764005 prefixEnd_764005 348712699945234276110143 := by
  unfold tailWord_764005
  simp only [CollatzResearch.WordTrace]
  refine ⟨27865551597147841510933469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18577034398098561007288979 27865551597147841510933469)
  ·
    refine ⟨10449581848930440566600051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27865551597147841510933469 10449581848930440566600051)
    ·
      refine ⟨15674372773395660849900077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10449581848930440566600051 15674372773395660849900077)
      ·
        refine ⟨5877889790023372818712529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15674372773395660849900077 5877889790023372818712529)
        ·
          refine ⟨4408417342517529614034397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877889790023372818712529 4408417342517529614034397)
          ·
            refine ⟨1653156503444073605262899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4408417342517529614034397 1653156503444073605262899)
            ·
              refine ⟨2479734755166110407894349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653156503444073605262899 2479734755166110407894349)
              ·
                refine ⟨929900533187291402960381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479734755166110407894349 929900533187291402960381)
                ·
                  refine ⟨348712699945234276110143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929900533187291402960381 348712699945234276110143)
                  ·
                    rfl

theorem cell20_764005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_764005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764005 prefixEnd_764005 := by exact prefixLift 764005
  have htrace : WordTrace (prefixWord ++ tailWord_764005) baseStart_764005 baseEnd_764005 := by
    simpa [prefixWord, tailWord_764005, baseEnd_764005] using wordTrace_append hprefix tailTrace_764005
  have hstable : (prefixWord ++ tailWord_764005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764005).length < 2 ^ (prefixWord ++ tailWord_764005).sum := by decide
  have hdescent : baseEnd_764005 < baseStart_764005 := by decide
  rcases family_descends (prefixWord ++ tailWord_764005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764046 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_764046 : Nat := 118140960795 + 764046 * 2 ^ 59
def prefixEnd_764046 : Nat := 4983230072969 + 3 ^ 40 * 764046 * 2
def baseEnd_764046 : Nat := 348731413462420355743309

theorem tailTrace_764046 : CollatzResearch.WordTrace tailWord_764046 prefixEnd_764046 348731413462420355743309 := by
  unfold tailWord_764046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483380873749913189146999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18578031326666203675450661 3483380873749913189146999)
  ·
    refine ⟨5225071310624869783720499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3483380873749913189146999 5225071310624869783720499)
    ·
      refine ⟨7837606965937304675580749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225071310624869783720499 7837606965937304675580749)
      ·
        refine ⟨2939102612226489253342781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7837606965937304675580749 2939102612226489253342781)
        ·
          refine ⟨1102163479584933470003543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2939102612226489253342781 1102163479584933470003543)
          ·
            refine ⟨1653245219377400205005315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102163479584933470003543 1653245219377400205005315)
            ·
              refine ⟨2479867829066100307507973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653245219377400205005315 2479867829066100307507973)
              ·
                refine ⟨464975217949893807657745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2479867829066100307507973 464975217949893807657745)
                ·
                  refine ⟨348731413462420355743309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464975217949893807657745 348731413462420355743309)
                  ·
                    rfl

theorem cell20_764046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_764046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764046 prefixEnd_764046 := by exact prefixLift 764046
  have htrace : WordTrace (prefixWord ++ tailWord_764046) baseStart_764046 baseEnd_764046 := by
    simpa [prefixWord, tailWord_764046, baseEnd_764046] using wordTrace_append hprefix tailTrace_764046
  have hstable : (prefixWord ++ tailWord_764046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764046).length < 2 ^ (prefixWord ++ tailWord_764046).sum := by decide
  have hdescent : baseEnd_764046 < baseStart_764046 := by decide
  rcases family_descends (prefixWord ++ tailWord_764046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764050 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_764050 : Nat := 118140960795 + 764050 * 2 ^ 59
def prefixEnd_764050 : Nat := 4983230072969 + 3 ^ 40 * 764050 * 2
def baseEnd_764050 : Nat := 348733239171414119609959

theorem tailTrace_764050 : CollatzResearch.WordTrace tailWord_764050 prefixEnd_764050 348733239171414119609959 := by
  unfold tailWord_764050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966798220496203549080401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18578128587989876130881069 6966798220496203549080401)
  ·
    refine ⟨5225098665372152661810301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6966798220496203549080401 5225098665372152661810301)
    ·
      refine ⟨1959411999514557248178863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5225098665372152661810301 1959411999514557248178863)
      ·
        refine ⟨2939117999271835872268295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959411999514557248178863 2939117999271835872268295)
        ·
          refine ⟨4408676998907753808402443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939117999271835872268295 4408676998907753808402443)
          ·
            refine ⟨6613015498361630712603665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408676998907753808402443 6613015498361630712603665)
            ·
              refine ⟨4959761623771223034452749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613015498361630712603665 4959761623771223034452749)
              ·
                refine ⟨1859910608914208637919781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959761623771223034452749 1859910608914208637919781)
                ·
                  refine ⟨348733239171414119609959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859910608914208637919781 348733239171414119609959)
                  ·
                    rfl

theorem cell20_764050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_764050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764050 prefixEnd_764050 := by exact prefixLift 764050
  have htrace : WordTrace (prefixWord ++ tailWord_764050) baseStart_764050 baseEnd_764050 := by
    simpa [prefixWord, tailWord_764050, baseEnd_764050] using wordTrace_append hprefix tailTrace_764050
  have hstable : (prefixWord ++ tailWord_764050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764050).length < 2 ^ (prefixWord ++ tailWord_764050).sum := by decide
  have hdescent : baseEnd_764050 < baseStart_764050 := by decide
  rcases family_descends (prefixWord ++ tailWord_764050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764123 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_764123 : Nat := 118140960795 + 764123 * 2 ^ 59
def prefixEnd_764123 : Nat := 4983230072969 + 3 ^ 40 * 764123 * 2
def baseEnd_764123 : Nat := 348766558360550310176327

theorem tailTrace_764123 : CollatzResearch.WordTrace tailWord_764123 prefixEnd_764123 348766558360550310176327 := by
  unfold tailWord_764123
  simp only [CollatzResearch.WordTrace]
  refine ⟨27869855410720347663729023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18579903607146898442486015 27869855410720347663729023)
  ·
    refine ⟨41804783116080521495593535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27869855410720347663729023 41804783116080521495593535)
    ·
      refine ⟨62707174674120782243390303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41804783116080521495593535 62707174674120782243390303)
      ·
        refine ⟨94060762011181173365085455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62707174674120782243390303 94060762011181173365085455)
        ·
          refine ⟨141091143016771760047628183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94060762011181173365085455 141091143016771760047628183)
          ·
            refine ⟨211636714525157640071442275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141091143016771760047628183 211636714525157640071442275)
            ·
              refine ⟨317455071787736460107163413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211636714525157640071442275 317455071787736460107163413)
              ·
                refine ⟨14880706490050146567523285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 317455071787736460107163413 14880706490050146567523285)
                ·
                  refine ⟨348766558360550310176327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14880706490050146567523285 348766558360550310176327)
                  ·
                    rfl

theorem cell20_764123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_764123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764123 prefixEnd_764123 := by exact prefixLift 764123
  have htrace : WordTrace (prefixWord ++ tailWord_764123) baseStart_764123 baseEnd_764123 := by
    simpa [prefixWord, tailWord_764123, baseEnd_764123] using wordTrace_append hprefix tailTrace_764123
  have hstable : (prefixWord ++ tailWord_764123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764123).length < 2 ^ (prefixWord ++ tailWord_764123).sum := by decide
  have hdescent : baseEnd_764123 < baseStart_764123 := by decide
  rcases family_descends (prefixWord ++ tailWord_764123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764133 : List Nat := [1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_764133 : Nat := 118140960795 + 764133 * 2 ^ 59
def prefixEnd_764133 : Nat := 4983230072969 + 3 ^ 40 * 764133 * 2
def baseEnd_764133 : Nat := 116257040877678239947651

theorem tailTrace_764133 : CollatzResearch.WordTrace tailWord_764133 prefixEnd_764133 116257040877678239947651 := by
  unfold tailWord_764133
  simp only [CollatzResearch.WordTrace]
  refine ⟨27870220140684119371593053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18580146760456079581062035 27870220140684119371593053)
  ·
    refine ⟨10451332552756544764347395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27870220140684119371593053 10451332552756544764347395)
    ·
      refine ⟨15676998829134817146521093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10451332552756544764347395 15676998829134817146521093)
      ·
        refine ⟨2939437280462778214972705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15676998829134817146521093 2939437280462778214972705)
        ·
          refine ⟨2204577960347083661229529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2939437280462778214972705 2204577960347083661229529)
          ·
            refine ⟨1653433470260312745922147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204577960347083661229529 1653433470260312745922147)
            ·
              refine ⟨2480150205390469118883221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653433470260312745922147 2480150205390469118883221)
              ·
                refine ⟨116257040877678239947651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2480150205390469118883221 116257040877678239947651)
                ·
                  rfl

theorem cell20_764133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_764133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764133 prefixEnd_764133 := by exact prefixLift 764133
  have htrace : WordTrace (prefixWord ++ tailWord_764133) baseStart_764133 baseEnd_764133 := by
    simpa [prefixWord, tailWord_764133, baseEnd_764133] using wordTrace_append hprefix tailTrace_764133
  have hstable : (prefixWord ++ tailWord_764133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764133).length < 2 ^ (prefixWord ++ tailWord_764133).sum := by decide
  have hdescent : baseEnd_764133 < baseStart_764133 := by decide
  rcases family_descends (prefixWord ++ tailWord_764133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764143 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 2]
def baseStart_764143 : Nat := 118140960795 + 764143 * 2 ^ 59
def prefixEnd_764143 : Nat := 4983230072969 + 3 ^ 40 * 764143 * 2
def baseEnd_764143 : Nat := 348775686905519129509579

theorem tailTrace_764143 : CollatzResearch.WordTrace tailWord_764143 prefixEnd_764143 348775686905519129509579 := by
  unfold tailWord_764143
  simp only [CollatzResearch.WordTrace]
  refine ⟨27870584870647891079457083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18580389913765260719638055 27870584870647891079457083)
  ·
    refine ⟨41805877305971836619185625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27870584870647891079457083 41805877305971836619185625)
    ·
      refine ⟨31354407979478877464389219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41805877305971836619185625 31354407979478877464389219)
      ·
        refine ⟨47031611969218316196583829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31354407979478877464389219 47031611969218316196583829)
        ·
          refine ⟨2204606811057108571714867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47031611969218316196583829 2204606811057108571714867)
          ·
            refine ⟨3306910216585662857572301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204606811057108571714867 3306910216585662857572301)
            ·
              refine ⟨1240091331219623571589613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3306910216585662857572301 1240091331219623571589613)
              ·
                refine ⟨465034249207358839346105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240091331219623571589613 465034249207358839346105)
                ·
                  refine ⟨348775686905519129509579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465034249207358839346105 348775686905519129509579)
                  ·
                    rfl

theorem cell20_764143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 2].length) (baseStart_764143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764143 prefixEnd_764143 := by exact prefixLift 764143
  have htrace : WordTrace (prefixWord ++ tailWord_764143) baseStart_764143 baseEnd_764143 := by
    simpa [prefixWord, tailWord_764143, baseEnd_764143] using wordTrace_append hprefix tailTrace_764143
  have hstable : (prefixWord ++ tailWord_764143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764143).length < 2 ^ (prefixWord ++ tailWord_764143).sum := by decide
  have hdescent : baseEnd_764143 < baseStart_764143 := by decide
  rcases family_descends (prefixWord ++ tailWord_764143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764154 : List Nat := [3, 1, 1, 1, 1, 5, 8]
def baseStart_764154 : Nat := 118140960795 + 764154 * 2 ^ 59
def prefixEnd_764154 : Nat := 4983230072969 + 3 ^ 40 * 764154 * 2
def baseEnd_764154 : Nat := 38753411956139108904763

theorem tailTrace_764154 : CollatzResearch.WordTrace tailWord_764154 prefixEnd_764154 38753411956139108904763 := by
  unfold tailWord_764154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967746518402009989526879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18580657382405359972071677 6967746518402009989526879)
  ·
    refine ⟨10451619777603014984290319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6967746518402009989526879 10451619777603014984290319)
    ·
      refine ⟨15677429666404522476435479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10451619777603014984290319 15677429666404522476435479)
      ·
        refine ⟨23516144499606783714653219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15677429666404522476435479 23516144499606783714653219)
        ·
          refine ⟨35274216749410175571979829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23516144499606783714653219 35274216749410175571979829)
          ·
            refine ⟨3306957820257203959873109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35274216749410175571979829 3306957820257203959873109)
            ·
              refine ⟨38753411956139108904763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3306957820257203959873109 38753411956139108904763)
              ·
                rfl

theorem cell20_764154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_764154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764154 prefixEnd_764154 := by exact prefixLift 764154
  have htrace : WordTrace (prefixWord ++ tailWord_764154) baseStart_764154 baseEnd_764154 := by
    simpa [prefixWord, tailWord_764154, baseEnd_764154] using wordTrace_append hprefix tailTrace_764154
  have hstable : (prefixWord ++ tailWord_764154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764154).length < 2 ^ (prefixWord ++ tailWord_764154).sum := by decide
  have hdescent : baseEnd_764154 < baseStart_764154 := by decide
  rcases family_descends (prefixWord ++ tailWord_764154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764209 : List Nat := [1, 2, 2, 3, 5, 7]
def baseStart_764209 : Nat := 118140960795 + 764209 * 2 ^ 59
def prefixEnd_764209 : Nat := 4983230072969 + 3 ^ 40 * 764209 * 2
def baseEnd_764209 : Nat := 12918733744589490122567

theorem tailTrace_764209 : CollatzResearch.WordTrace tailWord_764209 prefixEnd_764209 12918733744589490122567 := by
  unfold tailWord_764209
  simp only [CollatzResearch.WordTrace]
  refine ⟨27872992088408784351359681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18581994725605856234239787 27872992088408784351359681)
  ·
    refine ⟨20904744066306588263519761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27872992088408784351359681 20904744066306588263519761)
    ·
      refine ⟨15678558049729941197639821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20904744066306588263519761 15678558049729941197639821)
      ·
        refine ⟨5879459268648727949114933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15678558049729941197639821 5879459268648727949114933)
        ·
          refine ⟨551199306435818245229525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5879459268648727949114933 551199306435818245229525)
          ·
            refine ⟨12918733744589490122567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 551199306435818245229525 12918733744589490122567)
            ·
              rfl

theorem cell20_764209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 7].length) (baseStart_764209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764209 prefixEnd_764209 := by exact prefixLift 764209
  have htrace : WordTrace (prefixWord ++ tailWord_764209) baseStart_764209 baseEnd_764209 := by
    simpa [prefixWord, tailWord_764209, baseEnd_764209] using wordTrace_append hprefix tailTrace_764209
  have hstable : (prefixWord ++ tailWord_764209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764209).length < 2 ^ (prefixWord ++ tailWord_764209).sum := by decide
  have hdescent : baseEnd_764209 < baseStart_764209 := by decide
  rcases family_descends (prefixWord ++ tailWord_764209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764212 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_764212 : Nat := 118140960795 + 764212 * 2 ^ 59
def prefixEnd_764212 : Nat := 4983230072969 + 3 ^ 40 * 764212 * 2
def baseEnd_764212 : Nat := 348807180385661556209297

theorem tailTrace_764212 : CollatzResearch.WordTrace tailWord_764212 prefixEnd_764212 348807180385661556209297 := by
  unfold tailWord_764212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13936550753698957931859445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18582067671598610575812593 13936550753698957931859445)
  ·
    refine ⟨1306551633159277306111823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13936550753698957931859445 1306551633159277306111823)
    ·
      refine ⟨1959827449738915959167735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306551633159277306111823 1959827449738915959167735)
      ·
        refine ⟨2939741174608373938751603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959827449738915959167735 2939741174608373938751603)
        ·
          refine ⟨4409611761912560908127405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939741174608373938751603 4409611761912560908127405)
          ·
            refine ⟨1653604410717210340547777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4409611761912560908127405 1653604410717210340547777)
            ·
              refine ⟨1240203308037907755410833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653604410717210340547777 1240203308037907755410833)
              ·
                refine ⟨930152481028430816558125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240203308037907755410833 930152481028430816558125)
                ·
                  refine ⟨348807180385661556209297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930152481028430816558125 348807180385661556209297)
                  ·
                    rfl

theorem cell20_764212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_764212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764212 prefixEnd_764212 := by exact prefixLift 764212
  have htrace : WordTrace (prefixWord ++ tailWord_764212) baseStart_764212 baseEnd_764212 := by
    simpa [prefixWord, tailWord_764212, baseEnd_764212] using wordTrace_append hprefix tailTrace_764212
  have hstable : (prefixWord ++ tailWord_764212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764212).length < 2 ^ (prefixWord ++ tailWord_764212).sum := by decide
  have hdescent : baseEnd_764212 < baseStart_764212 := by decide
  rcases family_descends (prefixWord ++ tailWord_764212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764216 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_764216 : Nat := 118140960795 + 764216 * 2 ^ 59
def prefixEnd_764216 : Nat := 4983230072969 + 3 ^ 40 * 764216 * 2
def baseEnd_764216 : Nat := 348809006094655320075947

theorem tailTrace_764216 : CollatzResearch.WordTrace tailWord_764216 prefixEnd_764216 348809006094655320075947 := by
  unfold tailWord_764216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13936623699691712273432251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18582164932922283031243001 13936623699691712273432251)
  ·
    refine ⟨20904935549537568410148377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13936623699691712273432251 20904935549537568410148377)
    ·
      refine ⟨15678701662153176307611283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20904935549537568410148377 15678701662153176307611283)
      ·
        refine ⟨23518052493229764461416925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15678701662153176307611283 23518052493229764461416925)
        ·
          refine ⟨8819269684961161673031347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23518052493229764461416925 8819269684961161673031347)
          ·
            refine ⟨13228904527441742509547021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819269684961161673031347 13228904527441742509547021)
            ·
              refine ⟨4960839197790653441080133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13228904527441742509547021 4960839197790653441080133)
              ·
                refine ⟨930157349585747520202525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4960839197790653441080133 930157349585747520202525)
                ·
                  refine ⟨348809006094655320075947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930157349585747520202525 348809006094655320075947)
                  ·
                    rfl

theorem cell20_764216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_764216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764216 prefixEnd_764216 := by exact prefixLift 764216
  have htrace : WordTrace (prefixWord ++ tailWord_764216) baseStart_764216 baseEnd_764216 := by
    simpa [prefixWord, tailWord_764216, baseEnd_764216] using wordTrace_append hprefix tailTrace_764216
  have hstable : (prefixWord ++ tailWord_764216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764216).length < 2 ^ (prefixWord ++ tailWord_764216).sum := by decide
  have hdescent : baseEnd_764216 < baseStart_764216 := by decide
  rcases family_descends (prefixWord ++ tailWord_764216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764223 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_764223 : Nat := 118140960795 + 764223 * 2 ^ 59
def prefixEnd_764223 : Nat := 4983230072969 + 3 ^ 40 * 764223 * 2
def baseEnd_764223 : Nat := 348812201085394406842585

theorem tailTrace_764223 : CollatzResearch.WordTrace tailWord_764223 prefixEnd_764223 348812201085394406842585 := by
  unfold tailWord_764223
  simp only [CollatzResearch.WordTrace]
  refine ⟨27873502710358064742369323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18582335140238709828246215 27873502710358064742369323)
  ·
    refine ⟨41810254065537097113553985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27873502710358064742369323 41810254065537097113553985)
    ·
      refine ⟨31357690549152822835165489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41810254065537097113553985 31357690549152822835165489)
      ·
        refine ⟨23518267911864617126374117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31357690549152822835165489 23518267911864617126374117)
        ·
          refine ⟨4409675233474615711195147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23518267911864617126374117 4409675233474615711195147)
          ·
            refine ⟨6614512850211923566792721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409675233474615711195147 6614512850211923566792721)
            ·
              refine ⟨4960884637658942675094541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6614512850211923566792721 4960884637658942675094541)
              ·
                refine ⟨1860331739122103503160453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4960884637658942675094541 1860331739122103503160453)
                ·
                  refine ⟨348812201085394406842585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860331739122103503160453 348812201085394406842585)
                  ·
                    rfl

theorem cell20_764223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_764223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764223 prefixEnd_764223 := by exact prefixLift 764223
  have htrace : WordTrace (prefixWord ++ tailWord_764223) baseStart_764223 baseEnd_764223 := by
    simpa [prefixWord, tailWord_764223, baseEnd_764223] using wordTrace_append hprefix tailTrace_764223
  have hstable : (prefixWord ++ tailWord_764223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764223).length < 2 ^ (prefixWord ++ tailWord_764223).sum := by decide
  have hdescent : baseEnd_764223 < baseStart_764223 := by decide
  rcases family_descends (prefixWord ++ tailWord_764223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764247 : List Nat := [1, 1, 3, 2, 3, 1, 5, 4]
def baseStart_764247 : Nat := 118140960795 + 764247 * 2 ^ 59
def prefixEnd_764247 : Nat := 4983230072969 + 3 ^ 40 * 764247 * 2
def baseEnd_764247 : Nat := 116274385113118996680829

theorem tailTrace_764247 : CollatzResearch.WordTrace tailWord_764247 prefixEnd_764247 116274385113118996680829 := by
  unfold tailWord_764247
  simp only [CollatzResearch.WordTrace]
  refine ⟨27874378062271116841242995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18582918708180744560828663 27874378062271116841242995)
  ·
    refine ⟨41811567093406675261864493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27874378062271116841242995 41811567093406675261864493)
    ·
      refine ⟨15679337660027503223199185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41811567093406675261864493 15679337660027503223199185)
      ·
        refine ⟨11759503245020627417399389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15679337660027503223199185 11759503245020627417399389)
        ·
          refine ⟨4409813716882735281524771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11759503245020627417399389 4409813716882735281524771)
          ·
            refine ⟨6614720575324102922287157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409813716882735281524771 6614720575324102922287157)
            ·
              refine ⟨620130053936634648964421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6614720575324102922287157 620130053936634648964421)
              ·
                refine ⟨116274385113118996680829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620130053936634648964421 116274385113118996680829)
                ·
                  rfl

theorem cell20_764247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_764247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764247 prefixEnd_764247 := by exact prefixLift 764247
  have htrace : WordTrace (prefixWord ++ tailWord_764247) baseStart_764247 baseEnd_764247 := by
    simpa [prefixWord, tailWord_764247, baseEnd_764247] using wordTrace_append hprefix tailTrace_764247
  have hstable : (prefixWord ++ tailWord_764247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764247).length < 2 ^ (prefixWord ++ tailWord_764247).sum := by decide
  have hdescent : baseEnd_764247 < baseStart_764247 := by decide
  rcases family_descends (prefixWord ++ tailWord_764247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764275 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_764275 : Nat := 118140960795 + 764275 * 2 ^ 59
def prefixEnd_764275 : Nat := 4983230072969 + 3 ^ 40 * 764275 * 2
def baseEnd_764275 : Nat := 348835935302313337109039

theorem tailTrace_764275 : CollatzResearch.WordTrace tailWord_764275 prefixEnd_764275 348835935302313337109039 := by
  unfold tailWord_764275
  simp only [CollatzResearch.WordTrace]
  refine ⟨27875399306169677623262279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18583599537446451748841519 27875399306169677623262279)
  ·
    refine ⟨41813098959254516434893419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27875399306169677623262279 41813098959254516434893419)
    ·
      refine ⟨62719648438881774652340129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41813098959254516434893419 62719648438881774652340129)
      ·
        refine ⟨47039736329161330989255097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62719648438881774652340129 47039736329161330989255097)
        ·
          refine ⟨35279802246870998241941323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47039736329161330989255097 35279802246870998241941323)
          ·
            refine ⟨52919703370306497362911985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35279802246870998241941323 52919703370306497362911985)
            ·
              refine ⟨39689777527729873022183989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52919703370306497362911985 39689777527729873022183989)
              ·
                refine ⟨3720916643224675595829749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39689777527729873022183989 3720916643224675595829749)
                ·
                  refine ⟨348835935302313337109039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3720916643224675595829749 348835935302313337109039)
                  ·
                    rfl

theorem cell20_764275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_764275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764275 prefixEnd_764275 := by exact prefixLift 764275
  have htrace : WordTrace (prefixWord ++ tailWord_764275) baseStart_764275 baseEnd_764275 := by
    simpa [prefixWord, tailWord_764275, baseEnd_764275] using wordTrace_append hprefix tailTrace_764275
  have hstable : (prefixWord ++ tailWord_764275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764275).length < 2 ^ (prefixWord ++ tailWord_764275).sum := by decide
  have hdescent : baseEnd_764275 < baseStart_764275 := by decide
  rcases family_descends (prefixWord ++ tailWord_764275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764298 : List Nat := [3, 1, 2, 5, 2, 1, 2, 4]
def baseStart_764298 : Nat := 118140960795 + 764298 * 2 ^ 59
def prefixEnd_764298 : Nat := 4983230072969 + 3 ^ 40 * 764298 * 2
def baseEnd_764298 : Nat := 116282144376342493114093

theorem tailTrace_764298 : CollatzResearch.WordTrace tailWord_764298 prefixEnd_764298 116282144376342493114093 := by
  unfold tailWord_764298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6969059546271588137837387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18584158790057568367566365 6969059546271588137837387)
  ·
    refine ⟨10453589319407382206756081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6969059546271588137837387 10453589319407382206756081)
    ·
      refine ⟨7840191989555536655067061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10453589319407382206756081 7840191989555536655067061)
      ·
        refine ⟨735017999020831561412537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7840191989555536655067061 735017999020831561412537)
        ·
          refine ⟨551263499265623671059403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735017999020831561412537 551263499265623671059403)
          ·
            refine ⟨826895248898435506589105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551263499265623671059403 826895248898435506589105)
            ·
              refine ⟨620171436673826629941829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826895248898435506589105 620171436673826629941829)
              ·
                refine ⟨116282144376342493114093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620171436673826629941829 116282144376342493114093)
                ·
                  rfl

theorem cell20_764298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_764298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764298 prefixEnd_764298 := by exact prefixLift 764298
  have htrace : WordTrace (prefixWord ++ tailWord_764298) baseStart_764298 baseEnd_764298 := by
    simpa [prefixWord, tailWord_764298, baseEnd_764298] using wordTrace_append hprefix tailTrace_764298
  have hstable : (prefixWord ++ tailWord_764298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764298).length < 2 ^ (prefixWord ++ tailWord_764298).sum := by decide
  have hdescent : baseEnd_764298 < baseStart_764298 := by decide
  rcases family_descends (prefixWord ++ tailWord_764298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764299 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_764299 : Nat := 118140960795 + 764299 * 2 ^ 59
def prefixEnd_764299 : Nat := 4983230072969 + 3 ^ 40 * 764299 * 2
def baseEnd_764299 : Nat := 348846889556275920308941

theorem tailTrace_764299 : CollatzResearch.WordTrace tailWord_764299 prefixEnd_764299 348846889556275920308941 := by
  unfold tailWord_764299
  simp only [CollatzResearch.WordTrace]
  refine ⟨27876274658082729722135951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18584183105388486481423967 27876274658082729722135951)
  ·
    refine ⟨41814411987124094583203927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27876274658082729722135951 41814411987124094583203927)
    ·
      refine ⟨62721617980686141874805891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41814411987124094583203927 62721617980686141874805891)
      ·
        refine ⟨94082426971029212812208837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62721617980686141874805891 94082426971029212812208837)
        ·
          refine ⟨17640455057067977402289157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94082426971029212812208837 17640455057067977402289157)
          ·
            refine ⟨3307585323200245762929217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17640455057067977402289157 3307585323200245762929217)
            ·
              refine ⟨2480688992400184322196913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3307585323200245762929217 2480688992400184322196913)
              ·
                refine ⟨1860516744300138241647685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2480688992400184322196913 1860516744300138241647685)
                ·
                  refine ⟨348846889556275920308941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860516744300138241647685 348846889556275920308941)
                  ·
                    rfl

theorem cell20_764299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_764299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764299 prefixEnd_764299 := by exact prefixLift 764299
  have htrace : WordTrace (prefixWord ++ tailWord_764299) baseStart_764299 baseEnd_764299 := by
    simpa [prefixWord, tailWord_764299, baseEnd_764299] using wordTrace_append hprefix tailTrace_764299
  have hstable : (prefixWord ++ tailWord_764299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764299).length < 2 ^ (prefixWord ++ tailWord_764299).sum := by decide
  have hdescent : baseEnd_764299 < baseStart_764299 := by decide
  rcases family_descends (prefixWord ++ tailWord_764299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764302 : List Nat := [4, 1, 1, 4, 1, 1, 4, 4]
def baseStart_764302 : Nat := 118140960795 + 764302 * 2 ^ 59
def prefixEnd_764302 : Nat := 4983230072969 + 3 ^ 40 * 764302 * 2
def baseEnd_764302 : Nat := 116282752946007081069643

theorem tailTrace_764302 : CollatzResearch.WordTrace tailWord_764302 prefixEnd_764302 116282752946007081069643 := by
  unfold tailWord_764302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484548009633982654311895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18584256051381240822996773 3484548009633982654311895)
  ·
    refine ⟨5226822014450973981467843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3484548009633982654311895 5226822014450973981467843)
    ·
      refine ⟨7840233021676460972201765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5226822014450973981467843 7840233021676460972201765)
      ·
        refine ⟨1470043691564336432287831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7840233021676460972201765 1470043691564336432287831)
        ·
          refine ⟨2205065537346504648431747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470043691564336432287831 2205065537346504648431747)
          ·
            refine ⟨3307598306019756972647621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205065537346504648431747 3307598306019756972647621)
            ·
              refine ⟨620174682378704432371429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3307598306019756972647621 620174682378704432371429)
              ·
                refine ⟨116282752946007081069643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620174682378704432371429 116282752946007081069643)
                ·
                  rfl

theorem cell20_764302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_764302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764302 prefixEnd_764302 := by exact prefixLift 764302
  have htrace : WordTrace (prefixWord ++ tailWord_764302) baseStart_764302 baseEnd_764302 := by
    simpa [prefixWord, tailWord_764302, baseEnd_764302] using wordTrace_append hprefix tailTrace_764302
  have hstable : (prefixWord ++ tailWord_764302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764302).length < 2 ^ (prefixWord ++ tailWord_764302).sum := by decide
  have hdescent : baseEnd_764302 < baseStart_764302 := by decide
  rcases family_descends (prefixWord ++ tailWord_764302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764312 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 2]
def baseStart_764312 : Nat := 118140960795 + 764312 * 2 ^ 59
def prefixEnd_764312 : Nat := 4983230072969 + 3 ^ 40 * 764312 * 2
def baseEnd_764312 : Nat := 348852823110505652875555

theorem tailTrace_764312 : CollatzResearch.WordTrace tailWord_764312 prefixEnd_764312 348852823110505652875555 := by
  unfold tailWord_764312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938374403517816471179595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18584499204690421961572793 13938374403517816471179595)
  ·
    refine ⟨20907561605276724706769393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13938374403517816471179595 20907561605276724706769393)
    ·
      refine ⟨15680671203957543530077045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20907561605276724706769393 15680671203957543530077045)
      ·
        refine ⟨1470062925371019705944723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15680671203957543530077045 1470062925371019705944723)
        ·
          refine ⟨2205094388056529558917085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470062925371019705944723 2205094388056529558917085)
          ·
            refine ⟨826910395521198584593907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2205094388056529558917085 826910395521198584593907)
            ·
              refine ⟨1240365593281797876890861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826910395521198584593907 1240365593281797876890861)
              ·
                refine ⟨465137097480674203834073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240365593281797876890861 465137097480674203834073)
                ·
                  refine ⟨348852823110505652875555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465137097480674203834073 348852823110505652875555)
                  ·
                    rfl

theorem cell20_764312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_764312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764312 prefixEnd_764312 := by exact prefixLift 764312
  have htrace : WordTrace (prefixWord ++ tailWord_764312) baseStart_764312 baseEnd_764312 := by
    simpa [prefixWord, tailWord_764312, baseEnd_764312] using wordTrace_append hprefix tailTrace_764312
  have hstable : (prefixWord ++ tailWord_764312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764312).length < 2 ^ (prefixWord ++ tailWord_764312).sum := by decide
  have hdescent : baseEnd_764312 < baseStart_764312 := by decide
  rcases family_descends (prefixWord ++ tailWord_764312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764313 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_764313 : Nat := 118140960795 + 764313 * 2 ^ 59
def prefixEnd_764313 : Nat := 4983230072969 + 3 ^ 40 * 764313 * 2
def baseEnd_764313 : Nat := 348853279537754093842217

theorem tailTrace_764313 : CollatzResearch.WordTrace tailWord_764313 prefixEnd_764313 348853279537754093842217 := by
  unfold tailWord_764313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27876785280032010113145593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18584523520021340075430395 27876785280032010113145593)
  ·
    refine ⟨20907588960024007584859195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27876785280032010113145593 20907588960024007584859195)
    ·
      refine ⟨31361383440036011377288793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20907588960024007584859195 31361383440036011377288793)
      ·
        refine ⟨23521037580027008532966595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31361383440036011377288793 23521037580027008532966595)
        ·
          refine ⟨35281556370040512799449893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23521037580027008532966595 35281556370040512799449893)
          ·
            refine ⟨6615291819382596149896855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35281556370040512799449893 6615291819382596149896855)
            ·
              refine ⟨9922937729073894224845283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615291819382596149896855 9922937729073894224845283)
              ·
                refine ⟨14884406593610841337267925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922937729073894224845283 14884406593610841337267925)
                ·
                  refine ⟨348853279537754093842217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14884406593610841337267925 348853279537754093842217)
                  ·
                    rfl

theorem cell20_764313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_764313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764313 prefixEnd_764313 := by exact prefixLift 764313
  have htrace : WordTrace (prefixWord ++ tailWord_764313) baseStart_764313 baseEnd_764313 := by
    simpa [prefixWord, tailWord_764313, baseEnd_764313] using wordTrace_append hprefix tailTrace_764313
  have hstable : (prefixWord ++ tailWord_764313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764313).length < 2 ^ (prefixWord ++ tailWord_764313).sum := by decide
  have hdescent : baseEnd_764313 < baseStart_764313 := by decide
  rcases family_descends (prefixWord ++ tailWord_764313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764413 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_764413 : Nat := 118140960795 + 764413 * 2 ^ 59
def prefixEnd_764413 : Nat := 4983230072969 + 3 ^ 40 * 764413 * 2
def baseEnd_764413 : Nat := 348898922262598190508475

theorem tailTrace_764413 : CollatzResearch.WordTrace tailWord_764413 prefixEnd_764413 348898922262598190508475 := by
  unfold tailWord_764413
  simp only [CollatzResearch.WordTrace]
  refine ⟨27880432579669727191785893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18586955053113151461190595 27880432579669727191785893)
  ·
    refine ⟨5227581108688073848459855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27880432579669727191785893 5227581108688073848459855)
    ·
      refine ⟨7841371663032110772689783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5227581108688073848459855 7841371663032110772689783)
      ·
        refine ⟨11762057494548166159034675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7841371663032110772689783 11762057494548166159034675)
        ·
          refine ⟨17643086241822249238552013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11762057494548166159034675 17643086241822249238552013)
          ·
            refine ⟨6616157340683343464457005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17643086241822249238552013 6616157340683343464457005)
            ·
              refine ⟨2481059002756253799171377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6616157340683343464457005 2481059002756253799171377)
              ·
                refine ⟨1860794252067190349378533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481059002756253799171377 1860794252067190349378533)
                ·
                  refine ⟨348898922262598190508475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860794252067190349378533 348898922262598190508475)
                  ·
                    rfl

theorem cell20_764413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_764413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764413 prefixEnd_764413 := by exact prefixLift 764413
  have htrace : WordTrace (prefixWord ++ tailWord_764413) baseStart_764413 baseEnd_764413 := by
    simpa [prefixWord, tailWord_764413, baseEnd_764413] using wordTrace_append hprefix tailTrace_764413
  have hstable : (prefixWord ++ tailWord_764413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764413).length < 2 ^ (prefixWord ++ tailWord_764413).sum := by decide
  have hdescent : baseEnd_764413 < baseStart_764413 := by decide
  rcases family_descends (prefixWord ++ tailWord_764413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764422 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_764422 : Nat := 118140960795 + 764422 * 2 ^ 59
def prefixEnd_764422 : Nat := 4983230072969 + 3 ^ 40 * 764422 * 2
def baseEnd_764422 : Nat := 348903030107834159208439

theorem tailTrace_764422 : CollatzResearch.WordTrace tailWord_764422 prefixEnd_764422 348903030107834159208439 := by
  unfold tailWord_764422
  simp only [CollatzResearch.WordTrace]
  refine ⟨871273776144910054026985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18587173891091414485909013 871273776144910054026985)
  ·
    refine ⟨653455332108682540520239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 871273776144910054026985 653455332108682540520239)
    ·
      refine ⟨980182998163023810780359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653455332108682540520239 980182998163023810780359)
      ·
        refine ⟨1470274497244535716170539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980182998163023810780359 1470274497244535716170539)
        ·
          refine ⟨2205411745866803574255809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470274497244535716170539 2205411745866803574255809)
          ·
            refine ⟨1654058809400102680691857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2205411745866803574255809 1654058809400102680691857)
            ·
              refine ⟨1240544107050077010518893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654058809400102680691857 1240544107050077010518893)
              ·
                refine ⟨465204040143778878944585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240544107050077010518893 465204040143778878944585)
                ·
                  refine ⟨348903030107834159208439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465204040143778878944585 348903030107834159208439)
                  ·
                    rfl

theorem cell20_764422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_764422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764422 prefixEnd_764422 := by exact prefixLift 764422
  have htrace : WordTrace (prefixWord ++ tailWord_764422) baseStart_764422 baseEnd_764422 := by
    simpa [prefixWord, tailWord_764422, baseEnd_764422] using wordTrace_append hprefix tailTrace_764422
  have hstable : (prefixWord ++ tailWord_764422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764422).length < 2 ^ (prefixWord ++ tailWord_764422).sum := by decide
  have hdescent : baseEnd_764422 < baseStart_764422 := by decide
  rcases family_descends (prefixWord ++ tailWord_764422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764444 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_764444 : Nat := 118140960795 + 764444 * 2 ^ 59
def prefixEnd_764444 : Nat := 4983230072969 + 3 ^ 40 * 764444 * 2
def baseEnd_764444 : Nat := 348913071507299860475015

theorem tailTrace_764444 : CollatzResearch.WordTrace tailWord_764444 prefixEnd_764444 348913071507299860475015 := by
  unfold tailWord_764444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13940781621278709743082193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18587708828371612990776257 13940781621278709743082193)
  ·
    refine ⟨10455586215959032307311645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13940781621278709743082193 10455586215959032307311645)
    ·
      refine ⟨3920844830984637115241867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10455586215959032307311645 3920844830984637115241867)
      ·
        refine ⟨5881267246476955672862801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920844830984637115241867 5881267246476955672862801)
        ·
          refine ⟨4410950434857716754647101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881267246476955672862801 4410950434857716754647101)
          ·
            refine ⟨1654106413071643782992663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4410950434857716754647101 1654106413071643782992663)
            ·
              refine ⟨2481159619607465674488995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654106413071643782992663 2481159619607465674488995)
              ·
                refine ⟨3721739429411198511733493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481159619607465674488995 3721739429411198511733493)
                ·
                  refine ⟨348913071507299860475015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3721739429411198511733493 348913071507299860475015)
                  ·
                    rfl

theorem cell20_764444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_764444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764444 prefixEnd_764444 := by exact prefixLift 764444
  have htrace : WordTrace (prefixWord ++ tailWord_764444) baseStart_764444 baseEnd_764444 := by
    simpa [prefixWord, tailWord_764444, baseEnd_764444] using wordTrace_append hprefix tailTrace_764444
  have hstable : (prefixWord ++ tailWord_764444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764444).length < 2 ^ (prefixWord ++ tailWord_764444).sum := by decide
  have hdescent : baseEnd_764444 < baseStart_764444 := by decide
  rcases family_descends (prefixWord ++ tailWord_764444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764451 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_764451 : Nat := 118140960795 + 764451 * 2 ^ 59
def prefixEnd_764451 : Nat := 4983230072969 + 3 ^ 40 * 764451 * 2
def baseEnd_764451 : Nat := 348916266498038947241653

theorem tailTrace_764451 : CollatzResearch.WordTrace tailWord_764451 prefixEnd_764451 348916266498038947241653 := by
  unfold tailWord_764451
  simp only [CollatzResearch.WordTrace]
  refine ⟨27881818553532059681669207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18587879035688039787779471 27881818553532059681669207)
  ·
    refine ⟨41822727830298089522503811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27881818553532059681669207 41822727830298089522503811)
    ·
      refine ⟨62734091745447134283755717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41822727830298089522503811 62734091745447134283755717)
      ·
        refine ⟨11762642202271337678204197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62734091745447134283755717 11762642202271337678204197)
        ·
          refine ⟨2205495412925875814663287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11762642202271337678204197 2205495412925875814663287)
          ·
            refine ⟨3308243119388813721994931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205495412925875814663287 3308243119388813721994931)
            ·
              refine ⟨4962364679083220582992397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308243119388813721994931 4962364679083220582992397)
              ·
                refine ⟨1860886754656207718622149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4962364679083220582992397 1860886754656207718622149)
                ·
                  refine ⟨348916266498038947241653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1860886754656207718622149 348916266498038947241653)
                  ·
                    rfl

theorem cell20_764451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_764451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764451 prefixEnd_764451 := by exact prefixLift 764451
  have htrace : WordTrace (prefixWord ++ tailWord_764451) baseStart_764451 baseEnd_764451 := by
    simpa [prefixWord, tailWord_764451, baseEnd_764451] using wordTrace_append hprefix tailTrace_764451
  have hstable : (prefixWord ++ tailWord_764451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764451).length < 2 ^ (prefixWord ++ tailWord_764451).sum := by decide
  have hdescent : baseEnd_764451 < baseStart_764451 := by decide
  rcases family_descends (prefixWord ++ tailWord_764451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764485 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 2]
def baseStart_764485 : Nat := 118140960795 + 764485 * 2 ^ 59
def prefixEnd_764485 : Nat := 4983230072969 + 3 ^ 40 * 764485 * 2
def baseEnd_764485 : Nat := 348931785024485940108181

theorem tailTrace_764485 : CollatzResearch.WordTrace tailWord_764485 prefixEnd_764485 348931785024485940108181 := by
  unfold tailWord_764485
  simp only [CollatzResearch.WordTrace]
  refine ⟨27883058635408883488406909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18588705756939255658937939 27883058635408883488406909)
  ·
    refine ⟨10456146988278331308152591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27883058635408883488406909 10456146988278331308152591)
    ·
      refine ⟨15684220482417496962228887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10456146988278331308152591 15684220482417496962228887)
      ·
        refine ⟨23526330723626245443343331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684220482417496962228887 23526330723626245443343331)
        ·
          refine ⟨35289496085439368165014997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23526330723626245443343331 35289496085439368165014997)
          ·
            refine ⟨827097564502485191367539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35289496085439368165014997 827097564502485191367539)
            ·
              refine ⟨1240646346753727787051309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827097564502485191367539 1240646346753727787051309)
              ·
                refine ⟨465242380032647920144241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240646346753727787051309 465242380032647920144241)
                ·
                  refine ⟨348931785024485940108181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465242380032647920144241 348931785024485940108181)
                  ·
                    rfl

theorem cell20_764485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_764485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764485 prefixEnd_764485 := by exact prefixLift 764485
  have htrace : WordTrace (prefixWord ++ tailWord_764485) baseStart_764485 baseEnd_764485 := by
    simpa [prefixWord, tailWord_764485, baseEnd_764485] using wordTrace_append hprefix tailTrace_764485
  have hstable : (prefixWord ++ tailWord_764485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764485).length < 2 ^ (prefixWord ++ tailWord_764485).sum := by decide
  have hdescent : baseEnd_764485 < baseStart_764485 := by decide
  rcases family_descends (prefixWord ++ tailWord_764485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764503 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_764503 : Nat := 118140960795 + 764503 * 2 ^ 59
def prefixEnd_764503 : Nat := 4983230072969 + 3 ^ 40 * 764503 * 2
def baseEnd_764503 : Nat := 348940000714957877508107

theorem tailTrace_764503 : CollatzResearch.WordTrace tailWord_764503 prefixEnd_764503 348940000714957877508107 := by
  unfold tailWord_764503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27883715149343672562562163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18589143432895781708374775 27883715149343672562562163)
  ·
    refine ⟨41825572724015508843843245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27883715149343672562562163 41825572724015508843843245)
    ·
      refine ⟨15684589771505815816441217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41825572724015508843843245 15684589771505815816441217)
      ·
        refine ⟨11763442328629361862330913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15684589771505815816441217 11763442328629361862330913)
        ·
          refine ⟨8822581746472021396748185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11763442328629361862330913 8822581746472021396748185)
          ·
            refine ⟨6616936309854016047561139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8822581746472021396748185 6616936309854016047561139)
            ·
              refine ⟨9925404464781024071341709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616936309854016047561139 9925404464781024071341709)
              ·
                refine ⟨3722026674292884026753141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9925404464781024071341709 3722026674292884026753141)
                ·
                  refine ⟨348940000714957877508107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722026674292884026753141 348940000714957877508107)
                  ·
                    rfl

theorem cell20_764503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_764503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764503 prefixEnd_764503 := by exact prefixLift 764503
  have htrace : WordTrace (prefixWord ++ tailWord_764503) baseStart_764503 baseEnd_764503 := by
    simpa [prefixWord, tailWord_764503, baseEnd_764503] using wordTrace_append hprefix tailTrace_764503
  have hstable : (prefixWord ++ tailWord_764503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764503).length < 2 ^ (prefixWord ++ tailWord_764503).sum := by decide
  have hdescent : baseEnd_764503 < baseStart_764503 := by decide
  rcases family_descends (prefixWord ++ tailWord_764503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764599 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 2]
def baseStart_764599 : Nat := 118140960795 + 764599 * 2 ^ 59
def prefixEnd_764599 : Nat := 4983230072969 + 3 ^ 40 * 764599 * 2
def baseEnd_764599 : Nat := 348983817730808210307715

theorem tailTrace_764599 : CollatzResearch.WordTrace tailWord_764599 prefixEnd_764599 348983817730808210307715 := by
  unfold tailWord_764599
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887216556995880958056851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18591477704663920638704567 27887216556995880958056851)
  ·
    refine ⟨41830824835493821437085277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27887216556995880958056851 41830824835493821437085277)
    ·
      refine ⟨15686559313310183038906979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41830824835493821437085277 15686559313310183038906979)
      ·
        refine ⟨23529838969965274558360469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15686559313310183038906979 23529838969965274558360469)
        ·
          refine ⟨1102961201717122244923147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23529838969965274558360469 1102961201717122244923147)
          ·
            refine ⟨1654441802575683367384721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102961201717122244923147 1654441802575683367384721)
            ·
              refine ⟨1240831351931762525538541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654441802575683367384721 1240831351931762525538541)
              ·
                refine ⟨465311756974410947076953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240831351931762525538541 465311756974410947076953)
                ·
                  refine ⟨348983817730808210307715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465311756974410947076953 348983817730808210307715)
                  ·
                    rfl

theorem cell20_764599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 2].length) (baseStart_764599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764599 prefixEnd_764599 := by exact prefixLift 764599
  have htrace : WordTrace (prefixWord ++ tailWord_764599) baseStart_764599 baseEnd_764599 := by
    simpa [prefixWord, tailWord_764599, baseEnd_764599] using wordTrace_append hprefix tailTrace_764599
  have hstable : (prefixWord ++ tailWord_764599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764599).length < 2 ^ (prefixWord ++ tailWord_764599).sum := by decide
  have hdescent : baseEnd_764599 < baseStart_764599 := by decide
  rcases family_descends (prefixWord ++ tailWord_764599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764609 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 3]
def baseStart_764609 : Nat := 118140960795 + 764609 * 2 ^ 59
def prefixEnd_764609 : Nat := 4983230072969 + 3 ^ 40 * 764609 * 2
def baseEnd_764609 : Nat := 348988382003292619974341

theorem tailTrace_764609 : CollatzResearch.WordTrace tailWord_764609 prefixEnd_764609 348988382003292619974341 := by
  unfold tailWord_764609
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887581286959652665920881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18591720857973101777280587 27887581286959652665920881)
  ·
    refine ⟨20915685965219739499440661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27887581286959652665920881 20915685965219739499440661)
    ·
      refine ⟨980422779619675289036281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20915685965219739499440661 980422779619675289036281)
      ·
        refine ⟨735317084714756466777211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980422779619675289036281 735317084714756466777211)
        ·
          refine ⟨1102975627072134700165817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735317084714756466777211 1102975627072134700165817)
          ·
            refine ⟨827231720304101025124363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102975627072134700165817 827231720304101025124363)
            ·
              refine ⟨1240847580456151537686545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827231720304101025124363 1240847580456151537686545)
              ·
                refine ⟨930635685342113653264909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240847580456151537686545 930635685342113653264909)
                ·
                  refine ⟨348988382003292619974341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930635685342113653264909 348988382003292619974341)
                  ·
                    rfl

theorem cell20_764609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_764609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764609 prefixEnd_764609 := by exact prefixLift 764609
  have htrace : WordTrace (prefixWord ++ tailWord_764609) baseStart_764609 baseEnd_764609 := by
    simpa [prefixWord, tailWord_764609, baseEnd_764609] using wordTrace_append hprefix tailTrace_764609
  have hstable : (prefixWord ++ tailWord_764609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764609).length < 2 ^ (prefixWord ++ tailWord_764609).sum := by decide
  have hdescent : baseEnd_764609 < baseStart_764609 := by decide
  rcases family_descends (prefixWord ++ tailWord_764609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764620 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_764620 : Nat := 118140960795 + 764620 * 2 ^ 59
def prefixEnd_764620 : Nat := 4983230072969 + 3 ^ 40 * 764620 * 2
def baseEnd_764620 : Nat := 348993402703025470607629

theorem tailTrace_764620 : CollatzResearch.WordTrace tailWord_764620 prefixEnd_764620 348993402703025470607629 := by
  unfold tailWord_764620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13943991244959900772285657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18591988326613201029714209 13943991244959900772285657)
  ·
    refine ⟨10457993433719925579214243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13943991244959900772285657 10457993433719925579214243)
    ·
      refine ⟨15686990150579888368821365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10457993433719925579214243 15686990150579888368821365)
      ·
        refine ⟨1470655326616864534577003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15686990150579888368821365 1470655326616864534577003)
        ·
          refine ⟨2205982989925296801865505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470655326616864534577003 2205982989925296801865505)
          ·
            refine ⟨1654487242443972601399129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2205982989925296801865505 1654487242443972601399129)
            ·
              refine ⟨1240865431832979451049347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654487242443972601399129 1240865431832979451049347)
              ·
                refine ⟨1861298147749469176574021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240865431832979451049347 1861298147749469176574021)
                ·
                  refine ⟨348993402703025470607629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1861298147749469176574021 348993402703025470607629)
                  ·
                    rfl

theorem cell20_764620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_764620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764620 prefixEnd_764620 := by exact prefixLift 764620
  have htrace : WordTrace (prefixWord ++ tailWord_764620) baseStart_764620 baseEnd_764620 := by
    simpa [prefixWord, tailWord_764620, baseEnd_764620] using wordTrace_append hprefix tailTrace_764620
  have hstable : (prefixWord ++ tailWord_764620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764620).length < 2 ^ (prefixWord ++ tailWord_764620).sum := by decide
  have hdescent : baseEnd_764620 < baseStart_764620 := by decide
  rcases family_descends (prefixWord ++ tailWord_764620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764641 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_764641 : Nat := 118140960795 + 764641 * 2 ^ 59
def prefixEnd_764641 : Nat := 4983230072969 + 3 ^ 40 * 764641 * 2
def baseEnd_764641 : Nat := 349002987675242730907543

theorem tailTrace_764641 : CollatzResearch.WordTrace tailWord_764641 prefixEnd_764641 349002987675242730907543 := by
  unfold tailWord_764641
  simp only [CollatzResearch.WordTrace]
  refine ⟨27888748422843722131085777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18592498948562481420723851 27888748422843722131085777)
  ·
    refine ⟨20916561317132791598314333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27888748422843722131085777 20916561317132791598314333)
    ·
      refine ⟨7843710493924796849367875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20916561317132791598314333 7843710493924796849367875)
      ·
        refine ⟨11765565740887195274051813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843710493924796849367875 11765565740887195274051813)
        ·
          refine ⟨2206043576416349113884715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11765565740887195274051813 2206043576416349113884715)
          ·
            refine ⟨3309065364624523670827073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206043576416349113884715 3309065364624523670827073)
            ·
              refine ⟨2481799023468392753120305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3309065364624523670827073 2481799023468392753120305)
              ·
                refine ⟨1861349267601294564840229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481799023468392753120305 1861349267601294564840229)
                ·
                  refine ⟨349002987675242730907543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1861349267601294564840229 349002987675242730907543)
                  ·
                    rfl

theorem cell20_764641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_764641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764641 prefixEnd_764641 := by exact prefixLift 764641
  have htrace : WordTrace (prefixWord ++ tailWord_764641) baseStart_764641 baseEnd_764641 := by
    simpa [prefixWord, tailWord_764641, baseEnd_764641] using wordTrace_append hprefix tailTrace_764641
  have hstable : (prefixWord ++ tailWord_764641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764641).length < 2 ^ (prefixWord ++ tailWord_764641).sum := by decide
  have hdescent : baseEnd_764641 < baseStart_764641 := by decide
  rcases family_descends (prefixWord ++ tailWord_764641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764655 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_764655 : Nat := 118140960795 + 764655 * 2 ^ 59
def prefixEnd_764655 : Nat := 4983230072969 + 3 ^ 40 * 764655 * 2
def baseEnd_764655 : Nat := 349009377656720904440819

theorem tailTrace_764655 : CollatzResearch.WordTrace tailWord_764655 prefixEnd_764655 349009377656720904440819 := by
  unfold tailWord_764655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27889259044793002522095419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18592839363195335014730279 27889259044793002522095419)
  ·
    refine ⟨41833888567189503783143129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27889259044793002522095419 41833888567189503783143129)
    ·
      refine ⟨31375416425392127837357347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41833888567189503783143129 31375416425392127837357347)
      ·
        refine ⟨47063124638088191756036021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31375416425392127837357347 47063124638088191756036021)
        ·
          refine ⟨4412167934820767977128377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47063124638088191756036021 4412167934820767977128377)
          ·
            refine ⟨3309125951115575982846283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4412167934820767977128377 3309125951115575982846283)
            ·
              refine ⟨4963688926673363974269425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309125951115575982846283 4963688926673363974269425)
              ·
                refine ⟨3722766695005022980702069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963688926673363974269425 3722766695005022980702069)
                ·
                  refine ⟨349009377656720904440819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3722766695005022980702069 349009377656720904440819)
                  ·
                    rfl

theorem cell20_764655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_764655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764655 prefixEnd_764655 := by exact prefixLift 764655
  have htrace : WordTrace (prefixWord ++ tailWord_764655) baseStart_764655 baseEnd_764655 := by
    simpa [prefixWord, tailWord_764655, baseEnd_764655] using wordTrace_append hprefix tailTrace_764655
  have hstable : (prefixWord ++ tailWord_764655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764655).length < 2 ^ (prefixWord ++ tailWord_764655).sum := by decide
  have hdescent : baseEnd_764655 < baseStart_764655 := by decide
  rcases family_descends (prefixWord ++ tailWord_764655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764661 : List Nat := [1, 3, 6, 1, 1, 2, 6]
def baseStart_764661 : Nat := 118140960795 + 764661 * 2 ^ 59
def prefixEnd_764661 : Nat := 4983230072969 + 3 ^ 40 * 764661 * 2
def baseEnd_764661 : Nat := 38779124024467950026755

theorem tailTrace_764661 : CollatzResearch.WordTrace tailWord_764661 prefixEnd_764661 38779124024467950026755 := by
  unfold tailWord_764661
  simp only [CollatzResearch.WordTrace]
  refine ⟨27889477882771265546813837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18592985255180843697875891 27889477882771265546813837)
  ·
    refine ⟨10458554206039224580055189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27889477882771265546813837 10458554206039224580055189)
    ·
      refine ⟨490244728408088652190087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10458554206039224580055189 490244728408088652190087)
      ·
        refine ⟨735367092612132978285131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490244728408088652190087 735367092612132978285131)
        ·
          refine ⟨1103050638918199467427697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735367092612132978285131 1103050638918199467427697)
          ·
            refine ⟨827287979188649600570773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103050638918199467427697 827287979188649600570773)
            ·
              refine ⟨38779124024467950026755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 827287979188649600570773 38779124024467950026755)
              ·
                rfl

theorem cell20_764661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 6].length) (baseStart_764661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764661 prefixEnd_764661 := by exact prefixLift 764661
  have htrace : WordTrace (prefixWord ++ tailWord_764661) baseStart_764661 baseEnd_764661 := by
    simpa [prefixWord, tailWord_764661, baseEnd_764661] using wordTrace_append hprefix tailTrace_764661
  have hstable : (prefixWord ++ tailWord_764661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764661).length < 2 ^ (prefixWord ++ tailWord_764661).sum := by decide
  have hdescent : baseEnd_764661 < baseStart_764661 := by decide
  rcases family_descends (prefixWord ++ tailWord_764661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764724 : List Nat := [2, 5, 1, 1, 11]
def baseStart_764724 : Nat := 118140960795 + 764724 * 2 ^ 59
def prefixEnd_764724 : Nat := 4983230072969 + 3 ^ 40 * 764724 * 2
def baseEnd_764724 : Nat := 4309146557245226310377

theorem tailTrace_764724 : CollatzResearch.WordTrace tailWord_764724 prefixEnd_764724 4309146557245226310377 := by
  unfold tailWord_764724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13945887840771513653178613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18594517121028684870904817 13945887840771513653178613)
  ·
    refine ⟨1307426985072329404985495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13945887840771513653178613 1307426985072329404985495)
    ·
      refine ⟨1961140477608494107478243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307426985072329404985495 1961140477608494107478243)
      ·
        refine ⟨2941710716412741161217365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961140477608494107478243 2941710716412741161217365)
        ·
          refine ⟨4309146557245226310377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2941710716412741161217365 4309146557245226310377)
          ·
            rfl

theorem cell20_764724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 11].length) (baseStart_764724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764724 prefixEnd_764724 := by exact prefixLift 764724
  have htrace : WordTrace (prefixWord ++ tailWord_764724) baseStart_764724 baseEnd_764724 := by
    simpa [prefixWord, tailWord_764724, baseEnd_764724] using wordTrace_append hprefix tailTrace_764724
  have hstable : (prefixWord ++ tailWord_764724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764724).length < 2 ^ (prefixWord ++ tailWord_764724).sum := by decide
  have hdescent : baseEnd_764724 < baseStart_764724 := by decide
  rcases family_descends (prefixWord ++ tailWord_764724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764726 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_764726 : Nat := 118140960795 + 764726 * 2 ^ 59
def prefixEnd_764726 : Nat := 4983230072969 + 3 ^ 40 * 764726 * 2
def baseEnd_764726 : Nat := 349041783991360213073863

theorem tailTrace_764726 : CollatzResearch.WordTrace tailWord_764726 prefixEnd_764726 349041783991360213073863 := by
  unfold tailWord_764726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743240539220986352995627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18594565751690521098620021 1743240539220986352995627)
  ·
    refine ⟨2614860808831479529493441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743240539220986352995627 2614860808831479529493441)
    ·
      refine ⟨1961145606623609647120081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2614860808831479529493441 1961145606623609647120081)
      ·
        refine ⟨1470859204967707235340061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1961145606623609647120081 1470859204967707235340061)
        ·
          refine ⟨551572201862890213252523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1470859204967707235340061 551572201862890213252523)
          ·
            refine ⟨827358302794335319878785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551572201862890213252523 827358302794335319878785)
            ·
              refine ⟨620518727095751489909089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827358302794335319878785 620518727095751489909089)
              ·
                refine ⟨465389045321813617431817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620518727095751489909089 465389045321813617431817)
                ·
                  refine ⟨349041783991360213073863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465389045321813617431817 349041783991360213073863)
                  ·
                    rfl

theorem cell20_764726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_764726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764726 prefixEnd_764726 := by exact prefixLift 764726
  have htrace : WordTrace (prefixWord ++ tailWord_764726) baseStart_764726 baseEnd_764726 := by
    simpa [prefixWord, tailWord_764726, baseEnd_764726] using wordTrace_append hprefix tailTrace_764726
  have hstable : (prefixWord ++ tailWord_764726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764726).length < 2 ^ (prefixWord ++ tailWord_764726).sum := by decide
  have hdescent : baseEnd_764726 < baseStart_764726 := by decide
  rcases family_descends (prefixWord ++ tailWord_764726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764730 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_764730 : Nat := 118140960795 + 764730 * 2 ^ 59
def prefixEnd_764730 : Nat := 4983230072969 + 3 ^ 40 * 764730 * 2
def baseEnd_764730 : Nat := 349043609700353976940513

theorem tailTrace_764730 : CollatzResearch.WordTrace tailWord_764730 prefixEnd_764730 349043609700353976940513 := by
  unfold tailWord_764730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972998629880322582768911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18594663013014193554050429 6972998629880322582768911)
  ·
    refine ⟨10459497944820483874153367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6972998629880322582768911 10459497944820483874153367)
    ·
      refine ⟨15689246917230725811230051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10459497944820483874153367 15689246917230725811230051)
      ·
        refine ⟨23533870375846088716845077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15689246917230725811230051 23533870375846088716845077)
        ·
          refine ⟨1103150173867785408602113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23533870375846088716845077 1103150173867785408602113)
          ·
            refine ⟨827362630400839056451585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103150173867785408602113 827362630400839056451585)
            ·
              refine ⟨620521972800629292338689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827362630400839056451585 620521972800629292338689)
              ·
                refine ⟨465391479600471969254017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620521972800629292338689 465391479600471969254017)
                ·
                  refine ⟨349043609700353976940513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465391479600471969254017 349043609700353976940513)
                  ·
                    rfl

theorem cell20_764730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_764730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764730 prefixEnd_764730 := by exact prefixLift 764730
  have htrace : WordTrace (prefixWord ++ tailWord_764730) baseStart_764730 baseEnd_764730 := by
    simpa [prefixWord, tailWord_764730, baseEnd_764730] using wordTrace_append hprefix tailTrace_764730
  have hstable : (prefixWord ++ tailWord_764730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764730).length < 2 ^ (prefixWord ++ tailWord_764730).sum := by decide
  have hdescent : baseEnd_764730 < baseStart_764730 := by decide
  rcases family_descends (prefixWord ++ tailWord_764730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764737 : List Nat := [1, 2, 5, 3, 2, 1, 1, 5]
def baseStart_764737 : Nat := 118140960795 + 764737 * 2 ^ 59
def prefixEnd_764737 : Nat := 4983230072969 + 3 ^ 40 * 764737 * 2
def baseEnd_764737 : Nat := 116348934897031021235717

theorem tailTrace_764737 : CollatzResearch.WordTrace tailWord_764737 prefixEnd_764737 116348934897031021235717 := by
  unfold tailWord_764737
  simp only [CollatzResearch.WordTrace]
  refine ⟨27892249830495930526580465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18594833220330620351053643 27892249830495930526580465)
  ·
    refine ⟨20919187372871947894935349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27892249830495930526580465 20919187372871947894935349)
    ·
      refine ⟨1961173816206745115150189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20919187372871947894935349 1961173816206745115150189)
      ·
        refine ⟨735440181077529418181321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1961173816206745115150189 735440181077529418181321)
        ·
          refine ⟨551580135808147063635991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735440181077529418181321 551580135808147063635991)
          ·
            refine ⟨827370203712220595453987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551580135808147063635991 827370203712220595453987)
            ·
              refine ⟨1241055305568330893180981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827370203712220595453987 1241055305568330893180981)
              ·
                refine ⟨116348934897031021235717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1241055305568330893180981 116348934897031021235717)
                ·
                  rfl

theorem cell20_764737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].length) (baseStart_764737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764737 prefixEnd_764737 := by exact prefixLift 764737
  have htrace : WordTrace (prefixWord ++ tailWord_764737) baseStart_764737 baseEnd_764737 := by
    simpa [prefixWord, tailWord_764737, baseEnd_764737] using wordTrace_append hprefix tailTrace_764737
  have hstable : (prefixWord ++ tailWord_764737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764737).length < 2 ^ (prefixWord ++ tailWord_764737).sum := by decide
  have hdescent : baseEnd_764737 < baseStart_764737 := by decide
  rcases family_descends (prefixWord ++ tailWord_764737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764748 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_764748 : Nat := 118140960795 + 764748 * 2 ^ 59
def prefixEnd_764748 : Nat := 4983230072969 + 3 ^ 40 * 764748 * 2
def baseEnd_764748 : Nat := 349051825390825914340439

theorem tailTrace_764748 : CollatzResearch.WordTrace tailWord_764748 prefixEnd_764748 349051825390825914340439 := by
  unfold tailWord_764748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13946325516728039702615449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18595100688970719603487265 13946325516728039702615449)
  ·
    refine ⟨10459744137546029776961587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13946325516728039702615449 10459744137546029776961587)
    ·
      refine ⟨15689616206319044665442381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10459744137546029776961587 15689616206319044665442381)
      ·
        refine ⟨5883606077369641749540893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15689616206319044665442381 5883606077369641749540893)
        ·
          refine ⟨2206352279013615656077835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5883606077369641749540893 2206352279013615656077835)
          ·
            refine ⟨3309528418520423484116753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206352279013615656077835 3309528418520423484116753)
            ·
              refine ⟨2482146313890317613087565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3309528418520423484116753 2482146313890317613087565)
              ·
                refine ⟨930804867708869104907837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482146313890317613087565 930804867708869104907837)
                ·
                  refine ⟨349051825390825914340439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930804867708869104907837 349051825390825914340439)
                  ·
                    rfl

theorem cell20_764748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_764748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764748 prefixEnd_764748 := by exact prefixLift 764748
  have htrace : WordTrace (prefixWord ++ tailWord_764748) baseStart_764748 baseEnd_764748 := by
    simpa [prefixWord, tailWord_764748, baseEnd_764748] using wordTrace_append hprefix tailTrace_764748
  have hstable : (prefixWord ++ tailWord_764748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764748).length < 2 ^ (prefixWord ++ tailWord_764748).sum := by decide
  have hdescent : baseEnd_764748 < baseStart_764748 := by decide
  rcases family_descends (prefixWord ++ tailWord_764748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764772 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 2]
def baseStart_764772 : Nat := 118140960795 + 764772 * 2 ^ 59
def prefixEnd_764772 : Nat := 4983230072969 + 3 ^ 40 * 764772 * 2
def baseEnd_764772 : Nat := 349062779644788497540341

theorem tailTrace_764772 : CollatzResearch.WordTrace tailWord_764772 prefixEnd_764772 349062779644788497540341 := by
  unfold tailWord_764772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13946763192684565752052285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18595684256912754336069713 13946763192684565752052285)
  ·
    refine ⟨5230036197256712157019607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13946763192684565752052285 5230036197256712157019607)
    ·
      refine ⟨7845054295885068235529411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230036197256712157019607 7845054295885068235529411)
      ·
        refine ⟨11767581443827602353294117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7845054295885068235529411 11767581443827602353294117)
        ·
          refine ⟨2206421520717675441242647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11767581443827602353294117 2206421520717675441242647)
          ·
            refine ⟨3309632281076513161863971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206421520717675441242647 3309632281076513161863971)
            ·
              refine ⟨4964448421614769742795957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309632281076513161863971 4964448421614769742795957)
              ·
                refine ⟨465417039526384663387121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4964448421614769742795957 465417039526384663387121)
                ·
                  refine ⟨349062779644788497540341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465417039526384663387121 349062779644788497540341)
                  ·
                    rfl

theorem cell20_764772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_764772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764772 prefixEnd_764772 := by exact prefixLift 764772
  have htrace : WordTrace (prefixWord ++ tailWord_764772) baseStart_764772 baseEnd_764772 := by
    simpa [prefixWord, tailWord_764772, baseEnd_764772] using wordTrace_append hprefix tailTrace_764772
  have hstable : (prefixWord ++ tailWord_764772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764772).length < 2 ^ (prefixWord ++ tailWord_764772).sum := by decide
  have hdescent : baseEnd_764772 < baseStart_764772 := by decide
  rcases family_descends (prefixWord ++ tailWord_764772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764782 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_764782 : Nat := 118140960795 + 764782 * 2 ^ 59
def prefixEnd_764782 : Nat := 4983230072969 + 3 ^ 40 * 764782 * 2
def baseEnd_764782 : Nat := 349067343917272907206967

theorem tailTrace_764782 : CollatzResearch.WordTrace tailWord_764782 prefixEnd_764782 349067343917272907206967 := by
  unfold tailWord_764782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486736389416612901496075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18595927410221935474645733 3486736389416612901496075)
  ·
    refine ⟨5230104584124919352244113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486736389416612901496075 5230104584124919352244113)
    ·
      refine ⟨3922578438093689514183085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230104584124919352244113 3922578438093689514183085)
      ·
        refine ⟨1470966914285133567818657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3922578438093689514183085 1470966914285133567818657)
        ·
          refine ⟨1103225185713850175863993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470966914285133567818657 1103225185713850175863993)
          ·
            refine ⟨827418889285387631897995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103225185713850175863993 827418889285387631897995)
            ·
              refine ⟨1241128333928081447846993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827418889285387631897995 1241128333928081447846993)
              ·
                refine ⟨930846250446061085885245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241128333928081447846993 930846250446061085885245)
                ·
                  refine ⟨349067343917272907206967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930846250446061085885245 349067343917272907206967)
                  ·
                    rfl

theorem cell20_764782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_764782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764782 prefixEnd_764782 := by exact prefixLift 764782
  have htrace : WordTrace (prefixWord ++ tailWord_764782) baseStart_764782 baseEnd_764782 := by
    simpa [prefixWord, tailWord_764782, baseEnd_764782] using wordTrace_append hprefix tailTrace_764782
  have hstable : (prefixWord ++ tailWord_764782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764782).length < 2 ^ (prefixWord ++ tailWord_764782).sum := by decide
  have hdescent : baseEnd_764782 < baseStart_764782 := by decide
  rcases family_descends (prefixWord ++ tailWord_764782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764786 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_764786 : Nat := 118140960795 + 764786 * 2 ^ 59
def prefixEnd_764786 : Nat := 4983230072969 + 3 ^ 40 * 764786 * 2
def baseEnd_764786 : Nat := 349069169626266671073617

theorem tailTrace_764786 : CollatzResearch.WordTrace tailWord_764786 prefixEnd_764786 349069169626266671073617 := by
  unfold tailWord_764786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973509251829602973778553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18596024671545607930076141 6973509251829602973778553)
  ·
    refine ⟨5230131938872202230333915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6973509251829602973778553 5230131938872202230333915)
    ·
      refine ⟨7845197908308303345500873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230131938872202230333915 7845197908308303345500873)
      ·
        refine ⟨5883898431231227509125655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7845197908308303345500873 5883898431231227509125655)
        ·
          refine ⟨8825847646846841263688483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883898431231227509125655 8825847646846841263688483)
          ·
            refine ⟨13238771470270261895532725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8825847646846841263688483 13238771470270261895532725)
            ·
              refine ⟨1241134825337837052706193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13238771470270261895532725 1241134825337837052706193)
              ·
                refine ⟨930851119003377789529645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241134825337837052706193 930851119003377789529645)
                ·
                  refine ⟨349069169626266671073617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930851119003377789529645 349069169626266671073617)
                  ·
                    rfl

theorem cell20_764786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_764786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764786 prefixEnd_764786 := by exact prefixLift 764786
  have htrace : WordTrace (prefixWord ++ tailWord_764786) baseStart_764786 baseEnd_764786 := by
    simpa [prefixWord, tailWord_764786, baseEnd_764786] using wordTrace_append hprefix tailTrace_764786
  have hstable : (prefixWord ++ tailWord_764786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764786).length < 2 ^ (prefixWord ++ tailWord_764786).sum := by decide
  have hdescent : baseEnd_764786 < baseStart_764786 := by decide
  rcases family_descends (prefixWord ++ tailWord_764786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764793 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_764793 : Nat := 118140960795 + 764793 * 2 ^ 59
def prefixEnd_764793 : Nat := 4983230072969 + 3 ^ 40 * 764793 * 2
def baseEnd_764793 : Nat := 349072364617005757840255

theorem tailTrace_764793 : CollatzResearch.WordTrace tailWord_764793 prefixEnd_764793 349072364617005757840255 := by
  unfold tailWord_764793
  simp only [CollatzResearch.WordTrace]
  refine ⟨27894292318293052090619033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18596194878862034727079355 27894292318293052090619033)
  ·
    refine ⟨20920719238719789067964275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27894292318293052090619033 20920719238719789067964275)
    ·
      refine ⟨31381078858079683601946413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20920719238719789067964275 31381078858079683601946413)
      ·
        refine ⟨11767904571779881350729905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31381078858079683601946413 11767904571779881350729905)
        ·
          refine ⟨8825928428834911013047429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11767904571779881350729905 8825928428834911013047429)
          ·
            refine ⟨1654861580406545814946393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8825928428834911013047429 1654861580406545814946393)
            ·
              refine ⟨1241146185304909361209795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654861580406545814946393 1241146185304909361209795)
              ·
                refine ⟨1861719277957364041814693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241146185304909361209795 1861719277957364041814693)
                ·
                  refine ⟨349072364617005757840255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1861719277957364041814693 349072364617005757840255)
                  ·
                    rfl

theorem cell20_764793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_764793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764793 prefixEnd_764793 := by exact prefixLift 764793
  have htrace : WordTrace (prefixWord ++ tailWord_764793) baseStart_764793 baseEnd_764793 := by
    simpa [prefixWord, tailWord_764793, baseEnd_764793] using wordTrace_append hprefix tailTrace_764793
  have hstable : (prefixWord ++ tailWord_764793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764793).length < 2 ^ (prefixWord ++ tailWord_764793).sum := by decide
  have hdescent : baseEnd_764793 < baseStart_764793 := by decide
  rcases family_descends (prefixWord ++ tailWord_764793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764862 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_764862 : Nat := 118140960795 + 764862 * 2 ^ 59
def prefixEnd_764862 : Nat := 4983230072969 + 3 ^ 40 * 764862 * 2
def baseEnd_764862 : Nat := 349103858097148184539973

theorem tailTrace_764862 : CollatzResearch.WordTrace tailWord_764862 prefixEnd_764862 349103858097148184539973 := by
  unfold tailWord_764862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487101119380384609360105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18597872636695384583253893 3487101119380384609360105)
  ·
    refine ⟨2615325839535288457020079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3487101119380384609360105 2615325839535288457020079)
    ·
      refine ⟨3922988759302932685530119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615325839535288457020079 3922988759302932685530119)
      ·
        refine ⟨5884483138954399028295179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922988759302932685530119 5884483138954399028295179)
        ·
          refine ⟨8826724708431598542442769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5884483138954399028295179 8826724708431598542442769)
          ·
            refine ⟨6620043531323698906832077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8826724708431598542442769 6620043531323698906832077)
            ·
              refine ⟨2482516324246387090062029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6620043531323698906832077 2482516324246387090062029)
              ·
                refine ⟨930943621592395158773261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482516324246387090062029 930943621592395158773261)
                ·
                  refine ⟨349103858097148184539973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930943621592395158773261 349103858097148184539973)
                  ·
                    rfl

theorem cell20_764862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_764862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764862 prefixEnd_764862 := by exact prefixLift 764862
  have htrace : WordTrace (prefixWord ++ tailWord_764862) baseStart_764862 baseEnd_764862 := by
    simpa [prefixWord, tailWord_764862, baseEnd_764862] using wordTrace_append hprefix tailTrace_764862
  have hstable : (prefixWord ++ tailWord_764862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764862).length < 2 ^ (prefixWord ++ tailWord_764862).sum := by decide
  have hdescent : baseEnd_764862 < baseStart_764862 := by decide
  rcases family_descends (prefixWord ++ tailWord_764862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764903 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 2]
def baseStart_764903 : Nat := 118140960795 + 764903 * 2 ^ 59
def prefixEnd_764903 : Nat := 4983230072969 + 3 ^ 40 * 764903 * 2
def baseEnd_764903 : Nat := 349122571614334264173139

theorem tailTrace_764903 : CollatzResearch.WordTrace tailWord_764903 prefixEnd_764903 349122571614334264173139 := by
  unfold tailWord_764903
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898304347894540877123363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18598869565263027251415575 27898304347894540877123363)
  ·
    refine ⟨41847456521841811315685045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27898304347894540877123363 41847456521841811315685045)
    ·
      refine ⟨3923199048922669810845473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41847456521841811315685045 3923199048922669810845473)
      ·
        refine ⟨2942399286692002358134105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3923199048922669810845473 2942399286692002358134105)
        ·
          refine ⟨2206799465019001768600579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2942399286692002358134105 2206799465019001768600579)
          ·
            refine ⟨3310199197528502652900869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206799465019001768600579 3310199197528502652900869)
            ·
              refine ⟨620662349536594247418913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3310199197528502652900869 620662349536594247418913)
              ·
                refine ⟨465496762152445685564185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620662349536594247418913 465496762152445685564185)
                ·
                  refine ⟨349122571614334264173139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465496762152445685564185 349122571614334264173139)
                  ·
                    rfl

theorem cell20_764903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 2].length) (baseStart_764903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764903 prefixEnd_764903 := by exact prefixLift 764903
  have htrace : WordTrace (prefixWord ++ tailWord_764903) baseStart_764903 baseEnd_764903 := by
    simpa [prefixWord, tailWord_764903, baseEnd_764903] using wordTrace_append hprefix tailTrace_764903
  have hstable : (prefixWord ++ tailWord_764903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764903).length < 2 ^ (prefixWord ++ tailWord_764903).sum := by decide
  have hdescent : baseEnd_764903 < baseStart_764903 := by decide
  rcases family_descends (prefixWord ++ tailWord_764903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764910 : List Nat := [4, 1, 2, 1, 5, 1, 1, 5]
def baseStart_764910 : Nat := 118140960795 + 764910 * 2 ^ 59
def prefixEnd_764910 : Nat := 4983230072969 + 3 ^ 40 * 764910 * 2
def baseEnd_764910 : Nat := 116375255535024450313259

theorem tailTrace_764910 : CollatzResearch.WordTrace tailWord_764910 prefixEnd_764910 116375255535024450313259 := by
  unfold tailWord_764910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487319957358647634078523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18599039772579454048418789 3487319957358647634078523)
  ·
    refine ⟨5230979936037971451117785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487319957358647634078523 5230979936037971451117785)
    ·
      refine ⟨3923234952028478588338339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230979936037971451117785 3923234952028478588338339)
      ·
        refine ⟨5884852428042717882507509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923234952028478588338339 5884852428042717882507509)
        ·
          refine ⟨551704915129004801485079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5884852428042717882507509 551704915129004801485079)
          ·
            refine ⟨827557372693507202227619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551704915129004801485079 827557372693507202227619)
            ·
              refine ⟨1241336059040260803341429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827557372693507202227619 1241336059040260803341429)
              ·
                refine ⟨116375255535024450313259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1241336059040260803341429 116375255535024450313259)
                ·
                  rfl

theorem cell20_764910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_764910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764910 prefixEnd_764910 := by exact prefixLift 764910
  have htrace : WordTrace (prefixWord ++ tailWord_764910) baseStart_764910 baseEnd_764910 := by
    simpa [prefixWord, tailWord_764910, baseEnd_764910] using wordTrace_append hprefix tailTrace_764910
  have hstable : (prefixWord ++ tailWord_764910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764910).length < 2 ^ (prefixWord ++ tailWord_764910).sum := by decide
  have hdescent : baseEnd_764910 < baseStart_764910 := by decide
  rcases family_descends (prefixWord ++ tailWord_764910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764921 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_764921 : Nat := 118140960795 + 764921 * 2 ^ 59
def prefixEnd_764921 : Nat := 4983230072969 + 3 ^ 40 * 764921 * 2
def baseEnd_764921 : Nat := 349130787304806201573065

theorem tailTrace_764921 : CollatzResearch.WordTrace tailWord_764921 prefixEnd_764921 349130787304806201573065 := by
  unfold tailWord_764921
  simp only [CollatzResearch.WordTrace]
  refine ⟨27898960861829329951278617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18599307241219553300852411 27898960861829329951278617)
  ·
    refine ⟨20924220646371997463458963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27898960861829329951278617 20924220646371997463458963)
    ·
      refine ⟨31386330969557996195188445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20924220646371997463458963 31386330969557996195188445)
      ·
        refine ⟨11769874113584248573195667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31386330969557996195188445 11769874113584248573195667)
        ·
          refine ⟨17654811170376372859793501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769874113584248573195667 17654811170376372859793501)
          ·
            refine ⟨6620554188891139822422563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17654811170376372859793501 6620554188891139822422563)
            ·
              refine ⟨9930831283336709733633845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6620554188891139822422563 9930831283336709733633845)
              ·
                refine ⟨931015432812816537528173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9930831283336709733633845 931015432812816537528173)
                ·
                  refine ⟨349130787304806201573065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931015432812816537528173 349130787304806201573065)
                  ·
                    rfl

theorem cell20_764921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_764921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764921 prefixEnd_764921 := by exact prefixLift 764921
  have htrace : WordTrace (prefixWord ++ tailWord_764921) baseStart_764921 baseEnd_764921 := by
    simpa [prefixWord, tailWord_764921, baseEnd_764921] using wordTrace_append hprefix tailTrace_764921
  have hstable : (prefixWord ++ tailWord_764921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764921).length < 2 ^ (prefixWord ++ tailWord_764921).sum := by decide
  have hdescent : baseEnd_764921 < baseStart_764921 := by decide
  rcases family_descends (prefixWord ++ tailWord_764921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764959 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_764959 : Nat := 118140960795 + 764959 * 2 ^ 59
def prefixEnd_764959 : Nat := 4983230072969 + 3 ^ 40 * 764959 * 2
def baseEnd_764959 : Nat := 349148131540246958306243

theorem tailTrace_764959 : CollatzResearch.WordTrace tailWord_764959 prefixEnd_764959 349148131540246958306243 := by
  unfold tailWord_764959
  simp only [CollatzResearch.WordTrace]
  refine ⟨27900346835691662441161931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18600231223794441627441287 27900346835691662441161931)
  ·
    refine ⟨41850520253537493661742897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27900346835691662441161931 41850520253537493661742897)
    ·
      refine ⟨31387890190153120246307173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41850520253537493661742897 31387890190153120246307173)
      ·
        refine ⟨5885229410653710046182595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31387890190153120246307173 5885229410653710046182595)
        ·
          refine ⟨8827844115980565069273893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885229410653710046182595 8827844115980565069273893)
          ·
            refine ⟨1655220771746355950488855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8827844115980565069273893 1655220771746355950488855)
            ·
              refine ⟨2482831157619533925733283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655220771746355950488855 2482831157619533925733283)
              ·
                refine ⟨3724246736429300888599925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482831157619533925733283 3724246736429300888599925)
                ·
                  refine ⟨349148131540246958306243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3724246736429300888599925 349148131540246958306243)
                  ·
                    rfl

theorem cell20_764959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_764959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764959 prefixEnd_764959 := by exact prefixLift 764959
  have htrace : WordTrace (prefixWord ++ tailWord_764959) baseStart_764959 baseEnd_764959 := by
    simpa [prefixWord, tailWord_764959, baseEnd_764959] using wordTrace_append hprefix tailTrace_764959
  have hstable : (prefixWord ++ tailWord_764959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764959).length < 2 ^ (prefixWord ++ tailWord_764959).sum := by decide
  have hdescent : baseEnd_764959 < baseStart_764959 := by decide
  rcases family_descends (prefixWord ++ tailWord_764959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764962 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_764962 : Nat := 118140960795 + 764962 * 2 ^ 59
def prefixEnd_764962 : Nat := 4983230072969 + 3 ^ 40 * 764962 * 2
def baseEnd_764962 : Nat := 349149500821992281206231

theorem tailTrace_764962 : CollatzResearch.WordTrace tailWord_764962 prefixEnd_764962 349149500821992281206231 := by
  unfold tailWord_764962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975114063670198488380285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18600304169787195969014093 6975114063670198488380285)
  ·
    refine ⟨2615667773876324433142607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6975114063670198488380285 2615667773876324433142607)
    ·
      refine ⟨3923501660814486649713911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615667773876324433142607 3923501660814486649713911)
      ·
        refine ⟨5885252491221729974570867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923501660814486649713911 5885252491221729974570867)
        ·
          refine ⟨8827878736832594961856301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885252491221729974570867 8827878736832594961856301)
          ·
            refine ⟨3310454526312223110696113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8827878736832594961856301 3310454526312223110696113)
            ·
              refine ⟨2482840894734167333022085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3310454526312223110696113 2482840894734167333022085)
              ·
                refine ⟨465532667762656374941641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2482840894734167333022085 465532667762656374941641)
                ·
                  refine ⟨349149500821992281206231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465532667762656374941641 349149500821992281206231)
                  ·
                    rfl

theorem cell20_764962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_764962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764962 prefixEnd_764962 := by exact prefixLift 764962
  have htrace : WordTrace (prefixWord ++ tailWord_764962) baseStart_764962 baseEnd_764962 := by
    simpa [prefixWord, tailWord_764962, baseEnd_764962] using wordTrace_append hprefix tailTrace_764962
  have hstable : (prefixWord ++ tailWord_764962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764962).length < 2 ^ (prefixWord ++ tailWord_764962).sum := by decide
  have hdescent : baseEnd_764962 < baseStart_764962 := by decide
  rcases family_descends (prefixWord ++ tailWord_764962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764976 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_764976 : Nat := 118140960795 + 764976 * 2 ^ 59
def prefixEnd_764976 : Nat := 4983230072969 + 3 ^ 40 * 764976 * 2
def baseEnd_764976 : Nat := 349155890803470454739507

theorem tailTrace_764976 : CollatzResearch.WordTrace tailWord_764976 prefixEnd_764976 349155890803470454739507 := by
  unfold tailWord_764976
  simp only [CollatzResearch.WordTrace]
  refine ⟨13950483438315037172265391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18600644584420049563020521 13950483438315037172265391)
  ·
    refine ⟨20925725157472555758398087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13950483438315037172265391 20925725157472555758398087)
    ·
      refine ⟨31388587736208833637597131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20925725157472555758398087 31388587736208833637597131)
      ·
        refine ⟨47082881604313250456395697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31388587736208833637597131 47082881604313250456395697)
        ·
          refine ⟨35312161203234937842296773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47082881604313250456395697 35312161203234937842296773)
          ·
            refine ⟨6621030225606550845430645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35312161203234937842296773 6621030225606550845430645)
            ·
              refine ⟨620721583650614141759123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6621030225606550845430645 620721583650614141759123)
              ·
                refine ⟨931082375475921212638685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620721583650614141759123 931082375475921212638685)
                ·
                  refine ⟨349155890803470454739507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931082375475921212638685 349155890803470454739507)
                  ·
                    rfl

theorem cell20_764976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_764976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_764976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_764976 prefixEnd_764976 := by exact prefixLift 764976
  have htrace : WordTrace (prefixWord ++ tailWord_764976) baseStart_764976 baseEnd_764976 := by
    simpa [prefixWord, tailWord_764976, baseEnd_764976] using wordTrace_append hprefix tailTrace_764976
  have hstable : (prefixWord ++ tailWord_764976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764976).length < 2 ^ (prefixWord ++ tailWord_764976).sum := by decide
  have hdescent : baseEnd_764976 < baseStart_764976 := by decide
  rcases family_descends (prefixWord ++ tailWord_764976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765031 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 3]
def baseStart_765031 : Nat := 118140960795 + 765031 * 2 ^ 59
def prefixEnd_765031 : Nat := 4983230072969 + 3 ^ 40 * 765031 * 2
def baseEnd_765031 : Nat := 349180994302134707905949

theorem tailTrace_765031 : CollatzResearch.WordTrace tailWord_765031 prefixEnd_765031 349180994302134707905949 := by
  unfold tailWord_765031
  simp only [CollatzResearch.WordTrace]
  refine ⟨27902972891430818737782947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18601981927620545825188631 27902972891430818737782947)
  ·
    refine ⟨41854459337146228106674421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27902972891430818737782947 41854459337146228106674421)
    ·
      refine ⟨3923855562857458885000727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41854459337146228106674421 3923855562857458885000727)
      ·
        refine ⟨5885783344286188327501091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923855562857458885000727 5885783344286188327501091)
        ·
          refine ⟨8828675016429282491251637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5885783344286188327501091 8828675016429282491251637)
          ·
            refine ⟨827688282790245233554841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8828675016429282491251637 827688282790245233554841)
            ·
              refine ⟨620766212092683925166131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827688282790245233554841 620766212092683925166131)
              ·
                refine ⟨931149318139025887749197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620766212092683925166131 931149318139025887749197)
                ·
                  refine ⟨349180994302134707905949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931149318139025887749197 349180994302134707905949)
                  ·
                    rfl

theorem cell20_765031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_765031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765031 prefixEnd_765031 := by exact prefixLift 765031
  have htrace : WordTrace (prefixWord ++ tailWord_765031) baseStart_765031 baseEnd_765031 := by
    simpa [prefixWord, tailWord_765031, baseEnd_765031] using wordTrace_append hprefix tailTrace_765031
  have hstable : (prefixWord ++ tailWord_765031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765031).length < 2 ^ (prefixWord ++ tailWord_765031).sum := by decide
  have hdescent : baseEnd_765031 < baseStart_765031 := by decide
  rcases family_descends (prefixWord ++ tailWord_765031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765042 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_765042 : Nat := 118140960795 + 765042 * 2 ^ 59
def prefixEnd_765042 : Nat := 4983230072969 + 3 ^ 40 * 765042 * 2
def baseEnd_765042 : Nat := 349186015001867558539237

theorem tailTrace_765042 : CollatzResearch.WordTrace tailWord_765042 prefixEnd_765042 349186015001867558539237 := by
  unfold tailWord_765042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975843523597741904108345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18602249396260645077622253 6975843523597741904108345)
  ·
    refine ⟨5231882642698306428081259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6975843523597741904108345 5231882642698306428081259)
    ·
      refine ⟨7847823964047459642121889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5231882642698306428081259 7847823964047459642121889)
      ·
        refine ⟨5885867973035594731591417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7847823964047459642121889 5885867973035594731591417)
        ·
          refine ⟨4414400979776696048693563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5885867973035594731591417 4414400979776696048693563)
          ·
            refine ⟨6621601469665044073040345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414400979776696048693563 6621601469665044073040345)
            ·
              refine ⟨4966201102248783054780259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621601469665044073040345 4966201102248783054780259)
              ·
                refine ⟨7449301653373174582170389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966201102248783054780259 7449301653373174582170389)
                ·
                  refine ⟨349186015001867558539237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7449301653373174582170389 349186015001867558539237)
                  ·
                    rfl

theorem cell20_765042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_765042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765042 prefixEnd_765042 := by exact prefixLift 765042
  have htrace : WordTrace (prefixWord ++ tailWord_765042) baseStart_765042 baseEnd_765042 := by
    simpa [prefixWord, tailWord_765042, baseEnd_765042] using wordTrace_append hprefix tailTrace_765042
  have hstable : (prefixWord ++ tailWord_765042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765042).length < 2 ^ (prefixWord ++ tailWord_765042).sum := by decide
  have hdescent : baseEnd_765042 < baseStart_765042 := by decide
  rcases family_descends (prefixWord ++ tailWord_765042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765056 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_765056 : Nat := 118140960795 + 765056 * 2 ^ 59
def prefixEnd_765056 : Nat := 4983230072969 + 3 ^ 40 * 765056 * 2
def baseEnd_765056 : Nat := 349192404983345732072513

theorem tailTrace_765056 : CollatzResearch.WordTrace tailWord_765056 prefixEnd_765056 349192404983345732072513 := by
  unfold tailWord_765056
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951942358170124003721511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18602589810893498671628681 13951942358170124003721511)
  ·
    refine ⟨20927913537255186005582267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13951942358170124003721511 20927913537255186005582267)
    ·
      refine ⟨31391870305882779008373401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20927913537255186005582267 31391870305882779008373401)
      ·
        refine ⟨23543902729412084256280051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31391870305882779008373401 23543902729412084256280051)
        ·
          refine ⟨35315854094118126384420077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23543902729412084256280051 35315854094118126384420077)
          ·
            refine ⟨13243445285294297394157529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35315854094118126384420077 13243445285294297394157529)
            ·
              refine ⟨9932583963970723045618147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13243445285294297394157529 9932583963970723045618147)
              ·
                refine ⟨14898875945956084568427221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9932583963970723045618147 14898875945956084568427221)
                ·
                  refine ⟨349192404983345732072513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14898875945956084568427221 349192404983345732072513)
                  ·
                    rfl

theorem cell20_765056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_765056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765056 prefixEnd_765056 := by exact prefixLift 765056
  have htrace : WordTrace (prefixWord ++ tailWord_765056) baseStart_765056 baseEnd_765056 := by
    simpa [prefixWord, tailWord_765056, baseEnd_765056] using wordTrace_append hprefix tailTrace_765056
  have hstable : (prefixWord ++ tailWord_765056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765056).length < 2 ^ (prefixWord ++ tailWord_765056).sum := by decide
  have hdescent : baseEnd_765056 < baseStart_765056 := by decide
  rcases family_descends (prefixWord ++ tailWord_765056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765059 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 2]
def baseStart_765059 : Nat := 118140960795 + 765059 * 2 ^ 59
def prefixEnd_765059 : Nat := 4983230072969 + 3 ^ 40 * 765059 * 2
def baseEnd_765059 : Nat := 349193774265091054972501

theorem tailTrace_765059 : CollatzResearch.WordTrace tailWord_765059 prefixEnd_765059 349193774265091054972501 := by
  unfold tailWord_765059
  simp only [CollatzResearch.WordTrace]
  refine ⟨27903994135329379519802231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18602662756886253013201487 27903994135329379519802231)
  ·
    refine ⟨41855991202994069279703347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27903994135329379519802231 41855991202994069279703347)
    ·
      refine ⟨62783986804491103919555021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41855991202994069279703347 62783986804491103919555021)
      ·
        refine ⟨23543995051684163969833133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62783986804491103919555021 23543995051684163969833133)
        ·
          refine ⟨8828998144381561488687425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23543995051684163969833133 8828998144381561488687425)
          ·
            refine ⟨6621748608286171116515569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8828998144381561488687425 6621748608286171116515569)
            ·
              refine ⟨4966311456214628337386677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621748608286171116515569 4966311456214628337386677)
              ·
                refine ⟨465591699020121406630001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4966311456214628337386677 465591699020121406630001)
                ·
                  refine ⟨349193774265091054972501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465591699020121406630001 349193774265091054972501)
                  ·
                    rfl

theorem cell20_765059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 2].length) (baseStart_765059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765059 prefixEnd_765059 := by exact prefixLift 765059
  have htrace : WordTrace (prefixWord ++ tailWord_765059) baseStart_765059 baseEnd_765059 := by
    simpa [prefixWord, tailWord_765059, baseEnd_765059] using wordTrace_append hprefix tailTrace_765059
  have hstable : (prefixWord ++ tailWord_765059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765059).length < 2 ^ (prefixWord ++ tailWord_765059).sum := by decide
  have hdescent : baseEnd_765059 < baseStart_765059 := by decide
  rcases family_descends (prefixWord ++ tailWord_765059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765124 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 3]
def baseStart_765124 : Nat := 118140960795 + 765124 * 2 ^ 59
def prefixEnd_765124 : Nat := 4983230072969 + 3 ^ 40 * 765124 * 2
def baseEnd_765124 : Nat := 349223442036239717805569

theorem tailTrace_765124 : CollatzResearch.WordTrace tailWord_765124 prefixEnd_765124 349223442036239717805569 := by
  unfold tailWord_765124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13953182440046947810459213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18604243253395930413945617 13953182440046947810459213)
  ·
    refine ⟨5232443415017605428922205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13953182440046947810459213 5232443415017605428922205)
    ·
      refine ⟨1962166280631602035845827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5232443415017605428922205 1962166280631602035845827)
      ·
        refine ⟨2943249420947403053768741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962166280631602035845827 2943249420947403053768741)
        ·
          refine ⟨551859266427638072581639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2943249420947403053768741 551859266427638072581639)
          ·
            refine ⟨827788899641457108872459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551859266427638072581639 827788899641457108872459)
            ·
              refine ⟨1241683349462185663308689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827788899641457108872459 1241683349462185663308689)
              ·
                refine ⟨931262512096639247481517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241683349462185663308689 931262512096639247481517)
                ·
                  refine ⟨349223442036239717805569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931262512096639247481517 349223442036239717805569)
                  ·
                    rfl

theorem cell20_765124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_765124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765124 prefixEnd_765124 := by exact prefixLift 765124
  have htrace : WordTrace (prefixWord ++ tailWord_765124) baseStart_765124 baseEnd_765124 := by
    simpa [prefixWord, tailWord_765124, baseEnd_765124] using wordTrace_append hprefix tailTrace_765124
  have hstable : (prefixWord ++ tailWord_765124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765124).length < 2 ^ (prefixWord ++ tailWord_765124).sum := by decide
  have hdescent : baseEnd_765124 < baseStart_765124 := by decide
  rcases family_descends (prefixWord ++ tailWord_765124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765139 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_765139 : Nat := 118140960795 + 765139 * 2 ^ 59
def prefixEnd_765139 : Nat := 4983230072969 + 3 ^ 40 * 765139 * 2
def baseEnd_765139 : Nat := 349230288444966332305507

theorem tailTrace_765139 : CollatzResearch.WordTrace tailWord_765139 prefixEnd_765139 349230288444966332305507 := by
  unfold tailWord_765139
  simp only [CollatzResearch.WordTrace]
  refine ⟨27906911975039553182714471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18604607983359702121809647 27906911975039553182714471)
  ·
    refine ⟨41860367962559329774071707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27906911975039553182714471 41860367962559329774071707)
    ·
      refine ⟨62790551943838994661107561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41860367962559329774071707 62790551943838994661107561)
      ·
        refine ⟨47092913957879245995830671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62790551943838994661107561 47092913957879245995830671)
        ·
          refine ⟨70639370936818868993746007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47092913957879245995830671 70639370936818868993746007)
          ·
            refine ⟨105959056405228303490619011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70639370936818868993746007 105959056405228303490619011)
            ·
              refine ⟨158938584607842455235928517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105959056405228303490619011 158938584607842455235928517)
              ·
                refine ⟨29800984613970460356736597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158938584607842455235928517 29800984613970460356736597)
                ·
                  refine ⟨349230288444966332305507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29800984613970460356736597 349230288444966332305507)
                  ·
                    rfl

theorem cell20_765139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_765139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765139 prefixEnd_765139 := by exact prefixLift 765139
  have htrace : WordTrace (prefixWord ++ tailWord_765139) baseStart_765139 baseEnd_765139 := by
    simpa [prefixWord, tailWord_765139, baseEnd_765139] using wordTrace_append hprefix tailTrace_765139
  have hstable : (prefixWord ++ tailWord_765139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765139).length < 2 ^ (prefixWord ++ tailWord_765139).sum := by decide
  have hdescent : baseEnd_765139 < baseStart_765139 := by decide
  rcases family_descends (prefixWord ++ tailWord_765139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765156 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_765156 : Nat := 118140960795 + 765156 * 2 ^ 59
def prefixEnd_765156 : Nat := 4983230072969 + 3 ^ 40 * 765156 * 2
def baseEnd_765156 : Nat := 349238047708189828738771

theorem tailTrace_765156 : CollatzResearch.WordTrace tailWord_765156 prefixEnd_765156 349238047708189828738771 := by
  unfold tailWord_765156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13953766007988982543041661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18605021343985310057388881 13953766007988982543041661)
  ·
    refine ⟨5232662252995868453640623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13953766007988982543041661 5232662252995868453640623)
    ·
      refine ⟨7848993379493802680460935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5232662252995868453640623 7848993379493802680460935)
      ·
        refine ⟨11773490069240704020691403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848993379493802680460935 11773490069240704020691403)
        ·
          refine ⟨17660235103861056031037105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11773490069240704020691403 17660235103861056031037105)
          ·
            refine ⟨13245176327895792023277829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17660235103861056031037105 13245176327895792023277829)
            ·
              refine ⟨2483470561480461004364593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13245176327895792023277829 2483470561480461004364593)
              ·
                refine ⟨1862602921110345753273445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483470561480461004364593 1862602921110345753273445)
                ·
                  refine ⟨349238047708189828738771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1862602921110345753273445 349238047708189828738771)
                  ·
                    rfl

theorem cell20_765156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_765156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765156 prefixEnd_765156 := by exact prefixLift 765156
  have htrace : WordTrace (prefixWord ++ tailWord_765156) baseStart_765156 baseEnd_765156 := by
    simpa [prefixWord, tailWord_765156, baseEnd_765156] using wordTrace_append hprefix tailTrace_765156
  have hstable : (prefixWord ++ tailWord_765156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765156).length < 2 ^ (prefixWord ++ tailWord_765156).sum := by decide
  have hdescent : baseEnd_765156 < baseStart_765156 := by decide
  rcases family_descends (prefixWord ++ tailWord_765156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765163 : List Nat := [1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_765163 : Nat := 118140960795 + 765163 * 2 ^ 59
def prefixEnd_765163 : Nat := 4983230072969 + 3 ^ 40 * 765163 * 2
def baseEnd_765163 : Nat := 116413747566309638501803

theorem tailTrace_765163 : CollatzResearch.WordTrace tailWord_765163 prefixEnd_765163 116413747566309638501803 := by
  unfold tailWord_765163
  simp only [CollatzResearch.WordTrace]
  refine ⟨27907787326952605281588143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18605191551301736854392095 27907787326952605281588143)
  ·
    refine ⟨41861680990428907922382215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27907787326952605281588143 41861680990428907922382215)
    ·
      refine ⟨62792521485643361883573323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41861680990428907922382215 62792521485643361883573323)
      ·
        refine ⟨94188782228465042825359985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62792521485643361883573323 94188782228465042825359985)
        ·
          refine ⟨70641586671348782119019989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94188782228465042825359985 70641586671348782119019989)
          ·
            refine ⟨1655662187609737080914531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70641586671348782119019989 1655662187609737080914531)
            ·
              refine ⟨2483493281414605621371797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655662187609737080914531 2483493281414605621371797)
              ·
                refine ⟨116413747566309638501803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2483493281414605621371797 116413747566309638501803)
                ·
                  rfl

theorem cell20_765163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_765163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765163 prefixEnd_765163 := by exact prefixLift 765163
  have htrace : WordTrace (prefixWord ++ tailWord_765163) baseStart_765163 baseEnd_765163 := by
    simpa [prefixWord, tailWord_765163, baseEnd_765163] using wordTrace_append hprefix tailTrace_765163
  have hstable : (prefixWord ++ tailWord_765163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765163).length < 2 ^ (prefixWord ++ tailWord_765163).sum := by decide
  have hdescent : baseEnd_765163 < baseStart_765163 := by decide
  rcases family_descends (prefixWord ++ tailWord_765163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765180 : List Nat := [2, 2, 2, 1, 5, 2, 6]
def baseStart_765180 : Nat := 118140960795 + 765180 * 2 ^ 59
def prefixEnd_765180 : Nat := 4983230072969 + 3 ^ 40 * 765180 * 2
def baseEnd_765180 : Nat := 38805444662461379104297

theorem tailTrace_765180 : CollatzResearch.WordTrace tailWord_765180 prefixEnd_765180 38805444662461379104297 := by
  unfold tailWord_765180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13954203683945508592478497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18605604911927344789971329 13954203683945508592478497)
  ·
    refine ⟨10465652762959131444358873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13954203683945508592478497 10465652762959131444358873)
    ·
      refine ⟨7849239572219348583269155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10465652762959131444358873 7849239572219348583269155)
      ·
        refine ⟨11773859358329022874903733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849239572219348583269155 11773859358329022874903733)
        ·
          refine ⟨1103799314843345894522225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11773859358329022874903733 1103799314843345894522225)
          ·
            refine ⟨827849486132509420891669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103799314843345894522225 827849486132509420891669)
            ·
              refine ⟨38805444662461379104297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 827849486132509420891669 38805444662461379104297)
              ·
                rfl

theorem cell20_765180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 6].length) (baseStart_765180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765180 prefixEnd_765180 := by exact prefixLift 765180
  have htrace : WordTrace (prefixWord ++ tailWord_765180) baseStart_765180 baseEnd_765180 := by
    simpa [prefixWord, tailWord_765180, baseEnd_765180] using wordTrace_append hprefix tailTrace_765180
  have hstable : (prefixWord ++ tailWord_765180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765180).length < 2 ^ (prefixWord ++ tailWord_765180).sum := by decide
  have hdescent : baseEnd_765180 < baseStart_765180 := by decide
  rcases family_descends (prefixWord ++ tailWord_765180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765186 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_765186 : Nat := 118140960795 + 765186 * 2 ^ 59
def prefixEnd_765186 : Nat := 4983230072969 + 3 ^ 40 * 765186 * 2
def baseEnd_765186 : Nat := 349251740525643057738649

theorem tailTrace_765186 : CollatzResearch.WordTrace tailWord_765186 prefixEnd_765186 349251740525643057738649 := by
  unfold tailWord_765186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977156551467320052418853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18605750803912853473116941 6977156551467320052418853)
  ·
    refine ⟨1308216853400122509828535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6977156551467320052418853 1308216853400122509828535)
    ·
      refine ⟨1962325280100183764742803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308216853400122509828535 1962325280100183764742803)
      ·
        refine ⟨2943487920150275647114205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962325280100183764742803 2943487920150275647114205)
        ·
          refine ⟨1103807970056353367667827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2943487920150275647114205 1103807970056353367667827)
          ·
            refine ⟨1655711955084530051501741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103807970056353367667827 1655711955084530051501741)
            ·
              refine ⟨620891983156698769313153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1655711955084530051501741 620891983156698769313153)
              ·
                refine ⟨465668987367524076984865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620891983156698769313153 465668987367524076984865)
                ·
                  refine ⟨349251740525643057738649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465668987367524076984865 349251740525643057738649)
                  ·
                    rfl

theorem cell20_765186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_765186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765186 prefixEnd_765186 := by exact prefixLift 765186
  have htrace : WordTrace (prefixWord ++ tailWord_765186) baseStart_765186 baseEnd_765186 := by
    simpa [prefixWord, tailWord_765186, baseEnd_765186] using wordTrace_append hprefix tailTrace_765186
  have hstable : (prefixWord ++ tailWord_765186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765186).length < 2 ^ (prefixWord ++ tailWord_765186).sum := by decide
  have hdescent : baseEnd_765186 < baseStart_765186 := by decide
  rcases family_descends (prefixWord ++ tailWord_765186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765201 : List Nat := [1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_765201 : Nat := 118140960795 + 765201 * 2 ^ 59
def prefixEnd_765201 : Nat := 4983230072969 + 3 ^ 40 * 765201 * 2
def baseEnd_765201 : Nat := 116419528978123224079529

theorem tailTrace_765201 : CollatzResearch.WordTrace tailWord_765201 prefixEnd_765201 116419528978123224079529 := by
  unfold tailWord_765201
  simp only [CollatzResearch.WordTrace]
  refine ⟨27909173300814937771471457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18606115533876625180980971 27909173300814937771471457)
  ·
    refine ⟨20931879975611203328603593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27909173300814937771471457 20931879975611203328603593)
    ·
      refine ⟨15698909981708402496452695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20931879975611203328603593 15698909981708402496452695)
      ·
        refine ⟨23548364972562603744679043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15698909981708402496452695 23548364972562603744679043)
        ·
          refine ⟨35322547458843905617018565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23548364972562603744679043 35322547458843905617018565)
          ·
            refine ⟨6622977648533232303190981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35322547458843905617018565 6622977648533232303190981)
            ·
              refine ⟨1241808309099981056848309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6622977648533232303190981 1241808309099981056848309)
              ·
                refine ⟨116419528978123224079529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1241808309099981056848309 116419528978123224079529)
                ·
                  rfl

theorem cell20_765201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_765201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765201 prefixEnd_765201 := by exact prefixLift 765201
  have htrace : WordTrace (prefixWord ++ tailWord_765201) baseStart_765201 baseEnd_765201 := by
    simpa [prefixWord, tailWord_765201, baseEnd_765201] using wordTrace_append hprefix tailTrace_765201
  have hstable : (prefixWord ++ tailWord_765201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765201).length < 2 ^ (prefixWord ++ tailWord_765201).sum := by decide
  have hdescent : baseEnd_765201 < baseStart_765201 := by decide
  rcases family_descends (prefixWord ++ tailWord_765201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765238 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_765238 : Nat := 118140960795 + 765238 * 2 ^ 59
def prefixEnd_765238 : Nat := 4983230072969 + 3 ^ 40 * 765238 * 2
def baseEnd_765238 : Nat := 349275474742561988005103

theorem tailTrace_765238 : CollatzResearch.WordTrace tailWord_765238 prefixEnd_765238 349275474742561988005103 := by
  unfold tailWord_765238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744407675105055818160523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18607015201120595393712245 1744407675105055818160523)
  ·
    refine ⟨2616611512657583727240785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1744407675105055818160523 2616611512657583727240785)
    ·
      refine ⟨1962458634493187795430589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2616611512657583727240785 1962458634493187795430589)
      ·
        refine ⟨735921987934945423286471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1962458634493187795430589 735921987934945423286471)
        ·
          refine ⟨1103882981902418134929707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735921987934945423286471 1103882981902418134929707)
          ·
            refine ⟨1655824472853627202394561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103882981902418134929707 1655824472853627202394561)
            ·
              refine ⟨1241868354640220401795921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655824472853627202394561 1241868354640220401795921)
              ·
                refine ⟨931401265980165301346941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241868354640220401795921 931401265980165301346941)
                ·
                  refine ⟨349275474742561988005103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931401265980165301346941 349275474742561988005103)
                  ·
                    rfl

theorem cell20_765238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_765238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765238 prefixEnd_765238 := by exact prefixLift 765238
  have htrace : WordTrace (prefixWord ++ tailWord_765238) baseStart_765238 baseEnd_765238 := by
    simpa [prefixWord, tailWord_765238, baseEnd_765238] using wordTrace_append hprefix tailTrace_765238
  have hstable : (prefixWord ++ tailWord_765238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765238).length < 2 ^ (prefixWord ++ tailWord_765238).sum := by decide
  have hdescent : baseEnd_765238 < baseStart_765238 := by decide
  rcases family_descends (prefixWord ++ tailWord_765238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765245 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 2]
def baseStart_765245 : Nat := 118140960795 + 765245 * 2 ^ 59
def prefixEnd_765245 : Nat := 4983230072969 + 3 ^ 40 * 765245 * 2
def baseEnd_765245 : Nat := 349278669733301074771741

theorem tailTrace_765245 : CollatzResearch.WordTrace tailWord_765245 prefixEnd_765245 349278669733301074771741 := by
  unfold tailWord_765245
  simp only [CollatzResearch.WordTrace]
  refine ⟨27910778112655533286073189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18607185408437022190715459 27910778112655533286073189)
  ·
    refine ⟨5233270896122912491138723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27910778112655533286073189 5233270896122912491138723)
    ·
      refine ⟨7849906344184368736708085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233270896122912491138723 7849906344184368736708085)
      ·
        refine ⟨735928719767284569066383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7849906344184368736708085 735928719767284569066383)
        ·
          refine ⟨1103893079650926853599575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735928719767284569066383 1103893079650926853599575)
          ·
            refine ⟨1655839619476390280399363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103893079650926853599575 1655839619476390280399363)
            ·
              refine ⟨2483759429214585420599045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655839619476390280399363 2483759429214585420599045)
              ·
                refine ⟨465704892977734766362321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2483759429214585420599045 465704892977734766362321)
                ·
                  refine ⟨349278669733301074771741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465704892977734766362321 349278669733301074771741)
                  ·
                    rfl

theorem cell20_765245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_765245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765245 prefixEnd_765245 := by exact prefixLift 765245
  have htrace : WordTrace (prefixWord ++ tailWord_765245) baseStart_765245 baseEnd_765245 := by
    simpa [prefixWord, tailWord_765245, baseEnd_765245] using wordTrace_append hprefix tailTrace_765245
  have hstable : (prefixWord ++ tailWord_765245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765245).length < 2 ^ (prefixWord ++ tailWord_765245).sum := by decide
  have hdescent : baseEnd_765245 < baseStart_765245 := by decide
  rcases family_descends (prefixWord ++ tailWord_765245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765253 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_765253 : Nat := 118140960795 + 765253 * 2 ^ 59
def prefixEnd_765253 : Nat := 4983230072969 + 3 ^ 40 * 765253 * 2
def baseEnd_765253 : Nat := 349282321151288602505041

theorem tailTrace_765253 : CollatzResearch.WordTrace tailWord_765253 prefixEnd_765253 349282321151288602505041 := by
  unfold tailWord_765253
  simp only [CollatzResearch.WordTrace]
  refine ⟨27911069896626550652364413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18607379931084367101576275 27911069896626550652364413)
  ·
    refine ⟨10466651211234956494636655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27911069896626550652364413 10466651211234956494636655)
    ·
      refine ⟨15699976816852434741954983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10466651211234956494636655 15699976816852434741954983)
      ·
        refine ⟨23549965225278652112932475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15699976816852434741954983 23549965225278652112932475)
        ·
          refine ⟨35324947837917978169398713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23549965225278652112932475 35324947837917978169398713)
          ·
            refine ⟨26493710878438483627049035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35324947837917978169398713 26493710878438483627049035)
            ·
              refine ⟨39740566317657725440573553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26493710878438483627049035 39740566317657725440573553)
              ·
                refine ⟨29805424738243294080430165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39740566317657725440573553 29805424738243294080430165)
                ·
                  refine ⟨349282321151288602505041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29805424738243294080430165 349282321151288602505041)
                  ·
                    rfl

theorem cell20_765253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_765253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765253 prefixEnd_765253 := by exact prefixLift 765253
  have htrace : WordTrace (prefixWord ++ tailWord_765253) baseStart_765253 baseEnd_765253 := by
    simpa [prefixWord, tailWord_765253, baseEnd_765253] using wordTrace_append hprefix tailTrace_765253
  have hstable : (prefixWord ++ tailWord_765253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765253).length < 2 ^ (prefixWord ++ tailWord_765253).sum := by decide
  have hdescent : baseEnd_765253 < baseStart_765253 := by decide
  rcases family_descends (prefixWord ++ tailWord_765253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765308 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_765308 : Nat := 118140960795 + 765308 * 2 ^ 59
def prefixEnd_765308 : Nat := 4983230072969 + 3 ^ 40 * 765308 * 2
def baseEnd_765308 : Nat := 349307424649952855671483

theorem tailTrace_765308 : CollatzResearch.WordTrace tailWord_765308 prefixEnd_765308 349307424649952855671483 := by
  unfold tailWord_765308
  simp only [CollatzResearch.WordTrace]
  refine ⟨13956537955713647522808289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18608717274284863363744385 13956537955713647522808289)
  ·
    refine ⟨10467403466785235642106217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13956537955713647522808289 10467403466785235642106217)
    ·
      refine ⟨7850552600088926731579663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10467403466785235642106217 7850552600088926731579663)
      ·
        refine ⟨11775828900133390097369495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7850552600088926731579663 11775828900133390097369495)
        ·
          refine ⟨17663743350200085146054243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11775828900133390097369495 17663743350200085146054243)
          ·
            refine ⟨26495615025300127719081365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17663743350200085146054243 26495615025300127719081365)
            ·
              refine ⟨1241981954310943486831939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26495615025300127719081365 1241981954310943486831939)
              ·
                refine ⟨1862972931466415230247909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241981954310943486831939 1862972931466415230247909)
                ·
                  refine ⟨349307424649952855671483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1862972931466415230247909 349307424649952855671483)
                  ·
                    rfl

theorem cell20_765308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_765308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765308 prefixEnd_765308 := by exact prefixLift 765308
  have htrace : WordTrace (prefixWord ++ tailWord_765308) baseStart_765308 baseEnd_765308 := by
    simpa [prefixWord, tailWord_765308, baseEnd_765308] using wordTrace_append hprefix tailTrace_765308
  have hstable : (prefixWord ++ tailWord_765308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765308).length < 2 ^ (prefixWord ++ tailWord_765308).sum := by decide
  have hdescent : baseEnd_765308 < baseStart_765308 := by decide
  rcases family_descends (prefixWord ++ tailWord_765308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765314 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_765314 : Nat := 118140960795 + 765314 * 2 ^ 59
def prefixEnd_765314 : Nat := 4983230072969 + 3 ^ 40 * 765314 * 2
def baseEnd_765314 : Nat := 349310163213443501471459

theorem tailTrace_765314 : CollatzResearch.WordTrace tailWord_765314 prefixEnd_765314 349310163213443501471459 := by
  unfold tailWord_765314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978323687351389517583749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18608863166270372046889997 6978323687351389517583749)
  ·
    refine ⟨1308435691378385534546953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6978323687351389517583749 1308435691378385534546953)
    ·
      refine ⟨981326768533789150910215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308435691378385534546953 981326768533789150910215)
      ·
        refine ⟨1471990152800683726365323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981326768533789150910215 1471990152800683726365323)
        ·
          refine ⟨2207985229201025589547985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471990152800683726365323 2207985229201025589547985)
          ·
            refine ⟨1655988921900769192160989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207985229201025589547985 1655988921900769192160989)
            ·
              refine ⟨620995845712788447060371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1655988921900769192160989 620995845712788447060371)
              ·
                refine ⟨931493768569182670590557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620995845712788447060371 931493768569182670590557)
                ·
                  refine ⟨349310163213443501471459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931493768569182670590557 349310163213443501471459)
                  ·
                    rfl

theorem cell20_765314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_765314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765314 prefixEnd_765314 := by exact prefixLift 765314
  have htrace : WordTrace (prefixWord ++ tailWord_765314) baseStart_765314 baseEnd_765314 := by
    simpa [prefixWord, tailWord_765314, baseEnd_765314] using wordTrace_append hprefix tailTrace_765314
  have hstable : (prefixWord ++ tailWord_765314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765314).length < 2 ^ (prefixWord ++ tailWord_765314).sum := by decide
  have hdescent : baseEnd_765314 < baseStart_765314 := by decide
  rcases family_descends (prefixWord ++ tailWord_765314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765332 : List Nat := [2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_765332 : Nat := 118140960795 + 765332 * 2 ^ 59
def prefixEnd_765332 : Nat := 4983230072969 + 3 ^ 40 * 765332 * 2
def baseEnd_765332 : Nat := 116439459634638479623795

theorem tailTrace_765332 : CollatzResearch.WordTrace tailWord_765332 prefixEnd_765332 116439459634638479623795 := by
  unfold tailWord_765332
  simp only [CollatzResearch.WordTrace]
  refine ⟨13956975631670173572245125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18609300842226898096326833 13956975631670173572245125)
  ·
    refine ⟨2616932930938157544795961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13956975631670173572245125 2616932930938157544795961)
    ·
      refine ⟨1962699698203618158596971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2616932930938157544795961 1962699698203618158596971)
      ·
        refine ⟨2944049547305427237895457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962699698203618158596971 2944049547305427237895457)
        ·
          refine ⟨2208037160479070428421593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944049547305427237895457 2208037160479070428421593)
          ·
            refine ⟨1656027870359302821316195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208037160479070428421593 1656027870359302821316195)
            ·
              refine ⟨2484041805538954231974293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656027870359302821316195 2484041805538954231974293)
              ·
                refine ⟨116439459634638479623795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2484041805538954231974293 116439459634638479623795)
                ·
                  rfl

theorem cell20_765332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_765332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765332 prefixEnd_765332 := by exact prefixLift 765332
  have htrace : WordTrace (prefixWord ++ tailWord_765332) baseStart_765332 baseEnd_765332 := by
    simpa [prefixWord, tailWord_765332, baseEnd_765332] using wordTrace_append hprefix tailTrace_765332
  have hstable : (prefixWord ++ tailWord_765332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765332).length < 2 ^ (prefixWord ++ tailWord_765332).sum := by decide
  have hdescent : baseEnd_765332 < baseStart_765332 := by decide
  rcases family_descends (prefixWord ++ tailWord_765332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765415 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_765415 : Nat := 118140960795 + 765415 * 2 ^ 59
def prefixEnd_765415 : Nat := 4983230072969 + 3 ^ 40 * 765415 * 2
def baseEnd_765415 : Nat := 349356262365536039104379

theorem tailTrace_765415 : CollatzResearch.WordTrace tailWord_765415 prefixEnd_765415 349356262365536039104379 := by
  unfold tailWord_765415
  simp only [CollatzResearch.WordTrace]
  refine ⟨27916978522039652319761699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18611319014693101546507799 27916978522039652319761699)
  ·
    refine ⟨41875467783059478479642549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27916978522039652319761699 41875467783059478479642549)
    ·
      refine ⟨3925825104661826107466489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41875467783059478479642549 3925825104661826107466489)
      ·
        refine ⟨2944368828496369580599867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3925825104661826107466489 2944368828496369580599867)
        ·
          refine ⟨4416553242744554370899801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944368828496369580599867 4416553242744554370899801)
          ·
            refine ⟨3312414932058415778174851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4416553242744554370899801 3312414932058415778174851)
            ·
              refine ⟨4968622398087623667262277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3312414932058415778174851 4968622398087623667262277)
              ·
                refine ⟨931616699641429437611677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4968622398087623667262277 931616699641429437611677)
                ·
                  refine ⟨349356262365536039104379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931616699641429437611677 349356262365536039104379)
                  ·
                    rfl

theorem cell20_765415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_765415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765415 prefixEnd_765415 := by exact prefixLift 765415
  have htrace : WordTrace (prefixWord ++ tailWord_765415) baseStart_765415 baseEnd_765415 := by
    simpa [prefixWord, tailWord_765415, baseEnd_765415] using wordTrace_append hprefix tailTrace_765415
  have hstable : (prefixWord ++ tailWord_765415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765415).length < 2 ^ (prefixWord ++ tailWord_765415).sum := by decide
  have hdescent : baseEnd_765415 < baseStart_765415 := by decide
  rcases family_descends (prefixWord ++ tailWord_765415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765418 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_765418 : Nat := 118140960795 + 765418 * 2 ^ 59
def prefixEnd_765418 : Nat := 4983230072969 + 3 ^ 40 * 765418 * 2
def baseEnd_765418 : Nat := 349357631647281362004367

theorem tailTrace_765418 : CollatzResearch.WordTrace tailWord_765418 prefixEnd_765418 349357631647281362004367 := by
  unfold tailWord_765418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979271985257195958030227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18611391960685855888080605 6979271985257195958030227)
  ·
    refine ⟨10468907977885793937045341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6979271985257195958030227 10468907977885793937045341)
    ·
      refine ⟨3925840491707172726392003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10468907977885793937045341 3925840491707172726392003)
      ·
        refine ⟨5888760737560759089588005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925840491707172726392003 5888760737560759089588005)
        ·
          refine ⟨1104142638292642329297751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5888760737560759089588005 1104142638292642329297751)
          ·
            refine ⟨1656213957438963493946627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104142638292642329297751 1656213957438963493946627)
            ·
              refine ⟨2484320936158445240919941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656213957438963493946627 2484320936158445240919941)
              ·
                refine ⟨465810175529708482672489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2484320936158445240919941 465810175529708482672489)
                ·
                  refine ⟨349357631647281362004367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465810175529708482672489 349357631647281362004367)
                  ·
                    rfl

theorem cell20_765418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_765418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765418 prefixEnd_765418 := by exact prefixLift 765418
  have htrace : WordTrace (prefixWord ++ tailWord_765418) baseStart_765418 baseEnd_765418 := by
    simpa [prefixWord, tailWord_765418, baseEnd_765418] using wordTrace_append hprefix tailTrace_765418
  have hstable : (prefixWord ++ tailWord_765418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765418).length < 2 ^ (prefixWord ++ tailWord_765418).sum := by decide
  have hdescent : baseEnd_765418 < baseStart_765418 := by decide
  rcases family_descends (prefixWord ++ tailWord_765418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765422 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_765422 : Nat := 118140960795 + 765422 * 2 ^ 59
def prefixEnd_765422 : Nat := 4983230072969 + 3 ^ 40 * 765422 * 2
def baseEnd_765422 : Nat := 349359457356275125871017

theorem tailTrace_765422 : CollatzResearch.WordTrace tailWord_765422 prefixEnd_765422 349359457356275125871017 := by
  unfold tailWord_765422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489654229126786564408315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18611489222009528343511013 3489654229126786564408315)
  ·
    refine ⟨5234481343690179846612473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3489654229126786564408315 5234481343690179846612473)
    ·
      refine ⟨3925861007767634884959355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5234481343690179846612473 3925861007767634884959355)
      ·
        refine ⟨5888791511651452327439033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925861007767634884959355 5888791511651452327439033)
        ·
          refine ⟨4416593633738589245579275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5888791511651452327439033 4416593633738589245579275)
          ·
            refine ⟨6624890450607883868368913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416593633738589245579275 6624890450607883868368913)
            ·
              refine ⟨4968667837955912901276685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6624890450607883868368913 4968667837955912901276685)
              ·
                refine ⟨1863250439233467337978757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4968667837955912901276685 1863250439233467337978757)
                ·
                  refine ⟨349359457356275125871017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863250439233467337978757 349359457356275125871017)
                  ·
                    rfl

theorem cell20_765422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_765422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765422 prefixEnd_765422 := by exact prefixLift 765422
  have htrace : WordTrace (prefixWord ++ tailWord_765422) baseStart_765422 baseEnd_765422 := by
    simpa [prefixWord, tailWord_765422, baseEnd_765422] using wordTrace_append hprefix tailTrace_765422
  have hstable : (prefixWord ++ tailWord_765422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765422).length < 2 ^ (prefixWord ++ tailWord_765422).sum := by decide
  have hdescent : baseEnd_765422 < baseStart_765422 := by decide
  rcases family_descends (prefixWord ++ tailWord_765422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765488 : List Nat := [2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_765488 : Nat := 118140960795 + 765488 * 2 ^ 59
def prefixEnd_765488 : Nat := 4983230072969 + 3 ^ 40 * 765488 * 2
def baseEnd_765488 : Nat := 116463193851557409890249

theorem tailTrace_765488 : CollatzResearch.WordTrace tailWord_765488 prefixEnd_765488 116463193851557409890249 := by
  unfold tailWord_765488
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959820525387592893584559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18613094033850123858112745 13959820525387592893584559)
  ·
    refine ⟨20939730788081389340376839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13959820525387592893584559 20939730788081389340376839)
    ·
      refine ⟨31409596182122084010565259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20939730788081389340376839 31409596182122084010565259)
      ·
        refine ⟨47114394273183126015847889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31409596182122084010565259 47114394273183126015847889)
        ·
          refine ⟨35335795704887344511885917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47114394273183126015847889 35335795704887344511885917)
          ·
            refine ⟨13250923389332754191957219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35335795704887344511885917 13250923389332754191957219)
            ·
              refine ⟨19876385083999131287935829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13250923389332754191957219 19876385083999131287935829)
              ·
                refine ⟨116463193851557409890249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19876385083999131287935829 116463193851557409890249)
                ·
                  rfl

theorem cell20_765488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_765488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765488 prefixEnd_765488 := by exact prefixLift 765488
  have htrace : WordTrace (prefixWord ++ tailWord_765488) baseStart_765488 baseEnd_765488 := by
    simpa [prefixWord, tailWord_765488, baseEnd_765488] using wordTrace_append hprefix tailTrace_765488
  have hstable : (prefixWord ++ tailWord_765488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765488).length < 2 ^ (prefixWord ++ tailWord_765488).sum := by decide
  have hdescent : baseEnd_765488 < baseStart_765488 := by decide
  rcases family_descends (prefixWord ++ tailWord_765488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765501 : List Nat := [1, 4, 1, 3, 3, 2, 2, 4]
def baseStart_765501 : Nat := 118140960795 + 765501 * 2 ^ 59
def prefixEnd_765501 : Nat := 4983230072969 + 3 ^ 40 * 765501 * 2
def baseEnd_765501 : Nat := 116465171702967320745787

theorem tailTrace_765501 : CollatzResearch.WordTrace tailWord_765501 prefixEnd_765501 116465171702967320745787 := by
  unfold tailWord_765501
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920115199728089007392357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18613410133152059338261571 27920115199728089007392357)
  ·
    refine ⟨5235021599949016688886067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27920115199728089007392357 5235021599949016688886067)
    ·
      refine ⟨7852532399923525033329101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235021599949016688886067 7852532399923525033329101)
      ·
        refine ⟨2944699649971321887498413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7852532399923525033329101 2944699649971321887498413)
        ·
          refine ⟨1104262368739245707811905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2944699649971321887498413 1104262368739245707811905)
          ·
            refine ⟨828196776554434280858929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104262368739245707811905 828196776554434280858929)
            ·
              refine ⟨621147582415825710644197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828196776554434280858929 621147582415825710644197)
              ·
                refine ⟨116465171702967320745787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621147582415825710644197 116465171702967320745787)
                ·
                  rfl

theorem cell20_765501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_765501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765501 prefixEnd_765501 := by exact prefixLift 765501
  have htrace : WordTrace (prefixWord ++ tailWord_765501) baseStart_765501 baseEnd_765501 := by
    simpa [prefixWord, tailWord_765501, baseEnd_765501] using wordTrace_append hprefix tailTrace_765501
  have hstable : (prefixWord ++ tailWord_765501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765501).length < 2 ^ (prefixWord ++ tailWord_765501).sum := by decide
  have hdescent : baseEnd_765501 < baseStart_765501 := by decide
  rcases family_descends (prefixWord ++ tailWord_765501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765505 : List Nat := [1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_765505 : Nat := 118140960795 + 765505 * 2 ^ 59
def prefixEnd_765505 : Nat := 4983230072969 + 3 ^ 40 * 765505 * 2
def baseEnd_765505 : Nat := 116465780272631908701337

theorem tailTrace_765505 : CollatzResearch.WordTrace tailWord_765505 prefixEnd_765505 116465780272631908701337 := by
  unfold tailWord_765505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920261091713597690537969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18613507394475731793691979 27920261091713597690537969)
  ·
    refine ⟨20940195818785198267903477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27920261091713597690537969 20940195818785198267903477)
    ·
      refine ⟨1963143358011112337615951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20940195818785198267903477 1963143358011112337615951)
      ·
        refine ⟨2944715037016668506423927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963143358011112337615951 2944715037016668506423927)
        ·
          refine ⟨4417072555525002759635891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944715037016668506423927 4417072555525002759635891)
          ·
            refine ⟨6625608833287504139453837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417072555525002759635891 6625608833287504139453837)
            ·
              refine ⟨2484603312482814052295189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6625608833287504139453837 2484603312482814052295189)
              ·
                refine ⟨116465780272631908701337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2484603312482814052295189 116465780272631908701337)
                ·
                  rfl

theorem cell20_765505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_765505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765505 prefixEnd_765505 := by exact prefixLift 765505
  have htrace : WordTrace (prefixWord ++ tailWord_765505) baseStart_765505 baseEnd_765505 := by
    simpa [prefixWord, tailWord_765505, baseEnd_765505] using wordTrace_append hprefix tailTrace_765505
  have hstable : (prefixWord ++ tailWord_765505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765505).length < 2 ^ (prefixWord ++ tailWord_765505).sum := by decide
  have hdescent : baseEnd_765505 < baseStart_765505 := by decide
  rcases family_descends (prefixWord ++ tailWord_765505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765511 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 2]
def baseStart_765511 : Nat := 118140960795 + 765511 * 2 ^ 59
def prefixEnd_765511 : Nat := 4983230072969 + 3 ^ 40 * 765511 * 2
def baseEnd_765511 : Nat := 349400079381386371903987

theorem tailTrace_765511 : CollatzResearch.WordTrace tailWord_765511 prefixEnd_765511 349400079381386371903987 := by
  unfold tailWord_765511
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920479929691860715256387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18613653286461240476837591 27920479929691860715256387)
  ·
    refine ⟨41880719894537791072884581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27920479929691860715256387 41880719894537791072884581)
    ·
      refine ⟨7852634980225835826165859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41880719894537791072884581 7852634980225835826165859)
      ·
        refine ⟨11778952470338753739248789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7852634980225835826165859 11778952470338753739248789)
        ·
          refine ⟨552138397047129081527287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11778952470338753739248789 552138397047129081527287)
          ·
            refine ⟨828207595570693622290931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552138397047129081527287 828207595570693622290931)
            ·
              refine ⟨1242311393356040433436397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828207595570693622290931 1242311393356040433436397)
              ·
                refine ⟨465866772508515162538649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1242311393356040433436397 465866772508515162538649)
                ·
                  refine ⟨349400079381386371903987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465866772508515162538649 349400079381386371903987)
                  ·
                    rfl

theorem cell20_765511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 2].length) (baseStart_765511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765511 prefixEnd_765511 := by exact prefixLift 765511
  have htrace : WordTrace (prefixWord ++ tailWord_765511) baseStart_765511 baseEnd_765511 := by
    simpa [prefixWord, tailWord_765511, baseEnd_765511] using wordTrace_append hprefix tailTrace_765511
  have hstable : (prefixWord ++ tailWord_765511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765511).length < 2 ^ (prefixWord ++ tailWord_765511).sum := by decide
  have hdescent : baseEnd_765511 < baseStart_765511 := by decide
  rcases family_descends (prefixWord ++ tailWord_765511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765546 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_765546 : Nat := 118140960795 + 765546 * 2 ^ 59
def prefixEnd_765546 : Nat := 4983230072969 + 3 ^ 40 * 765546 * 2
def baseEnd_765546 : Nat := 349416054335081805737177

theorem tailTrace_765546 : CollatzResearch.WordTrace tailWord_765546 prefixEnd_765546 349416054335081805737177 := by
  unfold tailWord_765546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980439121141265423195123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18614504323043374461853661 6980439121141265423195123)
  ·
    refine ⟨10470658681711898134792685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6980439121141265423195123 10470658681711898134792685)
    ·
      refine ⟨3926497005641961800547257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10470658681711898134792685 3926497005641961800547257)
      ·
        refine ⟨2944872754231471350410443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3926497005641961800547257 2944872754231471350410443)
        ·
          refine ⟨4417309131347207025615665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944872754231471350410443 4417309131347207025615665)
          ·
            refine ⟨3312981848510405269211749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4417309131347207025615665 3312981848510405269211749)
            ·
              refine ⟨621184096595700987977203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3312981848510405269211749 621184096595700987977203)
              ·
                refine ⟨931776144893551481965805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621184096595700987977203 931776144893551481965805)
                ·
                  refine ⟨349416054335081805737177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931776144893551481965805 349416054335081805737177)
                  ·
                    rfl

theorem cell20_765546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_765546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765546 prefixEnd_765546 := by exact prefixLift 765546
  have htrace : WordTrace (prefixWord ++ tailWord_765546) baseStart_765546 baseEnd_765546 := by
    simpa [prefixWord, tailWord_765546, baseEnd_765546] using wordTrace_append hprefix tailTrace_765546
  have hstable : (prefixWord ++ tailWord_765546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765546).length < 2 ^ (prefixWord ++ tailWord_765546).sum := by decide
  have hdescent : baseEnd_765546 < baseStart_765546 := by decide
  rcases family_descends (prefixWord ++ tailWord_765546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765591 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 2]
def baseStart_765591 : Nat := 118140960795 + 765591 * 2 ^ 59
def prefixEnd_765591 : Nat := 4983230072969 + 3 ^ 40 * 765591 * 2
def baseEnd_765591 : Nat := 349436593561261649236993

theorem tailTrace_765591 : CollatzResearch.WordTrace tailWord_765591 prefixEnd_765591 349436593561261649236993 := by
  unfold tailWord_765591
  simp only [CollatzResearch.WordTrace]
  refine ⟨27923397769402034378168627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18615598512934689585445751 27923397769402034378168627)
  ·
    refine ⟨41885096654103051567252941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27923397769402034378168627 41885096654103051567252941)
    ·
      refine ⟨15706911245288644337719853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41885096654103051567252941 15706911245288644337719853)
      ·
        refine ⟨5890091716983241626644945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15706911245288644337719853 5890091716983241626644945)
        ·
          refine ⟨4417568787737431219983709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5890091716983241626644945 4417568787737431219983709)
          ·
            refine ⟨1656588295401536707493891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4417568787737431219983709 1656588295401536707493891)
            ·
              refine ⟨2484882443102305061240837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656588295401536707493891 2484882443102305061240837)
              ·
                refine ⟨465915458081682198982657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2484882443102305061240837 465915458081682198982657)
                ·
                  refine ⟨349436593561261649236993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465915458081682198982657 349436593561261649236993)
                  ·
                    rfl

theorem cell20_765591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 2].length) (baseStart_765591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765591 prefixEnd_765591 := by exact prefixLift 765591
  have htrace : WordTrace (prefixWord ++ tailWord_765591) baseStart_765591 baseEnd_765591 := by
    simpa [prefixWord, tailWord_765591, baseEnd_765591] using wordTrace_append hprefix tailTrace_765591
  have hstable : (prefixWord ++ tailWord_765591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765591).length < 2 ^ (prefixWord ++ tailWord_765591).sum := by decide
  have hdescent : baseEnd_765591 < baseStart_765591 := by decide
  rcases family_descends (prefixWord ++ tailWord_765591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765598 : List Nat := [4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_765598 : Nat := 118140960795 + 765598 * 2 ^ 59
def prefixEnd_765598 : Nat := 4983230072969 + 3 ^ 40 * 765598 * 2
def baseEnd_765598 : Nat := 116479929517333578667877

theorem tailTrace_765598 : CollatzResearch.WordTrace tailWord_765598 prefixEnd_765598 116479929517333578667877 := by
  unfold tailWord_765598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3490456635047084321709181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18615768720251116382448965 3490456635047084321709181)
  ·
    refine ⟨1308921238142656620640943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3490456635047084321709181 1308921238142656620640943)
    ·
      refine ⟨1963381857213984930961415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308921238142656620640943 1963381857213984930961415)
      ·
        refine ⟨2945072785820977396442123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963381857213984930961415 2945072785820977396442123)
        ·
          refine ⟨4417609178731466094663185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945072785820977396442123 4417609178731466094663185)
          ·
            refine ⟨3313206884048599570997389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4417609178731466094663185 3313206884048599570997389)
            ·
              refine ⟨1242452581518224839124021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3313206884048599570997389 1242452581518224839124021)
              ·
                refine ⟨116479929517333578667877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1242452581518224839124021 116479929517333578667877)
                ·
                  rfl

theorem cell20_765598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_765598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765598 prefixEnd_765598 := by exact prefixLift 765598
  have htrace : WordTrace (prefixWord ++ tailWord_765598) baseStart_765598 baseEnd_765598 := by
    simpa [prefixWord, tailWord_765598, baseEnd_765598] using wordTrace_append hprefix tailTrace_765598
  have hstable : (prefixWord ++ tailWord_765598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765598).length < 2 ^ (prefixWord ++ tailWord_765598).sum := by decide
  have hdescent : baseEnd_765598 < baseStart_765598 := by decide
  rcases family_descends (prefixWord ++ tailWord_765598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765619 : List Nat := [1, 1, 1, 2, 3, 3, 5, 4]
def baseStart_765619 : Nat := 118140960795 + 765619 * 2 ^ 59
def prefixEnd_765619 : Nat := 4983230072969 + 3 ^ 40 * 765619 * 2
def baseEnd_765619 : Nat := 116483124508072665434515

theorem tailTrace_765619 : CollatzResearch.WordTrace tailWord_765619 prefixEnd_765619 116483124508072665434515 := by
  unfold tailWord_765619
  simp only [CollatzResearch.WordTrace]
  refine ⟨27924419013300595160187911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18616279342200396773458607 27924419013300595160187911)
  ·
    refine ⟨41886628519950892740281867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27924419013300595160187911 41886628519950892740281867)
    ·
      refine ⟨62829942779926339110422801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41886628519950892740281867 62829942779926339110422801)
      ·
        refine ⟨47122457084944754332817101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62829942779926339110422801 47122457084944754332817101)
        ·
          refine ⟨17670921406854282874806413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47122457084944754332817101 17670921406854282874806413)
          ·
            refine ⟨6626595527570356078052405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17670921406854282874806413 6626595527570356078052405)
            ·
              refine ⟨621243330709720882317413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6626595527570356078052405 621243330709720882317413)
              ·
                refine ⟨116483124508072665434515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621243330709720882317413 116483124508072665434515)
                ·
                  rfl

theorem cell20_765619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_765619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765619 prefixEnd_765619 := by exact prefixLift 765619
  have htrace : WordTrace (prefixWord ++ tailWord_765619) baseStart_765619 baseEnd_765619 := by
    simpa [prefixWord, tailWord_765619, baseEnd_765619] using wordTrace_append hprefix tailTrace_765619
  have hstable : (prefixWord ++ tailWord_765619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765619).length < 2 ^ (prefixWord ++ tailWord_765619).sum := by decide
  have hdescent : baseEnd_765619 < baseStart_765619 := by decide
  rcases family_descends (prefixWord ++ tailWord_765619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765629 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 2]
def baseStart_765629 : Nat := 118140960795 + 765629 * 2 ^ 59
def prefixEnd_765629 : Nat := 4983230072969 + 3 ^ 40 * 765629 * 2
def baseEnd_765629 : Nat := 349453937796702405970171

theorem tailTrace_765629 : CollatzResearch.WordTrace tailWord_765629 prefixEnd_765629 349453937796702405970171 := by
  unfold tailWord_765629
  simp only [CollatzResearch.WordTrace]
  refine ⟨27924783743264366868051941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18616522495509577912034627 27924783743264366868051941)
  ·
    refine ⟨5235896951862068787759739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27924783743264366868051941 5235896951862068787759739)
    ·
      refine ⟨7853845427793103181639609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235896951862068787759739 7853845427793103181639609)
      ·
        refine ⟨5890384070844827386229707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7853845427793103181639609 5890384070844827386229707)
        ·
          refine ⟨8835576106267241079344561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890384070844827386229707 8835576106267241079344561)
          ·
            refine ⟨6626682079700430809508421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8835576106267241079344561 6626682079700430809508421)
            ·
              refine ⟨1242502889943830776782829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6626682079700430809508421 1242502889943830776782829)
              ·
                refine ⟨465938583728936541293561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1242502889943830776782829 465938583728936541293561)
                ·
                  refine ⟨349453937796702405970171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465938583728936541293561 349453937796702405970171)
                  ·
                    rfl

theorem cell20_765629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_765629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765629 prefixEnd_765629 := by exact prefixLift 765629
  have htrace : WordTrace (prefixWord ++ tailWord_765629) baseStart_765629 baseEnd_765629 := by
    simpa [prefixWord, tailWord_765629, baseEnd_765629] using wordTrace_append hprefix tailTrace_765629
  have hstable : (prefixWord ++ tailWord_765629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765629).length < 2 ^ (prefixWord ++ tailWord_765629).sum := by decide
  have hdescent : baseEnd_765629 < baseStart_765629 := by decide
  rcases family_descends (prefixWord ++ tailWord_765629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765640 : List Nat := [2, 1, 3, 1, 2, 2, 9]
def baseStart_765640 : Nat := 118140960795 + 765640 * 2 ^ 59
def prefixEnd_765640 : Nat := 4983230072969 + 3 ^ 40 * 765640 * 2
def baseEnd_765640 : Nat := 38828773166270584067051

theorem tailTrace_765640 : CollatzResearch.WordTrace tailWord_765640 prefixEnd_765640 38828773166270584067051 := by
  unfold tailWord_765640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13962592473112257873351187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18616789964149677164468249 13962592473112257873351187)
  ·
    refine ⟨20943888709668386810026781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13962592473112257873351187 20943888709668386810026781)
    ·
      refine ⟨7853958266125645053760043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20943888709668386810026781 7853958266125645053760043)
      ·
        refine ⟨11780937399188467580640065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7853958266125645053760043 11780937399188467580640065)
        ·
          refine ⟨8835703049391350685480049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11780937399188467580640065 8835703049391350685480049)
          ·
            refine ⟨6626777287043513014110037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8835703049391350685480049 6626777287043513014110037)
            ·
              refine ⟨38828773166270584067051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6626777287043513014110037 38828773166270584067051)
              ·
                rfl

theorem cell20_765640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_765640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765640 prefixEnd_765640 := by exact prefixLift 765640
  have htrace : WordTrace (prefixWord ++ tailWord_765640) baseStart_765640 baseEnd_765640 := by
    simpa [prefixWord, tailWord_765640, baseEnd_765640] using wordTrace_append hprefix tailTrace_765640
  have hstable : (prefixWord ++ tailWord_765640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765640).length < 2 ^ (prefixWord ++ tailWord_765640).sum := by decide
  have hdescent : baseEnd_765640 < baseStart_765640 := by decide
  rcases family_descends (prefixWord ++ tailWord_765640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765650 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_765650 : Nat := 118140960795 + 765650 * 2 ^ 59
def prefixEnd_765650 : Nat := 4983230072969 + 3 ^ 40 * 765650 * 2
def baseEnd_765650 : Nat := 349463522768919666270085

theorem tailTrace_765650 : CollatzResearch.WordTrace tailWord_765650 prefixEnd_765650 349463522768919666270085 := by
  unfold tailWord_765650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6981387419047071863641601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18617033117458858303044269 6981387419047071863641601)
  ·
    refine ⟨5236040564285303897731201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6981387419047071863641601 5236040564285303897731201)
    ·
      refine ⟨3927030423213977923298401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5236040564285303897731201 3927030423213977923298401)
      ·
        refine ⟨2945272817410483442473801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3927030423213977923298401 2945272817410483442473801)
        ·
          refine ⟨2208954613057862581855351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945272817410483442473801 2208954613057862581855351)
          ·
            refine ⟨3313431919586793872783027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208954613057862581855351 3313431919586793872783027)
            ·
              refine ⟨4970147879380190809174541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313431919586793872783027 4970147879380190809174541)
              ·
                refine ⟨1863805454767571553440453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4970147879380190809174541 1863805454767571553440453)
                ·
                  refine ⟨349463522768919666270085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863805454767571553440453 349463522768919666270085)
                  ·
                    rfl

theorem cell20_765650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_765650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765650 prefixEnd_765650 := by exact prefixLift 765650
  have htrace : WordTrace (prefixWord ++ tailWord_765650) baseStart_765650 baseEnd_765650 := by
    simpa [prefixWord, tailWord_765650, baseEnd_765650] using wordTrace_append hprefix tailTrace_765650
  have hstable : (prefixWord ++ tailWord_765650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765650).length < 2 ^ (prefixWord ++ tailWord_765650).sum := by decide
  have hdescent : baseEnd_765650 < baseStart_765650 := by decide
  rcases family_descends (prefixWord ++ tailWord_765650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765664 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_765664 : Nat := 118140960795 + 765664 * 2 ^ 59
def prefixEnd_765664 : Nat := 4983230072969 + 3 ^ 40 * 765664 * 2
def baseEnd_765664 : Nat := 349469912750397839803361

theorem tailTrace_765664 : CollatzResearch.WordTrace tailWord_765664 prefixEnd_765664 349469912750397839803361 := by
  unfold tailWord_765664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963030149068783922788023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18617373532091711897050697 13963030149068783922788023)
  ·
    refine ⟨20944545223603175884182035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13963030149068783922788023 20944545223603175884182035)
    ·
      refine ⟨31416817835404763826273053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20944545223603175884182035 31416817835404763826273053)
      ·
        refine ⟨11781306688276786434852395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31416817835404763826273053 11781306688276786434852395)
        ·
          refine ⟨17671960032415179652278593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11781306688276786434852395 17671960032415179652278593)
          ·
            refine ⟨13253970024311384739208945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17671960032415179652278593 13253970024311384739208945)
            ·
              refine ⟨9940477518233538554406709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13253970024311384739208945 9940477518233538554406709)
              ·
                refine ⟨931919767334394239475629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9940477518233538554406709 931919767334394239475629)
                ·
                  refine ⟨349469912750397839803361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931919767334394239475629 349469912750397839803361)
                  ·
                    rfl

theorem cell20_765664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_765664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765664 prefixEnd_765664 := by exact prefixLift 765664
  have htrace : WordTrace (prefixWord ++ tailWord_765664) baseStart_765664 baseEnd_765664 := by
    simpa [prefixWord, tailWord_765664, baseEnd_765664] using wordTrace_append hprefix tailTrace_765664
  have hstable : (prefixWord ++ tailWord_765664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765664).length < 2 ^ (prefixWord ++ tailWord_765664).sum := by decide
  have hdescent : baseEnd_765664 < baseStart_765664 := by decide
  rcases family_descends (prefixWord ++ tailWord_765664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765688 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 2]
def baseStart_765688 : Nat := 118140960795 + 765688 * 2 ^ 59
def prefixEnd_765688 : Nat := 4983230072969 + 3 ^ 40 * 765688 * 2
def baseEnd_765688 : Nat := 349480867004360423003263

theorem tailTrace_765688 : CollatzResearch.WordTrace tailWord_765688 prefixEnd_765688 349480867004360423003263 := by
  unfold tailWord_765688
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963467825025309972224859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18617957100033746629633145 13963467825025309972224859)
  ·
    refine ⟨20945201737537964958337289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13963467825025309972224859 20945201737537964958337289)
    ·
      refine ⟨15708901303153473718752967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20945201737537964958337289 15708901303153473718752967)
      ·
        refine ⟨23563351954730210578129451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15708901303153473718752967 23563351954730210578129451)
        ·
          refine ⟨35345027932095315867194177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23563351954730210578129451 35345027932095315867194177)
          ·
            refine ⟨26508770949071486900395633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35345027932095315867194177 26508770949071486900395633)
            ·
              refine ⟨19881578211803615175296725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26508770949071486900395633 19881578211803615175296725)
              ·
                refine ⟨465974489339147230671017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19881578211803615175296725 465974489339147230671017)
                ·
                  refine ⟨349480867004360423003263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465974489339147230671017 349480867004360423003263)
                  ·
                    rfl

theorem cell20_765688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_765688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765688 prefixEnd_765688 := by exact prefixLift 765688
  have htrace : WordTrace (prefixWord ++ tailWord_765688) baseStart_765688 baseEnd_765688 := by
    simpa [prefixWord, tailWord_765688, baseEnd_765688] using wordTrace_append hprefix tailTrace_765688
  have hstable : (prefixWord ++ tailWord_765688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765688).length < 2 ^ (prefixWord ++ tailWord_765688).sum := by decide
  have hdescent : baseEnd_765688 < baseStart_765688 := by decide
  rcases family_descends (prefixWord ++ tailWord_765688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765719 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 3]
def baseStart_765719 : Nat := 118140960795 + 765719 * 2 ^ 59
def prefixEnd_765719 : Nat := 4983230072969 + 3 ^ 40 * 765719 * 2
def baseEnd_765719 : Nat := 349495016249062092969803

theorem tailTrace_765719 : CollatzResearch.WordTrace tailWord_765719 prefixEnd_765719 349495016249062092969803 := by
  unfold tailWord_765719
  simp only [CollatzResearch.WordTrace]
  refine ⟨27928066312938312238828211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18618710875292208159218807 27928066312938312238828211)
  ·
    refine ⟨41892099469407468358242317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27928066312938312238828211 41892099469407468358242317)
    ·
      refine ⟨15709537301027800634340869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41892099469407468358242317 15709537301027800634340869)
      ·
        refine ⟨2945538243942712618938913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15709537301027800634340869 2945538243942712618938913)
        ·
          refine ⟨2209153682957034464204185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945538243942712618938913 2209153682957034464204185)
          ·
            refine ⟨1656865262217775848153139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209153682957034464204185 1656865262217775848153139)
            ·
              refine ⟨2485297893326663772229709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656865262217775848153139 2485297893326663772229709)
              ·
                refine ⟨931986709997498914586141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2485297893326663772229709 931986709997498914586141)
                ·
                  refine ⟨349495016249062092969803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931986709997498914586141 349495016249062092969803)
                  ·
                    rfl

theorem cell20_765719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_765719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765719 prefixEnd_765719 := by exact prefixLift 765719
  have htrace : WordTrace (prefixWord ++ tailWord_765719) baseStart_765719 baseEnd_765719 := by
    simpa [prefixWord, tailWord_765719, baseEnd_765719] using wordTrace_append hprefix tailTrace_765719
  have hstable : (prefixWord ++ tailWord_765719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765719).length < 2 ^ (prefixWord ++ tailWord_765719).sum := by decide
  have hdescent : baseEnd_765719 < baseStart_765719 := by decide
  rcases family_descends (prefixWord ++ tailWord_765719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765754 : List Nat := [3, 1, 1, 1, 5, 9]
def baseStart_765754 : Nat := 118140960795 + 765754 * 2 ^ 59
def prefixEnd_765754 : Nat := 4983230072969 + 3 ^ 40 * 765754 * 2
def baseEnd_765754 : Nat := 12944851526028056548259

theorem tailTrace_765754 : CollatzResearch.WordTrace tailWord_765754 prefixEnd_765754 12944851526028056548259 := by
  unfold tailWord_765754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982335716952878304088079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18619561911874342144234877 6982335716952878304088079)
  ·
    refine ⟨10473503575429317456132119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6982335716952878304088079 10473503575429317456132119)
    ·
      refine ⟨15710255363143976184198179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10473503575429317456132119 15710255363143976184198179)
      ·
        refine ⟨23565383044715964276297269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15710255363143976184198179 23565383044715964276297269)
        ·
          refine ⟨2209254660442121650902869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23565383044715964276297269 2209254660442121650902869)
          ·
            refine ⟨12944851526028056548259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2209254660442121650902869 12944851526028056548259)
            ·
              rfl

theorem cell20_765754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 9].length) (baseStart_765754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765754 prefixEnd_765754 := by exact prefixLift 765754
  have htrace : WordTrace (prefixWord ++ tailWord_765754) baseStart_765754 baseEnd_765754 := by
    simpa [prefixWord, tailWord_765754, baseEnd_765754] using wordTrace_append hprefix tailTrace_765754
  have hstable : (prefixWord ++ tailWord_765754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765754).length < 2 ^ (prefixWord ++ tailWord_765754).sum := by decide
  have hdescent : baseEnd_765754 < baseStart_765754 := by decide
  rcases family_descends (prefixWord ++ tailWord_765754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765757 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_765757 : Nat := 118140960795 + 765757 * 2 ^ 59
def prefixEnd_765757 : Nat := 4983230072969 + 3 ^ 40 * 765757 * 2
def baseEnd_765757 : Nat := 349512360484502849702981

theorem tailTrace_765757 : CollatzResearch.WordTrace tailWord_765757 prefixEnd_765757 349512360484502849702981 := by
  unfold tailWord_765757
  simp only [CollatzResearch.WordTrace]
  refine ⟨27929452286800644728711525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18619634857867096485807683 27929452286800644728711525)
  ·
    refine ⟨5236772303775120886633411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27929452286800644728711525 5236772303775120886633411)
    ·
      refine ⟨7855158455662681329950117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5236772303775120886633411 7855158455662681329950117)
      ·
        refine ⟨1472842210436752749365647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7855158455662681329950117 1472842210436752749365647)
        ·
          refine ⟨2209263315655129124048471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472842210436752749365647 2209263315655129124048471)
          ·
            refine ⟨3313894973482693686072707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209263315655129124048471 3313894973482693686072707)
            ·
              refine ⟨4970842460224040529109061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313894973482693686072707 4970842460224040529109061)
              ·
                refine ⟨932032961292007599207949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4970842460224040529109061 932032961292007599207949)
                ·
                  refine ⟨349512360484502849702981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932032961292007599207949 349512360484502849702981)
                  ·
                    rfl

theorem cell20_765757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_765757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765757 prefixEnd_765757 := by exact prefixLift 765757
  have htrace : WordTrace (prefixWord ++ tailWord_765757) baseStart_765757 baseEnd_765757 := by
    simpa [prefixWord, tailWord_765757, baseEnd_765757] using wordTrace_append hprefix tailTrace_765757
  have hstable : (prefixWord ++ tailWord_765757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765757).length < 2 ^ (prefixWord ++ tailWord_765757).sum := by decide
  have hdescent : baseEnd_765757 < baseStart_765757 := by decide
  rcases family_descends (prefixWord ++ tailWord_765757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765785 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_765785 : Nat := 118140960795 + 765785 * 2 ^ 59
def prefixEnd_765785 : Nat := 4983230072969 + 3 ^ 40 * 765785 * 2
def baseEnd_765785 : Nat := 349525140447459196769533

theorem tailTrace_765785 : CollatzResearch.WordTrace tailWord_765785 prefixEnd_765785 349525140447459196769533 := by
  unfold tailWord_765785
  simp only [CollatzResearch.WordTrace]
  refine ⟨27930473530699205510730809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18620315687132803673820539 27930473530699205510730809)
  ·
    refine ⟨20947855148024404133048107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27930473530699205510730809 20947855148024404133048107)
    ·
      refine ⟨31421782722036606199572161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20947855148024404133048107 31421782722036606199572161)
      ·
        refine ⟨23566337041527454649679121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31421782722036606199572161 23566337041527454649679121)
        ·
          refine ⟨17674752781145590987259341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23566337041527454649679121 17674752781145590987259341)
          ·
            refine ⟨6628032292929596620222253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17674752781145590987259341 6628032292929596620222253)
            ·
              refine ⟨2485512109848598732583345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6628032292929596620222253 2485512109848598732583345)
              ·
                refine ⟨1864134082386449049437509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485512109848598732583345 1864134082386449049437509)
                ·
                  refine ⟨349525140447459196769533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864134082386449049437509 349525140447459196769533)
                  ·
                    rfl

theorem cell20_765785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_765785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765785 prefixEnd_765785 := by exact prefixLift 765785
  have htrace : WordTrace (prefixWord ++ tailWord_765785) baseStart_765785 baseEnd_765785 := by
    simpa [prefixWord, tailWord_765785, baseEnd_765785] using wordTrace_append hprefix tailTrace_765785
  have hstable : (prefixWord ++ tailWord_765785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765785).length < 2 ^ (prefixWord ++ tailWord_765785).sum := by decide
  have hdescent : baseEnd_765785 < baseStart_765785 := by decide
  rcases family_descends (prefixWord ++ tailWord_765785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765833 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 3]
def baseStart_765833 : Nat := 118140960795 + 765833 * 2 ^ 59
def prefixEnd_765833 : Nat := 4983230072969 + 3 ^ 40 * 765833 * 2
def baseEnd_765833 : Nat := 349547048955384363169337

theorem tailTrace_765833 : CollatzResearch.WordTrace tailWord_765833 prefixEnd_765833 349547048955384363169337 := by
  unfold tailWord_765833
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932224234525309708478153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18621482823016873138985435 27932224234525309708478153)
  ·
    refine ⟨20949168175893982281358615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27932224234525309708478153 20949168175893982281358615)
    ·
      refine ⟨31423752263840973422037923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20949168175893982281358615 31423752263840973422037923)
      ·
        refine ⟨47135628395761460133056885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31423752263840973422037923 47135628395761460133056885)
        ·
          refine ⟨4418965162102636887474083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47135628395761460133056885 4418965162102636887474083)
          ·
            refine ⟨6628447743153955331211125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418965162102636887474083 6628447743153955331211125)
            ·
              refine ⟨621416975920683312301043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6628447743153955331211125 621416975920683312301043)
              ·
                refine ⟨932125463881024968451565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621416975920683312301043 932125463881024968451565)
                ·
                  refine ⟨349547048955384363169337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932125463881024968451565 349547048955384363169337)
                  ·
                    rfl

theorem cell20_765833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_765833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765833 prefixEnd_765833 := by exact prefixLift 765833
  have htrace : WordTrace (prefixWord ++ tailWord_765833) baseStart_765833 baseEnd_765833 := by
    simpa [prefixWord, tailWord_765833, baseEnd_765833] using wordTrace_append hprefix tailTrace_765833
  have hstable : (prefixWord ++ tailWord_765833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765833).length < 2 ^ (prefixWord ++ tailWord_765833).sum := by decide
  have hdescent : baseEnd_765833 < baseStart_765833 := by decide
  rcases family_descends (prefixWord ++ tailWord_765833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765847 : List Nat := [1, 1, 3, 3, 1, 3, 4, 4]
def baseStart_765847 : Nat := 118140960795 + 765847 * 2 ^ 59
def prefixEnd_765847 : Nat := 4983230072969 + 3 ^ 40 * 765847 * 2
def baseEnd_765847 : Nat := 116517812978954178900871

theorem tailTrace_765847 : CollatzResearch.WordTrace tailWord_765847 prefixEnd_765847 116517812978954178900871 := by
  unfold tailWord_765847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932734856474590099487795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18621823237649726732991863 27932734856474590099487795)
  ·
    refine ⟨41899102284711885149231693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27932734856474590099487795 41899102284711885149231693)
    ·
      refine ⟨15712163356766956930961885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41899102284711885149231693 15712163356766956930961885)
      ·
        refine ⟨5892061258787608849110707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15712163356766956930961885 5892061258787608849110707)
        ·
          refine ⟨8838091888181413273666061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892061258787608849110707 8838091888181413273666061)
          ·
            refine ⟨3314284458068029977624773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8838091888181413273666061 3314284458068029977624773)
            ·
              refine ⟨621428335887755620804645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3314284458068029977624773 621428335887755620804645)
              ·
                refine ⟨116517812978954178900871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621428335887755620804645 116517812978954178900871)
                ·
                  rfl

theorem cell20_765847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_765847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765847 prefixEnd_765847 := by exact prefixLift 765847
  have htrace : WordTrace (prefixWord ++ tailWord_765847) baseStart_765847 baseEnd_765847 := by
    simpa [prefixWord, tailWord_765847, baseEnd_765847] using wordTrace_append hprefix tailTrace_765847
  have hstable : (prefixWord ++ tailWord_765847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765847).length < 2 ^ (prefixWord ++ tailWord_765847).sum := by decide
  have hdescent : baseEnd_765847 < baseStart_765847 := by decide
  rcases family_descends (prefixWord ++ tailWord_765847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765870 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_765870 : Nat := 118140960795 + 765870 * 2 ^ 59
def prefixEnd_765870 : Nat := 4983230072969 + 3 ^ 40 * 765870 * 2
def baseEnd_765870 : Nat := 349563936763576678935853

theorem tailTrace_765870 : CollatzResearch.WordTrace tailWord_765870 prefixEnd_765870 349563936763576678935853 := by
  unfold tailWord_765870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491696716923908128446883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18622382490260843351716709 3491696716923908128446883)
  ·
    refine ⟨5237545075385862192670325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491696716923908128446883 5237545075385862192670325)
    ·
      refine ⟨491019850817424580562843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5237545075385862192670325 491019850817424580562843)
      ·
        refine ⟨736529776226136870844265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491019850817424580562843 736529776226136870844265)
        ·
          refine ⟨552397332169602653133199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736529776226136870844265 552397332169602653133199)
          ·
            refine ⟨828595998254403979699799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552397332169602653133199 828595998254403979699799)
            ·
              refine ⟨1242893997381605969549699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828595998254403979699799 1242893997381605969549699)
              ·
                refine ⟨1864340996072408954324549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242893997381605969549699 1864340996072408954324549)
                ·
                  refine ⟨349563936763576678935853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864340996072408954324549 349563936763576678935853)
                  ·
                    rfl

theorem cell20_765870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_765870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765870 prefixEnd_765870 := by exact prefixLift 765870
  have htrace : WordTrace (prefixWord ++ tailWord_765870) baseStart_765870 baseEnd_765870 := by
    simpa [prefixWord, tailWord_765870, baseEnd_765870] using wordTrace_append hprefix tailTrace_765870
  have hstable : (prefixWord ++ tailWord_765870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765870).length < 2 ^ (prefixWord ++ tailWord_765870).sum := by decide
  have hdescent : baseEnd_765870 < baseStart_765870 := by decide
  rcases family_descends (prefixWord ++ tailWord_765870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765875 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_765875 : Nat := 118140960795 + 765875 * 2 ^ 59
def prefixEnd_765875 : Nat := 4983230072969 + 3 ^ 40 * 765875 * 2
def baseEnd_765875 : Nat := 349566218899818883769165

theorem tailTrace_765875 : CollatzResearch.WordTrace tailWord_765875 prefixEnd_765875 349566218899818883769165 := by
  unfold tailWord_765875
  simp only [CollatzResearch.WordTrace]
  refine ⟨27933756100373150881507079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18622504066915433921004719 27933756100373150881507079)
  ·
    refine ⟨41900634150559726322260619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27933756100373150881507079 41900634150559726322260619)
    ·
      refine ⟨62850951225839589483390929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41900634150559726322260619 62850951225839589483390929)
      ·
        refine ⟨47138213419379692112543197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62850951225839589483390929 47138213419379692112543197)
        ·
          refine ⟨17676830032267384542203699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47138213419379692112543197 17676830032267384542203699)
          ·
            refine ⟨26515245048401076813305549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676830032267384542203699 26515245048401076813305549)
            ·
              refine ⟨9943216893150403804989581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26515245048401076813305549 9943216893150403804989581)
              ·
                refine ⟨3728706334931401426871093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9943216893150403804989581 3728706334931401426871093)
                ·
                  refine ⟨349566218899818883769165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3728706334931401426871093 349566218899818883769165)
                  ·
                    rfl

theorem cell20_765875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_765875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765875 prefixEnd_765875 := by exact prefixLift 765875
  have htrace : WordTrace (prefixWord ++ tailWord_765875) baseStart_765875 baseEnd_765875 := by
    simpa [prefixWord, tailWord_765875, baseEnd_765875] using wordTrace_append hprefix tailTrace_765875
  have hstable : (prefixWord ++ tailWord_765875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765875).length < 2 ^ (prefixWord ++ tailWord_765875).sum := by decide
  have hdescent : baseEnd_765875 < baseStart_765875 := by decide
  rcases family_descends (prefixWord ++ tailWord_765875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765884 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 3]
def baseStart_765884 : Nat := 118140960795 + 765884 * 2 ^ 59
def prefixEnd_765884 : Nat := 4983230072969 + 3 ^ 40 * 765884 * 2
def baseEnd_765884 : Nat := 349570326745054852469129

theorem tailTrace_765884 : CollatzResearch.WordTrace tailWord_765884 prefixEnd_765884 349570326745054852469129 := by
  unfold tailWord_765884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13967042178670272709292353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18622722904893696945723137 13967042178670272709292353)
  ·
    refine ⟨10475281634002704531969265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13967042178670272709292353 10475281634002704531969265)
    ·
      refine ⟨7856461225502028398976949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10475281634002704531969265 7856461225502028398976949)
      ·
        refine ⟨736543239890815162404089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7856461225502028398976949 736543239890815162404089)
        ·
          refine ⟨552407429918111371803067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736543239890815162404089 552407429918111371803067)
          ·
            refine ⟨828611144877167057704601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552407429918111371803067 828611144877167057704601)
            ·
              refine ⟨621458358657875293278451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828611144877167057704601 621458358657875293278451)
              ·
                refine ⟨932187537986812939917677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621458358657875293278451 932187537986812939917677)
                ·
                  refine ⟨349570326745054852469129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932187537986812939917677 349570326745054852469129)
                  ·
                    rfl

theorem cell20_765884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_765884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765884 prefixEnd_765884 := by exact prefixLift 765884
  have htrace : WordTrace (prefixWord ++ tailWord_765884) baseStart_765884 baseEnd_765884 := by
    simpa [prefixWord, tailWord_765884, baseEnd_765884] using wordTrace_append hprefix tailTrace_765884
  have hstable : (prefixWord ++ tailWord_765884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765884).length < 2 ^ (prefixWord ++ tailWord_765884).sum := by decide
  have hdescent : baseEnd_765884 < baseStart_765884 := by decide
  rcases family_descends (prefixWord ++ tailWord_765884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765885 : List Nat := [1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_765885 : Nat := 118140960795 + 765885 * 2 ^ 59
def prefixEnd_765885 : Nat := 4983230072969 + 3 ^ 40 * 765885 * 2
def baseEnd_765885 : Nat := 116523594390767764478597

theorem tailTrace_765885 : CollatzResearch.WordTrace tailWord_765885 prefixEnd_765885 116523594390767764478597 := by
  unfold tailWord_765885
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934120830336922589371109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18622747220224615059580739 27934120830336922589371109)
  ·
    refine ⟨5237647655688172985507083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27934120830336922589371109 5237647655688172985507083)
    ·
      refine ⟨7856471483532259478260625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5237647655688172985507083 7856471483532259478260625)
      ·
        refine ⟨5892353612649194608695469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7856471483532259478260625 5892353612649194608695469)
        ·
          refine ⟨2209632604743447978260801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5892353612649194608695469 2209632604743447978260801)
          ·
            refine ⟨1657224453557585983695601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209632604743447978260801 1657224453557585983695601)
            ·
              refine ⟨1242918340168189487771701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657224453557585983695601 1242918340168189487771701)
              ·
                refine ⟨116523594390767764478597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1242918340168189487771701 116523594390767764478597)
                ·
                  rfl

theorem cell20_765885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_765885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765885 prefixEnd_765885 := by exact prefixLift 765885
  have htrace : WordTrace (prefixWord ++ tailWord_765885) baseStart_765885 baseEnd_765885 := by
    simpa [prefixWord, tailWord_765885, baseEnd_765885] using wordTrace_append hprefix tailTrace_765885
  have hstable : (prefixWord ++ tailWord_765885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765885).length < 2 ^ (prefixWord ++ tailWord_765885).sum := by decide
  have hdescent : baseEnd_765885 < baseStart_765885 := by decide
  rcases family_descends (prefixWord ++ tailWord_765885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765944 : List Nat := [2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_765944 : Nat := 118140960795 + 765944 * 2 ^ 59
def prefixEnd_765944 : Nat := 4983230072969 + 3 ^ 40 * 765944 * 2
def baseEnd_765944 : Nat := 116532570793320436822961

theorem tailTrace_765944 : CollatzResearch.WordTrace tailWord_765944 prefixEnd_765944 116532570793320436822961 := by
  unfold tailWord_765944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13968136368561587832884443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18624181824748783777179257 13968136368561587832884443)
  ·
    refine ⟨20952204552842381749326665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13968136368561587832884443 20952204552842381749326665)
    ·
      refine ⟨15714153414631786311994999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20952204552842381749326665 15714153414631786311994999)
      ·
        refine ⟨23571230121947679467992499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15714153414631786311994999 23571230121947679467992499)
        ·
          refine ⟨35356845182921519201988749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23571230121947679467992499 35356845182921519201988749)
          ·
            refine ⟨13258816943595569700745781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35356845182921519201988749 13258816943595569700745781)
            ·
              refine ⟨1243014088462084659444917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13258816943595569700745781 1243014088462084659444917)
              ·
                refine ⟨116532570793320436822961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1243014088462084659444917 116532570793320436822961)
                ·
                  rfl

theorem cell20_765944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_765944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_765944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_765944 prefixEnd_765944 := by exact prefixLift 765944
  have htrace : WordTrace (prefixWord ++ tailWord_765944) baseStart_765944 baseEnd_765944 := by
    simpa [prefixWord, tailWord_765944, baseEnd_765944] using wordTrace_append hprefix tailTrace_765944
  have hstable : (prefixWord ++ tailWord_765944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765944).length < 2 ^ (prefixWord ++ tailWord_765944).sum := by decide
  have hdescent : baseEnd_765944 < baseStart_765944 := by decide
  rcases family_descends (prefixWord ++ tailWord_765944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766013 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_766013 : Nat := 118140960795 + 766013 * 2 ^ 59
def prefixEnd_766013 : Nat := 4983230072969 + 3 ^ 40 * 766013 * 2
def baseEnd_766013 : Nat := 349629205860103737168601

theorem tailTrace_766013 : CollatzResearch.WordTrace tailWord_766013 prefixEnd_766013 349629205860103737168601 := by
  unfold tailWord_766013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27938789373873200450030693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18625859582582133633353795 27938789373873200450030693)
  ·
    refine ⟨5238523007601225084380755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27938789373873200450030693 5238523007601225084380755)
    ·
      refine ⟨7857784511401837626571133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238523007601225084380755 7857784511401837626571133)
      ·
        refine ⟨2946669191775689109964175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7857784511401837626571133 2946669191775689109964175)
        ·
          refine ⟨4420003787663533664946263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946669191775689109964175 4420003787663533664946263)
          ·
            refine ⟨6630005681495300497419395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420003787663533664946263 6630005681495300497419395)
            ·
              refine ⟨9945008522242950746129093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630005681495300497419395 9945008522242950746129093)
              ·
                refine ⟨1864689097920553264899205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9945008522242950746129093 1864689097920553264899205)
                ·
                  refine ⟨349629205860103737168601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864689097920553264899205 349629205860103737168601)
                  ·
                    rfl

theorem cell20_766013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_766013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766013 prefixEnd_766013 := by exact prefixLift 766013
  have htrace : WordTrace (prefixWord ++ tailWord_766013) baseStart_766013 baseEnd_766013 := by
    simpa [prefixWord, tailWord_766013, baseEnd_766013] using wordTrace_append hprefix tailTrace_766013
  have hstable : (prefixWord ++ tailWord_766013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766013).length < 2 ^ (prefixWord ++ tailWord_766013).sum := by decide
  have hdescent : baseEnd_766013 < baseStart_766013 := by decide
  rcases family_descends (prefixWord ++ tailWord_766013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766044 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_766044 : Nat := 118140960795 + 766044 * 2 ^ 59
def prefixEnd_766044 : Nat := 4983230072969 + 3 ^ 40 * 766044 * 2
def baseEnd_766044 : Nat := 349643355104805407135141

theorem tailTrace_766044 : CollatzResearch.WordTrace tailWord_766044 prefixEnd_766044 349643355104805407135141 := by
  unfold tailWord_766044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13969960018380446372204593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18626613357840595162939457 13969960018380446372204593)
  ·
    refine ⟨10477470013785334779153445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13969960018380446372204593 10477470013785334779153445)
    ·
      refine ⟨1964525627584750271091271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10477470013785334779153445 1964525627584750271091271)
      ·
        refine ⟨2946788441377125406636907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964525627584750271091271 2946788441377125406636907)
        ·
          refine ⟨4420182662065688109955361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946788441377125406636907 4420182662065688109955361)
          ·
            refine ⟨3315136996549266082466521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420182662065688109955361 3315136996549266082466521)
            ·
              refine ⟨2486352747411949561849891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315136996549266082466521 2486352747411949561849891)
              ·
                refine ⟨3729529121117924342774837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486352747411949561849891 3729529121117924342774837)
                ·
                  refine ⟨349643355104805407135141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3729529121117924342774837 349643355104805407135141)
                  ·
                    rfl

theorem cell20_766044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_766044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766044 prefixEnd_766044 := by exact prefixLift 766044
  have htrace : WordTrace (prefixWord ++ tailWord_766044) baseStart_766044 baseEnd_766044 := by
    simpa [prefixWord, tailWord_766044, baseEnd_766044] using wordTrace_append hprefix tailTrace_766044
  have hstable : (prefixWord ++ tailWord_766044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766044).length < 2 ^ (prefixWord ++ tailWord_766044).sum := by decide
  have hdescent : baseEnd_766044 < baseStart_766044 := by decide
  rcases family_descends (prefixWord ++ tailWord_766044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766051 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_766051 : Nat := 118140960795 + 766051 * 2 ^ 59
def prefixEnd_766051 : Nat := 4983230072969 + 3 ^ 40 * 766051 * 2
def baseEnd_766051 : Nat := 349646550095544493901779

theorem tailTrace_766051 : CollatzResearch.WordTrace tailWord_766051 prefixEnd_766051 349646550095544493901779 := by
  unfold tailWord_766051
  simp only [CollatzResearch.WordTrace]
  refine ⟨27940175347735532939914007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18626783565157021959942671 27940175347735532939914007)
  ·
    refine ⟨41910263021603299409871011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27940175347735532939914007 41910263021603299409871011)
    ·
      refine ⟨62865394532404949114806517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41910263021603299409871011 62865394532404949114806517)
      ·
        refine ⟨5893630737412963979513111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62865394532404949114806517 5893630737412963979513111)
        ·
          refine ⟨8840446106119445969269667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5893630737412963979513111 8840446106119445969269667)
          ·
            refine ⟨13260669159179168953904501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8840446106119445969269667 13260669159179168953904501)
            ·
              refine ⟨1243187733673047089428547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13260669159179168953904501 1243187733673047089428547)
              ·
                refine ⟨1864781600509570634142821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243187733673047089428547 1864781600509570634142821)
                ·
                  refine ⟨349646550095544493901779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1864781600509570634142821 349646550095544493901779)
                  ·
                    rfl

theorem cell20_766051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_766051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766051 prefixEnd_766051 := by exact prefixLift 766051
  have htrace : WordTrace (prefixWord ++ tailWord_766051) baseStart_766051 baseEnd_766051 := by
    simpa [prefixWord, tailWord_766051, baseEnd_766051] using wordTrace_append hprefix tailTrace_766051
  have hstable : (prefixWord ++ tailWord_766051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766051).length < 2 ^ (prefixWord ++ tailWord_766051).sum := by decide
  have hdescent : baseEnd_766051 < baseStart_766051 := by decide
  rcases family_descends (prefixWord ++ tailWord_766051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766072 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_766072 : Nat := 118140960795 + 766072 * 2 ^ 59
def prefixEnd_766072 : Nat := 4983230072969 + 3 ^ 40 * 766072 * 2
def baseEnd_766072 : Nat := 349656135067761754201693

theorem tailTrace_766072 : CollatzResearch.WordTrace tailWord_766072 prefixEnd_766072 349656135067761754201693 := by
  unfold tailWord_766072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970470640329726763214235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18627294187106302350952313 13970470640329726763214235)
  ·
    refine ⟨20955705960494590144821353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13970470640329726763214235 20955705960494590144821353)
    ·
      refine ⟨15716779470370942608616015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20955705960494590144821353 15716779470370942608616015)
      ·
        refine ⟨23575169205556413912924023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716779470370942608616015 23575169205556413912924023)
        ·
          refine ⟨35362753808334620869386035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23575169205556413912924023 35362753808334620869386035)
          ·
            refine ⟨53044130712501931304079053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35362753808334620869386035 53044130712501931304079053)
            ·
              refine ⟨19891549017188224239029645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53044130712501931304079053 19891549017188224239029645)
              ·
                refine ⟨7459330881445584089636117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19891549017188224239029645 7459330881445584089636117)
                ·
                  refine ⟨349656135067761754201693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7459330881445584089636117 349656135067761754201693)
                  ·
                    rfl

theorem cell20_766072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_766072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766072 prefixEnd_766072 := by exact prefixLift 766072
  have htrace : WordTrace (prefixWord ++ tailWord_766072) baseStart_766072 baseEnd_766072 := by
    simpa [prefixWord, tailWord_766072, baseEnd_766072] using wordTrace_append hprefix tailTrace_766072
  have hstable : (prefixWord ++ tailWord_766072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766072).length < 2 ^ (prefixWord ++ tailWord_766072).sum := by decide
  have hdescent : baseEnd_766072 < baseStart_766072 := by decide
  rcases family_descends (prefixWord ++ tailWord_766072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766113 : List Nat := [1, 2, 3, 3, 1, 4, 1, 5]
def baseStart_766113 : Nat := 118140960795 + 766113 * 2 ^ 59
def prefixEnd_766113 : Nat := 4983230072969 + 3 ^ 40 * 766113 * 2
def baseEnd_766113 : Nat := 116558282861649277944953

theorem tailTrace_766113 : CollatzResearch.WordTrace tailWord_766113 prefixEnd_766113 116558282861649277944953 := by
  unfold tailWord_766113
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942436673510917528670993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18628291115673945019113995 27942436673510917528670993)
  ·
    refine ⟨20956827505133188146503245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27942436673510917528670993 20956827505133188146503245)
    ·
      refine ⟨7858810314424945554938717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20956827505133188146503245 7858810314424945554938717)
      ·
        refine ⟨2947053867909354583102019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7858810314424945554938717 2947053867909354583102019)
        ·
          refine ⟨4420580801864031874653029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947053867909354583102019 4420580801864031874653029)
          ·
            refine ⟨828858900349505976497443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4420580801864031874653029 828858900349505976497443)
            ·
              refine ⟨1243288350524258964746165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828858900349505976497443 1243288350524258964746165)
              ·
                refine ⟨116558282861649277944953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1243288350524258964746165 116558282861649277944953)
                ·
                  rfl

theorem cell20_766113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_766113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766113 prefixEnd_766113 := by exact prefixLift 766113
  have htrace : WordTrace (prefixWord ++ tailWord_766113) baseStart_766113 baseEnd_766113 := by
    simpa [prefixWord, tailWord_766113, baseEnd_766113] using wordTrace_append hprefix tailTrace_766113
  have hstable : (prefixWord ++ tailWord_766113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766113).length < 2 ^ (prefixWord ++ tailWord_766113).sum := by decide
  have hdescent : baseEnd_766113 < baseStart_766113 := by decide
  rcases family_descends (prefixWord ++ tailWord_766113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766141 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_766141 : Nat := 118140960795 + 766141 * 2 ^ 59
def prefixEnd_766141 : Nat := 4983230072969 + 3 ^ 40 * 766141 * 2
def baseEnd_766141 : Nat := 349687628547904180901411

theorem tailTrace_766141 : CollatzResearch.WordTrace tailWord_766141 prefixEnd_766141 349687628547904180901411 := by
  unfold tailWord_766141
  simp only [CollatzResearch.WordTrace]
  refine ⟨27943457917409478310690277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18628971944939652207126851 27943457917409478310690277)
  ·
    refine ⟨5239398359514277183254427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27943457917409478310690277 5239398359514277183254427)
    ·
      refine ⟨7859097539271415774881641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239398359514277183254427 7859097539271415774881641)
      ·
        refine ⟨5894323154453561831161231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7859097539271415774881641 5894323154453561831161231)
        ·
          refine ⟨8841484731680342746741847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894323154453561831161231 8841484731680342746741847)
          ·
            refine ⟨13262227097520514120112771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8841484731680342746741847 13262227097520514120112771)
            ·
              refine ⟨19893340646280771180169157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13262227097520514120112771 19893340646280771180169157)
              ·
                refine ⟨3730001371177644596281717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19893340646280771180169157 3730001371177644596281717)
                ·
                  refine ⟨349687628547904180901411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3730001371177644596281717 349687628547904180901411)
                  ·
                    rfl

theorem cell20_766141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_766141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766141 prefixEnd_766141 := by exact prefixLift 766141
  have htrace : WordTrace (prefixWord ++ tailWord_766141) baseStart_766141 baseEnd_766141 := by
    simpa [prefixWord, tailWord_766141, baseEnd_766141] using wordTrace_append hprefix tailTrace_766141
  have hstable : (prefixWord ++ tailWord_766141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766141).length < 2 ^ (prefixWord ++ tailWord_766141).sum := by decide
  have hdescent : baseEnd_766141 < baseStart_766141 := by decide
  rcases family_descends (prefixWord ++ tailWord_766141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766144 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 2]
def baseStart_766144 : Nat := 118140960795 + 766144 * 2 ^ 59
def prefixEnd_766144 : Nat := 4983230072969 + 3 ^ 40 * 766144 * 2
def baseEnd_766144 : Nat := 349688997829649503801399

theorem tailTrace_766144 : CollatzResearch.WordTrace tailWord_766144 prefixEnd_766144 349688997829649503801399 := by
  unfold tailWord_766144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13971783668199304911524743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18629044890932406548699657 13971783668199304911524743)
  ·
    refine ⟨20957675502298957367287115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13971783668199304911524743 20957675502298957367287115)
    ·
      refine ⟨31436513253448436050930673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20957675502298957367287115 31436513253448436050930673)
      ·
        refine ⟨23577384940086327038198005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31436513253448436050930673 23577384940086327038198005)
        ·
          refine ⟨2210379838133093159831063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23577384940086327038198005 2210379838133093159831063)
          ·
            refine ⟨3315569757199639739746595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210379838133093159831063 3315569757199639739746595)
            ·
              refine ⟨4973354635799459609619893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315569757199639739746595 4973354635799459609619893)
              ·
                refine ⟨466251997106199338401865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4973354635799459609619893 466251997106199338401865)
                ·
                  refine ⟨349688997829649503801399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466251997106199338401865 349688997829649503801399)
                  ·
                    rfl

theorem cell20_766144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_766144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766144 prefixEnd_766144 := by exact prefixLift 766144
  have htrace : WordTrace (prefixWord ++ tailWord_766144) baseStart_766144 baseEnd_766144 := by
    simpa [prefixWord, tailWord_766144, baseEnd_766144] using wordTrace_append hprefix tailTrace_766144
  have hstable : (prefixWord ++ tailWord_766144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766144).length < 2 ^ (prefixWord ++ tailWord_766144).sum := by decide
  have hdescent : baseEnd_766144 < baseStart_766144 := by decide
  rcases family_descends (prefixWord ++ tailWord_766144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766155 : List Nat := [1, 1, 1, 1, 3, 2, 11]
def baseStart_766155 : Nat := 118140960795 + 766155 * 2 ^ 59
def prefixEnd_766155 : Nat := 4983230072969 + 3 ^ 40 * 766155 * 2
def baseEnd_766155 : Nat := 38854890947709150492743

theorem tailTrace_766155 : CollatzResearch.WordTrace tailWord_766155 prefixEnd_766155 38854890947709150492743 := by
  unfold tailWord_766155
  simp only [CollatzResearch.WordTrace]
  refine ⟨27943968539358758701699919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18629312359572505801133279 27943968539358758701699919)
  ·
    refine ⟨41915952809038138052549879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27943968539358758701699919 41915952809038138052549879)
    ·
      refine ⟨62873929213557207078824819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41915952809038138052549879 62873929213557207078824819)
      ·
        refine ⟨94310893820335810618237229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62873929213557207078824819 94310893820335810618237229)
        ·
          refine ⟨35366585182625928981838961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94310893820335810618237229 35366585182625928981838961)
          ·
            refine ⟨26524938886969446736379221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35366585182625928981838961 26524938886969446736379221)
            ·
              refine ⟨38854890947709150492743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26524938886969446736379221 38854890947709150492743)
              ·
                rfl

theorem cell20_766155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_766155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766155 prefixEnd_766155 := by exact prefixLift 766155
  have htrace : WordTrace (prefixWord ++ tailWord_766155) baseStart_766155 baseEnd_766155 := by
    simpa [prefixWord, tailWord_766155, baseEnd_766155] using wordTrace_append hprefix tailTrace_766155
  have hstable : (prefixWord ++ tailWord_766155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766155).length < 2 ^ (prefixWord ++ tailWord_766155).sum := by decide
  have hdescent : baseEnd_766155 < baseStart_766155 := by decide
  rcases family_descends (prefixWord ++ tailWord_766155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766158 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_766158 : Nat := 118140960795 + 766158 * 2 ^ 59
def prefixEnd_766158 : Nat := 4983230072969 + 3 ^ 40 * 766158 * 2
def baseEnd_766158 : Nat := 349695387811127677334675

theorem tailTrace_766158 : CollatzResearch.WordTrace tailWord_766158 prefixEnd_766158 349695387811127677334675 := by
  unfold tailWord_766158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493009744793486276757391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18629385305565260142706085 3493009744793486276757391)
  ·
    refine ⟨5239514617190229415136087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3493009744793486276757391 5239514617190229415136087)
    ·
      refine ⟨7859271925785344122704131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239514617190229415136087 7859271925785344122704131)
      ·
        refine ⟨11788907888678016184056197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859271925785344122704131 11788907888678016184056197)
        ·
          refine ⟨2210420229127128034510537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11788907888678016184056197 2210420229127128034510537)
          ·
            refine ⟨1657815171845346025882903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210420229127128034510537 1657815171845346025882903)
            ·
              refine ⟨2486722757768019038824355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657815171845346025882903 2486722757768019038824355)
              ·
                refine ⟨3730084136652028558236533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486722757768019038824355 3730084136652028558236533)
                ·
                  refine ⟨349695387811127677334675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3730084136652028558236533 349695387811127677334675)
                  ·
                    rfl

theorem cell20_766158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_766158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766158 prefixEnd_766158 := by exact prefixLift 766158
  have htrace : WordTrace (prefixWord ++ tailWord_766158) baseStart_766158 baseEnd_766158 := by
    simpa [prefixWord, tailWord_766158, baseEnd_766158] using wordTrace_append hprefix tailTrace_766158
  have hstable : (prefixWord ++ tailWord_766158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766158).length < 2 ^ (prefixWord ++ tailWord_766158).sum := by decide
  have hdescent : baseEnd_766158 < baseStart_766158 := by decide
  rcases family_descends (prefixWord ++ tailWord_766158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766189 : List Nat := [1, 5, 1, 2, 3, 1, 1, 6]
def baseStart_766189 : Nat := 118140960795 + 766189 * 2 ^ 59
def prefixEnd_766189 : Nat := 4983230072969 + 3 ^ 40 * 766189 * 2
def baseEnd_766189 : Nat := 116569845685276449100405

theorem tailTrace_766189 : CollatzResearch.WordTrace tailWord_766189 prefixEnd_766189 116569845685276449100405 := by
  unfold tailWord_766189
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945208621235582508437621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18630139080823721672291747 27945208621235582508437621)
  ·
    refine ⟨2619863308240835860166027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27945208621235582508437621 2619863308240835860166027)
    ·
      refine ⟨3929794962361253790249041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619863308240835860166027 3929794962361253790249041)
      ·
        refine ⟨2947346221770940342686781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3929794962361253790249041 2947346221770940342686781)
        ·
          refine ⟨1105254833164102628507543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2947346221770940342686781 1105254833164102628507543)
          ·
            refine ⟨1657882249746153942761315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105254833164102628507543 1657882249746153942761315)
            ·
              refine ⟨2486823374619230914141973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657882249746153942761315 2486823374619230914141973)
              ·
                refine ⟨116569845685276449100405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2486823374619230914141973 116569845685276449100405)
                ·
                  rfl

theorem cell20_766189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_766189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766189 prefixEnd_766189 := by exact prefixLift 766189
  have htrace : WordTrace (prefixWord ++ tailWord_766189) baseStart_766189 baseEnd_766189 := by
    simpa [prefixWord, tailWord_766189, baseEnd_766189] using wordTrace_append hprefix tailTrace_766189
  have hstable : (prefixWord ++ tailWord_766189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766189).length < 2 ^ (prefixWord ++ tailWord_766189).sum := by decide
  have hdescent : baseEnd_766189 < baseStart_766189 := by decide
  rcases family_descends (prefixWord ++ tailWord_766189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766217 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_766217 : Nat := 118140960795 + 766217 * 2 ^ 59
def prefixEnd_766217 : Nat := 4983230072969 + 3 ^ 40 * 766217 * 2
def baseEnd_766217 : Nat := 349722317018785694367767

theorem tailTrace_766217 : CollatzResearch.WordTrace tailWord_766217 prefixEnd_766217 349722317018785694367767 := by
  unfold tailWord_766217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27946229865134143290456905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18630819910089428860304603 27946229865134143290456905)
  ·
    refine ⟨20959672398850607467842679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27946229865134143290456905 20959672398850607467842679)
    ·
      refine ⟨31439508598275911201764019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20959672398850607467842679 31439508598275911201764019)
      ·
        refine ⟨47159262897413866802646029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31439508598275911201764019 47159262897413866802646029)
        ·
          refine ⟨17684723586530200050992261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47159262897413866802646029 17684723586530200050992261)
          ·
            refine ⟨3315885672474412509561049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17684723586530200050992261 3315885672474412509561049)
            ·
              refine ⟨2486914254355809382170787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315885672474412509561049 2486914254355809382170787)
              ·
                refine ⟨3730371381533714073256181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486914254355809382170787 3730371381533714073256181)
                ·
                  refine ⟨349722317018785694367767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3730371381533714073256181 349722317018785694367767)
                  ·
                    rfl

theorem cell20_766217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_766217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766217 prefixEnd_766217 := by exact prefixLift 766217
  have htrace : WordTrace (prefixWord ++ tailWord_766217) baseStart_766217 baseEnd_766217 := by
    simpa [prefixWord, tailWord_766217, baseEnd_766217] using wordTrace_append hprefix tailTrace_766217
  have hstable : (prefixWord ++ tailWord_766217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766217).length < 2 ^ (prefixWord ++ tailWord_766217).sum := by decide
  have hdescent : baseEnd_766217 < baseStart_766217 := by decide
  rcases family_descends (prefixWord ++ tailWord_766217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
