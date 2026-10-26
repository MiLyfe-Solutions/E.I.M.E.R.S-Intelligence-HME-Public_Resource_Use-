import V185TrunkScan20Chunk108

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_661690 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_661690 : Nat := 118140960795 + 661690 * 2 ^ 59
def prefixEnd_661690 : Nat := 4983230072969 + 3 ^ 40 * 661690 * 2
def baseEnd_661690 : Nat := 302013346020996772028399

theorem tailTrace_661690 : CollatzResearch.WordTrace tailWord_661690 prefixEnd_661690 302013346020996772028399 := by
  unfold tailWord_661690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033454243204403125027631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16089211315211741666740349 6033454243204403125027631)
  ·
    refine ⟨9050181364806604687541447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6033454243204403125027631 9050181364806604687541447)
    ·
      refine ⟨13575272047209907031312171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9050181364806604687541447 13575272047209907031312171)
      ·
        refine ⟨20362908070814860546968257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575272047209907031312171 20362908070814860546968257)
        ·
          refine ⟨15272181053111145410226193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20362908070814860546968257 15272181053111145410226193)
          ·
            refine ⟨11454135789833359057669645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15272181053111145410226193 11454135789833359057669645)
            ·
              refine ⟨4295300921187509646626117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11454135789833359057669645 4295300921187509646626117)
              ·
                refine ⟨805368922722658058742397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4295300921187509646626117 805368922722658058742397)
                ·
                  refine ⟨302013346020996772028399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805368922722658058742397 302013346020996772028399)
                  ·
                    rfl

theorem cell20_661690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_661690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661690 prefixEnd_661690 := by exact prefixLift 661690
  have htrace : WordTrace (prefixWord ++ tailWord_661690) baseStart_661690 baseEnd_661690 := by
    simpa [prefixWord, tailWord_661690, baseEnd_661690] using wordTrace_append hprefix tailTrace_661690
  have hstable : (prefixWord ++ tailWord_661690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661690).length < 2 ^ (prefixWord ++ tailWord_661690).sum := by decide
  have hdescent : baseEnd_661690 < baseStart_661690 := by decide
  rcases family_descends (prefixWord ++ tailWord_661690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661700 : List Nat := [2, 3, 3, 1, 2, 3, 1, 5]
def baseStart_661700 : Nat := 118140960795 + 661700 * 2 ^ 59
def prefixEnd_661700 : Nat := 4983230072969 + 3 ^ 40 * 661700 * 2
def baseEnd_661700 : Nat := 100672636764493727231675

theorem tailTrace_661700 : CollatzResearch.WordTrace tailWord_661700 prefixEnd_661700 100672636764493727231675 := by
  unfold tailWord_661700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12067090851390692103987277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16089454468520922805316369 12067090851390692103987277)
  ·
    refine ⟨4525159069271509538995229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12067090851390692103987277 4525159069271509538995229)
    ·
      refine ⟨1696934650976816077123211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4525159069271509538995229 1696934650976816077123211)
      ·
        refine ⟨2545401976465224115684817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696934650976816077123211 2545401976465224115684817)
        ·
          refine ⟨1909051482348918086763613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2545401976465224115684817 1909051482348918086763613)
          ·
            refine ⟨715894305880844282536355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1909051482348918086763613 715894305880844282536355)
            ·
              refine ⟨1073841458821266423804533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715894305880844282536355 1073841458821266423804533)
              ·
                refine ⟨100672636764493727231675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1073841458821266423804533 100672636764493727231675)
                ·
                  rfl

theorem cell20_661700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_661700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661700 prefixEnd_661700 := by exact prefixLift 661700
  have htrace : WordTrace (prefixWord ++ tailWord_661700) baseStart_661700 baseEnd_661700 := by
    simpa [prefixWord, tailWord_661700, baseEnd_661700] using wordTrace_append hprefix tailTrace_661700
  have hstable : (prefixWord ++ tailWord_661700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661700).length < 2 ^ (prefixWord ++ tailWord_661700).sum := by decide
  have hdescent : baseEnd_661700 < baseStart_661700 := by decide
  rcases family_descends (prefixWord ++ tailWord_661700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661714 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_661714 : Nat := 118140960795 + 661714 * 2 ^ 59
def prefixEnd_661714 : Nat := 4983230072969 + 3 ^ 40 * 661714 * 2
def baseEnd_661714 : Nat := 302024300274959355228301

theorem tailTrace_661714 : CollatzResearch.WordTrace tailWord_661714 prefixEnd_661714 302024300274959355228301 := by
  unfold tailWord_661714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033673081182666149746049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16089794883153776399322797 6033673081182666149746049)
  ·
    refine ⟨4525254810886999612309537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6033673081182666149746049 4525254810886999612309537)
    ·
      refine ⟨3393941108165249709232153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4525254810886999612309537 3393941108165249709232153)
      ·
        refine ⟨2545455831123937281924115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3393941108165249709232153 2545455831123937281924115)
        ·
          refine ⟨3818183746685905922886173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545455831123937281924115 3818183746685905922886173)
          ·
            refine ⟨1431818905007214721082315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3818183746685905922886173 1431818905007214721082315)
            ·
              refine ⟨2147728357510822081623473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431818905007214721082315 2147728357510822081623473)
              ·
                refine ⟨1610796268133116561217605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147728357510822081623473 1610796268133116561217605)
                ·
                  refine ⟨302024300274959355228301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610796268133116561217605 302024300274959355228301)
                  ·
                    rfl

theorem cell20_661714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_661714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661714 prefixEnd_661714 := by exact prefixLift 661714
  have htrace : WordTrace (prefixWord ++ tailWord_661714) baseStart_661714 baseEnd_661714 := by
    simpa [prefixWord, tailWord_661714, baseEnd_661714] using wordTrace_append hprefix tailTrace_661714
  have hstable : (prefixWord ++ tailWord_661714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661714).length < 2 ^ (prefixWord ++ tailWord_661714).sum := by decide
  have hdescent : baseEnd_661714 < baseStart_661714 := by decide
  rcases family_descends (prefixWord ++ tailWord_661714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661741 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 3]
def baseStart_661741 : Nat := 118140960795 + 661741 * 2 ^ 59
def prefixEnd_661741 : Nat := 4983230072969 + 3 ^ 40 * 661741 * 2
def baseEnd_661741 : Nat := 302036623810667261328191

theorem tailTrace_661741 : CollatzResearch.WordTrace tailWord_661741 prefixEnd_661741 302036623810667261328191 := by
  unfold tailWord_661741
  simp only [CollatzResearch.WordTrace]
  refine ⟨24135677095632848210217077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16090451397088565473478051 24135677095632848210217077)
  ·
    refine ⟨2262719727715579519707851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24135677095632848210217077 2262719727715579519707851)
    ·
      refine ⟨3394079591573369279561777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262719727715579519707851 3394079591573369279561777)
      ·
        refine ⟨2545559693680026959671333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3394079591573369279561777 2545559693680026959671333)
        ·
          refine ⟨477292442565005054938375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2545559693680026959671333 477292442565005054938375)
          ·
            refine ⟨715938663847507582407563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477292442565005054938375 715938663847507582407563)
            ·
              refine ⟨1073907995771261373611345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715938663847507582407563 1073907995771261373611345)
              ·
                refine ⟨805430996828446030208509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073907995771261373611345 805430996828446030208509)
                ·
                  refine ⟨302036623810667261328191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805430996828446030208509 302036623810667261328191)
                  ·
                    rfl

theorem cell20_661741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_661741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661741 prefixEnd_661741 := by exact prefixLift 661741
  have htrace : WordTrace (prefixWord ++ tailWord_661741) baseStart_661741 baseEnd_661741 := by
    simpa [prefixWord, tailWord_661741, baseEnd_661741] using wordTrace_append hprefix tailTrace_661741
  have hstable : (prefixWord ++ tailWord_661741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661741).length < 2 ^ (prefixWord ++ tailWord_661741).sum := by decide
  have hdescent : baseEnd_661741 < baseStart_661741 := by decide
  rcases family_descends (prefixWord ++ tailWord_661741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661786 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_661786 : Nat := 118140960795 + 661786 * 2 ^ 59
def prefixEnd_661786 : Nat := 4983230072969 + 3 ^ 40 * 661786 * 2
def baseEnd_661786 : Nat := 302057163036847104828007

theorem tailTrace_661786 : CollatzResearch.WordTrace tailWord_661786 prefixEnd_661786 302057163036847104828007 := by
  unfold tailWord_661786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034329595117455223901303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16091545586979880597070141 6034329595117455223901303)
  ·
    refine ⟨9051494392676182835851955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6034329595117455223901303 9051494392676182835851955)
    ·
      refine ⟨13577241589014274253777933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051494392676182835851955 13577241589014274253777933)
      ·
        refine ⟨5091465595880352845166725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13577241589014274253777933 5091465595880352845166725)
        ·
          refine ⟨954649799227566158468761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5091465595880352845166725 954649799227566158468761)
          ·
            refine ⟨715987349420674618851571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954649799227566158468761 715987349420674618851571)
            ·
              refine ⟨1073981024131011928277357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715987349420674618851571 1073981024131011928277357)
              ·
                refine ⟨402742884049129473104009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1073981024131011928277357 402742884049129473104009)
                ·
                  refine ⟨302057163036847104828007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402742884049129473104009 302057163036847104828007)
                  ·
                    rfl

theorem cell20_661786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_661786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661786 prefixEnd_661786 := by exact prefixLift 661786
  have htrace : WordTrace (prefixWord ++ tailWord_661786) baseStart_661786 baseEnd_661786 := by
    simpa [prefixWord, tailWord_661786, baseEnd_661786] using wordTrace_append hprefix tailTrace_661786
  have hstable : (prefixWord ++ tailWord_661786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661786).length < 2 ^ (prefixWord ++ tailWord_661786).sum := by decide
  have hdescent : baseEnd_661786 < baseStart_661786 := by decide
  rcases family_descends (prefixWord ++ tailWord_661786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661787 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_661787 : Nat := 118140960795 + 661787 * 2 ^ 59
def prefixEnd_661787 : Nat := 4983230072969 + 3 ^ 40 * 661787 * 2
def baseEnd_661787 : Nat := 302057619464095545794669

theorem tailTrace_661787 : CollatzResearch.WordTrace tailWord_661787 prefixEnd_661787 302057619464095545794669 := by
  unfold tailWord_661787
  simp only [CollatzResearch.WordTrace]
  refine ⟨24137354853466198066391615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16091569902310798710927743 24137354853466198066391615)
  ·
    refine ⟨36206032280199297099587423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24137354853466198066391615 36206032280199297099587423)
    ·
      refine ⟨54309048420298945649381135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36206032280199297099587423 54309048420298945649381135)
      ·
        refine ⟨81463572630448418474071703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54309048420298945649381135 81463572630448418474071703)
        ·
          refine ⟨122195358945672627711107555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81463572630448418474071703 122195358945672627711107555)
          ·
            refine ⟨183293038418508941566661333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122195358945672627711107555 183293038418508941566661333)
            ·
              refine ⟨4295930587933803317968625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183293038418508941566661333 4295930587933803317968625)
              ·
                refine ⟨3221947940950352488476469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4295930587933803317968625 3221947940950352488476469)
                ·
                  refine ⟨302057619464095545794669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3221947940950352488476469 302057619464095545794669)
                  ·
                    rfl

theorem cell20_661787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_661787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661787 prefixEnd_661787 := by exact prefixLift 661787
  have htrace : WordTrace (prefixWord ++ tailWord_661787) baseStart_661787 baseEnd_661787 := by
    simpa [prefixWord, tailWord_661787, baseEnd_661787] using wordTrace_append hprefix tailTrace_661787
  have hstable : (prefixWord ++ tailWord_661787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661787).length < 2 ^ (prefixWord ++ tailWord_661787).sum := by decide
  have hdescent : baseEnd_661787 < baseStart_661787 := by decide
  rcases family_descends (prefixWord ++ tailWord_661787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661797 : List Nat := [1, 3, 1, 2, 5, 2, 6]
def baseStart_661797 : Nat := 118140960795 + 661797 * 2 ^ 59
def prefixEnd_661797 : Nat := 4983230072969 + 3 ^ 40 * 661797 * 2
def baseEnd_661797 : Nat := 33562464859619995051255

theorem tailTrace_661797 : CollatzResearch.WordTrace tailWord_661797 prefixEnd_661797 33562464859619995051255 := by
  unfold tailWord_661797
  simp only [CollatzResearch.WordTrace]
  refine ⟨24137719583429969774255645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16091813055619979849503763 24137719583429969774255645)
  ·
    refine ⟨9051644843786238665345867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24137719583429969774255645 9051644843786238665345867)
    ·
      refine ⟨13577467265679357998018801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051644843786238665345867 13577467265679357998018801)
      ·
        refine ⟨10183100449259518498514101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13577467265679357998018801 10183100449259518498514101)
        ·
          refine ⟨954665667118079859235697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10183100449259518498514101 954665667118079859235697)
          ·
            refine ⟨715999250338559894426773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954665667118079859235697 715999250338559894426773)
            ·
              refine ⟨33562464859619995051255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 715999250338559894426773 33562464859619995051255)
              ·
                rfl

theorem cell20_661797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_661797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661797 prefixEnd_661797 := by exact prefixLift 661797
  have htrace : WordTrace (prefixWord ++ tailWord_661797) baseStart_661797 baseEnd_661797 := by
    simpa [prefixWord, tailWord_661797, baseEnd_661797] using wordTrace_append hprefix tailTrace_661797
  have hstable : (prefixWord ++ tailWord_661797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661797).length < 2 ^ (prefixWord ++ tailWord_661797).sum := by decide
  have hdescent : baseEnd_661797 < baseStart_661797 := by decide
  rcases family_descends (prefixWord ++ tailWord_661797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661818 : List Nat := [3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_661818 : Nat := 118140960795 + 661818 * 2 ^ 59
def prefixEnd_661818 : Nat := 4983230072969 + 3 ^ 40 * 661818 * 2
def baseEnd_661818 : Nat := 100690589569599071920403

theorem tailTrace_661818 : CollatzResearch.WordTrace tailWord_661818 prefixEnd_661818 100690589569599071920403 := by
  unfold tailWord_661818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034621379088472590192527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16092323677569260240513405 6034621379088472590192527)
  ·
    refine ⟨9051932068632708885288791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6034621379088472590192527 9051932068632708885288791)
    ·
      refine ⟨13577898102949063327933187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051932068632708885288791 13577898102949063327933187)
      ·
        refine ⟨20366847154423594991899781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13577898102949063327933187 20366847154423594991899781)
        ·
          refine ⟨3818783841454424060981209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20366847154423594991899781 3818783841454424060981209)
          ·
            refine ⟨2864087881090818045735907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3818783841454424060981209 2864087881090818045735907)
            ·
              refine ⟨4296131821636227068603861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864087881090818045735907 4296131821636227068603861)
              ·
                refine ⟨100690589569599071920403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4296131821636227068603861 100690589569599071920403)
                ·
                  rfl

theorem cell20_661818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_661818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661818 prefixEnd_661818 := by exact prefixLift 661818
  have htrace : WordTrace (prefixWord ++ tailWord_661818) baseStart_661818 baseEnd_661818 := by
    simpa [prefixWord, tailWord_661818, baseEnd_661818] using wordTrace_append hprefix tailTrace_661818
  have hstable : (prefixWord ++ tailWord_661818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661818).length < 2 ^ (prefixWord ++ tailWord_661818).sum := by decide
  have hdescent : baseEnd_661818 < baseStart_661818 := by decide
  rcases family_descends (prefixWord ++ tailWord_661818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661852 : List Nat := [2, 2, 4, 3, 2, 7]
def baseStart_661852 : Nat := 118140960795 + 661852 * 2 ^ 59
def prefixEnd_661852 : Nat := 4983230072969 + 3 ^ 40 * 661852 * 2
def baseEnd_661852 : Nat := 11188418045749785504731

theorem tailTrace_661852 : CollatzResearch.WordTrace tailWord_661852 prefixEnd_661852 11188418045749785504731 := by
  unfold tailWord_661852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069862799115357083753905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16093150398820476111671873 12069862799115357083753905)
  ·
    refine ⟨9052397099336517812815429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12069862799115357083753905 9052397099336517812815429)
    ·
      refine ⟨1697324456125597089902893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9052397099336517812815429 1697324456125597089902893)
      ·
        refine ⟨636496671047098908713585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1697324456125597089902893 636496671047098908713585)
        ·
          refine ⟨477372503285324181535189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636496671047098908713585 477372503285324181535189)
          ·
            refine ⟨11188418045749785504731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 477372503285324181535189 11188418045749785504731)
            ·
              rfl

theorem cell20_661852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 7].length) (baseStart_661852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661852 prefixEnd_661852 := by exact prefixLift 661852
  have htrace : WordTrace (prefixWord ++ tailWord_661852) baseStart_661852 baseEnd_661852 := by
    simpa [prefixWord, tailWord_661852, baseEnd_661852] using wordTrace_append hprefix tailTrace_661852
  have hstable : (prefixWord ++ tailWord_661852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661852).length < 2 ^ (prefixWord ++ tailWord_661852).sum := by decide
  have hdescent : baseEnd_661852 < baseStart_661852 := by decide
  rcases family_descends (prefixWord ++ tailWord_661852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661854 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_661854 : Nat := 118140960795 + 661854 * 2 ^ 59
def prefixEnd_661854 : Nat := 4983230072969 + 3 ^ 40 * 661854 * 2
def baseEnd_661854 : Nat := 302088200089741090561063

theorem tailTrace_661854 : CollatzResearch.WordTrace tailWord_661854 prefixEnd_661854 302088200089741090561063 := by
  unfold tailWord_661854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3017474818027933563635077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16093199029482312339387077 3017474818027933563635077)
  ·
    refine ⟨565776528380237543181577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3017474818027933563635077 565776528380237543181577)
    ·
      refine ⟨424332396285178157386183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 565776528380237543181577 424332396285178157386183)
      ·
        refine ⟨636498594427767236079275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424332396285178157386183 636498594427767236079275)
        ·
          refine ⟨954747891641650854118913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636498594427767236079275 954747891641650854118913)
          ·
            refine ⟨716060918731238140589185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954747891641650854118913 716060918731238140589185)
            ·
              refine ⟨537045689048428605441889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716060918731238140589185 537045689048428605441889)
              ·
                refine ⟨402784266786321454081417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537045689048428605441889 402784266786321454081417)
                ·
                  refine ⟨302088200089741090561063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402784266786321454081417 302088200089741090561063)
                  ·
                    rfl

theorem cell20_661854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_661854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661854 prefixEnd_661854 := by exact prefixLift 661854
  have htrace : WordTrace (prefixWord ++ tailWord_661854) baseStart_661854 baseEnd_661854 := by
    simpa [prefixWord, tailWord_661854, baseEnd_661854] using wordTrace_append hprefix tailTrace_661854
  have hstable : (prefixWord ++ tailWord_661854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661854).length < 2 ^ (prefixWord ++ tailWord_661854).sum := by decide
  have hdescent : baseEnd_661854 < baseStart_661854 := by decide
  rcases family_descends (prefixWord ++ tailWord_661854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661856 : List Nat := [2, 1, 1, 3, 5, 8]
def baseStart_661856 : Nat := 118140960795 + 661856 * 2 ^ 59
def prefixEnd_661856 : Nat := 4983230072969 + 3 ^ 40 * 661856 * 2
def baseEnd_661856 : Nat := 11188485664601406388681

theorem tailTrace_661856 : CollatzResearch.WordTrace tailWord_661856 prefixEnd_661856 11188485664601406388681 := by
  unfold tailWord_661856
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069935745108111425326711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16093247660144148567102281 12069935745108111425326711)
  ·
    refine ⟨18104903617662167137990067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12069935745108111425326711 18104903617662167137990067)
    ·
      refine ⟨27157355426493250706985101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18104903617662167137990067 27157355426493250706985101)
      ·
        refine ⟨10184008284934969015119413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27157355426493250706985101 10184008284934969015119413)
        ·
          refine ⟨954750776712653345167445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10184008284934969015119413 954750776712653345167445)
          ·
            refine ⟨11188485664601406388681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 954750776712653345167445 11188485664601406388681)
            ·
              rfl

theorem cell20_661856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 8].length) (baseStart_661856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661856 prefixEnd_661856 := by exact prefixLift 661856
  have htrace : WordTrace (prefixWord ++ tailWord_661856) baseStart_661856 baseEnd_661856 := by
    simpa [prefixWord, tailWord_661856, baseEnd_661856] using wordTrace_append hprefix tailTrace_661856
  have hstable : (prefixWord ++ tailWord_661856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661856).length < 2 ^ (prefixWord ++ tailWord_661856).sum := by decide
  have hdescent : baseEnd_661856 < baseStart_661856 := by decide
  rcases family_descends (prefixWord ++ tailWord_661856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661921 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 4]
def baseStart_661921 : Nat := 118140960795 + 661921 * 2 ^ 59
def prefixEnd_661921 : Nat := 4983230072969 + 3 ^ 40 * 661921 * 2
def baseEnd_661921 : Nat := 302118780715386635327455

theorem tailTrace_661921 : CollatzResearch.WordTrace tailWord_661921 prefixEnd_661921 302118780715386635327455 := by
  unfold tailWord_661921
  simp only [CollatzResearch.WordTrace]
  refine ⟨24142242234980738951769617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16094828156653825967846411 24142242234980738951769617)
  ·
    refine ⟨18106681676235554213827213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24142242234980738951769617 18106681676235554213827213)
    ·
      refine ⟨6790005628588332830185205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18106681676235554213827213 6790005628588332830185205)
      ·
        refine ⟨636563027680156202829863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6790005628588332830185205 636563027680156202829863)
        ·
          refine ⟨954844541520234304244795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636563027680156202829863 954844541520234304244795)
          ·
            refine ⟨1432266812280351456367193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954844541520234304244795 1432266812280351456367193)
            ·
              refine ⟨1074200109210263592275395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432266812280351456367193 1074200109210263592275395)
              ·
                refine ⟨1611300163815395388413093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074200109210263592275395 1611300163815395388413093)
                ·
                  refine ⟨302118780715386635327455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611300163815395388413093 302118780715386635327455)
                  ·
                    rfl

theorem cell20_661921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_661921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661921 prefixEnd_661921 := by exact prefixLift 661921
  have htrace : WordTrace (prefixWord ++ tailWord_661921) baseStart_661921 baseEnd_661921 := by
    simpa [prefixWord, tailWord_661921, baseEnd_661921] using wordTrace_append hprefix tailTrace_661921
  have hstable : (prefixWord ++ tailWord_661921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661921).length < 2 ^ (prefixWord ++ tailWord_661921).sum := by decide
  have hdescent : baseEnd_661921 < baseStart_661921 := by decide
  rcases family_descends (prefixWord ++ tailWord_661921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661925 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_661925 : Nat := 118140960795 + 661925 * 2 ^ 59
def prefixEnd_661925 : Nat := 4983230072969 + 3 ^ 40 * 661925 * 2
def baseEnd_661925 : Nat := 302120606424380399194105

theorem tailTrace_661925 : CollatzResearch.WordTrace tailWord_661925 prefixEnd_661925 302120606424380399194105 := by
  unfold tailWord_661925
  simp only [CollatzResearch.WordTrace]
  refine ⟨24142388126966247634915229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16094925417977498423276819 24142388126966247634915229)
  ·
    refine ⟨9053395547612342863093211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24142388126966247634915229 9053395547612342863093211)
    ·
      refine ⟨13580093321418514294639817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9053395547612342863093211 13580093321418514294639817)
      ·
        refine ⟨10185069991063885720979863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13580093321418514294639817 10185069991063885720979863)
        ·
          refine ⟨15277604986595828581469795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10185069991063885720979863 15277604986595828581469795)
          ·
            refine ⟨22916407479893742872204693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15277604986595828581469795 22916407479893742872204693)
            ·
              refine ⟨1074206600620019197134595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22916407479893742872204693 1074206600620019197134595)
              ·
                refine ⟨1611309900930028795701893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074206600620019197134595 1611309900930028795701893)
                ·
                  refine ⟨302120606424380399194105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611309900930028795701893 302120606424380399194105)
                  ·
                    rfl

theorem cell20_661925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_661925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661925 prefixEnd_661925 := by exact prefixLift 661925
  have htrace : WordTrace (prefixWord ++ tailWord_661925) baseStart_661925 baseEnd_661925 := by
    simpa [prefixWord, tailWord_661925, baseEnd_661925] using wordTrace_append hprefix tailTrace_661925
  have hstable : (prefixWord ++ tailWord_661925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661925).length < 2 ^ (prefixWord ++ tailWord_661925).sum := by decide
  have hdescent : baseEnd_661925 < baseStart_661925 := by decide
  rcases family_descends (prefixWord ++ tailWord_661925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661949 : List Nat := [1, 4, 1, 2, 2, 2, 4, 4]
def baseStart_661949 : Nat := 118140960795 + 661949 * 2 ^ 59
def prefixEnd_661949 : Nat := 4983230072969 + 3 ^ 40 * 661949 * 2
def baseEnd_661949 : Nat := 100710520226114327464669

theorem tailTrace_661949 : CollatzResearch.WordTrace tailWord_661949 prefixEnd_661949 100710520226114327464669 := by
  unfold tailWord_661949
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143263478879299733788901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16095508985919533155859267 24143263478879299733788901)
  ·
    refine ⟨4526861902289868700085419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24143263478879299733788901 4526861902289868700085419)
    ·
      refine ⟨6790292853434803050128129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4526861902289868700085419 6790292853434803050128129)
      ·
        refine ⟨5092719640076102287596097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6790292853434803050128129 5092719640076102287596097)
        ·
          refine ⟨3819539730057076715697073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5092719640076102287596097 3819539730057076715697073)
          ·
            refine ⟨2864654797542807536772805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3819539730057076715697073 2864654797542807536772805)
            ·
              refine ⟨537122774539276413144901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2864654797542807536772805 537122774539276413144901)
              ·
                refine ⟨100710520226114327464669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537122774539276413144901 100710520226114327464669)
                ·
                  rfl

theorem cell20_661949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_661949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661949 prefixEnd_661949 := by exact prefixLift 661949
  have htrace : WordTrace (prefixWord ++ tailWord_661949) baseStart_661949 baseEnd_661949 := by
    simpa [prefixWord, tailWord_661949, baseEnd_661949] using wordTrace_append hprefix tailTrace_661949
  have hstable : (prefixWord ++ tailWord_661949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661949).length < 2 ^ (prefixWord ++ tailWord_661949).sum := by decide
  have hdescent : baseEnd_661949 < baseStart_661949 := by decide
  rcases family_descends (prefixWord ++ tailWord_661949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661959 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 2]
def baseStart_661959 : Nat := 118140960795 + 661959 * 2 ^ 59
def prefixEnd_661959 : Nat := 4983230072969 + 3 ^ 40 * 661959 * 2
def baseEnd_661959 : Nat := 302136124950827392060633

theorem tailTrace_661959 : CollatzResearch.WordTrace tailWord_661959 prefixEnd_661959 302136124950827392060633 := by
  unfold tailWord_661959
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143628208843071441652931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16095752139228714294435287 24143628208843071441652931)
  ·
    refine ⟨36215442313264607162479397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24143628208843071441652931 36215442313264607162479397)
    ·
      refine ⟨6790395433737113842964887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36215442313264607162479397 6790395433737113842964887)
      ·
        refine ⟨10185593150605670764447331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790395433737113842964887 10185593150605670764447331)
        ·
          refine ⟨15278389725908506146670997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10185593150605670764447331 15278389725908506146670997)
          ·
            refine ⟨716174518401961225625203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15278389725908506146670997 716174518401961225625203)
            ·
              refine ⟨1074261777602941838437805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716174518401961225625203 1074261777602941838437805)
              ·
                refine ⟨402848166601103189414177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074261777602941838437805 402848166601103189414177)
                ·
                  refine ⟨302136124950827392060633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402848166601103189414177 302136124950827392060633)
                  ·
                    rfl

theorem cell20_661959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 2].length) (baseStart_661959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661959 prefixEnd_661959 := by exact prefixLift 661959
  have htrace : WordTrace (prefixWord ++ tailWord_661959) baseStart_661959 baseEnd_661959 := by
    simpa [prefixWord, tailWord_661959, baseEnd_661959] using wordTrace_append hprefix tailTrace_661959
  have hstable : (prefixWord ++ tailWord_661959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661959).length < 2 ^ (prefixWord ++ tailWord_661959).sum := by decide
  have hdescent : baseEnd_661959 < baseStart_661959 := by decide
  rcases family_descends (prefixWord ++ tailWord_661959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661977 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_661977 : Nat := 118140960795 + 661977 * 2 ^ 59
def prefixEnd_661977 : Nat := 4983230072969 + 3 ^ 40 * 661977 * 2
def baseEnd_661977 : Nat := 302144340641299329460559

theorem tailTrace_661977 : CollatzResearch.WordTrace tailWord_661977 prefixEnd_661977 302144340641299329460559 := by
  unfold tailWord_661977
  simp only [CollatzResearch.WordTrace]
  refine ⟨24144284722777860515808185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16096189815185240343872123 24144284722777860515808185)
  ·
    refine ⟨18108213542083395386856139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24144284722777860515808185 18108213542083395386856139)
    ·
      refine ⟨27162320313125093080284209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18108213542083395386856139 27162320313125093080284209)
      ·
        refine ⟨20371740234843819810213157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27162320313125093080284209 20371740234843819810213157)
        ·
          refine ⟨3819701294033216214414967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20371740234843819810213157 3819701294033216214414967)
          ·
            refine ⟨5729551941049824321622451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819701294033216214414967 5729551941049824321622451)
            ·
              refine ⟨8594327911574736482433677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729551941049824321622451 8594327911574736482433677)
              ·
                refine ⟨3222872966840526180912629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8594327911574736482433677 3222872966840526180912629)
                ·
                  refine ⟨302144340641299329460559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222872966840526180912629 302144340641299329460559)
                  ·
                    rfl

theorem cell20_661977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_661977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661977 prefixEnd_661977 := by exact prefixLift 661977
  have htrace : WordTrace (prefixWord ++ tailWord_661977) baseStart_661977 baseEnd_661977 := by
    simpa [prefixWord, tailWord_661977, baseEnd_661977] using wordTrace_append hprefix tailTrace_661977
  have hstable : (prefixWord ++ tailWord_661977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661977).length < 2 ^ (prefixWord ++ tailWord_661977).sum := by decide
  have hdescent : baseEnd_661977 < baseStart_661977 := by decide
  rcases family_descends (prefixWord ++ tailWord_661977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661986 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_661986 : Nat := 118140960795 + 661986 * 2 ^ 59
def prefixEnd_661986 : Nat := 4983230072969 + 3 ^ 40 * 661986 * 2
def baseEnd_661986 : Nat := 302148448486535298160523

theorem tailTrace_661986 : CollatzResearch.WordTrace tailWord_661986 prefixEnd_661986 302148448486535298160523 := by
  unfold tailWord_661986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036153244936313763221453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16096408653163503368590541 6036153244936313763221453)
  ·
    refine ⟨2263557466851117661208045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6036153244936313763221453 2263557466851117661208045)
    ·
      refine ⟨848834050069169122953017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2263557466851117661208045 848834050069169122953017)
      ·
        refine ⟨636625537551876842214763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848834050069169122953017 636625537551876842214763)
        ·
          refine ⟨954938306327815263322145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636625537551876842214763 954938306327815263322145)
          ·
            refine ⟨716203729745861447491609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954938306327815263322145 716203729745861447491609)
            ·
              refine ⟨537152797309396085618707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716203729745861447491609 537152797309396085618707)
              ·
                refine ⟨805729195964094128428061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537152797309396085618707 805729195964094128428061)
                ·
                  refine ⟨302148448486535298160523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805729195964094128428061 302148448486535298160523)
                  ·
                    rfl

theorem cell20_661986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_661986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661986 prefixEnd_661986 := by exact prefixLift 661986
  have htrace : WordTrace (prefixWord ++ tailWord_661986) baseStart_661986 baseEnd_661986 := by
    simpa [prefixWord, tailWord_661986, baseEnd_661986] using wordTrace_append hprefix tailTrace_661986
  have hstable : (prefixWord ++ tailWord_661986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661986).length < 2 ^ (prefixWord ++ tailWord_661986).sum := by decide
  have hdescent : baseEnd_661986 < baseStart_661986 := by decide
  rcases family_descends (prefixWord ++ tailWord_661986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661987 : List Nat := [1, 1, 1, 6, 3, 1, 2, 5]
def baseStart_661987 : Nat := 118140960795 + 661987 * 2 ^ 59
def prefixEnd_661987 : Nat := 4983230072969 + 3 ^ 40 * 661987 * 2
def baseEnd_661987 : Nat := 100716301637927913042395

theorem tailTrace_661987 : CollatzResearch.WordTrace tailWord_661987 prefixEnd_661987 100716301637927913042395 := by
  unfold tailWord_661987
  simp only [CollatzResearch.WordTrace]
  refine ⟨24144649452741632223672215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16096432968494421482448143 24144649452741632223672215)
  ·
    refine ⟨36216974179112448335508323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24144649452741632223672215 36216974179112448335508323)
    ·
      refine ⟨54325461268668672503262485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36216974179112448335508323 54325461268668672503262485)
      ·
        refine ⟨2546505996968844023590429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54325461268668672503262485 2546505996968844023590429)
        ·
          refine ⟨954939748863316508846411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2546505996968844023590429 954939748863316508846411)
          ·
            refine ⟨1432409623294974763269617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954939748863316508846411 1432409623294974763269617)
            ·
              refine ⟨1074307217471231072452213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432409623294974763269617 1074307217471231072452213)
              ·
                refine ⟨100716301637927913042395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1074307217471231072452213 100716301637927913042395)
                ·
                  rfl

theorem cell20_661987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_661987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661987 prefixEnd_661987 := by exact prefixLift 661987
  have htrace : WordTrace (prefixWord ++ tailWord_661987) baseStart_661987 baseEnd_661987 := by
    simpa [prefixWord, tailWord_661987, baseEnd_661987] using wordTrace_append hprefix tailTrace_661987
  have hstable : (prefixWord ++ tailWord_661987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661987).length < 2 ^ (prefixWord ++ tailWord_661987).sum := by decide
  have hdescent : baseEnd_661987 < baseStart_661987 := by decide
  rcases family_descends (prefixWord ++ tailWord_661987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662056 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_662056 : Nat := 118140960795 + 662056 * 2 ^ 59
def prefixEnd_662056 : Nat := 4983230072969 + 3 ^ 40 * 662056 * 2
def baseEnd_662056 : Nat := 302180398393926165826903

theorem tailTrace_662056 : CollatzResearch.WordTrace tailWord_662056 prefixEnd_662056 302180398393926165826903 := by
  unfold tailWord_662056
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073583044745828503967011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16098110726327771338622681 12073583044745828503967011)
  ·
    refine ⟨18110374567118742755950517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12073583044745828503967011 18110374567118742755950517)
    ·
      refine ⟨1697847615667382133370361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18110374567118742755950517 1697847615667382133370361)
      ·
        refine ⟨1273385711750536600027771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1697847615667382133370361 1273385711750536600027771)
        ·
          refine ⟨1910078567625804900041657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273385711750536600027771 1910078567625804900041657)
          ·
            refine ⟨1432558925719353675031243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910078567625804900041657 1432558925719353675031243)
            ·
              refine ⟨2148838388579030512546865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432558925719353675031243 2148838388579030512546865)
              ·
                refine ⟨1611628791434272884410149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148838388579030512546865 1611628791434272884410149)
                ·
                  refine ⟨302180398393926165826903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611628791434272884410149 302180398393926165826903)
                  ·
                    rfl

theorem cell20_662056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_662056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662056 prefixEnd_662056 := by exact prefixLift 662056
  have htrace : WordTrace (prefixWord ++ tailWord_662056) baseStart_662056 baseEnd_662056 := by
    simpa [prefixWord, tailWord_662056, baseEnd_662056] using wordTrace_append hprefix tailTrace_662056
  have hstable : (prefixWord ++ tailWord_662056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662056).length < 2 ^ (prefixWord ++ tailWord_662056).sum := by decide
  have hdescent : baseEnd_662056 < baseStart_662056 := by decide
  rcases family_descends (prefixWord ++ tailWord_662056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662087 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 3]
def baseStart_662087 : Nat := 118140960795 + 662087 * 2 ^ 59
def prefixEnd_662087 : Nat := 4983230072969 + 3 ^ 40 * 662087 * 2
def baseEnd_662087 : Nat := 302194547638627835793443

theorem tailTrace_662087 : CollatzResearch.WordTrace tailWord_662087 prefixEnd_662087 302194547638627835793443 := by
  unfold tailWord_662087
  simp only [CollatzResearch.WordTrace]
  refine ⟨24148296752379349302312515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16098864501586232868208343 24148296752379349302312515)
  ·
    refine ⟨36222445128569023953468773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24148296752379349302312515 36222445128569023953468773)
    ·
      refine ⟨6791708461606691991275395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36222445128569023953468773 6791708461606691991275395)
      ·
        refine ⟨10187562692410037986913093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791708461606691991275395 10187562692410037986913093)
        ·
          refine ⟨1910168004826882122546205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10187562692410037986913093 1910168004826882122546205)
          ·
            refine ⟨716313001810080795954827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1910168004826882122546205 716313001810080795954827)
            ·
              refine ⟨1074469502715121193932241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716313001810080795954827 1074469502715121193932241)
              ·
                refine ⟨805852127036340895449181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074469502715121193932241 805852127036340895449181)
                ·
                  refine ⟨302194547638627835793443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805852127036340895449181 302194547638627835793443)
                  ·
                    rfl

theorem cell20_662087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_662087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662087 prefixEnd_662087 := by exact prefixLift 662087
  have htrace : WordTrace (prefixWord ++ tailWord_662087) baseStart_662087 baseEnd_662087 := by
    simpa [prefixWord, tailWord_662087, baseEnd_662087] using wordTrace_append hprefix tailTrace_662087
  have hstable : (prefixWord ++ tailWord_662087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662087).length < 2 ^ (prefixWord ++ tailWord_662087).sum := by decide
  have hdescent : baseEnd_662087 < baseStart_662087 := by decide
  rcases family_descends (prefixWord ++ tailWord_662087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662094 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_662094 : Nat := 118140960795 + 662094 * 2 ^ 59
def prefixEnd_662094 : Nat := 4983230072969 + 3 ^ 40 * 662094 * 2
def baseEnd_662094 : Nat := 302197742629366922560081

theorem tailTrace_662094 : CollatzResearch.WordTrace tailWord_662094 prefixEnd_662094 302197742629366922560081 := by
  unfold tailWord_662094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018569007919248687227167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16099034708902659665211557 3018569007919248687227167)
  ·
    refine ⟨4527853511878873030840751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018569007919248687227167 4527853511878873030840751)
    ·
      refine ⟨6791780267818309546261127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527853511878873030840751 6791780267818309546261127)
      ·
        refine ⟨10187670401727464319391691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791780267818309546261127 10187670401727464319391691)
        ·
          refine ⟨15281505602591196479087537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10187670401727464319391691 15281505602591196479087537)
          ·
            refine ⟨11461129201943397359315653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15281505602591196479087537 11461129201943397359315653)
            ·
              refine ⟨2148961725364387004871685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11461129201943397359315653 2148961725364387004871685)
              ·
                refine ⟨402930323505822563413441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2148961725364387004871685 402930323505822563413441)
                ·
                  refine ⟨302197742629366922560081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402930323505822563413441 302197742629366922560081)
                  ·
                    rfl

theorem cell20_662094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_662094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662094 prefixEnd_662094 := by exact prefixLift 662094
  have htrace : WordTrace (prefixWord ++ tailWord_662094) baseStart_662094 baseEnd_662094 := by
    simpa [prefixWord, tailWord_662094, baseEnd_662094] using wordTrace_append hprefix tailTrace_662094
  have hstable : (prefixWord ++ tailWord_662094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662094).length < 2 ^ (prefixWord ++ tailWord_662094).sum := by decide
  have hdescent : baseEnd_662094 < baseStart_662094 := by decide
  rcases family_descends (prefixWord ++ tailWord_662094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662114 : List Nat := [3, 3, 2, 3, 2, 1, 2, 4]
def baseStart_662114 : Nat := 118140960795 + 662114 * 2 ^ 59
def prefixEnd_662114 : Nat := 4983230072969 + 3 ^ 40 * 662114 * 2
def baseEnd_662114 : Nat := 100735623724778580631111

theorem tailTrace_662114 : CollatzResearch.WordTrace tailWord_662114 prefixEnd_662114 100735623724778580631111 := by
  unfold tailWord_662114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037320380820383228386349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16099521015521021942363597 6037320380820383228386349)
  ·
    refine ⟨2263995142807643710644881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6037320380820383228386349 2263995142807643710644881)
    ·
      refine ⟨1697996357105732782983661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2263995142807643710644881 1697996357105732782983661)
      ·
        refine ⟨636748633914649793618873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1697996357105732782983661 636748633914649793618873)
        ·
          refine ⟨477561475435987345214155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636748633914649793618873 477561475435987345214155)
          ·
            refine ⟨716342213153981017821233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477561475435987345214155 716342213153981017821233)
            ·
              refine ⟨537256659865485763365925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716342213153981017821233 537256659865485763365925)
              ·
                refine ⟨100735623724778580631111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537256659865485763365925 100735623724778580631111)
                ·
                  rfl

theorem cell20_662114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_662114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662114 prefixEnd_662114 := by exact prefixLift 662114
  have htrace : WordTrace (prefixWord ++ tailWord_662114) baseStart_662114 baseEnd_662114 := by
    simpa [prefixWord, tailWord_662114, baseEnd_662114] using wordTrace_append hprefix tailTrace_662114
  have hstable : (prefixWord ++ tailWord_662114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662114).length < 2 ^ (prefixWord ++ tailWord_662114).sum := by decide
  have hdescent : baseEnd_662114 < baseStart_662114 := by decide
  rcases family_descends (prefixWord ++ tailWord_662114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662122 : List Nat := [3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_662122 : Nat := 118140960795 + 662122 * 2 ^ 59
def prefixEnd_662122 : Nat := 4983230072969 + 3 ^ 40 * 662122 * 2
def baseEnd_662122 : Nat := 100736840864107756542211

theorem tailTrace_662122 : CollatzResearch.WordTrace tailWord_662122 prefixEnd_662122 100736840864107756542211 := by
  unfold tailWord_662122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037393326813137569959155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16099715538168366853224413 6037393326813137569959155)
  ·
    refine ⟨9056089990219706354938733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6037393326813137569959155 9056089990219706354938733)
    ·
      refine ⟨3396033746332389883102025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9056089990219706354938733 3396033746332389883102025)
      ·
        refine ⟨2547025309749292412326519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3396033746332389883102025 2547025309749292412326519)
        ·
          refine ⟨3820537964623938618489779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547025309749292412326519 3820537964623938618489779)
          ·
            refine ⟨5730806946935907927734669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820537964623938618489779 5730806946935907927734669)
            ·
              refine ⟨2149052605100965472900501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5730806946935907927734669 2149052605100965472900501)
              ·
                refine ⟨100736840864107756542211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2149052605100965472900501 100736840864107756542211)
                ·
                  rfl

theorem cell20_662122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_662122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662122 prefixEnd_662122 := by exact prefixLift 662122
  have htrace : WordTrace (prefixWord ++ tailWord_662122) baseStart_662122 baseEnd_662122 := by
    simpa [prefixWord, tailWord_662122, baseEnd_662122] using wordTrace_append hprefix tailTrace_662122
  have hstable : (prefixWord ++ tailWord_662122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662122).length < 2 ^ (prefixWord ++ tailWord_662122).sum := by decide
  have hdescent : baseEnd_662122 < baseStart_662122 := by decide
  rcases family_descends (prefixWord ++ tailWord_662122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662128 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 2]
def baseStart_662128 : Nat := 118140960795 + 662128 * 2 ^ 59
def prefixEnd_662128 : Nat := 4983230072969 + 3 ^ 40 * 662128 * 2
def baseEnd_662128 : Nat := 302213261155813915426609

theorem tailTrace_662128 : CollatzResearch.WordTrace tailWord_662128 prefixEnd_662128 302213261155813915426609 := by
  unfold tailWord_662128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12074896072615406652277519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16099861430153875536370025 12074896072615406652277519)
  ·
    refine ⟨18112344108923109978416279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12074896072615406652277519 18112344108923109978416279)
    ·
      refine ⟨27168516163384664967624419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18112344108923109978416279 27168516163384664967624419)
      ·
        refine ⟨40752774245076997451436629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27168516163384664967624419 40752774245076997451436629)
        ·
          refine ⟨477571573184496063884023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 40752774245076997451436629 477571573184496063884023)
          ·
            refine ⟨716357359776744095826035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477571573184496063884023 716357359776744095826035)
            ·
              refine ⟨1074536039665116143739053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716357359776744095826035 1074536039665116143739053)
              ·
                refine ⟨402951014874418553902145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074536039665116143739053 402951014874418553902145)
                ·
                  refine ⟨302213261155813915426609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402951014874418553902145 302213261155813915426609)
                  ·
                    rfl

theorem cell20_662128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_662128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662128 prefixEnd_662128 := by exact prefixLift 662128
  have htrace : WordTrace (prefixWord ++ tailWord_662128) baseStart_662128 baseEnd_662128 := by
    simpa [prefixWord, tailWord_662128, baseEnd_662128] using wordTrace_append hprefix tailTrace_662128
  have hstable : (prefixWord ++ tailWord_662128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662128).length < 2 ^ (prefixWord ++ tailWord_662128).sum := by decide
  have hdescent : baseEnd_662128 < baseStart_662128 := by decide
  rcases family_descends (prefixWord ++ tailWord_662128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662149 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 2]
def baseStart_662149 : Nat := 118140960795 + 662149 * 2 ^ 59
def prefixEnd_662149 : Nat := 4983230072969 + 3 ^ 40 * 662149 * 2
def baseEnd_662149 : Nat := 302222846128031175726523

theorem tailTrace_662149 : CollatzResearch.WordTrace tailWord_662149 prefixEnd_662149 302222846128031175726523 := by
  unfold tailWord_662149
  simp only [CollatzResearch.WordTrace]
  refine ⟨24150558078154733891069501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16100372052103155927379667 24150558078154733891069501)
  ·
    refine ⟨9056459279308025209151063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24150558078154733891069501 9056459279308025209151063)
    ·
      refine ⟨13584688918962037813726595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9056459279308025209151063 13584688918962037813726595)
      ·
        refine ⟨20377033378443056720589893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13584688918962037813726595 20377033378443056720589893)
        ·
          refine ⟨3820693758458073135110605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20377033378443056720589893 3820693758458073135110605)
          ·
            refine ⟨1432760159421777425666477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3820693758458073135110605 1432760159421777425666477)
            ·
              refine ⟨537285059783166534624929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1432760159421777425666477 537285059783166534624929)
              ·
                refine ⟨402963794837374900968697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537285059783166534624929 402963794837374900968697)
                ·
                  refine ⟨302222846128031175726523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402963794837374900968697 302222846128031175726523)
                  ·
                    rfl

theorem cell20_662149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_662149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662149 prefixEnd_662149 := by exact prefixLift 662149
  have htrace : WordTrace (prefixWord ++ tailWord_662149) baseStart_662149 baseEnd_662149 := by
    simpa [prefixWord, tailWord_662149, baseEnd_662149] using wordTrace_append hprefix tailTrace_662149
  have hstable : (prefixWord ++ tailWord_662149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662149).length < 2 ^ (prefixWord ++ tailWord_662149).sum := by decide
  have hdescent : baseEnd_662149 < baseStart_662149 := by decide
  rcases family_descends (prefixWord ++ tailWord_662149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662208 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 2]
def baseStart_662208 : Nat := 118140960795 + 662208 * 2 ^ 59
def prefixEnd_662208 : Nat := 4983230072969 + 3 ^ 40 * 662208 * 2
def baseEnd_662208 : Nat := 302249775335689192759615

theorem tailTrace_662208 : CollatzResearch.WordTrace tailWord_662208 prefixEnd_662208 302249775335689192759615 := by
  unfold tailWord_662208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076354992470493483733639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16101806656627324644978185 12076354992470493483733639)
  ·
    refine ⟨18114532488705740225600459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12076354992470493483733639 18114532488705740225600459)
    ·
      refine ⟨27171798733058610338400689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18114532488705740225600459 27171798733058610338400689)
      ·
        refine ⟨20378849049793957753800517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27171798733058610338400689 20378849049793957753800517)
        ·
          refine ⟨3821034196836367078837597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20378849049793957753800517 3821034196836367078837597)
          ·
            refine ⟨1432887823813637654564099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3821034196836367078837597 1432887823813637654564099)
            ·
              refine ⟨2149331735720456481846149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432887823813637654564099 2149331735720456481846149)
              ·
                refine ⟨402999700447585590346153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2149331735720456481846149 402999700447585590346153)
                ·
                  refine ⟨302249775335689192759615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402999700447585590346153 302249775335689192759615)
                  ·
                    rfl

theorem cell20_662208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_662208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662208 prefixEnd_662208 := by exact prefixLift 662208
  have htrace : WordTrace (prefixWord ++ tailWord_662208) baseStart_662208 baseEnd_662208 := by
    simpa [prefixWord, tailWord_662208, baseEnd_662208] using wordTrace_append hprefix tailTrace_662208
  have hstable : (prefixWord ++ tailWord_662208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662208).length < 2 ^ (prefixWord ++ tailWord_662208).sum := by decide
  have hdescent : baseEnd_662208 < baseStart_662208 := by decide
  rcases family_descends (prefixWord ++ tailWord_662208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662222 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_662222 : Nat := 118140960795 + 662222 * 2 ^ 59
def prefixEnd_662222 : Nat := 4983230072969 + 3 ^ 40 * 662222 * 2
def baseEnd_662222 : Nat := 302256165317167366292891

theorem tailTrace_662222 : CollatzResearch.WordTrace tailWord_662222 prefixEnd_662222 302256165317167366292891 := by
  unfold tailWord_662222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3019152575861283419809615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16102147071260178238984613 3019152575861283419809615)
  ·
    refine ⟨4528728863791925129714423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3019152575861283419809615 4528728863791925129714423)
    ·
      refine ⟨6793093295687887694571635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4528728863791925129714423 6793093295687887694571635)
      ·
        refine ⟨10189639943531831541857453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6793093295687887694571635 10189639943531831541857453)
        ·
          refine ⟨3821114978824436828196545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10189639943531831541857453 3821114978824436828196545)
          ·
            refine ⟨2865836234118327621147409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821114978824436828196545 2865836234118327621147409)
            ·
              refine ⟨2149377175588745715860557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2865836234118327621147409 2149377175588745715860557)
              ·
                refine ⟨806016440845779643447709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149377175588745715860557 806016440845779643447709)
                ·
                  refine ⟨302256165317167366292891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806016440845779643447709 302256165317167366292891)
                  ·
                    rfl

theorem cell20_662222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_662222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662222 prefixEnd_662222 := by exact prefixLift 662222
  have htrace : WordTrace (prefixWord ++ tailWord_662222) baseStart_662222 baseEnd_662222 := by
    simpa [prefixWord, tailWord_662222, baseEnd_662222] using wordTrace_append hprefix tailTrace_662222
  have hstable : (prefixWord ++ tailWord_662222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662222).length < 2 ^ (prefixWord ++ tailWord_662222).sum := by decide
  have hdescent : baseEnd_662222 < baseStart_662222 := by decide
  rcases family_descends (prefixWord ++ tailWord_662222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662250 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_662250 : Nat := 118140960795 + 662250 * 2 ^ 59
def prefixEnd_662250 : Nat := 4983230072969 + 3 ^ 40 * 662250 * 2
def baseEnd_662250 : Nat := 302268945280123713359443

theorem tailTrace_662250 : CollatzResearch.WordTrace tailWord_662250 prefixEnd_662250 302268945280123713359443 := by
  unfold tailWord_662250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038560462697207035124051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16102827900525885426997469 6038560462697207035124051)
  ·
    refine ⟨9057840694045810552686077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6038560462697207035124051 9057840694045810552686077)
    ·
      refine ⟨3396690260267178957257279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9057840694045810552686077 3396690260267178957257279)
      ·
        refine ⟨5095035390400768435885919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3396690260267178957257279 5095035390400768435885919)
        ·
          refine ⟨7642553085601152653828879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095035390400768435885919 7642553085601152653828879)
          ·
            refine ⟨11463829628401728980743319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7642553085601152653828879 11463829628401728980743319)
            ·
              refine ⟨17195744442602593471114979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11463829628401728980743319 17195744442602593471114979)
              ·
                refine ⟨25793616663903890206672469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17195744442602593471114979 25793616663903890206672469)
                ·
                  refine ⟨302268945280123713359443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25793616663903890206672469 302268945280123713359443)
                  ·
                    rfl

theorem cell20_662250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_662250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662250 prefixEnd_662250 := by exact prefixLift 662250
  have htrace : WordTrace (prefixWord ++ tailWord_662250) baseStart_662250 baseEnd_662250 := by
    simpa [prefixWord, tailWord_662250, baseEnd_662250] using wordTrace_append hprefix tailTrace_662250
  have hstable : (prefixWord ++ tailWord_662250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662250).length < 2 ^ (prefixWord ++ tailWord_662250).sum := by decide
  have hdescent : baseEnd_662250 < baseStart_662250 := by decide
  rcases family_descends (prefixWord ++ tailWord_662250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662257 : List Nat := [1, 2, 2, 2, 2, 2, 9]
def baseStart_662257 : Nat := 118140960795 + 662257 * 2 ^ 59
def prefixEnd_662257 : Nat := 4983230072969 + 3 ^ 40 * 662257 * 2
def baseEnd_662257 : Nat := 33585793363429200014009

theorem tailTrace_662257 : CollatzResearch.WordTrace tailWord_662257 prefixEnd_662257 33585793363429200014009 := by
  unfold tailWord_662257
  simp only [CollatzResearch.WordTrace]
  refine ⟨24154497161763468336001025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16102998107842312224000683 24154497161763468336001025)
  ·
    refine ⟨18115872871322601252000769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24154497161763468336001025 18115872871322601252000769)
    ·
      refine ⟨13586904653491950939000577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18115872871322601252000769 13586904653491950939000577)
      ·
        refine ⟨10190178490118963204250433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13586904653491950939000577 10190178490118963204250433)
        ·
          refine ⟨7642633867589222403187825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10190178490118963204250433 7642633867589222403187825)
          ·
            refine ⟨5731975400691916802390869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7642633867589222403187825 5731975400691916802390869)
            ·
              refine ⟨33585793363429200014009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5731975400691916802390869 33585793363429200014009)
              ·
                rfl

theorem cell20_662257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_662257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662257 prefixEnd_662257 := by exact prefixLift 662257
  have htrace : WordTrace (prefixWord ++ tailWord_662257) baseStart_662257 baseEnd_662257 := by
    simpa [prefixWord, tailWord_662257, baseEnd_662257] using wordTrace_append hprefix tailTrace_662257
  have hstable : (prefixWord ++ tailWord_662257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662257).length < 2 ^ (prefixWord ++ tailWord_662257).sum := by decide
  have hdescent : baseEnd_662257 < baseStart_662257 := by decide
  rcases family_descends (prefixWord ++ tailWord_662257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662281 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_662281 : Nat := 118140960795 + 662281 * 2 ^ 59
def prefixEnd_662281 : Nat := 4983230072969 + 3 ^ 40 * 662281 * 2
def baseEnd_662281 : Nat := 302283094524825383325983

theorem tailTrace_662281 : CollatzResearch.WordTrace tailWord_662281 prefixEnd_662281 302283094524825383325983 := by
  unfold tailWord_662281
  simp only [CollatzResearch.WordTrace]
  refine ⟨24155372513676520434874697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16103581675784346956583131 24155372513676520434874697)
  ·
    refine ⟨18116529385257390326156023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24155372513676520434874697 18116529385257390326156023)
    ·
      refine ⟨27174794077886085489234035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18116529385257390326156023 27174794077886085489234035)
      ·
        refine ⟨40762191116829128233851053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27174794077886085489234035 40762191116829128233851053)
        ·
          refine ⟨15285821668810923087694145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40762191116829128233851053 15285821668810923087694145)
          ·
            refine ⟨11464366251608192315770609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15285821668810923087694145 11464366251608192315770609)
            ·
              refine ⟨8598274688706144236827957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11464366251608192315770609 8598274688706144236827957)
              ·
                refine ⟨806088252066201022202621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8598274688706144236827957 806088252066201022202621)
                ·
                  refine ⟨302283094524825383325983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806088252066201022202621 302283094524825383325983)
                  ·
                    rfl

theorem cell20_662281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_662281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662281 prefixEnd_662281 := by exact prefixLift 662281
  have htrace : WordTrace (prefixWord ++ tailWord_662281) baseStart_662281 baseEnd_662281 := by
    simpa [prefixWord, tailWord_662281, baseEnd_662281] using wordTrace_append hprefix tailTrace_662281
  have hstable : (prefixWord ++ tailWord_662281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662281).length < 2 ^ (prefixWord ++ tailWord_662281).sum := by decide
  have hdescent : baseEnd_662281 < baseStart_662281 := by decide
  rcases family_descends (prefixWord ++ tailWord_662281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662318 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_662318 : Nat := 118140960795 + 662318 * 2 ^ 59
def prefixEnd_662318 : Nat := 4983230072969 + 3 ^ 40 * 662318 * 2
def baseEnd_662318 : Nat := 302299982333017699092499

theorem tailTrace_662318 : CollatzResearch.WordTrace tailWord_662318 prefixEnd_662318 302299982333017699092499 := by
  unfold tailWord_662318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3019590251817809469246451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16104481343028317169314405 3019590251817809469246451)
  ·
    refine ⟨4529385377726714203869677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3019590251817809469246451 4529385377726714203869677)
    ·
      refine ⟨1698519516647517826451129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4529385377726714203869677 1698519516647517826451129)
      ·
        refine ⟨1273889637485638369838347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1698519516647517826451129 1273889637485638369838347)
        ·
          refine ⟨1910834456228457554757521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273889637485638369838347 1910834456228457554757521)
          ·
            refine ⟨1433125842171343166068141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910834456228457554757521 1433125842171343166068141)
            ·
              refine ⟨537422190814253687275553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1433125842171343166068141 537422190814253687275553)
              ·
                refine ⟨403066643110690265456665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537422190814253687275553 403066643110690265456665)
                ·
                  refine ⟨302299982333017699092499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403066643110690265456665 302299982333017699092499)
                  ·
                    rfl

theorem cell20_662318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_662318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662318 prefixEnd_662318 := by exact prefixLift 662318
  have htrace : WordTrace (prefixWord ++ tailWord_662318) baseStart_662318 baseEnd_662318 := by
    simpa [prefixWord, tailWord_662318, baseEnd_662318] using wordTrace_append hprefix tailTrace_662318
  have hstable : (prefixWord ++ tailWord_662318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662318).length < 2 ^ (prefixWord ++ tailWord_662318).sum := by decide
  have hdescent : baseEnd_662318 < baseStart_662318 := by decide
  rcases family_descends (prefixWord ++ tailWord_662318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662371 : List Nat := [1, 1, 1, 5, 3, 9]
def baseStart_662371 : Nat := 118140960795 + 662371 * 2 ^ 59
def prefixEnd_662371 : Nat := 4983230072969 + 3 ^ 40 * 662371 * 2
def baseEnd_662371 : Nat := 11197191591747595197245

theorem tailTrace_662371 : CollatzResearch.WordTrace tailWord_662371 prefixEnd_662371 11197191591747595197245 := by
  unfold tailWord_662371
  simp only [CollatzResearch.WordTrace]
  refine ⟨24158655083350465805650967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16105770055566977203767311 24158655083350465805650967)
  ·
    refine ⟨36237982625025698708476451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24158655083350465805650967 36237982625025698708476451)
    ·
      refine ⟨54356973937538548062714677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36237982625025698708476451 54356973937538548062714677)
      ·
        refine ⟨5095966306644238880879501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54356973937538548062714677 5095966306644238880879501)
        ·
          refine ⟨1910987364991589580329813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5095966306644238880879501 1910987364991589580329813)
          ·
            refine ⟨11197191591747595197245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1910987364991589580329813 11197191591747595197245)
            ·
              rfl

theorem cell20_662371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 9].length) (baseStart_662371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662371 prefixEnd_662371 := by exact prefixLift 662371
  have htrace : WordTrace (prefixWord ++ tailWord_662371) baseStart_662371 baseEnd_662371 := by
    simpa [prefixWord, tailWord_662371, baseEnd_662371] using wordTrace_append hprefix tailTrace_662371
  have hstable : (prefixWord ++ tailWord_662371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662371).length < 2 ^ (prefixWord ++ tailWord_662371).sum := by decide
  have hdescent : baseEnd_662371 < baseStart_662371 := by decide
  rcases family_descends (prefixWord ++ tailWord_662371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662395 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_662395 : Nat := 118140960795 + 662395 * 2 ^ 59
def prefixEnd_662395 : Nat := 4983230072969 + 3 ^ 40 * 662395 * 2
def baseEnd_662395 : Nat := 302335127231147653525517

theorem tailTrace_662395 : CollatzResearch.WordTrace tailWord_662395 prefixEnd_662395 302335127231147653525517 := by
  unfold tailWord_662395
  simp only [CollatzResearch.WordTrace]
  refine ⟨24159530435263517904524639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16106353623509011936349759 24159530435263517904524639)
  ·
    refine ⟨36239295652895276856786959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24159530435263517904524639 36239295652895276856786959)
    ·
      refine ⟨54358943479342915285180439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36239295652895276856786959 54358943479342915285180439)
      ·
        refine ⟨81538415219014372927770659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54358943479342915285180439 81538415219014372927770659)
        ·
          refine ⟨122307622828521559391655989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81538415219014372927770659 122307622828521559391655989)
          ·
            refine ⟨11466339640173896192967749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122307622828521559391655989 11466339640173896192967749)
            ·
              refine ⟨2149938682532605536181453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11466339640173896192967749 2149938682532605536181453)
              ·
                refine ⟨806227005949727076068045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149938682532605536181453 806227005949727076068045)
                ·
                  refine ⟨302335127231147653525517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806227005949727076068045 302335127231147653525517)
                  ·
                    rfl

theorem cell20_662395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_662395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662395 prefixEnd_662395 := by exact prefixLift 662395
  have htrace : WordTrace (prefixWord ++ tailWord_662395) baseStart_662395 baseEnd_662395 := by
    simpa [prefixWord, tailWord_662395, baseEnd_662395] using wordTrace_append hprefix tailTrace_662395
  have hstable : (prefixWord ++ tailWord_662395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662395).length < 2 ^ (prefixWord ++ tailWord_662395).sum := by decide
  have hdescent : baseEnd_662395 < baseStart_662395 := by decide
  rcases family_descends (prefixWord ++ tailWord_662395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662422 : List Nat := [5, 3, 1, 1, 1, 2, 7]
def baseStart_662422 : Nat := 118140960795 + 662422 * 2 ^ 59
def prefixEnd_662422 : Nat := 4983230072969 + 3 ^ 40 * 662422 * 2
def baseEnd_662422 : Nat := 33594161196317284402823

theorem tailTrace_662422 : CollatzResearch.WordTrace tailWord_662422 prefixEnd_662422 33594161196317284402823 := by
  unfold tailWord_662422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510032200385356344734845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16107010137443801010505013 1510032200385356344734845)
  ·
    refine ⟨566262075144508629275567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1510032200385356344734845 566262075144508629275567)
    ·
      refine ⟨849393112716762943913351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566262075144508629275567 849393112716762943913351)
      ·
        refine ⟨1274089669075144415870027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849393112716762943913351 1274089669075144415870027)
        ·
          refine ⟨1911134503612716623805041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274089669075144415870027 1911134503612716623805041)
          ·
            refine ⟨1433350877709537467853781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911134503612716623805041 1433350877709537467853781)
            ·
              refine ⟨33594161196317284402823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1433350877709537467853781 33594161196317284402823)
              ·
                rfl

theorem cell20_662422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 7].length) (baseStart_662422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662422 prefixEnd_662422 := by exact prefixLift 662422
  have htrace : WordTrace (prefixWord ++ tailWord_662422) baseStart_662422 baseEnd_662422 := by
    simpa [prefixWord, tailWord_662422, baseEnd_662422] using wordTrace_append hprefix tailTrace_662422
  have hstable : (prefixWord ++ tailWord_662422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662422).length < 2 ^ (prefixWord ++ tailWord_662422).sum := by decide
  have hdescent : baseEnd_662422 < baseStart_662422 := by decide
  rcases family_descends (prefixWord ++ tailWord_662422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662426 : List Nat := [3, 1, 1, 4, 3, 1, 7]
def baseStart_662426 : Nat := 118140960795 + 662426 * 2 ^ 59
def prefixEnd_662426 : Nat := 4983230072969 + 3 ^ 40 * 662426 * 2
def baseEnd_662426 : Nat := 33594364052872147054673

theorem tailTrace_662426 : CollatzResearch.WordTrace tailWord_662426 prefixEnd_662426 33594364052872147054673 := by
  unfold tailWord_662426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6040165274537802549725783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16107107398767473465935421 6040165274537802549725783)
  ·
    refine ⟨9060247911806703824588675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6040165274537802549725783 9060247911806703824588675)
    ·
      refine ⟨13590371867710055736883013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9060247911806703824588675 13590371867710055736883013)
      ·
        refine ⟨2548194725195635450665565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13590371867710055736883013 2548194725195635450665565)
        ·
          refine ⟨955573021948363293999587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2548194725195635450665565 955573021948363293999587)
          ·
            refine ⟨1433359532922544940999381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955573021948363293999587 1433359532922544940999381)
            ·
              refine ⟨33594364052872147054673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1433359532922544940999381 33594364052872147054673)
              ·
                rfl

theorem cell20_662426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 7].length) (baseStart_662426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662426 prefixEnd_662426 := by exact prefixLift 662426
  have htrace : WordTrace (prefixWord ++ tailWord_662426) baseStart_662426 baseEnd_662426 := by
    simpa [prefixWord, tailWord_662426, baseEnd_662426] using wordTrace_append hprefix tailTrace_662426
  have hstable : (prefixWord ++ tailWord_662426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662426).length < 2 ^ (prefixWord ++ tailWord_662426).sum := by decide
  have hdescent : baseEnd_662426 < baseStart_662426 := by decide
  rcases family_descends (prefixWord ++ tailWord_662426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662464 : List Nat := [2, 1, 1, 2, 3, 3, 4, 4]
def baseStart_662464 : Nat := 118140960795 + 662464 * 2 ^ 59
def prefixEnd_662464 : Nat := 4983230072969 + 3 ^ 40 * 662464 * 2
def baseEnd_662464 : Nat := 100788873570430026741745

theorem tailTrace_662464 : CollatzResearch.WordTrace tailWord_662464 prefixEnd_662464 100788873570430026741745 := by
  unfold tailWord_662464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081023536006771344393223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16108031381342361792524297 12081023536006771344393223)
  ·
    refine ⟨18121535304010157016589835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081023536006771344393223 18121535304010157016589835)
    ·
      refine ⟨27182302956015235524884753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18121535304010157016589835 27182302956015235524884753)
      ·
        refine ⟨20386727217011426643663565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27182302956015235524884753 20386727217011426643663565)
        ·
          refine ⟨7645022706379284991373837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20386727217011426643663565 7645022706379284991373837)
          ·
            refine ⟨2866883514892231871765189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7645022706379284991373837 2866883514892231871765189)
            ·
              refine ⟨537540659042293475955973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2866883514892231871765189 537540659042293475955973)
              ·
                refine ⟨100788873570430026741745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537540659042293475955973 100788873570430026741745)
                ·
                  rfl

theorem cell20_662464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_662464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662464 prefixEnd_662464 := by exact prefixLift 662464
  have htrace : WordTrace (prefixWord ++ tailWord_662464) baseStart_662464 baseEnd_662464 := by
    simpa [prefixWord, tailWord_662464, baseEnd_662464] using wordTrace_append hprefix tailTrace_662464
  have hstable : (prefixWord ++ tailWord_662464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662464).length < 2 ^ (prefixWord ++ tailWord_662464).sum := by decide
  have hdescent : baseEnd_662464 < baseStart_662464 := by decide
  rcases family_descends (prefixWord ++ tailWord_662464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662477 : List Nat := [1, 6, 3, 1, 1, 2, 6]
def baseStart_662477 : Nat := 118140960795 + 662477 * 2 ^ 59
def prefixEnd_662477 : Nat := 4983230072969 + 3 ^ 40 * 662477 * 2
def baseEnd_662477 : Nat := 33596950473946645865761

theorem tailTrace_662477 : CollatzResearch.WordTrace tailWord_662477 prefixEnd_662477 33596950473946645865761 := by
  unfold tailWord_662477
  simp only [CollatzResearch.WordTrace]
  refine ⟨24162521220966445909009685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16108347480644297272673123 24162521220966445909009685)
  ·
    refine ⟨1132618182232802151984829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24162521220966445909009685 1132618182232802151984829)
    ·
      refine ⟨424731818337300806994311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1132618182232802151984829 424731818337300806994311)
      ·
        refine ⟨637097727505951210491467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424731818337300806994311 637097727505951210491467)
        ·
          refine ⟨955646591258926815737201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637097727505951210491467 955646591258926815737201)
          ·
            refine ⟨716734943444195111802901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955646591258926815737201 716734943444195111802901)
            ·
              refine ⟨33596950473946645865761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 716734943444195111802901 33596950473946645865761)
              ·
                rfl

theorem cell20_662477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 6].length) (baseStart_662477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662477 prefixEnd_662477 := by exact prefixLift 662477
  have htrace : WordTrace (prefixWord ++ tailWord_662477) baseStart_662477 baseEnd_662477 := by
    simpa [prefixWord, tailWord_662477, baseEnd_662477] using wordTrace_append hprefix tailTrace_662477
  have hstable : (prefixWord ++ tailWord_662477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662477).length < 2 ^ (prefixWord ++ tailWord_662477).sum := by decide
  have hdescent : baseEnd_662477 < baseStart_662477 := by decide
  rcases family_descends (prefixWord ++ tailWord_662477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662501 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 3]
def baseStart_662501 : Nat := 118140960795 + 662501 * 2 ^ 59
def prefixEnd_662501 : Nat := 4983230072969 + 3 ^ 40 * 662501 * 2
def baseEnd_662501 : Nat := 302383508519482395991751

theorem tailTrace_662501 : CollatzResearch.WordTrace tailWord_662501 prefixEnd_662501 302383508519482395991751 := by
  unfold tailWord_662501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24163396572879498007883357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16108931048586332005255571 24163396572879498007883357)
  ·
    refine ⟨9061273714829811752956259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24163396572879498007883357 9061273714829811752956259)
    ·
      refine ⟨13591910572244717629434389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9061273714829811752956259 13591910572244717629434389)
      ·
        refine ⟨637120808073971138879737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13591910572244717629434389 637120808073971138879737)
        ·
          refine ⟨477840606055478354159803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637120808073971138879737 477840606055478354159803)
          ·
            refine ⟨716760909083217531239705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477840606055478354159803 716760909083217531239705)
            ·
              refine ⟨537570681812413148429779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716760909083217531239705 537570681812413148429779)
              ·
                refine ⟨806356022718619722644669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537570681812413148429779 806356022718619722644669)
                ·
                  refine ⟨302383508519482395991751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806356022718619722644669 302383508519482395991751)
                  ·
                    rfl

theorem cell20_662501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_662501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662501 prefixEnd_662501 := by exact prefixLift 662501
  have htrace : WordTrace (prefixWord ++ tailWord_662501) baseStart_662501 baseEnd_662501 := by
    simpa [prefixWord, tailWord_662501, baseEnd_662501] using wordTrace_append hprefix tailTrace_662501
  have hstable : (prefixWord ++ tailWord_662501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662501).length < 2 ^ (prefixWord ++ tailWord_662501).sum := by decide
  have hdescent : baseEnd_662501 < baseStart_662501 := by decide
  rcases family_descends (prefixWord ++ tailWord_662501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662533 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 2]
def baseStart_662533 : Nat := 118140960795 + 662533 * 2 ^ 59
def prefixEnd_662533 : Nat := 4983230072969 + 3 ^ 40 * 662533 * 2
def baseEnd_662533 : Nat := 302398114191432506924953

theorem tailTrace_662533 : CollatzResearch.WordTrace tailWord_662533 prefixEnd_662533 302398114191432506924953 := by
  unfold tailWord_662533
  simp only [CollatzResearch.WordTrace]
  refine ⟨24164563708763567473048253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16109709139175711648698835 24164563708763567473048253)
  ·
    refine ⟨9061711390786337802393095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24164563708763567473048253 9061711390786337802393095)
    ·
      refine ⟨13592567086179506703589643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9061711390786337802393095 13592567086179506703589643)
      ·
        refine ⟨20388850629269260055384465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13592567086179506703589643 20388850629269260055384465)
        ·
          refine ⟨15291637971951945041538349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20388850629269260055384465 15291637971951945041538349)
          ·
            refine ⟨5734364239481979390576881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15291637971951945041538349 5734364239481979390576881)
            ·
              refine ⟨4300773179611484542932661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734364239481979390576881 4300773179611484542932661)
              ·
                refine ⟨403197485588576675899937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4300773179611484542932661 403197485588576675899937)
                ·
                  refine ⟨302398114191432506924953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403197485588576675899937 302398114191432506924953)
                  ·
                    rfl

theorem cell20_662533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_662533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662533 prefixEnd_662533 := by exact prefixLift 662533
  have htrace : WordTrace (prefixWord ++ tailWord_662533) baseStart_662533 baseEnd_662533 := by
    simpa [prefixWord, tailWord_662533, baseEnd_662533] using wordTrace_append hprefix tailTrace_662533
  have hstable : (prefixWord ++ tailWord_662533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662533).length < 2 ^ (prefixWord ++ tailWord_662533).sum := by decide
  have hdescent : baseEnd_662533 < baseStart_662533 := by decide
  rcases family_descends (prefixWord ++ tailWord_662533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662554 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_662554 : Nat := 118140960795 + 662554 * 2 ^ 59
def prefixEnd_662554 : Nat := 4983230072969 + 3 ^ 40 * 662554 * 2
def baseEnd_662554 : Nat := 302407699163649767224867

theorem tailTrace_662554 : CollatzResearch.WordTrace tailWord_662554 prefixEnd_662554 302407699163649767224867 := by
  unfold tailWord_662554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041332410421872014890679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16110219761124992039708477 6041332410421872014890679)
  ·
    refine ⟨9061998615632808022336019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6041332410421872014890679 9061998615632808022336019)
    ·
      refine ⟨13592997923449212033504029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9061998615632808022336019 13592997923449212033504029)
      ·
        refine ⟨5097374221293454512564011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13592997923449212033504029 5097374221293454512564011)
        ·
          refine ⟨7646061331940181768846017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097374221293454512564011 7646061331940181768846017)
          ·
            refine ⟨5734545998955136326634513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646061331940181768846017 5734545998955136326634513)
            ·
              refine ⟨4300909499216352244975885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734545998955136326634513 4300909499216352244975885)
              ·
                refine ⟨1612841062206132091865957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4300909499216352244975885 1612841062206132091865957)
                ·
                  refine ⟨302407699163649767224867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612841062206132091865957 302407699163649767224867)
                  ·
                    rfl

theorem cell20_662554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_662554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662554 prefixEnd_662554 := by exact prefixLift 662554
  have htrace : WordTrace (prefixWord ++ tailWord_662554) baseStart_662554 baseEnd_662554 := by
    simpa [prefixWord, tailWord_662554, baseEnd_662554] using wordTrace_append hprefix tailTrace_662554
  have hstable : (prefixWord ++ tailWord_662554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662554).length < 2 ^ (prefixWord ++ tailWord_662554).sum := by decide
  have hdescent : baseEnd_662554 < baseStart_662554 := by decide
  rcases family_descends (prefixWord ++ tailWord_662554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662557 : List Nat := [1, 4, 2, 2, 3, 2, 1, 5]
def baseStart_662557 : Nat := 118140960795 + 662557 * 2 ^ 59
def prefixEnd_662557 : Nat := 4983230072969 + 3 ^ 40 * 662557 * 2
def baseEnd_662557 : Nat := 100803022815131696708285

theorem tailTrace_662557 : CollatzResearch.WordTrace tailWord_662557 prefixEnd_662557 100803022815131696708285 := by
  unfold tailWord_662557
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165439060676619571921925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16110292707117746381281283 24165439060676619571921925)
  ·
    refine ⟨4531019823876866169735361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24165439060676619571921925 4531019823876866169735361)
    ·
      refine ⟨3398264867907649627301521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4531019823876866169735361 3398264867907649627301521)
      ·
        refine ⟨2548698650930737220476141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3398264867907649627301521 2548698650930737220476141)
        ·
          refine ⟨955761994099026457678553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2548698650930737220476141 955761994099026457678553)
          ·
            refine ⟨716821495574269843258915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955761994099026457678553 716821495574269843258915)
            ·
              refine ⟨1075232243361404764888373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716821495574269843258915 1075232243361404764888373)
              ·
                refine ⟨100803022815131696708285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1075232243361404764888373 100803022815131696708285)
                ·
                  rfl

theorem cell20_662557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_662557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662557 prefixEnd_662557 := by exact prefixLift 662557
  have htrace : WordTrace (prefixWord ++ tailWord_662557) baseStart_662557 baseEnd_662557 := by
    simpa [prefixWord, tailWord_662557, baseEnd_662557] using wordTrace_append hprefix tailTrace_662557
  have hstable : (prefixWord ++ tailWord_662557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662557).length < 2 ^ (prefixWord ++ tailWord_662557).sum := by decide
  have hdescent : baseEnd_662557 < baseStart_662557 := by decide
  rcases family_descends (prefixWord ++ tailWord_662557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662564 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_662564 : Nat := 118140960795 + 662564 * 2 ^ 59
def prefixEnd_662564 : Nat := 4983230072969 + 3 ^ 40 * 662564 * 2
def baseEnd_662564 : Nat := 302412263436134176891493

theorem tailTrace_662564 : CollatzResearch.WordTrace tailWord_662564 prefixEnd_662564 302412263436134176891493 := by
  unfold tailWord_662564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12082847185825629883713373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16110462914434173178284497 12082847185825629883713373)
  ·
    refine ⟨4531067694684611206392515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12082847185825629883713373 4531067694684611206392515)
    ·
      refine ⟨6796601542026916809588773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531067694684611206392515 6796601542026916809588773)
      ·
        refine ⟨1274362789130046901797895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6796601542026916809588773 1274362789130046901797895)
        ·
          refine ⟨1911544183695070352696843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274362789130046901797895 1911544183695070352696843)
          ·
            refine ⟨2867316275542605529045265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911544183695070352696843 2867316275542605529045265)
            ·
              refine ⟨2150487206656954146783949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2867316275542605529045265 2150487206656954146783949)
              ·
                refine ⟨806432702496357805043981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2150487206656954146783949 806432702496357805043981)
                ·
                  refine ⟨302412263436134176891493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806432702496357805043981 302412263436134176891493)
                  ·
                    rfl

theorem cell20_662564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_662564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662564 prefixEnd_662564 := by exact prefixLift 662564
  have htrace : WordTrace (prefixWord ++ tailWord_662564) baseStart_662564 baseEnd_662564 := by
    simpa [prefixWord, tailWord_662564, baseEnd_662564] using wordTrace_append hprefix tailTrace_662564
  have hstable : (prefixWord ++ tailWord_662564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662564).length < 2 ^ (prefixWord ++ tailWord_662564).sum := by decide
  have hdescent : baseEnd_662564 < baseStart_662564 := by decide
  rcases family_descends (prefixWord ++ tailWord_662564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662578 : List Nat := [3, 2, 1, 1, 2, 2, 5, 4]
def baseStart_662578 : Nat := 118140960795 + 662578 * 2 ^ 59
def prefixEnd_662578 : Nat := 4983230072969 + 3 ^ 40 * 662578 * 2
def baseEnd_662578 : Nat := 100806217805870783474923

theorem tailTrace_662578 : CollatzResearch.WordTrace tailWord_662578 prefixEnd_662578 100806217805870783474923 := by
  unfold tailWord_662578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041551248400135039609097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16110803329067026772290925 6041551248400135039609097)
  ·
    refine ⟨4531163436300101279706823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6041551248400135039609097 4531163436300101279706823)
    ·
      refine ⟨6796745154450151919560235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531163436300101279706823 6796745154450151919560235)
      ·
        refine ⟨10195117731675227879340353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796745154450151919560235 10195117731675227879340353)
        ·
          refine ⟨7646338298756420909505265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10195117731675227879340353 7646338298756420909505265)
          ·
            refine ⟨5734753724067315682128949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646338298756420909505265 5734753724067315682128949)
            ·
              refine ⟨537633161631310845199589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5734753724067315682128949 537633161631310845199589)
              ·
                refine ⟨100806217805870783474923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537633161631310845199589 100806217805870783474923)
                ·
                  rfl

theorem cell20_662578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_662578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662578 prefixEnd_662578 := by exact prefixLift 662578
  have htrace : WordTrace (prefixWord ++ tailWord_662578) baseStart_662578 baseEnd_662578 := by
    simpa [prefixWord, tailWord_662578, baseEnd_662578] using wordTrace_append hprefix tailTrace_662578
  have hstable : (prefixWord ++ tailWord_662578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662578).length < 2 ^ (prefixWord ++ tailWord_662578).sum := by decide
  have hdescent : baseEnd_662578 < baseStart_662578 := by decide
  rcases family_descends (prefixWord ++ tailWord_662578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662588 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 2]
def baseStart_662588 : Nat := 118140960795 + 662588 * 2 ^ 59
def prefixEnd_662588 : Nat := 4983230072969 + 3 ^ 40 * 662588 * 2
def baseEnd_662588 : Nat := 302423217690096760091395

theorem tailTrace_662588 : CollatzResearch.WordTrace tailWord_662588 prefixEnd_662588 302423217690096760091395 := by
  unfold tailWord_662588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12083284861782155933150209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16111046482376207910866945 12083284861782155933150209)
  ·
    refine ⟨9062463646336616949862657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12083284861782155933150209 9062463646336616949862657)
    ·
      refine ⟨6796847734752462712396993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9062463646336616949862657 6796847734752462712396993)
      ·
        refine ⟨5097635801064347034297745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6796847734752462712396993 5097635801064347034297745)
        ·
          refine ⟨3823226850798260275723309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5097635801064347034297745 3823226850798260275723309)
          ·
            refine ⟨1433710069049347603396241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3823226850798260275723309 1433710069049347603396241)
            ·
              refine ⟨1075282551787010702547181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433710069049347603396241 1075282551787010702547181)
              ·
                refine ⟨403230956920129013455193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1075282551787010702547181 403230956920129013455193)
                ·
                  refine ⟨302423217690096760091395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403230956920129013455193 302423217690096760091395)
                  ·
                    rfl

theorem cell20_662588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_662588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662588 prefixEnd_662588 := by exact prefixLift 662588
  have htrace : WordTrace (prefixWord ++ tailWord_662588) baseStart_662588 baseEnd_662588 := by
    simpa [prefixWord, tailWord_662588, baseEnd_662588] using wordTrace_append hprefix tailTrace_662588
  have hstable : (prefixWord ++ tailWord_662588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662588).length < 2 ^ (prefixWord ++ tailWord_662588).sum := by decide
  have hdescent : baseEnd_662588 < baseStart_662588 := by decide
  rcases family_descends (prefixWord ++ tailWord_662588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662598 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_662598 : Nat := 118140960795 + 662598 * 2 ^ 59
def prefixEnd_662598 : Nat := 4983230072969 + 3 ^ 40 * 662598 * 2
def baseEnd_662598 : Nat := 302427781962581169758021

theorem tailTrace_662598 : CollatzResearch.WordTrace tailWord_662598 prefixEnd_662598 302427781962581169758021 := by
  unfold tailWord_662598
  simp only [CollatzResearch.WordTrace]
  refine ⟨755216701672752611692639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16111289635685389049442965 755216701672752611692639)
  ·
    refine ⟨1132825052509128917538959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 755216701672752611692639 1132825052509128917538959)
    ·
      refine ⟨1699237578763693376308439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1132825052509128917538959 1699237578763693376308439)
      ·
        refine ⟨2548856368145540064462659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1699237578763693376308439 2548856368145540064462659)
        ·
          refine ⟨3823284552218310096693989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548856368145540064462659 3823284552218310096693989)
          ·
            refine ⟨716865853540933143130123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3823284552218310096693989 716865853540933143130123)
            ·
              refine ⟨1075298780311399714695185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716865853540933143130123 1075298780311399714695185)
              ·
                refine ⟨806474085233549786021389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075298780311399714695185 806474085233549786021389)
                ·
                  refine ⟨302427781962581169758021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806474085233549786021389 302427781962581169758021)
                  ·
                    rfl

theorem cell20_662598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_662598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662598 prefixEnd_662598 := by exact prefixLift 662598
  have htrace : WordTrace (prefixWord ++ tailWord_662598) baseStart_662598 baseEnd_662598 := by
    simpa [prefixWord, tailWord_662598, baseEnd_662598] using wordTrace_append hprefix tailTrace_662598
  have hstable : (prefixWord ++ tailWord_662598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662598).length < 2 ^ (prefixWord ++ tailWord_662598).sum := by decide
  have hdescent : baseEnd_662598 < baseStart_662598 := by decide
  rcases family_descends (prefixWord ++ tailWord_662598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662599 : List Nat := [1, 1, 4, 1, 3, 3, 7]
def baseStart_662599 : Nat := 118140960795 + 662599 * 2 ^ 59
def prefixEnd_662599 : Nat := 4983230072969 + 3 ^ 40 * 662599 * 2
def baseEnd_662599 : Nat := 33603137598869956747187

theorem tailTrace_662599 : CollatzResearch.WordTrace tailWord_662599 prefixEnd_662599 33603137598869956747187 := by
  unfold tailWord_662599
  simp only [CollatzResearch.WordTrace]
  refine ⟨24166970926524460744950851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16111313951016307163300567 24166970926524460744950851)
  ·
    refine ⟨36250456389786691117426277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24166970926524460744950851 36250456389786691117426277)
    ·
      refine ⟨6796960573085004584517427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36250456389786691117426277 6796960573085004584517427)
      ·
        refine ⟨10195440859627506876776141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796960573085004584517427 10195440859627506876776141)
        ·
          refine ⟨3823290322360315078791053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10195440859627506876776141 3823290322360315078791053)
          ·
            refine ⟨1433733870885118154546645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3823290322360315078791053 1433733870885118154546645)
            ·
              refine ⟨33603137598869956747187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1433733870885118154546645 33603137598869956747187)
              ·
                rfl

theorem cell20_662599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_662599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662599 prefixEnd_662599 := by exact prefixLift 662599
  have htrace : WordTrace (prefixWord ++ tailWord_662599) baseStart_662599 baseEnd_662599 := by
    simpa [prefixWord, tailWord_662599, baseEnd_662599] using wordTrace_append hprefix tailTrace_662599
  have hstable : (prefixWord ++ tailWord_662599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662599).length < 2 ^ (prefixWord ++ tailWord_662599).sum := by decide
  have hdescent : baseEnd_662599 < baseStart_662599 := by decide
  rcases family_descends (prefixWord ++ tailWord_662599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662609 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 2]
def baseStart_662609 : Nat := 118140960795 + 662609 * 2 ^ 59
def prefixEnd_662609 : Nat := 4983230072969 + 3 ^ 40 * 662609 * 2
def baseEnd_662609 : Nat := 302432802662314020391309

theorem tailTrace_662609 : CollatzResearch.WordTrace tailWord_662609 prefixEnd_662609 302432802662314020391309 := by
  unfold tailWord_662609
  simp only [CollatzResearch.WordTrace]
  refine ⟨24167335656488232452814881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16111557104325488301876587 24167335656488232452814881)
  ·
    refine ⟨18125501742366174339611161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24167335656488232452814881 18125501742366174339611161)
    ·
      refine ⟨13594126306774630754708371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18125501742366174339611161 13594126306774630754708371)
      ·
        refine ⟨20391189460161946132062557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13594126306774630754708371 20391189460161946132062557)
        ·
          refine ⟨7646696047560729799523459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20391189460161946132062557 7646696047560729799523459)
          ·
            refine ⟨11470044071341094699285189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7646696047560729799523459 11470044071341094699285189)
            ·
              refine ⟨2150633263376455256115973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11470044071341094699285189 2150633263376455256115973)
              ·
                refine ⟨403243736883085360521745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2150633263376455256115973 403243736883085360521745)
                ·
                  refine ⟨302432802662314020391309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403243736883085360521745 302432802662314020391309)
                  ·
                    rfl

theorem cell20_662609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_662609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662609 prefixEnd_662609 := by exact prefixLift 662609
  have htrace : WordTrace (prefixWord ++ tailWord_662609) baseStart_662609 baseEnd_662609 := by
    simpa [prefixWord, tailWord_662609, baseEnd_662609] using wordTrace_append hprefix tailTrace_662609
  have hstable : (prefixWord ++ tailWord_662609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662609).length < 2 ^ (prefixWord ++ tailWord_662609).sum := by decide
  have hdescent : baseEnd_662609 < baseStart_662609 := by decide
  rcases family_descends (prefixWord ++ tailWord_662609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662651 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_662651 : Nat := 118140960795 + 662651 * 2 ^ 59
def prefixEnd_662651 : Nat := 4983230072969 + 3 ^ 40 * 662651 * 2
def baseEnd_662651 : Nat := 302451972606748540991137

theorem tailTrace_662651 : CollatzResearch.WordTrace tailWord_662651 prefixEnd_662651 302451972606748540991137 := by
  unfold tailWord_662651
  simp only [CollatzResearch.WordTrace]
  refine ⟨24168867522336073625843807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16112578348224049083895871 24168867522336073625843807)
  ·
    refine ⟨36253301283504110438765711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24168867522336073625843807 36253301283504110438765711)
    ·
      refine ⟨54379951925256165658148567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36253301283504110438765711 54379951925256165658148567)
      ·
        refine ⟨81569927887884248487222851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54379951925256165658148567 81569927887884248487222851)
        ·
          refine ⟨122354891831826372730834277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81569927887884248487222851 122354891831826372730834277)
          ·
            refine ⟨22941542218467444887031427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122354891831826372730834277 22941542218467444887031427)
            ·
              refine ⟨34412313327701167330547141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22941542218467444887031427 34412313327701167330547141)
              ·
                refine ⟨6452308748943968874477589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34412313327701167330547141 6452308748943968874477589)
                ·
                  refine ⟨302451972606748540991137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6452308748943968874477589 302451972606748540991137)
                  ·
                    rfl

theorem cell20_662651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_662651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662651 prefixEnd_662651 := by exact prefixLift 662651
  have htrace : WordTrace (prefixWord ++ tailWord_662651) baseStart_662651 baseEnd_662651 := by
    simpa [prefixWord, tailWord_662651, baseEnd_662651] using wordTrace_append hprefix tailTrace_662651
  have hstable : (prefixWord ++ tailWord_662651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662651).length < 2 ^ (prefixWord ++ tailWord_662651).sum := by decide
  have hdescent : baseEnd_662651 < baseStart_662651 := by decide
  rcases family_descends (prefixWord ++ tailWord_662651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662664 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_662664 : Nat := 118140960795 + 662664 * 2 ^ 59
def prefixEnd_662664 : Nat := 4983230072969 + 3 ^ 40 * 662664 * 2
def baseEnd_662664 : Nat := 302457906160978273557751

theorem tailTrace_662664 : CollatzResearch.WordTrace tailWord_662664 prefixEnd_662664 302457906160978273557751 := by
  unfold tailWord_662664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084670835644488423033523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16112894447525984564044697 12084670835644488423033523)
  ·
    refine ⟨18127006253466732634550285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12084670835644488423033523 18127006253466732634550285)
    ·
      refine ⟨6797627345050024737956357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18127006253466732634550285 6797627345050024737956357)
      ·
        refine ⟨1274555127196879638366817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6797627345050024737956357 1274555127196879638366817)
        ·
          refine ⟨955916345397659728775113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274555127196879638366817 955916345397659728775113)
          ·
            refine ⟨716937259048244796581335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955916345397659728775113 716937259048244796581335)
            ·
              refine ⟨1075405888572367194872003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716937259048244796581335 1075405888572367194872003)
              ·
                refine ⟨1613108832858550792308005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075405888572367194872003 1613108832858550792308005)
                ·
                  refine ⟨302457906160978273557751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613108832858550792308005 302457906160978273557751)
                  ·
                    rfl

theorem cell20_662664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_662664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662664 prefixEnd_662664 := by exact prefixLift 662664
  have htrace : WordTrace (prefixWord ++ tailWord_662664) baseStart_662664 baseEnd_662664 := by
    simpa [prefixWord, tailWord_662664, baseEnd_662664] using wordTrace_append hprefix tailTrace_662664
  have hstable : (prefixWord ++ tailWord_662664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662664).length < 2 ^ (prefixWord ++ tailWord_662664).sum := by decide
  have hdescent : baseEnd_662664 < baseStart_662664 := by decide
  rcases family_descends (prefixWord ++ tailWord_662664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662716 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_662716 : Nat := 118140960795 + 662716 * 2 ^ 59
def prefixEnd_662716 : Nat := 4983230072969 + 3 ^ 40 * 662716 * 2
def baseEnd_662716 : Nat := 302481640377897203824205

theorem tailTrace_662716 : CollatzResearch.WordTrace tailWord_662716 prefixEnd_662716 302481640377897203824205 := by
  unfold tailWord_662716
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085619133550294863480001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16114158844733726484640001 12085619133550294863480001)
  ·
    refine ⟨9064214350162721147610001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12085619133550294863480001 9064214350162721147610001)
    ·
      refine ⟨6798160762622040860707501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9064214350162721147610001 6798160762622040860707501)
      ·
        refine ⟨2549310285983265322765313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6798160762622040860707501 2549310285983265322765313)
        ·
          refine ⟨1911982714487448992073985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2549310285983265322765313 1911982714487448992073985)
          ·
            refine ⟨1433987035865586744055489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911982714487448992073985 1433987035865586744055489)
            ·
              refine ⟨1075490276899190058041617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433987035865586744055489 1075490276899190058041617)
              ·
                refine ⟨806617707674392543531213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075490276899190058041617 806617707674392543531213)
                ·
                  refine ⟨302481640377897203824205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806617707674392543531213 302481640377897203824205)
                  ·
                    rfl

theorem cell20_662716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_662716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662716 prefixEnd_662716 := by exact prefixLift 662716
  have htrace : WordTrace (prefixWord ++ tailWord_662716) baseStart_662716 baseEnd_662716 := by
    simpa [prefixWord, tailWord_662716, baseEnd_662716] using wordTrace_append hprefix tailTrace_662716
  have hstable : (prefixWord ++ tailWord_662716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662716).length < 2 ^ (prefixWord ++ tailWord_662716).sum := by decide
  have hdescent : baseEnd_662716 < baseStart_662716 := by decide
  rcases family_descends (prefixWord ++ tailWord_662716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662727 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_662727 : Nat := 118140960795 + 662727 * 2 ^ 59
def prefixEnd_662727 : Nat := 4983230072969 + 3 ^ 40 * 662727 * 2
def baseEnd_662727 : Nat := 302486661077630054457493

theorem tailTrace_662727 : CollatzResearch.WordTrace tailWord_662727 prefixEnd_662727 302486661077630054457493 := by
  unfold tailWord_662727
  simp only [CollatzResearch.WordTrace]
  refine ⟨24171639470060738605610435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16114426313373825737073623 24171639470060738605610435)
  ·
    refine ⟨36257459205091107908415653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24171639470060738605610435 36257459205091107908415653)
    ·
      refine ⟨6798273600954582732827935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36257459205091107908415653 6798273600954582732827935)
      ·
        refine ⟨10197410401431874099241903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6798273600954582732827935 10197410401431874099241903)
        ·
          refine ⟨15296115602147811148862855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10197410401431874099241903 15296115602147811148862855)
          ·
            refine ⟨22944173403221716723294283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15296115602147811148862855 22944173403221716723294283)
            ·
              refine ⟨34416260104832575084941425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22944173403221716723294283 34416260104832575084941425)
              ·
                refine ⟨25812195078624431313706069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34416260104832575084941425 25812195078624431313706069)
                ·
                  refine ⟨302486661077630054457493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25812195078624431313706069 302486661077630054457493)
                  ·
                    rfl

theorem cell20_662727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_662727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662727 prefixEnd_662727 := by exact prefixLift 662727
  have htrace : WordTrace (prefixWord ++ tailWord_662727) baseStart_662727 baseEnd_662727 := by
    simpa [prefixWord, tailWord_662727, baseEnd_662727] using wordTrace_append hprefix tailTrace_662727
  have hstable : (prefixWord ++ tailWord_662727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662727).length < 2 ^ (prefixWord ++ tailWord_662727).sum := by decide
  have hdescent : baseEnd_662727 < baseStart_662727 := by decide
  rcases family_descends (prefixWord ++ tailWord_662727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662730 : List Nat := [3, 1, 2, 1, 3, 4, 1, 5]
def baseStart_662730 : Nat := 118140960795 + 662730 * 2 ^ 59
def prefixEnd_662730 : Nat := 4983230072969 + 3 ^ 40 * 662730 * 2
def baseEnd_662730 : Nat := 100829343453125125785827

theorem tailTrace_662730 : CollatzResearch.WordTrace tailWord_662730 prefixEnd_662730 100829343453125125785827 := by
  unfold tailWord_662730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042937222262467529492411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16114499259366580078646429 6042937222262467529492411)
  ·
    refine ⟨9064405833393701294238617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6042937222262467529492411 9064405833393701294238617)
    ·
      refine ⟨6798304375045275970678963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9064405833393701294238617 6798304375045275970678963)
      ·
        refine ⟨10197456562567913956018445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6798304375045275970678963 10197456562567913956018445)
        ·
          refine ⟨3824046210962967733506917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10197456562567913956018445 3824046210962967733506917)
          ·
            refine ⟨717008664555556450032547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3824046210962967733506917 717008664555556450032547)
            ·
              refine ⟨1075512996833334675048821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717008664555556450032547 1075512996833334675048821)
              ·
                refine ⟨100829343453125125785827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1075512996833334675048821 100829343453125125785827)
                ·
                  rfl

theorem cell20_662730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_662730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662730 prefixEnd_662730 := by exact prefixLift 662730
  have htrace : WordTrace (prefixWord ++ tailWord_662730) baseStart_662730 baseEnd_662730 := by
    simpa [prefixWord, tailWord_662730, baseEnd_662730] using wordTrace_append hprefix tailTrace_662730
  have hstable : (prefixWord ++ tailWord_662730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662730).length < 2 ^ (prefixWord ++ tailWord_662730).sum := by decide
  have hdescent : baseEnd_662730 < baseStart_662730 := by decide
  rcases family_descends (prefixWord ++ tailWord_662730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662740 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_662740 : Nat := 118140960795 + 662740 * 2 ^ 59
def prefixEnd_662740 : Nat := 4983230072969 + 3 ^ 40 * 662740 * 2
def baseEnd_662740 : Nat := 302492594631859787024107

theorem tailTrace_662740 : CollatzResearch.WordTrace tailWord_662740 prefixEnd_662740 302492594631859787024107 := by
  unfold tailWord_662740
  simp only [CollatzResearch.WordTrace]
  refine ⟨12086056809506820912916837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16114742412675761217222449 12086056809506820912916837)
  ·
    refine ⟨2266135651782528921171907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12086056809506820912916837 2266135651782528921171907)
    ·
      refine ⟨3399203477673793381757861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266135651782528921171907 3399203477673793381757861)
      ·
        refine ⟨637350652063836259079599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3399203477673793381757861 637350652063836259079599)
        ·
          refine ⟨956025978095754388619399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637350652063836259079599 956025978095754388619399)
          ·
            refine ⟨1434038967143631582929099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956025978095754388619399 1434038967143631582929099)
            ·
              refine ⟨2151058450715447374393649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434038967143631582929099 2151058450715447374393649)
              ·
                refine ⟨1613293838036585530795237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151058450715447374393649 1613293838036585530795237)
                ·
                  refine ⟨302492594631859787024107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613293838036585530795237 302492594631859787024107)
                  ·
                    rfl

theorem cell20_662740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_662740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662740 prefixEnd_662740 := by exact prefixLift 662740
  have htrace : WordTrace (prefixWord ++ tailWord_662740) baseStart_662740 baseEnd_662740 := by
    simpa [prefixWord, tailWord_662740, baseEnd_662740] using wordTrace_append hprefix tailTrace_662740
  have hstable : (prefixWord ++ tailWord_662740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662740).length < 2 ^ (prefixWord ++ tailWord_662740).sum := by decide
  have hdescent : baseEnd_662740 < baseStart_662740 := by decide
  rcases family_descends (prefixWord ++ tailWord_662740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662813 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_662813 : Nat := 118140960795 + 662813 * 2 ^ 59
def prefixEnd_662813 : Nat := 4983230072969 + 3 ^ 40 * 662813 * 2
def baseEnd_662813 : Nat := 302525913820995977590475

theorem tailTrace_662813 : CollatzResearch.WordTrace tailWord_662813 prefixEnd_662813 302525913820995977590475 := by
  unfold tailWord_662813
  simp only [CollatzResearch.WordTrace]
  refine ⟨24174776147749175293241093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16116517431832783528827395 24174776147749175293241093)
  ·
    refine ⟨4532770527702970367482705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24174776147749175293241093 4532770527702970367482705)
    ·
      refine ⟨3399577895777227775612029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4532770527702970367482705 3399577895777227775612029)
      ·
        refine ⟨1274841710916460415854511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3399577895777227775612029 1274841710916460415854511)
        ·
          refine ⟨1912262566374690623781767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274841710916460415854511 1912262566374690623781767)
          ·
            refine ⟨2868393849562035935672651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912262566374690623781767 2868393849562035935672651)
            ·
              refine ⟨4302590774343053903508977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868393849562035935672651 4302590774343053903508977)
              ·
                refine ⟨3226943080757290427631733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4302590774343053903508977 3226943080757290427631733)
                ·
                  refine ⟨302525913820995977590475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3226943080757290427631733 302525913820995977590475)
                  ·
                    rfl

theorem cell20_662813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_662813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662813 prefixEnd_662813 := by exact prefixLift 662813
  have htrace : WordTrace (prefixWord ++ tailWord_662813) baseStart_662813 baseEnd_662813 := by
    simpa [prefixWord, tailWord_662813, baseEnd_662813] using wordTrace_append hprefix tailTrace_662813
  have hstable : (prefixWord ++ tailWord_662813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662813).length < 2 ^ (prefixWord ++ tailWord_662813).sum := by decide
  have hdescent : baseEnd_662813 < baseStart_662813 := by decide
  rcases family_descends (prefixWord ++ tailWord_662813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662837 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 4]
def baseStart_662837 : Nat := 118140960795 + 662837 * 2 ^ 59
def prefixEnd_662837 : Nat := 4983230072969 + 3 ^ 40 * 662837 * 2
def baseEnd_662837 : Nat := 302536868074958560790377

theorem tailTrace_662837 : CollatzResearch.WordTrace tailWord_662837 prefixEnd_662837 302536868074958560790377 := by
  unfold tailWord_662837
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175651499662227392114765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16117100999774818261409843 24175651499662227392114765)
  ·
    refine ⟨9065869312373335272043037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24175651499662227392114765 9065869312373335272043037)
    ·
      refine ⟨3399700992140000727016139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9065869312373335272043037 3399700992140000727016139)
      ·
        refine ⟨5099551488210001090524209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399700992140000727016139 5099551488210001090524209)
        ·
          refine ⟨3824663616157500817893157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5099551488210001090524209 3824663616157500817893157)
          ·
            refine ⟨717124428029531403354967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3824663616157500817893157 717124428029531403354967)
            ·
              refine ⟨1075686642044297105032451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717124428029531403354967 1075686642044297105032451)
              ·
                refine ⟨1613529963066445657548677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075686642044297105032451 1613529963066445657548677)
                ·
                  refine ⟨302536868074958560790377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613529963066445657548677 302536868074958560790377)
                  ·
                    rfl

theorem cell20_662837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_662837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662837 prefixEnd_662837 := by exact prefixLift 662837
  have htrace : WordTrace (prefixWord ++ tailWord_662837) baseStart_662837 baseEnd_662837 := by
    simpa [prefixWord, tailWord_662837, baseEnd_662837] using wordTrace_append hprefix tailTrace_662837
  have hstable : (prefixWord ++ tailWord_662837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662837).length < 2 ^ (prefixWord ++ tailWord_662837).sum := by decide
  have hdescent : baseEnd_662837 < baseStart_662837 := by decide
  rcases family_descends (prefixWord ++ tailWord_662837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662888 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 2]
def baseStart_662888 : Nat := 118140960795 + 662888 * 2 ^ 59
def prefixEnd_662888 : Nat := 4983230072969 + 3 ^ 40 * 662888 * 2
def baseEnd_662888 : Nat := 302560145864629050090169

theorem tailTrace_662888 : CollatzResearch.WordTrace tailWord_662888 prefixEnd_662888 302560145864629050090169 := by
  unfold tailWord_662888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12088755811238731551110659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16118341081651642068147545 12088755811238731551110659)
  ·
    refine ⟨18133133716858097326665989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12088755811238731551110659 18133133716858097326665989)
    ·
      refine ⟨3399962571910893248749873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18133133716858097326665989 3399962571910893248749873)
      ·
        refine ⟨2549971928933169936562405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3399962571910893248749873 2549971928933169936562405)
        ·
          refine ⟨478119736674969363105451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2549971928933169936562405 478119736674969363105451)
          ·
            refine ⟨717179605012454044658177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478119736674969363105451 717179605012454044658177)
            ·
              refine ⟨537884703759340533493633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717179605012454044658177 537884703759340533493633)
              ·
                refine ⟨403413527819505400120225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537884703759340533493633 403413527819505400120225)
                ·
                  refine ⟨302560145864629050090169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403413527819505400120225 302560145864629050090169)
                  ·
                    rfl

theorem cell20_662888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_662888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662888 prefixEnd_662888 := by exact prefixLift 662888
  have htrace : WordTrace (prefixWord ++ tailWord_662888) baseStart_662888 baseEnd_662888 := by
    simpa [prefixWord, tailWord_662888, baseEnd_662888] using wordTrace_append hprefix tailTrace_662888
  have hstable : (prefixWord ++ tailWord_662888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662888).length < 2 ^ (prefixWord ++ tailWord_662888).sum := by decide
  have hdescent : baseEnd_662888 < baseStart_662888 := by decide
  rcases family_descends (prefixWord ++ tailWord_662888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662892 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 2]
def baseStart_662892 : Nat := 118140960795 + 662892 * 2 ^ 59
def prefixEnd_662892 : Nat := 4983230072969 + 3 ^ 40 * 662892 * 2
def baseEnd_662892 : Nat := 302561971573622813956819

theorem tailTrace_662892 : CollatzResearch.WordTrace tailWord_662892 prefixEnd_662892 302561971573622813956819 := by
  unfold tailWord_662892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12088828757231485892683465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16118438342975314523577953 12088828757231485892683465)
  ·
    refine ⟨9066621567923614419512599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12088828757231485892683465 9066621567923614419512599)
    ·
      refine ⟨13599932351885421629268899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9066621567923614419512599 13599932351885421629268899)
      ·
        refine ⟨20399898527828132443903349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13599932351885421629268899 20399898527828132443903349)
        ·
          refine ⟨1912490486983887416615939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20399898527828132443903349 1912490486983887416615939)
          ·
            refine ⟨2868735730475831124923909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912490486983887416615939 2868735730475831124923909)
            ·
              refine ⟨537887949464218335923233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2868735730475831124923909 537887949464218335923233)
              ·
                refine ⟨403415962098163751942425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537887949464218335923233 403415962098163751942425)
                ·
                  refine ⟨302561971573622813956819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403415962098163751942425 302561971573622813956819)
                  ·
                    rfl

theorem cell20_662892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_662892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662892 prefixEnd_662892 := by exact prefixLift 662892
  have htrace : WordTrace (prefixWord ++ tailWord_662892) baseStart_662892 baseEnd_662892 := by
    simpa [prefixWord, tailWord_662892, baseEnd_662892] using wordTrace_append hprefix tailTrace_662892
  have hstable : (prefixWord ++ tailWord_662892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662892).length < 2 ^ (prefixWord ++ tailWord_662892).sum := by decide
  have hdescent : baseEnd_662892 < baseStart_662892 := by decide
  rcases family_descends (prefixWord ++ tailWord_662892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662913 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_662913 : Nat := 118140960795 + 662913 * 2 ^ 59
def prefixEnd_662913 : Nat := 4983230072969 + 3 ^ 40 * 662913 * 2
def baseEnd_662913 : Nat := 302571556545840074256733

theorem tailTrace_662913 : CollatzResearch.WordTrace tailWord_662913 prefixEnd_662913 302571556545840074256733 := by
  unfold tailWord_662913
  simp only [CollatzResearch.WordTrace]
  refine ⟨24178423447386892371881393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16118948964924594914587595 24178423447386892371881393)
  ·
    refine ⟨18133817585540169278911045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24178423447386892371881393 18133817585540169278911045)
    ·
      refine ⟨3400090797288781739795821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18133817585540169278911045 3400090797288781739795821)
      ·
        refine ⟨1275034048983293152423433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3400090797288781739795821 1275034048983293152423433)
        ·
          refine ⟨956275536737469864317575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275034048983293152423433 956275536737469864317575)
          ·
            refine ⟨1434413305106204796476363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956275536737469864317575 1434413305106204796476363)
            ·
              refine ⟨2151619957659307194714545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434413305106204796476363 2151619957659307194714545)
              ·
                refine ⟨1613714968244480396035909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151619957659307194714545 1613714968244480396035909)
                ·
                  refine ⟨302571556545840074256733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613714968244480396035909 302571556545840074256733)
                  ·
                    rfl

theorem cell20_662913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_662913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662913 prefixEnd_662913 := by exact prefixLift 662913
  have htrace : WordTrace (prefixWord ++ tailWord_662913) baseStart_662913 baseEnd_662913 := by
    simpa [prefixWord, tailWord_662913, baseEnd_662913] using wordTrace_append hprefix tailTrace_662913
  have hstable : (prefixWord ++ tailWord_662913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662913).length < 2 ^ (prefixWord ++ tailWord_662913).sum := by decide
  have hdescent : baseEnd_662913 < baseStart_662913 := by decide
  rcases family_descends (prefixWord ++ tailWord_662913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662917 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_662917 : Nat := 118140960795 + 662917 * 2 ^ 59
def prefixEnd_662917 : Nat := 4983230072969 + 3 ^ 40 * 662917 * 2
def baseEnd_662917 : Nat := 302573382254833838123383

theorem tailTrace_662917 : CollatzResearch.WordTrace tailWord_662917 prefixEnd_662917 302573382254833838123383 := by
  unfold tailWord_662917
  simp only [CollatzResearch.WordTrace]
  refine ⟨24178569339372401055027005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16119046226248267370018003 24178569339372401055027005)
  ·
    refine ⟨9066963502264650395635127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24178569339372401055027005 9066963502264650395635127)
    ·
      refine ⟨13600445253396975593452691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9066963502264650395635127 13600445253396975593452691)
      ·
        refine ⟨20400667880095463390179037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13600445253396975593452691 20400667880095463390179037)
        ·
          refine ⟨7650250455035798771317139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20400667880095463390179037 7650250455035798771317139)
          ·
            refine ⟨11475375682553698156975709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7650250455035798771317139 11475375682553698156975709)
            ·
              refine ⟨4303265880957636808865891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11475375682553698156975709 4303265880957636808865891)
              ·
                refine ⟨6454898821436455213298837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303265880957636808865891 6454898821436455213298837)
                ·
                  refine ⟨302573382254833838123383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6454898821436455213298837 302573382254833838123383)
                  ·
                    rfl

theorem cell20_662917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_662917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662917 prefixEnd_662917 := by exact prefixLift 662917
  have htrace : WordTrace (prefixWord ++ tailWord_662917) baseStart_662917 baseEnd_662917 := by
    simpa [prefixWord, tailWord_662917, baseEnd_662917] using wordTrace_append hprefix tailTrace_662917
  have hstable : (prefixWord ++ tailWord_662917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662917).length < 2 ^ (prefixWord ++ tailWord_662917).sum := by decide
  have hdescent : baseEnd_662917 < baseStart_662917 := by decide
  rcases family_descends (prefixWord ++ tailWord_662917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662920 : List Nat := [2, 1, 3, 3, 1, 3, 3, 4]
def baseStart_662920 : Nat := 118140960795 + 662920 * 2 ^ 59
def prefixEnd_662920 : Nat := 4983230072969 + 3 ^ 40 * 662920 * 2
def baseEnd_662920 : Nat := 100858250512193053674457

theorem tailTrace_662920 : CollatzResearch.WordTrace tailWord_662920 prefixEnd_662920 100858250512193053674457 := by
  unfold tailWord_662920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12089339379180766283693107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16119119172241021711590809 12089339379180766283693107)
  ·
    refine ⟨18134009068771149425539661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12089339379180766283693107 18134009068771149425539661)
    ·
      refine ⟨6800253400789181034577373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18134009068771149425539661 6800253400789181034577373)
      ·
        refine ⟨2550095025295942887966515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6800253400789181034577373 2550095025295942887966515)
        ·
          refine ⟨3825142537943914331949773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550095025295942887966515 3825142537943914331949773)
          ·
            refine ⟨1434428451728967874481165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3825142537943914331949773 1434428451728967874481165)
            ·
              refine ⟨537910669398362952930437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1434428451728967874481165 537910669398362952930437)
              ·
                refine ⟨100858250512193053674457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537910669398362952930437 100858250512193053674457)
                ·
                  rfl

theorem cell20_662920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_662920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662920 prefixEnd_662920 := by exact prefixLift 662920
  have htrace : WordTrace (prefixWord ++ tailWord_662920) baseStart_662920 baseEnd_662920 := by
    simpa [prefixWord, tailWord_662920, baseEnd_662920] using wordTrace_append hprefix tailTrace_662920
  have hstable : (prefixWord ++ tailWord_662920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662920).length < 2 ^ (prefixWord ++ tailWord_662920).sum := by decide
  have hdescent : baseEnd_662920 < baseStart_662920 := by decide
  rcases family_descends (prefixWord ++ tailWord_662920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662940 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 3]
def baseStart_662940 : Nat := 118140960795 + 662940 * 2 ^ 59
def prefixEnd_662940 : Nat := 4983230072969 + 3 ^ 40 * 662940 * 2
def baseEnd_662940 : Nat := 302583880081547980356623

theorem tailTrace_662940 : CollatzResearch.WordTrace tailWord_662940 prefixEnd_662940 302583880081547980356623 := by
  unfold tailWord_662940
  simp only [CollatzResearch.WordTrace]
  refine ⟨12089704109144537991557137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16119605478859383988742849 12089704109144537991557137)
  ·
    refine ⟨9067278081858403493667853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12089704109144537991557137 9067278081858403493667853)
    ·
      refine ⟨3400229280696901310125445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9067278081858403493667853 3400229280696901310125445)
      ·
        refine ⟨637542990130668995648521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3400229280696901310125445 637542990130668995648521)
        ·
          refine ⟨478157242598001746736391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637542990130668995648521 478157242598001746736391)
          ·
            refine ⟨717235863897002620104587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478157242598001746736391 717235863897002620104587)
            ·
              refine ⟨1075853795845503930156881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717235863897002620104587 1075853795845503930156881)
              ·
                refine ⟨806890346884127947617661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075853795845503930156881 806890346884127947617661)
                ·
                  refine ⟨302583880081547980356623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806890346884127947617661 302583880081547980356623)
                  ·
                    rfl

theorem cell20_662940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_662940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662940 prefixEnd_662940 := by exact prefixLift 662940
  have htrace : WordTrace (prefixWord ++ tailWord_662940) baseStart_662940 baseEnd_662940 := by
    simpa [prefixWord, tailWord_662940, baseEnd_662940] using wordTrace_append hprefix tailTrace_662940
  have hstable : (prefixWord ++ tailWord_662940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662940).length < 2 ^ (prefixWord ++ tailWord_662940).sum := by decide
  have hdescent : baseEnd_662940 < baseStart_662940 := by decide
  rcases family_descends (prefixWord ++ tailWord_662940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662941 : List Nat := [1, 4, 2, 1, 3, 2, 7]
def baseStart_662941 : Nat := 118140960795 + 662941 * 2 ^ 59
def prefixEnd_662941 : Nat := 4983230072969 + 3 ^ 40 * 662941 * 2
def baseEnd_662941 : Nat := 33620481834310713480365

theorem tailTrace_662941 : CollatzResearch.WordTrace tailWord_662941 prefixEnd_662941 33620481834310713480365 := by
  unfold tailWord_662941
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179444691285453153900677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16119629794190302102600451 24179444691285453153900677)
  ·
    refine ⟨4533645879616022466356377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24179444691285453153900677 4533645879616022466356377)
    ·
      refine ⟨3400234409712016849767283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4533645879616022466356377 3400234409712016849767283)
      ·
        refine ⟨5100351614568025274650925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400234409712016849767283 5100351614568025274650925)
        ·
          refine ⟨1912631855463009477994097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5100351614568025274650925 1912631855463009477994097)
          ·
            refine ⟨1434473891597257108495573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912631855463009477994097 1434473891597257108495573)
            ·
              refine ⟨33620481834310713480365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1434473891597257108495573 33620481834310713480365)
              ·
                rfl

theorem cell20_662941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_662941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662941 prefixEnd_662941 := by exact prefixLift 662941
  have htrace : WordTrace (prefixWord ++ tailWord_662941) baseStart_662941 baseEnd_662941 := by
    simpa [prefixWord, tailWord_662941, baseEnd_662941] using wordTrace_append hprefix tailTrace_662941
  have hstable : (prefixWord ++ tailWord_662941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662941).length < 2 ^ (prefixWord ++ tailWord_662941).sum := by decide
  have hdescent : baseEnd_662941 < baseStart_662941 := by decide
  rcases family_descends (prefixWord ++ tailWord_662941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662951 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 2]
def baseStart_662951 : Nat := 118140960795 + 662951 * 2 ^ 59
def prefixEnd_662951 : Nat := 4983230072969 + 3 ^ 40 * 662951 * 2
def baseEnd_662951 : Nat := 302588900781280830989911

theorem tailTrace_662951 : CollatzResearch.WordTrace tailWord_662951 prefixEnd_662951 302588900781280830989911 := by
  unfold tailWord_662951
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179809421249224861764707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16119872947499483241176471 24179809421249224861764707)
  ·
    refine ⟨36269714131873837292647061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24179809421249224861764707 36269714131873837292647061)
    ·
      refine ⟨1700142849931586123092831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36269714131873837292647061 1700142849931586123092831)
      ·
        refine ⟨2550214274897379184639247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700142849931586123092831 2550214274897379184639247)
        ·
          refine ⟨3825321412346068776958871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550214274897379184639247 3825321412346068776958871)
          ·
            refine ⟨5737982118519103165438307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825321412346068776958871 5737982118519103165438307)
            ·
              refine ⟨8606973177778654748157461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737982118519103165438307 8606973177778654748157461)
              ·
                refine ⟨403451867708374441319881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8606973177778654748157461 403451867708374441319881)
                ·
                  refine ⟨302588900781280830989911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403451867708374441319881 302588900781280830989911)
                  ·
                    rfl

theorem cell20_662951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 2].length) (baseStart_662951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662951 prefixEnd_662951 := by exact prefixLift 662951
  have htrace : WordTrace (prefixWord ++ tailWord_662951) baseStart_662951 baseEnd_662951 := by
    simpa [prefixWord, tailWord_662951, baseEnd_662951] using wordTrace_append hprefix tailTrace_662951
  have hstable : (prefixWord ++ tailWord_662951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662951).length < 2 ^ (prefixWord ++ tailWord_662951).sum := by decide
  have hdescent : baseEnd_662951 < baseStart_662951 := by decide
  rcases family_descends (prefixWord ++ tailWord_662951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662979 : List Nat := [1, 1, 1, 3, 1, 1, 8, 4]
def baseStart_662979 : Nat := 118140960795 + 662979 * 2 ^ 59
def prefixEnd_662979 : Nat := 4983230072969 + 3 ^ 40 * 662979 * 2
def baseEnd_662979 : Nat := 100867226914745726018821

theorem tailTrace_662979 : CollatzResearch.WordTrace tailWord_662979 prefixEnd_662979 100867226914745726018821 := by
  unfold tailWord_662979
  simp only [CollatzResearch.WordTrace]
  refine ⟨24180830665147785643783991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16120553776765190429189327 24180830665147785643783991)
  ·
    refine ⟨36271245997721678465675987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24180830665147785643783991 36271245997721678465675987)
    ·
      refine ⟨54406868996582517698513981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36271245997721678465675987 54406868996582517698513981)
      ·
        refine ⟨20402575873718444136942743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54406868996582517698513981 20402575873718444136942743)
        ·
          refine ⟨30603863810577666205414115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20402575873718444136942743 30603863810577666205414115)
          ·
            refine ⟨45905795715866499308121173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30603863810577666205414115 45905795715866499308121173)
            ·
              refine ⟨537958543545310538767045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 45905795715866499308121173 537958543545310538767045)
              ·
                refine ⟨100867226914745726018821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537958543545310538767045 100867226914745726018821)
                ·
                  rfl

theorem cell20_662979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_662979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662979 prefixEnd_662979 := by exact prefixLift 662979
  have htrace : WordTrace (prefixWord ++ tailWord_662979) baseStart_662979 baseEnd_662979 := by
    simpa [prefixWord, tailWord_662979, baseEnd_662979] using wordTrace_append hprefix tailTrace_662979
  have hstable : (prefixWord ++ tailWord_662979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662979).length < 2 ^ (prefixWord ++ tailWord_662979).sum := by decide
  have hdescent : baseEnd_662979 < baseStart_662979 := by decide
  rcases family_descends (prefixWord ++ tailWord_662979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662986 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_662986 : Nat := 118140960795 + 662986 * 2 ^ 59
def prefixEnd_662986 : Nat := 4983230072969 + 3 ^ 40 * 662986 * 2
def baseEnd_662986 : Nat := 302604875734976264823101

theorem tailTrace_662986 : CollatzResearch.WordTrace tailWord_662986 prefixEnd_662986 302604875734976264823101 := by
  unfold tailWord_662986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045271494030606459822203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16120723984081617226192541 6045271494030606459822203)
  ·
    refine ⟨9067907241045909689733305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6045271494030606459822203 9067907241045909689733305)
    ·
      refine ⟨6800930430784432267299979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9067907241045909689733305 6800930430784432267299979)
      ·
        refine ⟨10201395646176648400949969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6800930430784432267299979 10201395646176648400949969)
        ·
          refine ⟨7651046734632486300712477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10201395646176648400949969 7651046734632486300712477)
          ·
            refine ⟨2869142525487182362767179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7651046734632486300712477 2869142525487182362767179)
            ·
              refine ⟨4303713788230773544150769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869142525487182362767179 4303713788230773544150769)
              ·
                refine ⟨3227785341173080158113077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303713788230773544150769 3227785341173080158113077)
                ·
                  refine ⟨302604875734976264823101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227785341173080158113077 302604875734976264823101)
                  ·
                    rfl

theorem cell20_662986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_662986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662986 prefixEnd_662986 := by exact prefixLift 662986
  have htrace : WordTrace (prefixWord ++ tailWord_662986) baseStart_662986 baseEnd_662986 := by
    simpa [prefixWord, tailWord_662986, baseEnd_662986] using wordTrace_append hprefix tailTrace_662986
  have hstable : (prefixWord ++ tailWord_662986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662986).length < 2 ^ (prefixWord ++ tailWord_662986).sum := by decide
  have hdescent : baseEnd_662986 < baseStart_662986 := by decide
  rcases family_descends (prefixWord ++ tailWord_662986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662996 : List Nat := [2, 4, 1, 2, 3, 2, 6]
def baseStart_662996 : Nat := 118140960795 + 662996 * 2 ^ 59
def prefixEnd_662996 : Nat := 4983230072969 + 3 ^ 40 * 662996 * 2
def baseEnd_662996 : Nat := 33623271111940074943303

theorem tailTrace_662996 : CollatzResearch.WordTrace tailWord_662996 prefixEnd_662996 33623271111940074943303 := by
  unfold tailWord_662996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090725353043098773576421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16120967137390798364768561 12090725353043098773576421)
  ·
    refine ⟨2267011003695581020045579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12090725353043098773576421 2267011003695581020045579)
    ·
      refine ⟨3400516505543371530068369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267011003695581020045579 3400516505543371530068369)
      ·
        refine ⟨2550387379157528647551277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3400516505543371530068369 2550387379157528647551277)
        ·
          refine ⟨956395267184073242831729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2550387379157528647551277 956395267184073242831729)
          ·
            refine ⟨717296450388054932123797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956395267184073242831729 717296450388054932123797)
            ·
              refine ⟨33623271111940074943303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 717296450388054932123797 33623271111940074943303)
              ·
                rfl

theorem cell20_662996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 6].length) (baseStart_662996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_662996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_662996 prefixEnd_662996 := by exact prefixLift 662996
  have htrace : WordTrace (prefixWord ++ tailWord_662996) baseStart_662996 baseEnd_662996 := by
    simpa [prefixWord, tailWord_662996, baseEnd_662996] using wordTrace_append hprefix tailTrace_662996
  have hstable : (prefixWord ++ tailWord_662996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662996).length < 2 ^ (prefixWord ++ tailWord_662996).sum := by decide
  have hdescent : baseEnd_662996 < baseStart_662996 := by decide
  rcases family_descends (prefixWord ++ tailWord_662996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663000 : List Nat := [2, 1, 2, 2, 2, 1, 10]
def baseStart_663000 : Nat := 118140960795 + 663000 * 2 ^ 59
def prefixEnd_663000 : Nat := 4983230072969 + 3 ^ 40 * 663000 * 2
def baseEnd_663000 : Nat := 33623473968494937595153

theorem tailTrace_663000 : CollatzResearch.WordTrace tailWord_663000 prefixEnd_663000 33623473968494937595153 := by
  unfold tailWord_663000
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090798299035853115149227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16121064398714470820198969 12090798299035853115149227)
  ·
    refine ⟨18136197448553779672723841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090798299035853115149227 18136197448553779672723841)
    ·
      refine ⟨13602148086415334754542881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18136197448553779672723841 13602148086415334754542881)
      ·
        refine ⟨10201611064811501065907161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13602148086415334754542881 10201611064811501065907161)
        ·
          refine ⟨7651208298608625799430371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10201611064811501065907161 7651208298608625799430371)
          ·
            refine ⟨11476812447912938699145557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651208298608625799430371 11476812447912938699145557)
            ·
              refine ⟨33623473968494937595153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11476812447912938699145557 33623473968494937595153)
              ·
                rfl

theorem cell20_663000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_663000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663000 prefixEnd_663000 := by exact prefixLift 663000
  have htrace : WordTrace (prefixWord ++ tailWord_663000) baseStart_663000 baseEnd_663000 := by
    simpa [prefixWord, tailWord_663000, baseEnd_663000] using wordTrace_append hprefix tailTrace_663000
  have hstable : (prefixWord ++ tailWord_663000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663000).length < 2 ^ (prefixWord ++ tailWord_663000).sum := by decide
  have hdescent : baseEnd_663000 < baseStart_663000 := by decide
  rcases family_descends (prefixWord ++ tailWord_663000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663072 : List Nat := [2, 1, 1, 6, 1, 3, 1, 5]
def baseStart_663072 : Nat := 118140960795 + 663072 * 2 ^ 59
def prefixEnd_663072 : Nat := 4983230072969 + 3 ^ 40 * 663072 * 2
def baseEnd_663072 : Nat := 100881376159447395985361

theorem tailTrace_663072 : CollatzResearch.WordTrace tailWord_663072 prefixEnd_663072 100881376159447395985361 := by
  unfold tailWord_663072
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092111326905431263459735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16122815102540575017946313 12092111326905431263459735)
  ·
    refine ⟨18138166990358146895189603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12092111326905431263459735 18138166990358146895189603)
    ·
      refine ⟨27207250485537220342784405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18138166990358146895189603 27207250485537220342784405)
      ·
        refine ⟨1275339866509557203568019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27207250485537220342784405 1275339866509557203568019)
        ·
          refine ⟨1913009799764335805352029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275339866509557203568019 1913009799764335805352029)
          ·
            refine ⟨717378674911625927007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1913009799764335805352029 717378674911625927007011)
            ·
              refine ⟨1076068012367438890510517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717378674911625927007011 1076068012367438890510517)
              ·
                refine ⟨100881376159447395985361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1076068012367438890510517 100881376159447395985361)
                ·
                  rfl

theorem cell20_663072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_663072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663072 prefixEnd_663072 := by exact prefixLift 663072
  have htrace : WordTrace (prefixWord ++ tailWord_663072) baseStart_663072 baseEnd_663072 := by
    simpa [prefixWord, tailWord_663072, baseEnd_663072] using wordTrace_append hprefix tailTrace_663072
  have hstable : (prefixWord ++ tailWord_663072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663072).length < 2 ^ (prefixWord ++ tailWord_663072).sum := by decide
  have hdescent : baseEnd_663072 < baseStart_663072 := by decide
  rcases family_descends (prefixWord ++ tailWord_663072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663083 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_663083 : Nat := 118140960795 + 663083 * 2 ^ 59
def prefixEnd_663083 : Nat := 4983230072969 + 3 ^ 40 * 663083 * 2
def baseEnd_663083 : Nat := 302649149178075038589371

theorem tailTrace_663083 : CollatzResearch.WordTrace tailWord_663083 prefixEnd_663083 302649149178075038589371 := by
  unfold tailWord_663083
  simp only [CollatzResearch.WordTrace]
  refine ⟨24184623856771011405569903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16123082571180674270379935 24184623856771011405569903)
  ·
    refine ⟨36276935785156517108354855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24184623856771011405569903 36276935785156517108354855)
    ·
      refine ⟨54415403677734775662532283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36276935785156517108354855 54415403677734775662532283)
      ·
        refine ⟨81623105516602163493798425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54415403677734775662532283 81623105516602163493798425)
        ·
          refine ⟨61217329137451622620348819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81623105516602163493798425 61217329137451622620348819)
          ·
            refine ⟨91825993706177433930523229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61217329137451622620348819 91825993706177433930523229)
            ·
              refine ⟨34434747639816537723946211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91825993706177433930523229 34434747639816537723946211)
              ·
                refine ⟨51652121459724806585919317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34434747639816537723946211 51652121459724806585919317)
                ·
                  refine ⟨302649149178075038589371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51652121459724806585919317 302649149178075038589371)
                  ·
                    rfl

theorem cell20_663083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_663083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663083 prefixEnd_663083 := by exact prefixLift 663083
  have htrace : WordTrace (prefixWord ++ tailWord_663083) baseStart_663083 baseEnd_663083 := by
    simpa [prefixWord, tailWord_663083, baseEnd_663083] using wordTrace_append hprefix tailTrace_663083
  have hstable : (prefixWord ++ tailWord_663083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663083).length < 2 ^ (prefixWord ++ tailWord_663083).sum := by decide
  have hdescent : baseEnd_663083 < baseStart_663083 := by decide
  rcases family_descends (prefixWord ++ tailWord_663083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663086 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_663086 : Nat := 118140960795 + 663086 * 2 ^ 59
def prefixEnd_663086 : Nat := 4983230072969 + 3 ^ 40 * 663086 * 2
def baseEnd_663086 : Nat := 302650518459820361489359

theorem tailTrace_663086 : CollatzResearch.WordTrace tailWord_663086 prefixEnd_663086 302650518459820361489359 := by
  unfold tailWord_663086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023091659470017864741139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16123155517173428611952741 3023091659470017864741139)
  ·
    refine ⟨4534637489205026797111709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3023091659470017864741139 4534637489205026797111709)
    ·
      refine ⟨1700489058451885048916891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4534637489205026797111709 1700489058451885048916891)
      ·
        refine ⟨2550733587677827573375337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700489058451885048916891 2550733587677827573375337)
        ·
          refine ⟨1913050190758370680031503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2550733587677827573375337 1913050190758370680031503)
          ·
            refine ⟨2869575286137556020047255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913050190758370680031503 2869575286137556020047255)
            ·
              refine ⟨4304362929206334030070883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869575286137556020047255 4304362929206334030070883)
              ·
                refine ⟨6456544393809501045106325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304362929206334030070883 6456544393809501045106325)
                ·
                  refine ⟨302650518459820361489359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6456544393809501045106325 302650518459820361489359)
                  ·
                    rfl

theorem cell20_663086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_663086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663086 prefixEnd_663086 := by exact prefixLift 663086
  have htrace : WordTrace (prefixWord ++ tailWord_663086) baseStart_663086 baseEnd_663086 := by
    simpa [prefixWord, tailWord_663086, baseEnd_663086] using wordTrace_append hprefix tailTrace_663086
  have hstable : (prefixWord ++ tailWord_663086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663086).length < 2 ^ (prefixWord ++ tailWord_663086).sum := by decide
  have hdescent : baseEnd_663086 < baseStart_663086 := by decide
  rcases family_descends (prefixWord ++ tailWord_663086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663103 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 2]
def baseStart_663103 : Nat := 118140960795 + 663103 * 2 ^ 59
def prefixEnd_663103 : Nat := 4983230072969 + 3 ^ 40 * 663103 * 2
def baseEnd_663103 : Nat := 302658277723043857922623

theorem tailTrace_663103 : CollatzResearch.WordTrace tailWord_663103 prefixEnd_663103 302658277723043857922623 := by
  unfold tailWord_663103
  simp only [CollatzResearch.WordTrace]
  refine ⟨24185353316698554821297963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16123568877799036547531975 24185353316698554821297963)
  ·
    refine ⟨36278029975047832231946945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24185353316698554821297963 36278029975047832231946945)
    ·
      refine ⟨27208522481285874173960209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36278029975047832231946945 27208522481285874173960209)
      ·
        refine ⟨20406391860964405630470157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27208522481285874173960209 20406391860964405630470157)
        ·
          refine ⟨7652396947861652111426309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20406391860964405630470157 7652396947861652111426309)
          ·
            refine ⟨1434824427724059770892433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7652396947861652111426309 1434824427724059770892433)
            ·
              refine ⟨1076118320793044828169325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434824427724059770892433 1076118320793044828169325)
              ·
                refine ⟨403544370297391810563497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076118320793044828169325 403544370297391810563497)
                ·
                  refine ⟨302658277723043857922623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403544370297391810563497 302658277723043857922623)
                  ·
                    rfl

theorem cell20_663103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 2].length) (baseStart_663103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663103 prefixEnd_663103 := by exact prefixLift 663103
  have htrace : WordTrace (prefixWord ++ tailWord_663103) baseStart_663103 baseEnd_663103 := by
    simpa [prefixWord, tailWord_663103, baseEnd_663103] using wordTrace_append hprefix tailTrace_663103
  have hstable : (prefixWord ++ tailWord_663103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663103).length < 2 ^ (prefixWord ++ tailWord_663103).sum := by decide
  have hdescent : baseEnd_663103 < baseStart_663103 := by decide
  rcases family_descends (prefixWord ++ tailWord_663103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663114 : List Nat := [3, 1, 2, 1, 1, 3, 9]
def baseStart_663114 : Nat := 118140960795 + 663114 * 2 ^ 59
def prefixEnd_663114 : Nat := 4983230072969 + 3 ^ 40 * 663114 * 2
def baseEnd_663114 : Nat := 33629255380308523172879

theorem tailTrace_663114 : CollatzResearch.WordTrace tailWord_663114 prefixEnd_663114 33629255380308523172879 := by
  unfold tailWord_663114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046438629914675924987099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16123836346439135799965597 6046438629914675924987099)
  ·
    refine ⟨9069657944872013887480649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6046438629914675924987099 9069657944872013887480649)
    ·
      refine ⟨6802243458654010415610487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9069657944872013887480649 6802243458654010415610487)
      ·
        refine ⟨10203365187981015623415731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802243458654010415610487 10203365187981015623415731)
        ·
          refine ⟨15305047781971523435123597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203365187981015623415731 15305047781971523435123597)
          ·
            refine ⟨5739392918239321288171349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15305047781971523435123597 5739392918239321288171349)
            ·
              refine ⟨33629255380308523172879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5739392918239321288171349 33629255380308523172879)
              ·
                rfl

theorem cell20_663114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_663114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663114 prefixEnd_663114 := by exact prefixLift 663114
  have htrace : WordTrace (prefixWord ++ tailWord_663114) baseStart_663114 baseEnd_663114 := by
    simpa [prefixWord, tailWord_663114, baseEnd_663114] using wordTrace_append hprefix tailTrace_663114
  have hstable : (prefixWord ++ tailWord_663114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663114).length < 2 ^ (prefixWord ++ tailWord_663114).sum := by decide
  have hdescent : baseEnd_663114 < baseStart_663114 := by decide
  rcases family_descends (prefixWord ++ tailWord_663114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663124 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_663124 : Nat := 118140960795 + 663124 * 2 ^ 59
def prefixEnd_663124 : Nat := 4983230072969 + 3 ^ 40 * 663124 * 2
def baseEnd_663124 : Nat := 302667862695261118222537

theorem tailTrace_663124 : CollatzResearch.WordTrace tailWord_663124 prefixEnd_663124 302667862695261118222537 := by
  unfold tailWord_663124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12093059624811237703906213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16124079499748316938541617 12093059624811237703906213)
  ·
    refine ⟨2267448679652107069482415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12093059624811237703906213 2267448679652107069482415)
    ·
      refine ⟨3401173019478160604223623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267448679652107069482415 3401173019478160604223623)
      ·
        refine ⟨5101759529217240906335435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401173019478160604223623 5101759529217240906335435)
        ·
          refine ⟨7652639293825861359503153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101759529217240906335435 7652639293825861359503153)
          ·
            refine ⟨5739479470369396019627365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7652639293825861359503153 5739479470369396019627365)
            ·
              refine ⟨1076152400694261753680131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5739479470369396019627365 1076152400694261753680131)
              ·
                refine ⟨1614228601041392630520197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076152400694261753680131 1614228601041392630520197)
                ·
                  refine ⟨302667862695261118222537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614228601041392630520197 302667862695261118222537)
                  ·
                    rfl

theorem cell20_663124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_663124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663124 prefixEnd_663124 := by exact prefixLift 663124
  have htrace : WordTrace (prefixWord ++ tailWord_663124) baseStart_663124 baseEnd_663124 := by
    simpa [prefixWord, tailWord_663124, baseEnd_663124] using wordTrace_append hprefix tailTrace_663124
  have hstable : (prefixWord ++ tailWord_663124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663124).length < 2 ^ (prefixWord ++ tailWord_663124).sum := by decide
  have hdescent : baseEnd_663124 < baseStart_663124 := by decide
  rcases family_descends (prefixWord ++ tailWord_663124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663145 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_663145 : Nat := 118140960795 + 663145 * 2 ^ 59
def prefixEnd_663145 : Nat := 4983230072969 + 3 ^ 40 * 663145 * 2
def baseEnd_663145 : Nat := 302677447667478378522451

theorem tailTrace_663145 : CollatzResearch.WordTrace tailWord_663145 prefixEnd_663145 302677447667478378522451 := by
  unfold tailWord_663145
  simp only [CollatzResearch.WordTrace]
  refine ⟨24186885182546395994326889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16124590121697597329551259 24186885182546395994326889)
  ·
    refine ⟨18140163886909796995745167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24186885182546395994326889 18140163886909796995745167)
    ·
      refine ⟨27210245830364695493617751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18140163886909796995745167 27210245830364695493617751)
      ·
        refine ⟨40815368745547043240426627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27210245830364695493617751 40815368745547043240426627)
        ·
          refine ⟨61223053118320564860639941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40815368745547043240426627 61223053118320564860639941)
          ·
            refine ⟨11479322459685105911369989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61223053118320564860639941 11479322459685105911369989)
            ·
              refine ⟨2152372961190957358381873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11479322459685105911369989 2152372961190957358381873)
              ·
                refine ⟨1614279720893218018786405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152372961190957358381873 1614279720893218018786405)
                ·
                  refine ⟨302677447667478378522451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614279720893218018786405 302677447667478378522451)
                  ·
                    rfl

theorem cell20_663145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_663145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663145 prefixEnd_663145 := by exact prefixLift 663145
  have htrace : WordTrace (prefixWord ++ tailWord_663145) baseStart_663145 baseEnd_663145 := by
    simpa [prefixWord, tailWord_663145, baseEnd_663145] using wordTrace_append hprefix tailTrace_663145
  have hstable : (prefixWord ++ tailWord_663145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663145).length < 2 ^ (prefixWord ++ tailWord_663145).sum := by decide
  have hdescent : baseEnd_663145 < baseStart_663145 := by decide
  rcases family_descends (prefixWord ++ tailWord_663145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663158 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_663158 : Nat := 118140960795 + 663158 * 2 ^ 59
def prefixEnd_663158 : Nat := 4983230072969 + 3 ^ 40 * 663158 * 2
def baseEnd_663158 : Nat := 302683381221708111089065

theorem tailTrace_663158 : CollatzResearch.WordTrace tailWord_663158 prefixEnd_663158 302683381221708111089065 := by
  unfold tailWord_663158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511709958218706200909383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16124906220999532809700085 1511709958218706200909383)
  ·
    refine ⟨2267564937328059301364075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511709958218706200909383 2267564937328059301364075)
    ·
      refine ⟨3401347405992088952046113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267564937328059301364075 3401347405992088952046113)
      ·
        refine ⟨2551010554494066714034585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3401347405992088952046113 2551010554494066714034585)
        ·
          refine ⟨1913257915870550035525939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551010554494066714034585 1913257915870550035525939)
          ·
            refine ⟨2869886873805825053288909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913257915870550035525939 2869886873805825053288909)
            ·
              refine ⟨1076207577677184394983341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2869886873805825053288909 1076207577677184394983341)
              ·
                refine ⟨403577841628944148118753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076207577677184394983341 403577841628944148118753)
                ·
                  refine ⟨302683381221708111089065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403577841628944148118753 302683381221708111089065)
                  ·
                    rfl

theorem cell20_663158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_663158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663158 prefixEnd_663158 := by exact prefixLift 663158
  have htrace : WordTrace (prefixWord ++ tailWord_663158) baseStart_663158 baseEnd_663158 := by
    simpa [prefixWord, tailWord_663158, baseEnd_663158] using wordTrace_append hprefix tailTrace_663158
  have hstable : (prefixWord ++ tailWord_663158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663158).length < 2 ^ (prefixWord ++ tailWord_663158).sum := by decide
  have hdescent : baseEnd_663158 < baseStart_663158 := by decide
  rcases family_descends (prefixWord ++ tailWord_663158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_663162 : Nat := 118140960795 + 663162 * 2 ^ 59
def prefixEnd_663162 : Nat := 4983230072969 + 3 ^ 40 * 663162 * 2
def baseEnd_663162 : Nat := 302685206930701874955715

theorem tailTrace_663162 : CollatzResearch.WordTrace tailWord_663162 prefixEnd_663162 302685206930701874955715 := by
  unfold tailWord_663162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046876305871201974423935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16125003482323205265130493 6046876305871201974423935)
  ·
    refine ⟨9070314458806802961635903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6046876305871201974423935 9070314458806802961635903)
    ·
      refine ⟨13605471688210204442453855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9070314458806802961635903 13605471688210204442453855)
      ·
        refine ⟨20408207532315306663680783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13605471688210204442453855 20408207532315306663680783)
        ·
          refine ⟨30612311298472959995521175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20408207532315306663680783 30612311298472959995521175)
          ·
            refine ⟨45918466947709439993281763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30612311298472959995521175 45918466947709439993281763)
            ·
              refine ⟨68877700421564159989922645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45918466947709439993281763 68877700421564159989922645)
              ·
                refine ⟨403580275907602499940953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 68877700421564159989922645 403580275907602499940953)
                ·
                  refine ⟨302685206930701874955715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403580275907602499940953 302685206930701874955715)
                  ·
                    rfl

theorem cell20_663162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_663162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663162 prefixEnd_663162 := by exact prefixLift 663162
  have htrace : WordTrace (prefixWord ++ tailWord_663162) baseStart_663162 baseEnd_663162 := by
    simpa [prefixWord, tailWord_663162, baseEnd_663162] using wordTrace_append hprefix tailTrace_663162
  have hstable : (prefixWord ++ tailWord_663162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663162).length < 2 ^ (prefixWord ++ tailWord_663162).sum := by decide
  have hdescent : baseEnd_663162 < baseStart_663162 := by decide
  rcases family_descends (prefixWord ++ tailWord_663162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663169 : List Nat := [1, 2, 4, 2, 1, 4, 6]
def baseStart_663169 : Nat := 118140960795 + 663169 * 2 ^ 59
def prefixEnd_663169 : Nat := 4983230072969 + 3 ^ 40 * 663169 * 2
def baseEnd_663169 : Nat := 33632044657937884635817

theorem tailTrace_663169 : CollatzResearch.WordTrace tailWord_663169 prefixEnd_663169 33632044657937884635817 := by
  unfold tailWord_663169
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187760534459448093200561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16125173689639632062133707 24187760534459448093200561)
  ·
    refine ⟨18140820400844586069900421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24187760534459448093200561 18140820400844586069900421)
    ·
      refine ⟨3401403825158359888106329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18140820400844586069900421 3401403825158359888106329)
      ·
        refine ⟨2551052868868769916079747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3401403825158359888106329 2551052868868769916079747)
        ·
          refine ⟨3826579303303154874119621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551052868868769916079747 3826579303303154874119621)
          ·
            refine ⟨717483619369341538897429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3826579303303154874119621 717483619369341538897429)
            ·
              refine ⟨33632044657937884635817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 717483619369341538897429 33632044657937884635817)
              ·
                rfl

theorem cell20_663169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_663169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663169 prefixEnd_663169 := by exact prefixLift 663169
  have htrace : WordTrace (prefixWord ++ tailWord_663169) baseStart_663169 baseEnd_663169 := by
    simpa [prefixWord, tailWord_663169, baseEnd_663169] using wordTrace_append hprefix tailTrace_663169
  have hstable : (prefixWord ++ tailWord_663169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663169).length < 2 ^ (prefixWord ++ tailWord_663169).sum := by decide
  have hdescent : baseEnd_663169 < baseStart_663169 := by decide
  rcases family_descends (prefixWord ++ tailWord_663169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663179 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 2]
def baseStart_663179 : Nat := 118140960795 + 663179 * 2 ^ 59
def prefixEnd_663179 : Nat := 4983230072969 + 3 ^ 40 * 663179 * 2
def baseEnd_663179 : Nat := 302692966193925371388979

theorem tailTrace_663179 : CollatzResearch.WordTrace tailWord_663179 prefixEnd_663179 302692966193925371388979 := by
  unfold tailWord_663179
  simp only [CollatzResearch.WordTrace]
  refine ⟨24188125264423219801064591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16125416842948813200709727 24188125264423219801064591)
  ·
    refine ⟨36282187896634829701596887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24188125264423219801064591 36282187896634829701596887)
    ·
      refine ⟨54423281844952244552395331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36282187896634829701596887 54423281844952244552395331)
      ·
        refine ⟨81634922767428366828592997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54423281844952244552395331 81634922767428366828592997)
        ·
          refine ⟨15306548018892818780361187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81634922767428366828592997 15306548018892818780361187)
          ·
            refine ⟨22959822028339228170541781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15306548018892818780361187 22959822028339228170541781)
            ·
              refine ⟨538120828789200660247073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22959822028339228170541781 538120828789200660247073)
              ·
                refine ⟨403590621591900495185305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538120828789200660247073 403590621591900495185305)
                ·
                  refine ⟨302692966193925371388979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403590621591900495185305 302692966193925371388979)
                  ·
                    rfl

theorem cell20_663179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 2].length) (baseStart_663179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663179 prefixEnd_663179 := by exact prefixLift 663179
  have htrace : WordTrace (prefixWord ++ tailWord_663179) baseStart_663179 baseEnd_663179 := by
    simpa [prefixWord, tailWord_663179, baseEnd_663179] using wordTrace_append hprefix tailTrace_663179
  have hstable : (prefixWord ++ tailWord_663179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663179).length < 2 ^ (prefixWord ++ tailWord_663179).sum := by decide
  have hdescent : baseEnd_663179 < baseStart_663179 := by decide
  rcases family_descends (prefixWord ++ tailWord_663179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663186 : List Nat := [3, 2, 3, 1, 3, 1, 2, 5]
def baseStart_663186 : Nat := 118140960795 + 663186 * 2 ^ 59
def prefixEnd_663186 : Nat := 4983230072969 + 3 ^ 40 * 663186 * 2
def baseEnd_663186 : Nat := 100898720394888152718539

theorem tailTrace_663186 : CollatzResearch.WordTrace tailWord_663186 prefixEnd_663186 100898720394888152718539 := by
  unfold tailWord_663186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047095143849464999142353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16125587050265239997712941 6047095143849464999142353)
  ·
    refine ⟨4535321357887098749356765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6047095143849464999142353 4535321357887098749356765)
    ·
      refine ⟨1700745509207662031008787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4535321357887098749356765 1700745509207662031008787)
      ·
        refine ⟨2551118263811493046513181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700745509207662031008787 2551118263811493046513181)
        ·
          refine ⟨956669348929309892442443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2551118263811493046513181 956669348929309892442443)
          ·
            refine ⟨1435004023393964838663665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956669348929309892442443 1435004023393964838663665)
            ·
              refine ⟨1076253017545473628997749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435004023393964838663665 1076253017545473628997749)
              ·
                refine ⟨100898720394888152718539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1076253017545473628997749 100898720394888152718539)
                ·
                  rfl

theorem cell20_663186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_663186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663186 prefixEnd_663186 := by exact prefixLift 663186
  have htrace : WordTrace (prefixWord ++ tailWord_663186) baseStart_663186 baseEnd_663186 := by
    simpa [prefixWord, tailWord_663186, baseEnd_663186] using wordTrace_append hprefix tailTrace_663186
  have hstable : (prefixWord ++ tailWord_663186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663186).length < 2 ^ (prefixWord ++ tailWord_663186).sum := by decide
  have hdescent : baseEnd_663186 < baseStart_663186 := by decide
  rcases family_descends (prefixWord ++ tailWord_663186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663228 : List Nat := [2, 2, 2, 3, 1, 10]
def baseStart_663228 : Nat := 118140960795 + 663228 * 2 ^ 59
def prefixEnd_663228 : Nat := 4983230072969 + 3 ^ 40 * 663228 * 2
def baseEnd_663228 : Nat := 11211678930707369583535

theorem tailTrace_663228 : CollatzResearch.WordTrace tailWord_663228 prefixEnd_663228 11211678930707369583535 := by
  unfold tailWord_663228
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094956220622850584799169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16126608294163800779732225 12094956220622850584799169)
  ·
    refine ⟨9071217165467137938599377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12094956220622850584799169 9071217165467137938599377)
    ·
      refine ⟨6803412874100353453949533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9071217165467137938599377 6803412874100353453949533)
      ·
        refine ⟨2551279827787632545231075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6803412874100353453949533 2551279827787632545231075)
        ·
          refine ⟨3826919741681448817846613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551279827787632545231075 3826919741681448817846613)
          ·
            refine ⟨11211678930707369583535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3826919741681448817846613 11211678930707369583535)
            ·
              rfl

theorem cell20_663228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 10].length) (baseStart_663228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663228 prefixEnd_663228 := by exact prefixLift 663228
  have htrace : WordTrace (prefixWord ++ tailWord_663228) baseStart_663228 baseEnd_663228 := by
    simpa [prefixWord, tailWord_663228, baseEnd_663228] using wordTrace_append hprefix tailTrace_663228
  have hstable : (prefixWord ++ tailWord_663228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663228).length < 2 ^ (prefixWord ++ tailWord_663228).sum := by decide
  have hdescent : baseEnd_663228 < baseStart_663228 := by decide
  rcases family_descends (prefixWord ++ tailWord_663228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663273 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_663273 : Nat := 118140960795 + 663273 * 2 ^ 59
def prefixEnd_663273 : Nat := 4983230072969 + 3 ^ 40 * 663273 * 2
def baseEnd_663273 : Nat := 302735870355278822255261

theorem tailTrace_663273 : CollatzResearch.WordTrace tailWord_663273 prefixEnd_663273 302735870355278822255261 := by
  unfold tailWord_663273
  simp only [CollatzResearch.WordTrace]
  refine ⟨24191553726082673854986473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16127702484055115903324315 24191553726082673854986473)
  ·
    refine ⟨18143665294562005391239855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24191553726082673854986473 18143665294562005391239855)
    ·
      refine ⟨27215497941843008086859783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18143665294562005391239855 27215497941843008086859783)
      ·
        refine ⟨40823246912764512130289675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27215497941843008086859783 40823246912764512130289675)
        ·
          refine ⟨61234870369146768195434513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40823246912764512130289675 61234870369146768195434513)
          ·
            refine ⟨45926152776860076146575885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61234870369146768195434513 45926152776860076146575885)
            ·
              refine ⟨17222307291322528554965957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45926152776860076146575885 17222307291322528554965957)
              ·
                refine ⟨3229182617122974104056117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17222307291322528554965957 3229182617122974104056117)
                ·
                  refine ⟨302735870355278822255261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3229182617122974104056117 302735870355278822255261)
                  ·
                    rfl

theorem cell20_663273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_663273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663273 prefixEnd_663273 := by exact prefixLift 663273
  have htrace : WordTrace (prefixWord ++ tailWord_663273) baseStart_663273 baseEnd_663273 := by
    simpa [prefixWord, tailWord_663273, baseEnd_663273] using wordTrace_append hprefix tailTrace_663273
  have hstable : (prefixWord ++ tailWord_663273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663273).length < 2 ^ (prefixWord ++ tailWord_663273).sum := by decide
  have hdescent : baseEnd_663273 < baseStart_663273 := by decide
  rcases family_descends (prefixWord ++ tailWord_663273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663276 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 2]
def baseStart_663276 : Nat := 118140960795 + 663276 * 2 ^ 59
def prefixEnd_663276 : Nat := 4983230072969 + 3 ^ 40 * 663276 * 2
def baseEnd_663276 : Nat := 302737239637024145155249

theorem tailTrace_663276 : CollatzResearch.WordTrace tailWord_663276 prefixEnd_663276 302737239637024145155249 := by
  unfold tailWord_663276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095831572535902683672841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16127775430047870244897121 12095831572535902683672841)
  ·
    refine ⟨9071873679401927012754631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12095831572535902683672841 9071873679401927012754631)
    ·
      refine ⟨13607810519102890519131947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9071873679401927012754631 13607810519102890519131947)
      ·
        refine ⟨20411715778654335778697921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13607810519102890519131947 20411715778654335778697921)
        ·
          refine ⟨15308786833990751834023441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20411715778654335778697921 15308786833990751834023441)
          ·
            refine ⟨11481590125493063875517581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15308786833990751834023441 11481590125493063875517581)
            ·
              refine ⟨4305596297059898953319093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11481590125493063875517581 4305596297059898953319093)
              ·
                refine ⟨403649652849365526873665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4305596297059898953319093 403649652849365526873665)
                ·
                  refine ⟨302737239637024145155249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403649652849365526873665 302737239637024145155249)
                  ·
                    rfl

theorem cell20_663276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_663276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663276 prefixEnd_663276 := by exact prefixLift 663276
  have htrace : WordTrace (prefixWord ++ tailWord_663276) baseStart_663276 baseEnd_663276 := by
    simpa [prefixWord, tailWord_663276, baseEnd_663276] using wordTrace_append hprefix tailTrace_663276
  have hstable : (prefixWord ++ tailWord_663276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663276).length < 2 ^ (prefixWord ++ tailWord_663276).sum := by decide
  have hdescent : baseEnd_663276 < baseStart_663276 := by decide
  rcases family_descends (prefixWord ++ tailWord_663276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663286 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_663286 : Nat := 118140960795 + 663286 * 2 ^ 59
def prefixEnd_663286 : Nat := 4983230072969 + 3 ^ 40 * 663286 * 2
def baseEnd_663286 : Nat := 302741803909508554821875

theorem tailTrace_663286 : CollatzResearch.WordTrace tailWord_663286 prefixEnd_663286 302741803909508554821875 := by
  unfold tailWord_663286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512001742189723567200607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16128018583357051383473141 1512001742189723567200607)
  ·
    refine ⟨2268002613284585350800911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512001742189723567200607 2268002613284585350800911)
    ·
      refine ⟨3402003919926878026201367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268002613284585350800911 3402003919926878026201367)
      ·
        refine ⟨5103005879890317039302051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402003919926878026201367 5103005879890317039302051)
        ·
          refine ⟨7654508819835475558953077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103005879890317039302051 7654508819835475558953077)
          ·
            refine ⟨717610201859575833651851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7654508819835475558953077 717610201859575833651851)
            ·
              refine ⟨1076415302789363750477777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717610201859575833651851 1076415302789363750477777)
              ·
                refine ⟨807311477092022812858333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076415302789363750477777 807311477092022812858333)
                ·
                  refine ⟨302741803909508554821875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807311477092022812858333 302741803909508554821875)
                  ·
                    rfl

theorem cell20_663286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_663286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663286 prefixEnd_663286 := by exact prefixLift 663286
  have htrace : WordTrace (prefixWord ++ tailWord_663286) baseStart_663286 baseEnd_663286 := by
    simpa [prefixWord, tailWord_663286, baseEnd_663286] using wordTrace_append hprefix tailTrace_663286
  have hstable : (prefixWord ++ tailWord_663286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663286).length < 2 ^ (prefixWord ++ tailWord_663286).sum := by decide
  have hdescent : baseEnd_663286 < baseStart_663286 := by decide
  rcases family_descends (prefixWord ++ tailWord_663286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663297 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_663297 : Nat := 118140960795 + 663297 * 2 ^ 59
def prefixEnd_663297 : Nat := 4983230072969 + 3 ^ 40 * 663297 * 2
def baseEnd_663297 : Nat := 302746824609241405455163

theorem tailTrace_663297 : CollatzResearch.WordTrace tailWord_663297 prefixEnd_663297 302746824609241405455163 := by
  unfold tailWord_663297
  simp only [CollatzResearch.WordTrace]
  refine ⟨24192429077995725953860145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16128286051997150635906763 24192429077995725953860145)
  ·
    refine ⟨18144321808496794465395109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24192429077995725953860145 18144321808496794465395109)
    ·
      refine ⟨3402060339093148962261583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18144321808496794465395109 3402060339093148962261583)
      ·
        refine ⟨5103090508639723443392375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402060339093148962261583 5103090508639723443392375)
        ·
          refine ⟨7654635762959585165088563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103090508639723443392375 7654635762959585165088563)
          ·
            refine ⟨11481953644439377747632845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654635762959585165088563 11481953644439377747632845)
            ·
              refine ⟨4305732616664766655362317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11481953644439377747632845 4305732616664766655362317)
              ·
                refine ⟨1614649731249287495760869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4305732616664766655362317 1614649731249287495760869)
                ·
                  refine ⟨302746824609241405455163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614649731249287495760869 302746824609241405455163)
                  ·
                    rfl

theorem cell20_663297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_663297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663297 prefixEnd_663297 := by exact prefixLift 663297
  have htrace : WordTrace (prefixWord ++ tailWord_663297) baseStart_663297 baseEnd_663297 := by
    simpa [prefixWord, tailWord_663297, baseEnd_663297] using wordTrace_append hprefix tailTrace_663297
  have hstable : (prefixWord ++ tailWord_663297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663297).length < 2 ^ (prefixWord ++ tailWord_663297).sum := by decide
  have hdescent : baseEnd_663297 < baseStart_663297 := by decide
  rcases family_descends (prefixWord ++ tailWord_663297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663304 : List Nat := [2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_663304 : Nat := 118140960795 + 663304 * 2 ^ 59
def prefixEnd_663304 : Nat := 4983230072969 + 3 ^ 40 * 663304 * 2
def baseEnd_663304 : Nat := 100916673199993497407267

theorem tailTrace_663304 : CollatzResearch.WordTrace tailWord_663304 prefixEnd_663304 100916673199993497407267 := by
  unfold tailWord_663304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12096342194485183074682483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16128456259313577432909977 12096342194485183074682483)
  ·
    refine ⟨18144513291727774612023725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12096342194485183074682483 18144513291727774612023725)
    ·
      refine ⟨6804192484397915479508897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18144513291727774612023725 6804192484397915479508897)
      ·
        refine ⟨5103144363298436609631673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6804192484397915479508897 5103144363298436609631673)
        ·
          refine ⟨3827358272473827457223755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5103144363298436609631673 3827358272473827457223755)
          ·
            refine ⟨5741037408710741185835633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827358272473827457223755 5741037408710741185835633)
            ·
              refine ⟨4305778056533055889376725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5741037408710741185835633 4305778056533055889376725)
              ·
                refine ⟨100916673199993497407267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4305778056533055889376725 100916673199993497407267)
                ·
                  rfl

theorem cell20_663304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_663304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663304 prefixEnd_663304 := by exact prefixLift 663304
  have htrace : WordTrace (prefixWord ++ tailWord_663304) baseStart_663304 baseEnd_663304 := by
    simpa [prefixWord, tailWord_663304, baseEnd_663304] using wordTrace_append hprefix tailTrace_663304
  have hstable : (prefixWord ++ tailWord_663304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663304).length < 2 ^ (prefixWord ++ tailWord_663304).sum := by decide
  have hdescent : baseEnd_663304 < baseStart_663304 := by decide
  rcases family_descends (prefixWord ++ tailWord_663304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663352 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_663352 : Nat := 118140960795 + 663352 * 2 ^ 59
def prefixEnd_663352 : Nat := 4983230072969 + 3 ^ 40 * 663352 * 2
def baseEnd_663352 : Nat := 302771928107905658621605

theorem tailTrace_663352 : CollatzResearch.WordTrace tailWord_663352 prefixEnd_663352 302771928107905658621605 := by
  unfold tailWord_663352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097217546398235173556155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16129623395197646898074873 12097217546398235173556155)
  ·
    refine ⟨18145826319597352760334233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12097217546398235173556155 18145826319597352760334233)
    ·
      refine ⟨13609369739698014570250675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18145826319597352760334233 13609369739698014570250675)
      ·
        refine ⟨20414054609547021855376013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13609369739698014570250675 20414054609547021855376013)
        ·
          refine ⟨7655270478580133195766005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20414054609547021855376013 7655270478580133195766005)
          ·
            refine ⟨717681607366887487103063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7655270478580133195766005 717681607366887487103063)
            ·
              refine ⟨1076522411050331230654595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717681607366887487103063 1076522411050331230654595)
              ·
                refine ⟨1614783616575496845981893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076522411050331230654595 1614783616575496845981893)
                ·
                  refine ⟨302771928107905658621605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614783616575496845981893 302771928107905658621605)
                  ·
                    rfl

theorem cell20_663352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_663352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663352 prefixEnd_663352 := by exact prefixLift 663352
  have htrace : WordTrace (prefixWord ++ tailWord_663352) baseStart_663352 baseEnd_663352 := by
    simpa [prefixWord, tailWord_663352, baseEnd_663352] using wordTrace_append hprefix tailTrace_663352
  have hstable : (prefixWord ++ tailWord_663352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663352).length < 2 ^ (prefixWord ++ tailWord_663352).sum := by decide
  have hdescent : baseEnd_663352 < baseStart_663352 := by decide
  rcases family_descends (prefixWord ++ tailWord_663352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663359 : List Nat := [1, 1, 2, 2, 6, 1, 2, 5]
def baseStart_663359 : Nat := 118140960795 + 663359 * 2 ^ 59
def prefixEnd_663359 : Nat := 4983230072969 + 3 ^ 40 * 663359 * 2
def baseEnd_663359 : Nat := 100925041032881581796081

theorem tailTrace_663359 : CollatzResearch.WordTrace tailWord_663359 prefixEnd_663359 100925041032881581796081 := by
  unfold tailWord_663359
  simp only [CollatzResearch.WordTrace]
  refine ⟨24194690403771110542617131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16129793602514073695078087 24194690403771110542617131)
  ·
    refine ⟨36292035605656665813925697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24194690403771110542617131 36292035605656665813925697)
    ·
      refine ⟨27219026704242499360444273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36292035605656665813925697 27219026704242499360444273)
      ·
        refine ⟨20414270028181874520333205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27219026704242499360444273 20414270028181874520333205)
        ·
          refine ⟨956918907571025368140619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20414270028181874520333205 956918907571025368140619)
          ·
            refine ⟨1435378361356538052210929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956918907571025368140619 1435378361356538052210929)
            ·
              refine ⟨1076533771017403539158197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435378361356538052210929 1076533771017403539158197)
              ·
                refine ⟨100925041032881581796081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1076533771017403539158197 100925041032881581796081)
                ·
                  rfl

theorem cell20_663359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_663359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663359 prefixEnd_663359 := by exact prefixLift 663359
  have htrace : WordTrace (prefixWord ++ tailWord_663359) baseStart_663359 baseEnd_663359 := by
    simpa [prefixWord, tailWord_663359, baseEnd_663359] using wordTrace_append hprefix tailTrace_663359
  have hstable : (prefixWord ++ tailWord_663359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663359).length < 2 ^ (prefixWord ++ tailWord_663359).sum := by decide
  have hdescent : baseEnd_663359 < baseStart_663359 := by decide
  rcases family_descends (prefixWord ++ tailWord_663359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663404 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_663404 : Nat := 118140960795 + 663404 * 2 ^ 59
def prefixEnd_663404 : Nat := 4983230072969 + 3 ^ 40 * 663404 * 2
def baseEnd_663404 : Nat := 302795662324824588888059

theorem tailTrace_663404 : CollatzResearch.WordTrace tailWord_663404 prefixEnd_663404 302795662324824588888059 := by
  unfold tailWord_663404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098165844304041614002633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16130887792405388818670177 12098165844304041614002633)
  ·
    refine ⟨9073624383228031210501975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12098165844304041614002633 9073624383228031210501975)
    ·
      refine ⟨13610436574842046815752963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073624383228031210501975 13610436574842046815752963)
      ·
        refine ⟨20415654862263070223629445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13610436574842046815752963 20415654862263070223629445)
        ·
          refine ⟨3827935286674325666930521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20415654862263070223629445 3827935286674325666930521)
          ·
            refine ⟨2870951465005744250197891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3827935286674325666930521 2870951465005744250197891)
            ·
              refine ⟨4306427197508616375296837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870951465005744250197891 4306427197508616375296837)
              ·
                refine ⟨807455099532865570368157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4306427197508616375296837 807455099532865570368157)
                ·
                  refine ⟨302795662324824588888059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807455099532865570368157 302795662324824588888059)
                  ·
                    rfl

theorem cell20_663404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_663404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663404 prefixEnd_663404 := by exact prefixLift 663404
  have htrace : WordTrace (prefixWord ++ tailWord_663404) baseStart_663404 baseEnd_663404 := by
    simpa [prefixWord, tailWord_663404, baseEnd_663404] using wordTrace_append hprefix tailTrace_663404
  have hstable : (prefixWord ++ tailWord_663404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663404).length < 2 ^ (prefixWord ++ tailWord_663404).sum := by decide
  have hdescent : baseEnd_663404 < baseStart_663404 := by decide
  rcases family_descends (prefixWord ++ tailWord_663404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663418 : List Nat := [3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_663418 : Nat := 118140960795 + 663418 * 2 ^ 59
def prefixEnd_663418 : Nat := 4983230072969 + 3 ^ 40 * 663418 * 2
def baseEnd_663418 : Nat := 100934017435434254140445

theorem tailTrace_663418 : CollatzResearch.WordTrace tailWord_663418 prefixEnd_663418 100934017435434254140445 := by
  unfold tailWord_663418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049210577639340904753727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16131228207038242412676605 6049210577639340904753727)
  ·
    refine ⟨9073815866459011357130591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6049210577639340904753727 9073815866459011357130591)
    ·
      refine ⟨13610723799688517035695887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073815866459011357130591 13610723799688517035695887)
      ·
        refine ⟨20416085699532775553543831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13610723799688517035695887 20416085699532775553543831)
        ·
          refine ⟨30624128549299163330315747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20416085699532775553543831 30624128549299163330315747)
          ·
            refine ⟨45936192823948744995473621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30624128549299163330315747 45936192823948744995473621)
            ·
              refine ⟨1076629519311298710831413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45936192823948744995473621 1076629519311298710831413)
              ·
                refine ⟨100934017435434254140445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1076629519311298710831413 100934017435434254140445)
                ·
                  rfl

theorem cell20_663418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_663418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663418 prefixEnd_663418 := by exact prefixLift 663418
  have htrace : WordTrace (prefixWord ++ tailWord_663418) baseStart_663418 baseEnd_663418 := by
    simpa [prefixWord, tailWord_663418, baseEnd_663418] using wordTrace_append hprefix tailTrace_663418
  have hstable : (prefixWord ++ tailWord_663418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663418).length < 2 ^ (prefixWord ++ tailWord_663418).sum := by decide
  have hdescent : baseEnd_663418 < baseStart_663418 := by decide
  rcases family_descends (prefixWord ++ tailWord_663418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663504 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 2]
def baseStart_663504 : Nat := 118140960795 + 663504 * 2 ^ 59
def prefixEnd_663504 : Nat := 4983230072969 + 3 ^ 40 * 663504 * 2
def baseEnd_663504 : Nat := 302841305049668685554317

theorem tailTrace_663504 : CollatzResearch.WordTrace tailWord_663504 prefixEnd_663504 302841305049668685554317 := by
  unfold tailWord_663504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12099989494122900153322783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16133319325497200204430377 12099989494122900153322783)
  ·
    refine ⟨18149984241184350229984175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12099989494122900153322783 18149984241184350229984175)
    ·
      refine ⟨27224976361776525344976263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18149984241184350229984175 27224976361776525344976263)
      ·
        refine ⟨40837464542664788017464395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27224976361776525344976263 40837464542664788017464395)
        ·
          refine ⟨61256196813997182026196593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40837464542664788017464395 61256196813997182026196593)
          ·
            refine ⟨45942147610497886519647445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61256196813997182026196593 45942147610497886519647445)
            ·
              refine ⟨1076769084621044215304237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45942147610497886519647445 1076769084621044215304237)
              ·
                refine ⟨403788406732891580739089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076769084621044215304237 403788406732891580739089)
                ·
                  refine ⟨302841305049668685554317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403788406732891580739089 302841305049668685554317)
                  ·
                    rfl

theorem cell20_663504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_663504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663504 prefixEnd_663504 := by exact prefixLift 663504
  have htrace : WordTrace (prefixWord ++ tailWord_663504) baseStart_663504 baseEnd_663504 := by
    simpa [prefixWord, tailWord_663504, baseEnd_663504] using wordTrace_append hprefix tailTrace_663504
  have hstable : (prefixWord ++ tailWord_663504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663504).length < 2 ^ (prefixWord ++ tailWord_663504).sum := by decide
  have hdescent : baseEnd_663504 < baseStart_663504 := by decide
  rcases family_descends (prefixWord ++ tailWord_663504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663572 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 2]
def baseStart_663572 : Nat := 118140960795 + 663572 * 2 ^ 59
def prefixEnd_663572 : Nat := 4983230072969 + 3 ^ 40 * 663572 * 2
def baseEnd_663572 : Nat := 302872342102562671287373

theorem tailTrace_663572 : CollatzResearch.WordTrace tailWord_663572 prefixEnd_663572 302872342102562671287373 := by
  unfold tailWord_663572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12101229575999723960060485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16134972767999631946747313 12101229575999723960060485)
  ·
    refine ⟨2268980545499948242511341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12101229575999723960060485 2268980545499948242511341)
    ·
      refine ⟨850867704562480590941753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2268980545499948242511341 850867704562480590941753)
      ·
        refine ⟨638150778421860443206315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 850867704562480590941753 638150778421860443206315)
        ·
          refine ⟨957226167632790664809473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638150778421860443206315 957226167632790664809473)
          ·
            refine ⟨717919625724592998607105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957226167632790664809473 717919625724592998607105)
            ·
              refine ⟨538439719293444748955329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717919625724592998607105 538439719293444748955329)
              ·
                refine ⟨403829789470083561716497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538439719293444748955329 403829789470083561716497)
                ·
                  refine ⟨302872342102562671287373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403829789470083561716497 302872342102562671287373)
                  ·
                    rfl

theorem cell20_663572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_663572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663572 prefixEnd_663572 := by exact prefixLift 663572
  have htrace : WordTrace (prefixWord ++ tailWord_663572) baseStart_663572 baseEnd_663572 := by
    simpa [prefixWord, tailWord_663572, baseEnd_663572] using wordTrace_append hprefix tailTrace_663572
  have hstable : (prefixWord ++ tailWord_663572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663572).length < 2 ^ (prefixWord ++ tailWord_663572).sum := by decide
  have hdescent : baseEnd_663572 < baseStart_663572 := by decide
  rcases family_descends (prefixWord ++ tailWord_663572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663573 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_663573 : Nat := 118140960795 + 663573 * 2 ^ 59
def prefixEnd_663573 : Nat := 4983230072969 + 3 ^ 40 * 663573 * 2
def baseEnd_663573 : Nat := 302872798529811112254035

theorem tailTrace_663573 : CollatzResearch.WordTrace tailWord_663573 prefixEnd_663573 302872798529811112254035 := by
  unfold tailWord_663573
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202495624995825090907373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16134997083330550060604915 24202495624995825090907373)
  ·
    refine ⟨9075935859373434409090265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24202495624995825090907373 9075935859373434409090265)
    ·
      refine ⟨6806951894530075806817699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9075935859373434409090265 6806951894530075806817699)
      ·
        refine ⟨10210427841795113710226549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806951894530075806817699 10210427841795113710226549)
        ·
          refine ⟨957227610168291910333739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10210427841795113710226549 957227610168291910333739)
          ·
            refine ⟨1435841415252437865500609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957227610168291910333739 1435841415252437865500609)
            ·
              refine ⟨1076881061439328399125457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435841415252437865500609 1076881061439328399125457)
              ·
                refine ⟨807660796079496299344093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076881061439328399125457 807660796079496299344093)
                ·
                  refine ⟨302872798529811112254035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807660796079496299344093 302872798529811112254035)
                  ·
                    rfl

theorem cell20_663573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_663573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663573 prefixEnd_663573 := by exact prefixLift 663573
  have htrace : WordTrace (prefixWord ++ tailWord_663573) baseStart_663573 baseEnd_663573 := by
    simpa [prefixWord, tailWord_663573, baseEnd_663573] using wordTrace_append hprefix tailTrace_663573
  have hstable : (prefixWord ++ tailWord_663573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663573).length < 2 ^ (prefixWord ++ tailWord_663573).sum := by decide
  have hdescent : baseEnd_663573 < baseStart_663573 := by decide
  rcases family_descends (prefixWord ++ tailWord_663573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663601 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_663601 : Nat := 118140960795 + 663601 * 2 ^ 59
def prefixEnd_663601 : Nat := 4983230072969 + 3 ^ 40 * 663601 * 2
def baseEnd_663601 : Nat := 302885578492767459320587

theorem tailTrace_663601 : CollatzResearch.WordTrace tailWord_663601 prefixEnd_663601 302885578492767459320587 := by
  unfold tailWord_663601
  simp only [CollatzResearch.WordTrace]
  refine ⟨24203516868894385872926657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16135677912596257248617771 24203516868894385872926657)
  ·
    refine ⟨18152637651670789404694993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24203516868894385872926657 18152637651670789404694993)
    ·
      refine ⟨13614478238753092053521245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18152637651670789404694993 13614478238753092053521245)
      ·
        refine ⟨5105429339532409520070467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13614478238753092053521245 5105429339532409520070467)
        ·
          refine ⟨7658144009298614280105701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105429339532409520070467 7658144009298614280105701)
          ·
            refine ⟨1435902001743490177519819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7658144009298614280105701 1435902001743490177519819)
            ·
              refine ⟨2153853002615235266279729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435902001743490177519819 2153853002615235266279729)
              ·
                refine ⟨1615389751961426449709797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153853002615235266279729 1615389751961426449709797)
                ·
                  refine ⟨302885578492767459320587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615389751961426449709797 302885578492767459320587)
                  ·
                    rfl

theorem cell20_663601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_663601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663601 prefixEnd_663601 := by exact prefixLift 663601
  have htrace : WordTrace (prefixWord ++ tailWord_663601) baseStart_663601 baseEnd_663601 := by
    simpa [prefixWord, tailWord_663601, baseEnd_663601] using wordTrace_append hprefix tailTrace_663601
  have hstable : (prefixWord ++ tailWord_663601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663601).length < 2 ^ (prefixWord ++ tailWord_663601).sum := by decide
  have hdescent : baseEnd_663601 < baseStart_663601 := by decide
  rcases family_descends (prefixWord ++ tailWord_663601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663614 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_663614 : Nat := 118140960795 + 663614 * 2 ^ 59
def prefixEnd_663614 : Nat := 4983230072969 + 3 ^ 40 * 663614 * 2
def baseEnd_663614 : Nat := 302891512046997191887201

theorem tailTrace_663614 : CollatzResearch.WordTrace tailWord_663614 prefixEnd_663614 302891512046997191887201 := by
  unfold tailWord_663614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025498877230911136643737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16135994011898192728766597 3025498877230911136643737)
  ·
    refine ⟨2269124157923183352482803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3025498877230911136643737 2269124157923183352482803)
    ·
      refine ⟨3403686236884775028724205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269124157923183352482803 3403686236884775028724205)
      ·
        refine ⟨1276382338831790635771577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3403686236884775028724205 1276382338831790635771577)
        ·
          refine ⟨957286754123842976828683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276382338831790635771577 957286754123842976828683)
          ·
            refine ⟨1435930131185764465243025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957286754123842976828683 1435930131185764465243025)
            ·
              refine ⟨1076947598389323348932269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435930131185764465243025 1076947598389323348932269)
              ·
                refine ⟨403855349395996255849601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076947598389323348932269 403855349395996255849601)
                ·
                  refine ⟨302891512046997191887201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403855349395996255849601 302891512046997191887201)
                  ·
                    rfl

theorem cell20_663614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_663614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663614 prefixEnd_663614 := by exact prefixLift 663614
  have htrace : WordTrace (prefixWord ++ tailWord_663614) baseStart_663614 baseEnd_663614 := by
    simpa [prefixWord, tailWord_663614, baseEnd_663614] using wordTrace_append hprefix tailTrace_663614
  have hstable : (prefixWord ++ tailWord_663614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663614).length < 2 ^ (prefixWord ++ tailWord_663614).sum := by decide
  have hdescent : baseEnd_663614 < baseStart_663614 := by decide
  rcases family_descends (prefixWord ++ tailWord_663614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663663 : List Nat := [1, 1, 2, 1, 3, 6, 2, 4]
def baseStart_663663 : Nat := 118140960795 + 663663 * 2 ^ 59
def prefixEnd_663663 : Nat := 4983230072969 + 3 ^ 40 * 663663 * 2
def baseEnd_663663 : Nat := 100971292327390266417889

theorem tailTrace_663663 : CollatzResearch.WordTrace tailWord_663663 prefixEnd_663663 100971292327390266417889 := by
  unfold tailWord_663663
  simp only [CollatzResearch.WordTrace]
  refine ⟨24205778194669770461683643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16137185463113180307789095 24205778194669770461683643)
  ·
    refine ⟨36308667292004655692525465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24205778194669770461683643 36308667292004655692525465)
    ·
      refine ⟨27231500469003491769394099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36308667292004655692525465 27231500469003491769394099)
      ·
        refine ⟨40847250703505237654091149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27231500469003491769394099 40847250703505237654091149)
        ·
          refine ⟨15317719013814464120284181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40847250703505237654091149 15317719013814464120284181)
          ·
            refine ⟨718018078772553005638321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15317719013814464120284181 718018078772553005638321)
            ·
              refine ⟨538513559079414754228741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718018078772553005638321 538513559079414754228741)
              ·
                refine ⟨100971292327390266417889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538513559079414754228741 100971292327390266417889)
                ·
                  rfl

theorem cell20_663663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_663663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663663 prefixEnd_663663 := by exact prefixLift 663663
  have htrace : WordTrace (prefixWord ++ tailWord_663663) baseStart_663663 baseEnd_663663 := by
    simpa [prefixWord, tailWord_663663, baseEnd_663663] using wordTrace_append hprefix tailTrace_663663
  have hstable : (prefixWord ++ tailWord_663663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663663).length < 2 ^ (prefixWord ++ tailWord_663663).sum := by decide
  have hdescent : baseEnd_663663 < baseStart_663663 := by decide
  rcases family_descends (prefixWord ++ tailWord_663663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663670 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_663670 : Nat := 118140960795 + 663670 * 2 ^ 59
def prefixEnd_663670 : Nat := 4983230072969 + 3 ^ 40 * 663670 * 2
def baseEnd_663670 : Nat := 302917071972909886020305

theorem tailTrace_663670 : CollatzResearch.WordTrace tailWord_663670 prefixEnd_663670 302917071972909886020305 := by
  unfold tailWord_663670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512877094102775666074279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16137355670429607104792309 1512877094102775666074279)
  ·
    refine ⟨2269315641154163499111419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512877094102775666074279 2269315641154163499111419)
    ·
      refine ⟨3403973461731245248667129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269315641154163499111419 3403973461731245248667129)
      ·
        refine ⟨2552980096298433936500347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3403973461731245248667129 2552980096298433936500347)
        ·
          refine ⟨3829470144447650904750521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552980096298433936500347 3829470144447650904750521)
          ·
            refine ⟨2872102608335738178562891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3829470144447650904750521 2872102608335738178562891)
            ·
              refine ⟨4308153912503607267844337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872102608335738178562891 4308153912503607267844337)
              ·
                refine ⟨3231115434377705450883253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308153912503607267844337 3231115434377705450883253)
                ·
                  refine ⟨302917071972909886020305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3231115434377705450883253 302917071972909886020305)
                  ·
                    rfl

theorem cell20_663670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_663670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663670 prefixEnd_663670 := by exact prefixLift 663670
  have htrace : WordTrace (prefixWord ++ tailWord_663670) baseStart_663670 baseEnd_663670 := by
    simpa [prefixWord, tailWord_663670, baseEnd_663670] using wordTrace_append hprefix tailTrace_663670
  have hstable : (prefixWord ++ tailWord_663670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663670).length < 2 ^ (prefixWord ++ tailWord_663670).sum := by decide
  have hdescent : baseEnd_663670 < baseStart_663670 := by decide
  rcases family_descends (prefixWord ++ tailWord_663670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663673 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 2]
def baseStart_663673 : Nat := 118140960795 + 663673 * 2 ^ 59
def prefixEnd_663673 : Nat := 4983230072969 + 3 ^ 40 * 663673 * 2
def baseEnd_663673 : Nat := 302918441254655208920293

theorem tailTrace_663673 : CollatzResearch.WordTrace tailWord_663673 prefixEnd_663673 302918441254655208920293 := by
  unfold tailWord_663673
  simp only [CollatzResearch.WordTrace]
  refine ⟨24206142924633542169547673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16137428616422361446365115 24206142924633542169547673)
  ·
    refine ⟨18154607193475156627160755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24206142924633542169547673 18154607193475156627160755)
    ·
      refine ⟨27231910790212734940741133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18154607193475156627160755 27231910790212734940741133)
      ·
        refine ⟨10211966546329775602777925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27231910790212734940741133 10211966546329775602777925)
        ·
          refine ⟨1914743727436832925520861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10211966546329775602777925 1914743727436832925520861)
          ·
            refine ⟨718028897788812347070323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1914743727436832925520861 718028897788812347070323)
            ·
              refine ⟨1077043346683218520605485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718028897788812347070323 1077043346683218520605485)
              ·
                refine ⟨403891255006206945227057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1077043346683218520605485 403891255006206945227057)
                ·
                  refine ⟨302918441254655208920293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403891255006206945227057 302918441254655208920293)
                  ·
                    rfl

theorem cell20_663673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_663673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663673 prefixEnd_663673 := by exact prefixLift 663673
  have htrace : WordTrace (prefixWord ++ tailWord_663673) baseStart_663673 baseEnd_663673 := by
    simpa [prefixWord, tailWord_663673, baseEnd_663673] using wordTrace_append hprefix tailTrace_663673
  have hstable : (prefixWord ++ tailWord_663673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663673).length < 2 ^ (prefixWord ++ tailWord_663673).sum := by decide
  have hdescent : baseEnd_663673 < baseStart_663673 := by decide
  rcases family_descends (prefixWord ++ tailWord_663673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663700 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 3]
def baseStart_663700 : Nat := 118140960795 + 663700 * 2 ^ 59
def prefixEnd_663700 : Nat := 4983230072969 + 3 ^ 40 * 663700 * 2
def baseEnd_663700 : Nat := 302930764790363115020183

theorem tailTrace_663700 : CollatzResearch.WordTrace tailWord_663700 prefixEnd_663700 302930764790363115020183 := by
  unfold tailWord_663700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103563847767862890390277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16138085130357150520520369 12103563847767862890390277)
  ·
    refine ⟨2269418221456474291948177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12103563847767862890390277 2269418221456474291948177)
    ·
      refine ⟨1702063666092355718961133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2269418221456474291948177 1702063666092355718961133)
      ·
        refine ⟨638273874784633394610425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1702063666092355718961133 638273874784633394610425)
        ·
          refine ⟨478705406088475045957819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638273874784633394610425 478705406088475045957819)
          ·
            refine ⟨718058109132712568936729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478705406088475045957819 718058109132712568936729)
            ·
              refine ⟨538543581849534426702547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718058109132712568936729 538543581849534426702547)
              ·
                refine ⟨807815372774301640053821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538543581849534426702547 807815372774301640053821)
                ·
                  refine ⟨302930764790363115020183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807815372774301640053821 302930764790363115020183)
                  ·
                    rfl

theorem cell20_663700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_663700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663700 prefixEnd_663700 := by exact prefixLift 663700
  have htrace : WordTrace (prefixWord ++ tailWord_663700) baseStart_663700 baseEnd_663700 := by
    simpa [prefixWord, tailWord_663700, baseEnd_663700] using wordTrace_append hprefix tailTrace_663700
  have hstable : (prefixWord ++ tailWord_663700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663700).length < 2 ^ (prefixWord ++ tailWord_663700).sum := by decide
  have hdescent : baseEnd_663700 < baseStart_663700 := by decide
  rcases family_descends (prefixWord ++ tailWord_663700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663704 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_663704 : Nat := 118140960795 + 663704 * 2 ^ 59
def prefixEnd_663704 : Nat := 4983230072969 + 3 ^ 40 * 663704 * 2
def baseEnd_663704 : Nat := 302932590499356878886833

theorem tailTrace_663704 : CollatzResearch.WordTrace tailWord_663704 prefixEnd_663704 302932590499356878886833 := by
  unfold tailWord_663704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103636793760617231963083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16138182391680822975950777 12103636793760617231963083)
  ·
    refine ⟨18155455190640925847944625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12103636793760617231963083 18155455190640925847944625)
    ·
      refine ⟨13616591392980694385958469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18155455190640925847944625 13616591392980694385958469)
      ·
        refine ⟨2553110886183880197367213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13616591392980694385958469 2553110886183880197367213)
        ·
          refine ⟨957416582318955074012705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2553110886183880197367213 957416582318955074012705)
          ·
            refine ⟨718062436739216305509529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957416582318955074012705 718062436739216305509529)
            ·
              refine ⟨538546827554412229132147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718062436739216305509529 538546827554412229132147)
              ·
                refine ⟨807820241331618343698221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538546827554412229132147 807820241331618343698221)
                ·
                  refine ⟨302932590499356878886833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807820241331618343698221 302932590499356878886833)
                  ·
                    rfl

theorem cell20_663704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_663704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663704 prefixEnd_663704 := by exact prefixLift 663704
  have htrace : WordTrace (prefixWord ++ tailWord_663704) baseStart_663704 baseEnd_663704 := by
    simpa [prefixWord, tailWord_663704, baseEnd_663704] using wordTrace_append hprefix tailTrace_663704
  have hstable : (prefixWord ++ tailWord_663704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663704).length < 2 ^ (prefixWord ++ tailWord_663704).sum := by decide
  have hdescent : baseEnd_663704 < baseStart_663704 := by decide
  rcases family_descends (prefixWord ++ tailWord_663704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663708 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_663708 : Nat := 118140960795 + 663708 * 2 ^ 59
def prefixEnd_663708 : Nat := 4983230072969 + 3 ^ 40 * 663708 * 2
def baseEnd_663708 : Nat := 302934416208350642753483

theorem tailTrace_663708 : CollatzResearch.WordTrace tailWord_663708 prefixEnd_663708 302934416208350642753483 := by
  unfold tailWord_663708
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103709739753371573535889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16138279653004495431381185 12103709739753371573535889)
  ·
    refine ⟨9077782304815028680151917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12103709739753371573535889 9077782304815028680151917)
    ·
      refine ⟨3404168364305635755056969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9077782304815028680151917 3404168364305635755056969)
      ·
        refine ⟨2553126273229226816292727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3404168364305635755056969 2553126273229226816292727)
        ·
          refine ⟨3829689409843840224439091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553126273229226816292727 3829689409843840224439091)
          ·
            refine ⟨5744534114765760336658637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829689409843840224439091 5744534114765760336658637)
            ·
              refine ⟨2154200293037160126246989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5744534114765760336658637 2154200293037160126246989)
              ·
                refine ⟨807825109888935047342621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154200293037160126246989 807825109888935047342621)
                ·
                  refine ⟨302934416208350642753483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807825109888935047342621 302934416208350642753483)
                  ·
                    rfl

theorem cell20_663708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_663708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663708 prefixEnd_663708 := by exact prefixLift 663708
  have htrace : WordTrace (prefixWord ++ tailWord_663708) baseStart_663708 baseEnd_663708 := by
    simpa [prefixWord, tailWord_663708, baseEnd_663708] using wordTrace_append hprefix tailTrace_663708
  have hstable : (prefixWord ++ tailWord_663708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663708).length < 2 ^ (prefixWord ++ tailWord_663708).sum := by decide
  have hdescent : baseEnd_663708 < baseStart_663708 := by decide
  rcases family_descends (prefixWord ++ tailWord_663708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663745 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 2]
def baseStart_663745 : Nat := 118140960795 + 663745 * 2 ^ 59
def prefixEnd_663745 : Nat := 4983230072969 + 3 ^ 40 * 663745 * 2
def baseEnd_663745 : Nat := 302951304016542958519999

theorem tailTrace_663745 : CollatzResearch.WordTrace tailWord_663745 prefixEnd_663745 302951304016542958519999 := by
  unfold tailWord_663745
  simp only [CollatzResearch.WordTrace]
  refine ⟨24208768980372698466168689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16139179320248465644112459 24208768980372698466168689)
  ·
    refine ⟨18156576735279523849626517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24208768980372698466168689 18156576735279523849626517)
    ·
      refine ⟨851089534466227680451243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18156576735279523849626517 851089534466227680451243)
      ·
        refine ⟨1276634301699341520676865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851089534466227680451243 1276634301699341520676865)
        ·
          refine ⟨957475726274506140507649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276634301699341520676865 957475726274506140507649)
          ·
            refine ⟨718106794705879605380737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957475726274506140507649 718106794705879605380737)
            ·
              refine ⟨538580096029409704035553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718106794705879605380737 538580096029409704035553)
              ·
                refine ⟨403935072022057278026665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538580096029409704035553 403935072022057278026665)
                ·
                  refine ⟨302951304016542958519999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403935072022057278026665 302951304016542958519999)
                  ·
                    rfl

theorem cell20_663745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_663745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663745 prefixEnd_663745 := by exact prefixLift 663745
  have htrace : WordTrace (prefixWord ++ tailWord_663745) baseStart_663745 baseEnd_663745 := by
    simpa [prefixWord, tailWord_663745, baseEnd_663745] using wordTrace_append hprefix tailTrace_663745
  have hstable : (prefixWord ++ tailWord_663745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663745).length < 2 ^ (prefixWord ++ tailWord_663745).sum := by decide
  have hdescent : baseEnd_663745 < baseStart_663745 := by decide
  rcases family_descends (prefixWord ++ tailWord_663745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663756 : List Nat := [2, 2, 1, 6, 1, 2, 1, 5]
def baseStart_663756 : Nat := 118140960795 + 663756 * 2 ^ 59
def prefixEnd_663756 : Nat := 4983230072969 + 3 ^ 40 * 663756 * 2
def baseEnd_663756 : Nat := 100985441572091936384429

theorem tailTrace_663756 : CollatzResearch.WordTrace tailWord_663756 prefixEnd_663756 100985441572091936384429 := by
  unfold tailWord_663756
  simp only [CollatzResearch.WordTrace]
  refine ⟨12104585091666423672409561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16139446788888564896546081 12104585091666423672409561)
  ·
    refine ⟨9078438818749817754307171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12104585091666423672409561 9078438818749817754307171)
    ·
      refine ⟨13617658228124726631460757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9078438818749817754307171 13617658228124726631460757)
      ·
        refine ⟨638327729443346560849723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13617658228124726631460757 638327729443346560849723)
        ·
          refine ⟨957491594165019841274585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638327729443346560849723 957491594165019841274585)
          ·
            refine ⟨718118695623764880955939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957491594165019841274585 718118695623764880955939)
            ·
              refine ⟨1077178043435647321433909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718118695623764880955939 1077178043435647321433909)
              ·
                refine ⟨100985441572091936384429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1077178043435647321433909 100985441572091936384429)
                ·
                  rfl

theorem cell20_663756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_663756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663756 prefixEnd_663756 := by exact prefixLift 663756
  have htrace : WordTrace (prefixWord ++ tailWord_663756) baseStart_663756 baseEnd_663756 := by
    simpa [prefixWord, tailWord_663756, baseEnd_663756] using wordTrace_append hprefix tailTrace_663756
  have hstable : (prefixWord ++ tailWord_663756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663756).length < 2 ^ (prefixWord ++ tailWord_663756).sum := by decide
  have hdescent : baseEnd_663756 < baseStart_663756 := by decide
  rcases family_descends (prefixWord ++ tailWord_663756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663819 : List Nat := [1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_663819 : Nat := 118140960795 + 663819 * 2 ^ 59
def prefixEnd_663819 : Nat := 4983230072969 + 3 ^ 40 * 663819 * 2
def baseEnd_663819 : Nat := 100995026544309196684343

theorem tailTrace_663819 : CollatzResearch.WordTrace tailWord_663819 prefixEnd_663819 100995026544309196684343 := by
  unfold tailWord_663819
  simp only [CollatzResearch.WordTrace]
  refine ⟨24211467982104609104362511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16140978654736406069575007 24211467982104609104362511)
  ·
    refine ⟨36317201973156913656543767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24211467982104609104362511 36317201973156913656543767)
    ·
      refine ⟨54475802959735370484815651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36317201973156913656543767 54475802959735370484815651)
      ·
        refine ⟨81713704439603055727223477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54475802959735370484815651 81713704439603055727223477)
        ·
          refine ⟨7660659791212786474427201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81713704439603055727223477 7660659791212786474427201)
          ·
            refine ⟨5745494843409589855820401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660659791212786474427201 5745494843409589855820401)
            ·
              refine ⟨4309121132557192391865301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745494843409589855820401 4309121132557192391865301)
              ·
                refine ⟨100995026544309196684343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4309121132557192391865301 100995026544309196684343)
                ·
                  rfl

theorem cell20_663819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_663819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663819 prefixEnd_663819 := by exact prefixLift 663819
  have htrace : WordTrace (prefixWord ++ tailWord_663819) baseStart_663819 baseEnd_663819 := by
    simpa [prefixWord, tailWord_663819, baseEnd_663819] using wordTrace_append hprefix tailTrace_663819
  have hstable : (prefixWord ++ tailWord_663819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663819).length < 2 ^ (prefixWord ++ tailWord_663819).sum := by decide
  have hdescent : baseEnd_663819 < baseStart_663819 := by decide
  rcases family_descends (prefixWord ++ tailWord_663819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663860 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_663860 : Nat := 118140960795 + 663860 * 2 ^ 59
def prefixEnd_663860 : Nat := 4983230072969 + 3 ^ 40 * 663860 * 2
def baseEnd_663860 : Nat := 303003793150113669686195

theorem tailTrace_663860 : CollatzResearch.WordTrace tailWord_663860 prefixEnd_663860 303003793150113669686195 := by
  unfold tailWord_663860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12106481687478036553302517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16141975583304048737736689 12106481687478036553302517)
  ·
    refine ⟨1134982658201065926872111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12106481687478036553302517 1134982658201065926872111)
    ·
      refine ⟨1702473987301598890308167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1134982658201065926872111 1702473987301598890308167)
      ·
        refine ⟨2553710980952398335462251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702473987301598890308167 2553710980952398335462251)
        ·
          refine ⟨3830566471428597503193377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553710980952398335462251 3830566471428597503193377)
          ·
            refine ⟨2872924853571448127395033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3830566471428597503193377 2872924853571448127395033)
            ·
              refine ⟨2154693640178586095546275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872924853571448127395033 2154693640178586095546275)
              ·
                refine ⟨3232040460267879143319413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154693640178586095546275 3232040460267879143319413)
                ·
                  refine ⟨303003793150113669686195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3232040460267879143319413 303003793150113669686195)
                  ·
                    rfl

theorem cell20_663860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_663860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663860 prefixEnd_663860 := by exact prefixLift 663860
  have htrace : WordTrace (prefixWord ++ tailWord_663860) baseStart_663860 baseEnd_663860 := by
    simpa [prefixWord, tailWord_663860, baseEnd_663860] using wordTrace_append hprefix tailTrace_663860
  have hstable : (prefixWord ++ tailWord_663860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663860).length < 2 ^ (prefixWord ++ tailWord_663860).sum := by decide
  have hdescent : baseEnd_663860 < baseStart_663860 := by decide
  rcases family_descends (prefixWord ++ tailWord_663860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663873 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 3]
def baseStart_663873 : Nat := 118140960795 + 663873 * 2 ^ 59
def prefixEnd_663873 : Nat := 4983230072969 + 3 ^ 40 * 663873 * 2
def baseEnd_663873 : Nat := 303009726704343402252809

theorem tailTrace_663873 : CollatzResearch.WordTrace tailWord_663873 prefixEnd_663873 303009726704343402252809 := by
  unfold tailWord_663873
  simp only [CollatzResearch.WordTrace]
  refine ⟨24213437523908976326828273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16142291682605984217885515 24213437523908976326828273)
  ·
    refine ⟨18160078142931732245121205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24213437523908976326828273 18160078142931732245121205)
    ·
      refine ⟨1702507325899849897980113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18160078142931732245121205 1702507325899849897980113)
      ·
        refine ⟨1276880494424887423485085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1702507325899849897980113 1276880494424887423485085)
        ·
          refine ⟨478830185409332783806907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1276880494424887423485085 478830185409332783806907)
          ·
            refine ⟨718245278113999175710361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478830185409332783806907 718245278113999175710361)
            ·
              refine ⟨538683958585499381782771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718245278113999175710361 538683958585499381782771)
              ·
                refine ⟨808025937878249072674157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538683958585499381782771 808025937878249072674157)
                ·
                  refine ⟨303009726704343402252809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808025937878249072674157 303009726704343402252809)
                  ·
                    rfl

theorem cell20_663873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_663873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663873 prefixEnd_663873 := by exact prefixLift 663873
  have htrace : WordTrace (prefixWord ++ tailWord_663873) baseStart_663873 baseEnd_663873 := by
    simpa [prefixWord, tailWord_663873, baseEnd_663873] using wordTrace_append hprefix tailTrace_663873
  have hstable : (prefixWord ++ tailWord_663873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663873).length < 2 ^ (prefixWord ++ tailWord_663873).sum := by decide
  have hdescent : baseEnd_663873 < baseStart_663873 := by decide
  rcases family_descends (prefixWord ++ tailWord_663873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663895 : List Nat := [1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_663895 : Nat := 118140960795 + 663895 * 2 ^ 59
def prefixEnd_663895 : Nat := 4983230072969 + 3 ^ 40 * 663895 * 2
def baseEnd_663895 : Nat := 101006589367936367839795

theorem tailTrace_663895 : CollatzResearch.WordTrace tailWord_663895 prefixEnd_663895 101006589367936367839795 := by
  unfold tailWord_663895
  simp only [CollatzResearch.WordTrace]
  refine ⟨24214239929829274084129139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16142826619886182722752759 24214239929829274084129139)
  ·
    refine ⟨36321359894743911126193709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24214239929829274084129139 36321359894743911126193709)
    ·
      refine ⟨13620509960528966672322641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36321359894743911126193709 13620509960528966672322641)
      ·
        refine ⟨10215382470396725004241981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13620509960528966672322641 10215382470396725004241981)
        ·
          refine ⟨3830768426398771876590743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10215382470396725004241981 3830768426398771876590743)
          ·
            refine ⟨5746152639598157814886115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830768426398771876590743 5746152639598157814886115)
            ·
              refine ⟨8619228959397236722329173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5746152639598157814886115 8619228959397236722329173)
              ·
                refine ⟨101006589367936367839795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8619228959397236722329173 101006589367936367839795)
                ·
                  rfl

theorem cell20_663895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_663895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663895 prefixEnd_663895 := by exact prefixLift 663895
  have htrace : WordTrace (prefixWord ++ tailWord_663895) baseStart_663895 baseEnd_663895 := by
    simpa [prefixWord, tailWord_663895, baseEnd_663895] using wordTrace_append hprefix tailTrace_663895
  have hstable : (prefixWord ++ tailWord_663895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663895).length < 2 ^ (prefixWord ++ tailWord_663895).sum := by decide
  have hdescent : baseEnd_663895 < baseStart_663895 := by decide
  rcases family_descends (prefixWord ++ tailWord_663895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663922 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_663922 : Nat := 118140960795 + 663922 * 2 ^ 59
def prefixEnd_663922 : Nat := 4983230072969 + 3 ^ 40 * 663922 * 2
def baseEnd_663922 : Nat := 303032091639517009619275

theorem tailTrace_663922 : CollatzResearch.WordTrace tailWord_663922 prefixEnd_663922 303032091639517009619275 := by
  unfold tailWord_663922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053806175182864423840505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16143483133820971796908013 6053806175182864423840505)
  ·
    refine ⟨4540354631387148317880379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6053806175182864423840505 4540354631387148317880379)
    ·
      refine ⟨6810531947080722476820569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4540354631387148317880379 6810531947080722476820569)
      ·
        refine ⟨5107898960310541857615427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6810531947080722476820569 5107898960310541857615427)
        ·
          refine ⟨7661848440465812786423141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107898960310541857615427 7661848440465812786423141)
          ·
            refine ⟨1436596582587339897454339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7661848440465812786423141 1436596582587339897454339)
            ·
              refine ⟨2154894873881009846181509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436596582587339897454339 2154894873881009846181509)
              ·
                refine ⟨404042788852689346159033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2154894873881009846181509 404042788852689346159033)
                ·
                  refine ⟨303032091639517009619275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404042788852689346159033 303032091639517009619275)
                  ·
                    rfl

theorem cell20_663922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_663922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663922 prefixEnd_663922 := by exact prefixLift 663922
  have htrace : WordTrace (prefixWord ++ tailWord_663922) baseStart_663922 baseEnd_663922 := by
    simpa [prefixWord, tailWord_663922, baseEnd_663922] using wordTrace_append hprefix tailTrace_663922
  have hstable : (prefixWord ++ tailWord_663922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663922).length < 2 ^ (prefixWord ++ tailWord_663922).sum := by decide
  have hdescent : baseEnd_663922 < baseStart_663922 := by decide
  rcases family_descends (prefixWord ++ tailWord_663922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663946 : List Nat := [3, 1, 2, 5, 1, 1, 3, 4]
def baseStart_663946 : Nat := 118140960795 + 663946 * 2 ^ 59
def prefixEnd_663946 : Nat := 4983230072969 + 3 ^ 40 * 663946 * 2
def baseEnd_663946 : Nat := 101014348631159864273059

theorem tailTrace_663946 : CollatzResearch.WordTrace tailWord_663946 prefixEnd_663946 101014348631159864273059 := by
  unfold tailWord_663946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054025013161127448558923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16144066701763006529490461 6054025013161127448558923)
  ·
    refine ⟨9081037519741691172838385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054025013161127448558923 9081037519741691172838385)
    ·
      refine ⟨6810778139806268379628789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9081037519741691172838385 6810778139806268379628789)
      ·
        refine ⟨638510450606837660590199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6810778139806268379628789 638510450606837660590199)
        ·
          refine ⟨957765675910256490885299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638510450606837660590199 957765675910256490885299)
          ·
            refine ⟨1436648513865384736327949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957765675910256490885299 1436648513865384736327949)
            ·
              refine ⟨538743192699519276122981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1436648513865384736327949 538743192699519276122981)
              ·
                refine ⟨101014348631159864273059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538743192699519276122981 101014348631159864273059)
                ·
                  rfl

theorem cell20_663946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_663946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663946 prefixEnd_663946 := by exact prefixLift 663946
  have htrace : WordTrace (prefixWord ++ tailWord_663946) baseStart_663946 baseEnd_663946 := by
    simpa [prefixWord, tailWord_663946, baseEnd_663946] using wordTrace_append hprefix tailTrace_663946
  have hstable : (prefixWord ++ tailWord_663946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663946).length < 2 ^ (prefixWord ++ tailWord_663946).sum := by decide
  have hdescent : baseEnd_663946 < baseStart_663946 := by decide
  rcases family_descends (prefixWord ++ tailWord_663946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663960 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 2]
def baseStart_663960 : Nat := 118140960795 + 663960 * 2 ^ 59
def prefixEnd_663960 : Nat := 4983230072969 + 3 ^ 40 * 663960 * 2
def baseEnd_663960 : Nat := 303049435874957766352453

theorem tailTrace_663960 : CollatzResearch.WordTrace tailWord_663960 prefixEnd_663960 303049435874957766352453 := by
  unfold tailWord_663960
  simp only [CollatzResearch.WordTrace]
  refine ⟨12108305337296895092622667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16144407116395860123496889 12108305337296895092622667)
  ·
    refine ⟨18162458005945342638934001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12108305337296895092622667 18162458005945342638934001)
    ·
      refine ⟨13621843504459006979200501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18162458005945342638934001 13621843504459006979200501)
      ·
        refine ⟨1277047828543031904300047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13621843504459006979200501 1277047828543031904300047)
        ·
          refine ⟨1915571742814547856450071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277047828543031904300047 1915571742814547856450071)
          ·
            refine ⟨2873357614221821784675107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915571742814547856450071 2873357614221821784675107)
            ·
              refine ⟨4310036421332732677012661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873357614221821784675107 4310036421332732677012661)
              ·
                refine ⟨404065914499943688469937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4310036421332732677012661 404065914499943688469937)
                ·
                  refine ⟨303049435874957766352453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404065914499943688469937 303049435874957766352453)
                  ·
                    rfl

theorem cell20_663960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_663960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663960 prefixEnd_663960 := by exact prefixLift 663960
  have htrace : WordTrace (prefixWord ++ tailWord_663960) baseStart_663960 baseEnd_663960 := by
    simpa [prefixWord, tailWord_663960, baseEnd_663960] using wordTrace_append hprefix tailTrace_663960
  have hstable : (prefixWord ++ tailWord_663960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663960).length < 2 ^ (prefixWord ++ tailWord_663960).sum := by decide
  have hdescent : baseEnd_663960 < baseStart_663960 := by decide
  rcases family_descends (prefixWord ++ tailWord_663960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663971 : List Nat := [1, 1, 1, 4, 1, 5, 7]
def baseStart_663971 : Nat := 118140960795 + 663971 * 2 ^ 59
def prefixEnd_663971 : Nat := 4983230072969 + 3 ^ 40 * 663971 * 2
def baseEnd_663971 : Nat := 33672717397187846331749

theorem tailTrace_663971 : CollatzResearch.WordTrace tailWord_663971 prefixEnd_663971 33672717397187846331749 := by
  unfold tailWord_663971
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217011877553939063895767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16144674585035959375930511 24217011877553939063895767)
  ·
    refine ⟨36325517816330908595843651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24217011877553939063895767 36325517816330908595843651)
    ·
      refine ⟨54488276724496362893765477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36325517816330908595843651 54488276724496362893765477)
      ·
        refine ⟨10216551885843068042581027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54488276724496362893765477 10216551885843068042581027)
        ·
          refine ⟨15324827828764602063871541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10216551885843068042581027 15324827828764602063871541)
          ·
            refine ⟨1436702608946681443487957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15324827828764602063871541 1436702608946681443487957)
            ·
              refine ⟨33672717397187846331749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1436702608946681443487957 33672717397187846331749)
              ·
                rfl

theorem cell20_663971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_663971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_663971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_663971 prefixEnd_663971 := by exact prefixLift 663971
  have htrace : WordTrace (prefixWord ++ tailWord_663971) baseStart_663971 baseEnd_663971 := by
    simpa [prefixWord, tailWord_663971, baseEnd_663971] using wordTrace_append hprefix tailTrace_663971
  have hstable : (prefixWord ++ tailWord_663971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663971).length < 2 ^ (prefixWord ++ tailWord_663971).sum := by decide
  have hdescent : baseEnd_663971 < baseStart_663971 := by decide
  rcases family_descends (prefixWord ++ tailWord_663971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664033 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_664033 : Nat := 118140960795 + 664033 * 2 ^ 59
def prefixEnd_664033 : Nat := 4983230072969 + 3 ^ 40 * 664033 * 2
def baseEnd_664033 : Nat := 303082755064093956918821

theorem tailTrace_664033 : CollatzResearch.WordTrace tailWord_664033 prefixEnd_664033 303082755064093956918821 := by
  unfold tailWord_664033
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219273203329323652652753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16146182135552882435101835 24219273203329323652652753)
  ·
    refine ⟨18164454902496992739489565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24219273203329323652652753 18164454902496992739489565)
    ·
      refine ⟨6811670588436372277308587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18164454902496992739489565 6811670588436372277308587)
      ·
        refine ⟨10217505882654558415962881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811670588436372277308587 10217505882654558415962881)
        ·
          refine ⟨7663129411990918811972161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10217505882654558415962881 7663129411990918811972161)
          ·
            refine ⟨5747347058993189108979121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7663129411990918811972161 5747347058993189108979121)
            ·
              refine ⟨4310510294244891831734341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5747347058993189108979121 4310510294244891831734341)
              ·
                refine ⟨808220680170917218450189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4310510294244891831734341 808220680170917218450189)
                ·
                  refine ⟨303082755064093956918821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808220680170917218450189 303082755064093956918821)
                  ·
                    rfl

theorem cell20_664033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_664033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664033 prefixEnd_664033 := by exact prefixLift 664033
  have htrace : WordTrace (prefixWord ++ tailWord_664033) baseStart_664033 baseEnd_664033 := by
    simpa [prefixWord, tailWord_664033, baseEnd_664033] using wordTrace_append hprefix tailTrace_664033
  have hstable : (prefixWord ++ tailWord_664033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664033).length < 2 ^ (prefixWord ++ tailWord_664033).sum := by decide
  have hdescent : baseEnd_664033 < baseStart_664033 := by decide
  rcases family_descends (prefixWord ++ tailWord_664033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664087 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 2]
def baseStart_664087 : Nat := 118140960795 + 664087 * 2 ^ 59
def prefixEnd_664087 : Nat := 4983230072969 + 3 ^ 40 * 664087 * 2
def baseEnd_664087 : Nat := 303107402135509769118601

theorem tailTrace_664087 : CollatzResearch.WordTrace tailWord_664087 prefixEnd_664087 303107402135509769118601 := by
  unfold tailWord_664087
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221242745133690875118515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16147495163422460583412343 24221242745133690875118515)
  ·
    refine ⟨36331864117700536312677773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24221242745133690875118515 36331864117700536312677773)
    ·
      refine ⟨13624449044137701117254165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36331864117700536312677773 13624449044137701117254165)
      ·
        refine ⟨638646048943954739871289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13624449044137701117254165 638646048943954739871289)
        ·
          refine ⟨478984536707966054903467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638646048943954739871289 478984536707966054903467)
          ·
            refine ⟨718476805061949082355201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478984536707966054903467 718476805061949082355201)
            ·
              refine ⟨538857603796461811766401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718476805061949082355201 538857603796461811766401)
              ·
                refine ⟨404143202847346358824801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538857603796461811766401 404143202847346358824801)
                ·
                  refine ⟨303107402135509769118601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404143202847346358824801 303107402135509769118601)
                  ·
                    rfl

theorem cell20_664087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 2].length) (baseStart_664087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664087 prefixEnd_664087 := by exact prefixLift 664087
  have htrace : WordTrace (prefixWord ++ tailWord_664087) baseStart_664087 baseEnd_664087 := by
    simpa [prefixWord, tailWord_664087, baseEnd_664087] using wordTrace_append hprefix tailTrace_664087
  have hstable : (prefixWord ++ tailWord_664087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664087).length < 2 ^ (prefixWord ++ tailWord_664087).sum := by decide
  have hdescent : baseEnd_664087 < baseStart_664087 := by decide
  rcases family_descends (prefixWord ++ tailWord_664087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664088 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_664088 : Nat := 118140960795 + 664088 * 2 ^ 59
def prefixEnd_664088 : Nat := 4983230072969 + 3 ^ 40 * 664088 * 2
def baseEnd_664088 : Nat := 303107858562758210085263

theorem tailTrace_664088 : CollatzResearch.WordTrace tailWord_664088 prefixEnd_664088 303107858562758210085263 := by
  unfold tailWord_664088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110639609065034022952459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16147519478753378697269945 12110639609065034022952459)
  ·
    refine ⟨18165959413597551034428689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12110639609065034022952459 18165959413597551034428689)
    ·
      refine ⟨13624469560198163275821517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18165959413597551034428689 13624469560198163275821517)
      ·
        refine ⟨5109176085074311228433069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13624469560198163275821517 5109176085074311228433069)
        ·
          refine ⟨1915941031902866710662401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5109176085074311228433069 1915941031902866710662401)
          ·
            refine ⟨1436955773927150032996801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915941031902866710662401 1436955773927150032996801)
            ·
              refine ⟨1077716830445362524747601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436955773927150032996801 1077716830445362524747601)
              ·
                refine ⟨808287622834021893560701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077716830445362524747601 808287622834021893560701)
                ·
                  refine ⟨303107858562758210085263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808287622834021893560701 303107858562758210085263)
                  ·
                    rfl

theorem cell20_664088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_664088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664088 prefixEnd_664088 := by exact prefixLift 664088
  have htrace : WordTrace (prefixWord ++ tailWord_664088) baseStart_664088 baseEnd_664088 := by
    simpa [prefixWord, tailWord_664088, baseEnd_664088] using wordTrace_append hprefix tailTrace_664088
  have hstable : (prefixWord ++ tailWord_664088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664088).length < 2 ^ (prefixWord ++ tailWord_664088).sum := by decide
  have hdescent : baseEnd_664088 < baseStart_664088 := by decide
  rcases family_descends (prefixWord ++ tailWord_664088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664133 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 2]
def baseStart_664133 : Nat := 118140960795 + 664133 * 2 ^ 59
def prefixEnd_664133 : Nat := 4983230072969 + 3 ^ 40 * 664133 * 2
def baseEnd_664133 : Nat := 303128397788938053585079

theorem tailTrace_664133 : CollatzResearch.WordTrace tailWord_664133 prefixEnd_664133 303128397788938053585079 := by
  unfold tailWord_664133
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222920502967040731293053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16148613668644693820862035 24222920502967040731293053)
  ·
    refine ⟨9083595188612640274234895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24222920502967040731293053 9083595188612640274234895)
    ·
      refine ⟨13625392782918960411352343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9083595188612640274234895 13625392782918960411352343)
      ·
        refine ⟨20438089174378440617028515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13625392782918960411352343 20438089174378440617028515)
        ·
          refine ⟨30657133761567660925542773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20438089174378440617028515 30657133761567660925542773)
          ·
            refine ⟨2874106290146968211769635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30657133761567660925542773 2874106290146968211769635)
            ·
              refine ⟨4311159435220452317654453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874106290146968211769635 4311159435220452317654453)
              ·
                refine ⟨404171197051917404780105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4311159435220452317654453 404171197051917404780105)
                ·
                  refine ⟨303128397788938053585079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404171197051917404780105 303128397788938053585079)
                  ·
                    rfl

theorem cell20_664133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_664133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664133 prefixEnd_664133 := by exact prefixLift 664133
  have htrace : WordTrace (prefixWord ++ tailWord_664133) baseStart_664133 baseEnd_664133 := by
    simpa [prefixWord, tailWord_664133, baseEnd_664133] using wordTrace_append hprefix tailTrace_664133
  have hstable : (prefixWord ++ tailWord_664133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664133).length < 2 ^ (prefixWord ++ tailWord_664133).sum := by decide
  have hdescent : baseEnd_664133 < baseStart_664133 := by decide
  rcases family_descends (prefixWord ++ tailWord_664133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664164 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_664164 : Nat := 118140960795 + 664164 * 2 ^ 59
def prefixEnd_664164 : Nat := 4983230072969 + 3 ^ 40 * 664164 * 2
def baseEnd_664164 : Nat := 303142547033639723551619

theorem tailTrace_664164 : CollatzResearch.WordTrace tailWord_664164 prefixEnd_664164 303142547033639723551619 := by
  unfold tailWord_664164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112025582927366512835773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16149367443903155350447697 12112025582927366512835773)
  ·
    refine ⟨4542009593597762442313415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12112025582927366512835773 4542009593597762442313415)
    ·
      refine ⟨6813014390396643663470123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542009593597762442313415 6813014390396643663470123)
      ·
        refine ⟨10219521585594965495205185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813014390396643663470123 10219521585594965495205185)
        ·
          refine ⟨7664641189196224121403889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10219521585594965495205185 7664641189196224121403889)
          ·
            refine ⟨5748480891897168091052917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7664641189196224121403889 5748480891897168091052917)
            ·
              refine ⟨538920083615359508536211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5748480891897168091052917 538920083615359508536211)
              ·
                refine ⟨808380125423039262804317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538920083615359508536211 808380125423039262804317)
                ·
                  refine ⟨303142547033639723551619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808380125423039262804317 303142547033639723551619)
                  ·
                    rfl

theorem cell20_664164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_664164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664164 prefixEnd_664164 := by exact prefixLift 664164
  have htrace : WordTrace (prefixWord ++ tailWord_664164) baseStart_664164 baseEnd_664164 := by
    simpa [prefixWord, tailWord_664164, baseEnd_664164] using wordTrace_append hprefix tailTrace_664164
  have hstable : (prefixWord ++ tailWord_664164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664164).length < 2 ^ (prefixWord ++ tailWord_664164).sum := by decide
  have hdescent : baseEnd_664164 < baseStart_664164 := by decide
  rcases family_descends (prefixWord ++ tailWord_664164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664178 : List Nat := [3, 2, 1, 2, 4, 1, 1, 6]
def baseStart_664178 : Nat := 118140960795 + 664178 * 2 ^ 59
def prefixEnd_664178 : Nat := 4983230072969 + 3 ^ 40 * 664178 * 2
def baseEnd_664178 : Nat := 101049645671705965694965

theorem tailTrace_664178 : CollatzResearch.WordTrace tailWord_664178 prefixEnd_664178 101049645671705965694965 := by
  unfold tailWord_664178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056140446951003354170297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16149707858536008944454125 6056140446951003354170297)
  ·
    refine ⟨4542105335213252515627723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6056140446951003354170297 4542105335213252515627723)
    ·
      refine ⟨6813158002819878773441585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542105335213252515627723 6813158002819878773441585)
      ·
        refine ⟨5109868502114909080081189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6813158002819878773441585 5109868502114909080081189)
        ·
          refine ⟨958100344146545452515223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5109868502114909080081189 958100344146545452515223)
          ·
            refine ⟨1437150516219818178772835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958100344146545452515223 1437150516219818178772835)
            ·
              refine ⟨2155725774329727268159253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437150516219818178772835 2155725774329727268159253)
              ·
                refine ⟨101049645671705965694965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2155725774329727268159253 101049645671705965694965)
                ·
                  rfl

theorem cell20_664178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_664178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664178 prefixEnd_664178 := by exact prefixLift 664178
  have htrace : WordTrace (prefixWord ++ tailWord_664178) baseStart_664178 baseEnd_664178 := by
    simpa [prefixWord, tailWord_664178, baseEnd_664178] using wordTrace_append hprefix tailTrace_664178
  have hstable : (prefixWord ++ tailWord_664178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664178).length < 2 ^ (prefixWord ++ tailWord_664178).sum := by decide
  have hdescent : baseEnd_664178 < baseStart_664178 := by decide
  rcases family_descends (prefixWord ++ tailWord_664178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664264 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 2]
def baseStart_664264 : Nat := 118140960795 + 664264 * 2 ^ 59
def prefixEnd_664264 : Nat := 4983230072969 + 3 ^ 40 * 664264 * 2
def baseEnd_664264 : Nat := 303188189758483820217877

theorem tailTrace_664264 : CollatzResearch.WordTrace tailWord_664264 prefixEnd_664264 303188189758483820217877 := by
  unfold tailWord_664264
  simp only [CollatzResearch.WordTrace]
  refine ⟨12113849232746225052155923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16151798976994966736207897 12113849232746225052155923)
  ·
    refine ⟨18170773849119337578233885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12113849232746225052155923 18170773849119337578233885)
    ·
      refine ⟨6814040193419751591837707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18170773849119337578233885 6814040193419751591837707)
      ·
        refine ⟨10221060290129627387756561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814040193419751591837707 10221060290129627387756561)
        ·
          refine ⟨7665795217597220540817421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10221060290129627387756561 7665795217597220540817421)
          ·
            refine ⟨2874673206598957702806533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7665795217597220540817421 2874673206598957702806533)
            ·
              refine ⟨539001226237304569276225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2874673206598957702806533 539001226237304569276225)
              ·
                refine ⟨404250919677978426957169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539001226237304569276225 404250919677978426957169)
                ·
                  refine ⟨303188189758483820217877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404250919677978426957169 303188189758483820217877)
                  ·
                    rfl

theorem cell20_664264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_664264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664264 prefixEnd_664264 := by exact prefixLift 664264
  have htrace : WordTrace (prefixWord ++ tailWord_664264) baseStart_664264 baseEnd_664264 := by
    simpa [prefixWord, tailWord_664264, baseEnd_664264] using wordTrace_append hprefix tailTrace_664264
  have hstable : (prefixWord ++ tailWord_664264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664264).length < 2 ^ (prefixWord ++ tailWord_664264).sum := by decide
  have hdescent : baseEnd_664264 < baseStart_664264 := by decide
  rcases family_descends (prefixWord ++ tailWord_664264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664292 : List Nat := [2, 3, 1, 1, 1, 5, 3, 4]
def baseStart_664292 : Nat := 118140960795 + 664292 * 2 ^ 59
def prefixEnd_664292 : Nat := 4983230072969 + 3 ^ 40 * 664292 * 2
def baseEnd_664292 : Nat := 101066989907146722428143

theorem tailTrace_664292 : CollatzResearch.WordTrace tailWord_664292 prefixEnd_664292 101066989907146722428143 := by
  unfold tailWord_664292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114359854695505443165565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16152479806260673924220753 12114359854695505443165565)
  ·
    refine ⟨4542884945510814541187087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12114359854695505443165565 4542884945510814541187087)
    ·
      refine ⟨6814327418266221811780631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542884945510814541187087 6814327418266221811780631)
      ·
        refine ⟨10221491127399332717670947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814327418266221811780631 10221491127399332717670947)
        ·
          refine ⟨15332236691098999076506421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10221491127399332717670947 15332236691098999076506421)
          ·
            refine ⟨1437397189790531163422477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15332236691098999076506421 1437397189790531163422477)
            ·
              refine ⟨539023946171449186283429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1437397189790531163422477 539023946171449186283429)
              ·
                refine ⟨101066989907146722428143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 539023946171449186283429 101066989907146722428143)
                ·
                  rfl

theorem cell20_664292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_664292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664292 prefixEnd_664292 := by exact prefixLift 664292
  have htrace : WordTrace (prefixWord ++ tailWord_664292) baseStart_664292 baseEnd_664292 := by
    simpa [prefixWord, tailWord_664292, baseEnd_664292] using wordTrace_append hprefix tailTrace_664292
  have hstable : (prefixWord ++ tailWord_664292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664292).length < 2 ^ (prefixWord ++ tailWord_664292).sum := by decide
  have hdescent : baseEnd_664292 < baseStart_664292 := by decide
  rcases family_descends (prefixWord ++ tailWord_664292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664302 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_664302 : Nat := 118140960795 + 664302 * 2 ^ 59
def prefixEnd_664302 : Nat := 4983230072969 + 3 ^ 40 * 664302 * 2
def baseEnd_664302 : Nat := 303205533993924576951055

theorem tailTrace_664302 : CollatzResearch.WordTrace tailWord_664302 prefixEnd_664302 303205533993924576951055 := by
  unfold tailWord_664302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028635554919347824274395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16152722959569855062796773 3028635554919347824274395)
  ·
    refine ⟨4542953332379021736411593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3028635554919347824274395 4542953332379021736411593)
    ·
      refine ⟨3407214999284266302308695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4542953332379021736411593 3407214999284266302308695)
      ·
        refine ⟨5110822498926399453463043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407214999284266302308695 5110822498926399453463043)
        ·
          refine ⟨7666233748389599180194565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110822498926399453463043 7666233748389599180194565)
          ·
            refine ⟨1437418827823049846286481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7666233748389599180194565 1437418827823049846286481)
            ·
              refine ⟨1078064120867287384714861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437418827823049846286481 1078064120867287384714861)
              ·
                refine ⟨404274045325232769268073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1078064120867287384714861 404274045325232769268073)
                ·
                  refine ⟨303205533993924576951055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404274045325232769268073 303205533993924576951055)
                  ·
                    rfl

theorem cell20_664302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_664302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664302 prefixEnd_664302 := by exact prefixLift 664302
  have htrace : WordTrace (prefixWord ++ tailWord_664302) baseStart_664302 baseEnd_664302 := by
    simpa [prefixWord, tailWord_664302, baseEnd_664302] using wordTrace_append hprefix tailTrace_664302
  have hstable : (prefixWord ++ tailWord_664302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664302).length < 2 ^ (prefixWord ++ tailWord_664302).sum := by decide
  have hdescent : baseEnd_664302 < baseStart_664302 := by decide
  rcases family_descends (prefixWord ++ tailWord_664302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664316 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_664316 : Nat := 118140960795 + 664316 * 2 ^ 59
def prefixEnd_664316 : Nat := 4983230072969 + 3 ^ 40 * 664316 * 2
def baseEnd_664316 : Nat := 303211923975402750484331

theorem tailTrace_664316 : CollatzResearch.WordTrace tailWord_664316 prefixEnd_664316 303211923975402750484331 := by
  unfold tailWord_664316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114797530652031492602401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16153063374202708656803201 12114797530652031492602401)
  ·
    refine ⟨9086098147989023619451801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12114797530652031492602401 9086098147989023619451801)
    ·
      refine ⟨6814573610991767714588851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9086098147989023619451801 6814573610991767714588851)
      ·
        refine ⟨10221860416487651571883277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814573610991767714588851 10221860416487651571883277)
        ·
          refine ⟨3833197656182869339456229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10221860416487651571883277 3833197656182869339456229)
          ·
            refine ⟨718724560534288001148043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3833197656182869339456229 718724560534288001148043)
            ·
              refine ⟨1078086840801432001722065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718724560534288001148043 1078086840801432001722065)
              ·
                refine ⟨808565130601074001291549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078086840801432001722065 808565130601074001291549)
                ·
                  refine ⟨303211923975402750484331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808565130601074001291549 303211923975402750484331)
                  ·
                    rfl

theorem cell20_664316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_664316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664316 prefixEnd_664316 := by exact prefixLift 664316
  have htrace : WordTrace (prefixWord ++ tailWord_664316) baseStart_664316 baseEnd_664316 := by
    simpa [prefixWord, tailWord_664316, baseEnd_664316] using wordTrace_append hprefix tailTrace_664316
  have hstable : (prefixWord ++ tailWord_664316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664316).length < 2 ^ (prefixWord ++ tailWord_664316).sum := by decide
  have hdescent : baseEnd_664316 < baseStart_664316 := by decide
  rcases family_descends (prefixWord ++ tailWord_664316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664351 : List Nat := [1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_664351 : Nat := 118140960795 + 664351 * 2 ^ 59
def prefixEnd_664351 : Nat := 4983230072969 + 3 ^ 40 * 664351 * 2
def baseEnd_664351 : Nat := 101075966309699394772507

theorem tailTrace_664351 : CollatzResearch.WordTrace tailWord_664351 prefixEnd_664351 101075966309699394772507 := by
  unfold tailWord_664351
  simp only [CollatzResearch.WordTrace]
  refine ⟨24230871616177263962728907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16153914410784842641819271 24230871616177263962728907)
  ·
    refine ⟨36346307424265895944093361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24230871616177263962728907 36346307424265895944093361)
    ·
      refine ⟨27259730568199421958070021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36346307424265895944093361 27259730568199421958070021)
      ·
        refine ⟨5111199481537391617138129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27259730568199421958070021 5111199481537391617138129)
        ·
          refine ⟨3833399611153043712853597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5111199481537391617138129 3833399611153043712853597)
          ·
            refine ⟨1437524854182391392320099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3833399611153043712853597 1437524854182391392320099)
            ·
              refine ⟨2156287281273587088480149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437524854182391392320099 2156287281273587088480149)
              ·
                refine ⟨101075966309699394772507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2156287281273587088480149 101075966309699394772507)
                ·
                  rfl

theorem cell20_664351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_664351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664351 prefixEnd_664351 := by exact prefixLift 664351
  have htrace : WordTrace (prefixWord ++ tailWord_664351) baseStart_664351 baseEnd_664351 := by
    simpa [prefixWord, tailWord_664351, baseEnd_664351] using wordTrace_append hprefix tailTrace_664351
  have hstable : (prefixWord ++ tailWord_664351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664351).length < 2 ^ (prefixWord ++ tailWord_664351).sum := by decide
  have hdescent : baseEnd_664351 < baseStart_664351 := by decide
  rcases family_descends (prefixWord ++ tailWord_664351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664374 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_664374 : Nat := 118140960795 + 664374 * 2 ^ 59
def prefixEnd_664374 : Nat := 4983230072969 + 3 ^ 40 * 664374 * 2
def baseEnd_664374 : Nat := 303238396755812326550761

theorem tailTrace_664374 : CollatzResearch.WordTrace tailWord_664374 prefixEnd_664374 303238396755812326550761 := by
  unfold tailWord_664374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514481905943371180676011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16154473663395959260544117 1514481905943371180676011)
  ·
    refine ⟨2271722858915056771014017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1514481905943371180676011 2271722858915056771014017)
    ·
      refine ⟨1703792144186292578260513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2271722858915056771014017 1703792144186292578260513)
      ·
        refine ⟨1277844108139719433695385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1703792144186292578260513 1277844108139719433695385)
        ·
          refine ⟨958383081104789575271539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277844108139719433695385 958383081104789575271539)
          ·
            refine ⟨1437574621657184362907309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958383081104789575271539 1437574621657184362907309)
            ·
              refine ⟨539090483121444136090241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1437574621657184362907309 539090483121444136090241)
              ·
                refine ⟨404317862341083102067681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539090483121444136090241 404317862341083102067681)
                ·
                  refine ⟨303238396755812326550761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404317862341083102067681 303238396755812326550761)
                  ·
                    rfl

theorem cell20_664374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_664374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664374 prefixEnd_664374 := by exact prefixLift 664374
  have htrace : WordTrace (prefixWord ++ tailWord_664374) baseStart_664374 baseEnd_664374 := by
    simpa [prefixWord, tailWord_664374, baseEnd_664374] using wordTrace_append hprefix tailTrace_664374
  have hstable : (prefixWord ++ tailWord_664374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664374).length < 2 ^ (prefixWord ++ tailWord_664374).sum := by decide
  have hdescent : baseEnd_664374 < baseStart_664374 := by decide
  rcases family_descends (prefixWord ++ tailWord_664374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664378 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_664378 : Nat := 118140960795 + 664378 * 2 ^ 59
def prefixEnd_664378 : Nat := 4983230072969 + 3 ^ 40 * 664378 * 2
def baseEnd_664378 : Nat := 303240222464806090417411

theorem tailTrace_664378 : CollatzResearch.WordTrace tailWord_664378 prefixEnd_664378 303240222464806090417411 := by
  unfold tailWord_664378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057964096769861893490447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16154570924719631715974525 6057964096769861893490447)
  ·
    refine ⟨9086946145154792840235671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6057964096769861893490447 9086946145154792840235671)
    ·
      refine ⟨13630419217732189260353507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9086946145154792840235671 13630419217732189260353507)
      ·
        refine ⟨20445628826598283890530261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13630419217732189260353507 20445628826598283890530261)
        ·
          refine ⟨479194425623397278684303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20445628826598283890530261 479194425623397278684303)
          ·
            refine ⟨718791638435095918026455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479194425623397278684303 718791638435095918026455)
            ·
              refine ⟨1078187457652643877039683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718791638435095918026455 1078187457652643877039683)
              ·
                refine ⟨1617281186478965815559525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078187457652643877039683 1617281186478965815559525)
                ·
                  refine ⟨303240222464806090417411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617281186478965815559525 303240222464806090417411)
                  ·
                    rfl

theorem cell20_664378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_664378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664378 prefixEnd_664378 := by exact prefixLift 664378
  have htrace : WordTrace (prefixWord ++ tailWord_664378) baseStart_664378 baseEnd_664378 := by
    simpa [prefixWord, tailWord_664378, baseEnd_664378] using wordTrace_append hprefix tailTrace_664378
  have hstable : (prefixWord ++ tailWord_664378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664378).length < 2 ^ (prefixWord ++ tailWord_664378).sum := by decide
  have hdescent : baseEnd_664378 < baseStart_664378 := by decide
  rcases family_descends (prefixWord ++ tailWord_664378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664385 : List Nat := [1, 2, 5, 3, 1, 1, 2, 5]
def baseStart_664385 : Nat := 118140960795 + 664385 * 2 ^ 59
def prefixEnd_664385 : Nat := 4983230072969 + 3 ^ 40 * 664385 * 2
def baseEnd_664385 : Nat := 101081139151848392394683

theorem tailTrace_664385 : CollatzResearch.WordTrace tailWord_664385 prefixEnd_664385 101081139151848392394683 := by
  unfold tailWord_664385
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232111698054087769466609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16154741132036058512977739 24232111698054087769466609)
  ·
    refine ⟨18174083773540565827099957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24232111698054087769466609 18174083773540565827099957)
    ·
      refine ⟨1703820353769428046290621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18174083773540565827099957 1703820353769428046290621)
      ·
        refine ⟨638932632663535517358983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1703820353769428046290621 638932632663535517358983)
        ·
          refine ⟨958398948995303276038475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638932632663535517358983 958398948995303276038475)
          ·
            refine ⟨1437598423492954914057713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958398948995303276038475 1437598423492954914057713)
            ·
              refine ⟨1078198817619716185543285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437598423492954914057713 1078198817619716185543285)
              ·
                refine ⟨101081139151848392394683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078198817619716185543285 101081139151848392394683)
                ·
                  rfl

theorem cell20_664385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_664385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664385 prefixEnd_664385 := by exact prefixLift 664385
  have htrace : WordTrace (prefixWord ++ tailWord_664385) baseStart_664385 baseEnd_664385 := by
    simpa [prefixWord, tailWord_664385, baseEnd_664385] using wordTrace_append hprefix tailTrace_664385
  have hstable : (prefixWord ++ tailWord_664385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664385).length < 2 ^ (prefixWord ++ tailWord_664385).sum := by decide
  have hdescent : baseEnd_664385 < baseStart_664385 := by decide
  rcases family_descends (prefixWord ++ tailWord_664385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664403 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_664403 : Nat := 118140960795 + 664403 * 2 ^ 59
def prefixEnd_664403 : Nat := 4983230072969 + 3 ^ 40 * 664403 * 2
def baseEnd_664403 : Nat := 303251633146017114583975

theorem tailTrace_664403 : CollatzResearch.WordTrace tailWord_664403 prefixEnd_664403 303251633146017114583975 := by
  unfold tailWord_664403
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232768211988876843621863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16155178807992584562414575 24232768211988876843621863)
  ·
    refine ⟨36349152317983315265432795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24232768211988876843621863 36349152317983315265432795)
    ·
      refine ⟨54523728476974972898149193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36349152317983315265432795 54523728476974972898149193)
      ·
        refine ⟨40892796357731229673611895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54523728476974972898149193 40892796357731229673611895)
        ·
          refine ⟨61339194536596844510417843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40892796357731229673611895 61339194536596844510417843)
          ·
            refine ⟨92008791804895266765626765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61339194536596844510417843 92008791804895266765626765)
            ·
              refine ⟨34503296926835725037110037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92008791804895266765626765 34503296926835725037110037)
              ·
                refine ⟨1617342043445424611114533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34503296926835725037110037 1617342043445424611114533)
                ·
                  refine ⟨303251633146017114583975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617342043445424611114533 303251633146017114583975)
                  ·
                    rfl

theorem cell20_664403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_664403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664403 prefixEnd_664403 := by exact prefixLift 664403
  have htrace : WordTrace (prefixWord ++ tailWord_664403) baseStart_664403 baseEnd_664403 := by
    simpa [prefixWord, tailWord_664403, baseEnd_664403] using wordTrace_append hprefix tailTrace_664403
  have hstable : (prefixWord ++ tailWord_664403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664403).length < 2 ^ (prefixWord ++ tailWord_664403).sum := by decide
  have hdescent : baseEnd_664403 < baseStart_664403 := by decide
  rcases family_descends (prefixWord ++ tailWord_664403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664434 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_664434 : Nat := 118140960795 + 664434 * 2 ^ 59
def prefixEnd_664434 : Nat := 4983230072969 + 3 ^ 40 * 664434 * 2
def baseEnd_664434 : Nat := 303265782390718784550515

theorem tailTrace_664434 : CollatzResearch.WordTrace tailWord_664434 prefixEnd_664434 303265782390718784550515 := by
  unfold tailWord_664434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6058474718719142284500089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16155932583251046092000237 6058474718719142284500089)
  ·
    refine ⟨4543856039039356713375067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6058474718719142284500089 4543856039039356713375067)
    ·
      refine ⟨6815784058559035070062601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543856039039356713375067 6815784058559035070062601)
      ·
        refine ⟨5111838043919276302546951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6815784058559035070062601 5111838043919276302546951)
        ·
          refine ⟨7667757065878914453820427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111838043919276302546951 7667757065878914453820427)
          ·
            refine ⟨11501635598818371680730641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7667757065878914453820427 11501635598818371680730641)
            ·
              refine ⟨8626226699113778760547981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11501635598818371680730641 8626226699113778760547981)
              ·
                refine ⟨3234835012167667035205493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8626226699113778760547981 3234835012167667035205493)
                ·
                  refine ⟨303265782390718784550515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234835012167667035205493 303265782390718784550515)
                  ·
                    rfl

theorem cell20_664434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_664434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664434 prefixEnd_664434 := by exact prefixLift 664434
  have htrace : WordTrace (prefixWord ++ tailWord_664434) baseStart_664434 baseEnd_664434 := by
    simpa [prefixWord, tailWord_664434, baseEnd_664434] using wordTrace_append hprefix tailTrace_664434
  have hstable : (prefixWord ++ tailWord_664434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664434).length < 2 ^ (prefixWord ++ tailWord_664434).sum := by decide
  have hdescent : baseEnd_664434 < baseStart_664434 := by decide
  rcases family_descends (prefixWord ++ tailWord_664434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664448 : List Nat := [2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_664448 : Nat := 118140960795 + 664448 * 2 ^ 59
def prefixEnd_664448 : Nat := 4983230072969 + 3 ^ 40 * 664448 * 2
def baseEnd_664448 : Nat := 101090724124065652694597

theorem tailTrace_664448 : CollatzResearch.WordTrace tailWord_664448 prefixEnd_664448 101090724124065652694597 := by
  unfold tailWord_664448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12117204748412924764504999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16156272997883899686006665 12117204748412924764504999)
  ·
    refine ⟨18175807122619387146757499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12117204748412924764504999 18175807122619387146757499)
    ·
      refine ⟨27263710683929080720136249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18175807122619387146757499 27263710683929080720136249)
      ·
        refine ⟨20447783012946810540102187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27263710683929080720136249 20447783012946810540102187)
        ·
          refine ⟨30671674519420215810153281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20447783012946810540102187 30671674519420215810153281)
          ·
            refine ⟨23003755889565161857614961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30671674519420215810153281 23003755889565161857614961)
            ·
              refine ⟨17252816917173871393211221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23003755889565161857614961 17252816917173871393211221)
              ·
                refine ⟨101090724124065652694597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17252816917173871393211221 101090724124065652694597)
                ·
                  rfl

theorem cell20_664448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_664448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664448 prefixEnd_664448 := by exact prefixLift 664448
  have htrace : WordTrace (prefixWord ++ tailWord_664448) baseStart_664448 baseEnd_664448 := by
    simpa [prefixWord, tailWord_664448, baseEnd_664448] using wordTrace_append hprefix tailTrace_664448
  have hstable : (prefixWord ++ tailWord_664448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664448).length < 2 ^ (prefixWord ++ tailWord_664448).sum := by decide
  have hdescent : baseEnd_664448 < baseStart_664448 := by decide
  rcases family_descends (prefixWord ++ tailWord_664448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664458 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_664458 : Nat := 118140960795 + 664458 * 2 ^ 59
def prefixEnd_664458 : Nat := 4983230072969 + 3 ^ 40 * 664458 * 2
def baseEnd_664458 : Nat := 303276736644681367750417

theorem tailTrace_664458 : CollatzResearch.WordTrace tailWord_664458 prefixEnd_664458 303276736644681367750417 := by
  unfold tailWord_664458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6058693556697405309218507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16156516151193080824582685 6058693556697405309218507)
  ·
    refine ⟨9088040335046107963827761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6058693556697405309218507 9088040335046107963827761)
    ·
      refine ⟨6816030251284580972870821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9088040335046107963827761 6816030251284580972870821)
      ·
        refine ⟨1278005672115858932413279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6816030251284580972870821 1278005672115858932413279)
        ·
          refine ⟨1917008508173788398619919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278005672115858932413279 1917008508173788398619919)
          ·
            refine ⟨2875512762260682597929879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917008508173788398619919 2875512762260682597929879)
            ·
              refine ⟨4313269143391023896894819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875512762260682597929879 4313269143391023896894819)
              ·
                refine ⟨6469903715086535845342229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313269143391023896894819 6469903715086535845342229)
                ·
                  refine ⟨303276736644681367750417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6469903715086535845342229 303276736644681367750417)
                  ·
                    rfl

theorem cell20_664458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_664458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664458 prefixEnd_664458 := by exact prefixLift 664458
  have htrace : WordTrace (prefixWord ++ tailWord_664458) baseStart_664458 baseEnd_664458 := by
    simpa [prefixWord, tailWord_664458, baseEnd_664458] using wordTrace_append hprefix tailTrace_664458
  have hstable : (prefixWord ++ tailWord_664458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664458).length < 2 ^ (prefixWord ++ tailWord_664458).sum := by decide
  have hdescent : baseEnd_664458 < baseStart_664458 := by decide
  rcases family_descends (prefixWord ++ tailWord_664458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664516 : List Nat := [2, 3, 3, 3, 1, 2, 2, 4]
def baseStart_664516 : Nat := 118140960795 + 664516 * 2 ^ 59
def prefixEnd_664516 : Nat := 4983230072969 + 3 ^ 40 * 664516 * 2
def baseEnd_664516 : Nat := 101101069808363647938949

theorem tailTrace_664516 : CollatzResearch.WordTrace tailWord_664516 prefixEnd_664516 101101069808363647938949 := by
  unfold tailWord_664516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12118444830289748571242701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16157926440386331428323601 12118444830289748571242701)
  ·
    refine ⟨4544416811358655714216013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12118444830289748571242701 4544416811358655714216013)
    ·
      refine ⟨1704156304259495892831005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4544416811358655714216013 1704156304259495892831005)
      ·
        refine ⟨639058614097310959811627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1704156304259495892831005 639058614097310959811627)
        ·
          refine ⟨958587921145966439717441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639058614097310959811627 958587921145966439717441)
          ·
            refine ⟨718940940859474829788081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958587921145966439717441 718940940859474829788081)
            ·
              refine ⟨539205705644606122341061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718940940859474829788081 539205705644606122341061)
              ·
                refine ⟨101101069808363647938949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 539205705644606122341061 101101069808363647938949)
                ·
                  rfl

theorem cell20_664516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_664516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664516 prefixEnd_664516 := by exact prefixLift 664516
  have htrace : WordTrace (prefixWord ++ tailWord_664516) baseStart_664516 baseEnd_664516 := by
    simpa [prefixWord, tailWord_664516, baseEnd_664516] using wordTrace_append hprefix tailTrace_664516
  have hstable : (prefixWord ++ tailWord_664516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664516).length < 2 ^ (prefixWord ++ tailWord_664516).sum := by decide
  have hdescent : baseEnd_664516 < baseStart_664516 := by decide
  rcases family_descends (prefixWord ++ tailWord_664516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664530 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_664530 : Nat := 118140960795 + 664530 * 2 ^ 59
def prefixEnd_664530 : Nat := 4983230072969 + 3 ^ 40 * 664530 * 2
def baseEnd_664530 : Nat := 303309599406569117350123

theorem tailTrace_664530 : CollatzResearch.WordTrace tailWord_664530 prefixEnd_664530 303309599406569117350123 := by
  unfold tailWord_664530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6059350070632194383373761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16158266855019185022330029 6059350070632194383373761)
  ·
    refine ⟨4544512552974145787530321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6059350070632194383373761 4544512552974145787530321)
    ·
      refine ⟨3408384414730609340647741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4544512552974145787530321 3408384414730609340647741)
      ·
        refine ⟨1278144155523978502742903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3408384414730609340647741 1278144155523978502742903)
        ·
          refine ⟨1917216233285967754114355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278144155523978502742903 1917216233285967754114355)
          ·
            refine ⟨2875824349928951631171533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917216233285967754114355 2875824349928951631171533)
            ·
              refine ⟨1078434131223356861689325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2875824349928951631171533 1078434131223356861689325)
              ·
                refine ⟨404412799208758823133497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1078434131223356861689325 404412799208758823133497)
                ·
                  refine ⟨303309599406569117350123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404412799208758823133497 303309599406569117350123)
                  ·
                    rfl

theorem cell20_664530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_664530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664530 prefixEnd_664530 := by exact prefixLift 664530
  have htrace : WordTrace (prefixWord ++ tailWord_664530) baseStart_664530 baseEnd_664530 := by
    simpa [prefixWord, tailWord_664530, baseEnd_664530] using wordTrace_append hprefix tailTrace_664530
  have hstable : (prefixWord ++ tailWord_664530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664530).length < 2 ^ (prefixWord ++ tailWord_664530).sum := by decide
  have hdescent : baseEnd_664530 < baseStart_664530 := by decide
  rcases family_descends (prefixWord ++ tailWord_664530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664541 : List Nat := [1, 4, 3, 1, 2, 1, 8]
def baseStart_664541 : Nat := 118140960795 + 664541 * 2 ^ 59
def prefixEnd_664541 : Nat := 4983230072969 + 3 ^ 40 * 664541 * 2
def baseEnd_664541 : Nat := 33701624456255774220379

theorem tailTrace_664541 : CollatzResearch.WordTrace tailWord_664541 prefixEnd_664541 33701624456255774220379 := by
  unfold tailWord_664541
  simp only [CollatzResearch.WordTrace]
  refine ⟨24237801485488926412145477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16158534323659284274763651 24237801485488926412145477)
  ·
    refine ⟨4544587778529173702277277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24237801485488926412145477 4544587778529173702277277)
    ·
      refine ⟨1704220416948440138353979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4544587778529173702277277 1704220416948440138353979)
      ·
        refine ⟨2556330625422660207530969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704220416948440138353979 2556330625422660207530969)
        ·
          refine ⟨1917247969066995155648227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556330625422660207530969 1917247969066995155648227)
          ·
            refine ⟨2875871953600492733472341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917247969066995155648227 2875871953600492733472341)
            ·
              refine ⟨33701624456255774220379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2875871953600492733472341 33701624456255774220379)
              ·
                rfl

theorem cell20_664541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_664541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664541 prefixEnd_664541 := by exact prefixLift 664541
  have htrace : WordTrace (prefixWord ++ tailWord_664541) baseStart_664541 baseEnd_664541 := by
    simpa [prefixWord, tailWord_664541, baseEnd_664541] using wordTrace_append hprefix tailTrace_664541
  have hstable : (prefixWord ++ tailWord_664541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664541).length < 2 ^ (prefixWord ++ tailWord_664541).sum := by decide
  have hdescent : baseEnd_664541 < baseStart_664541 := by decide
  rcases family_descends (prefixWord ++ tailWord_664541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664551 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 4]
def baseStart_664551 : Nat := 118140960795 + 664551 * 2 ^ 59
def prefixEnd_664551 : Nat := 4983230072969 + 3 ^ 40 * 664551 * 2
def baseEnd_664551 : Nat := 303319184378786377650037

theorem tailTrace_664551 : CollatzResearch.WordTrace tailWord_664551 prefixEnd_664551 303319184378786377650037 := by
  unfold tailWord_664551
  simp only [CollatzResearch.WordTrace]
  refine ⟨24238166215452698120009507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16158777476968465413339671 24238166215452698120009507)
  ·
    refine ⟨36357249323179047180014261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24238166215452698120009507 36357249323179047180014261)
    ·
      refine ⟨3408492124048035673126337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36357249323179047180014261 3408492124048035673126337)
      ·
        refine ⟨2556369093036026754844753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3408492124048035673126337 2556369093036026754844753)
        ·
          refine ⟨1917276819777020066133565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556369093036026754844753 1917276819777020066133565)
          ·
            refine ⟨718978807416382524800087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1917276819777020066133565 718978807416382524800087)
            ·
              refine ⟨1078468211124573787200131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718978807416382524800087 1078468211124573787200131)
              ·
                refine ⟨1617702316686860680800197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078468211124573787200131 1617702316686860680800197)
                ·
                  refine ⟨303319184378786377650037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617702316686860680800197 303319184378786377650037)
                  ·
                    rfl

theorem cell20_664551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_664551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664551 prefixEnd_664551 := by exact prefixLift 664551
  have htrace : WordTrace (prefixWord ++ tailWord_664551) baseStart_664551 baseEnd_664551 := by
    simpa [prefixWord, tailWord_664551, baseEnd_664551] using wordTrace_append hprefix tailTrace_664551
  have hstable : (prefixWord ++ tailWord_664551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664551).length < 2 ^ (prefixWord ++ tailWord_664551).sum := by decide
  have hdescent : baseEnd_664551 < baseStart_664551 := by decide
  rcases family_descends (prefixWord ++ tailWord_664551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664558 : List Nat := [4, 1, 2, 1, 4, 1, 2, 5]
def baseStart_664558 : Nat := 118140960795 + 664558 * 2 ^ 59
def prefixEnd_664558 : Nat := 4983230072969 + 3 ^ 40 * 664558 * 2
def baseEnd_664558 : Nat := 101107459789841821472225

theorem tailTrace_664558 : CollatzResearch.WordTrace tailWord_664558 prefixEnd_664558 101107459789841821472225 := by
  unfold tailWord_664558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029802690803417289439291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16158947684284892210342885 3029802690803417289439291)
  ·
    refine ⟨4544704036205125934158937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029802690803417289439291 4544704036205125934158937)
    ·
      refine ⟨3408528027153844450619203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4544704036205125934158937 3408528027153844450619203)
      ·
        refine ⟨5112792040730766675928805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408528027153844450619203 5112792040730766675928805)
        ·
          refine ⟨958648507637018751736651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5112792040730766675928805 958648507637018751736651)
          ·
            refine ⟨1437972761455528127604977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958648507637018751736651 1437972761455528127604977)
            ·
              refine ⟨1078479571091646095703733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437972761455528127604977 1078479571091646095703733)
              ·
                refine ⟨101107459789841821472225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078479571091646095703733 101107459789841821472225)
                ·
                  rfl

theorem cell20_664558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_664558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664558 prefixEnd_664558 := by exact prefixLift 664558
  have htrace : WordTrace (prefixWord ++ tailWord_664558) baseStart_664558 baseEnd_664558 := by
    simpa [prefixWord, tailWord_664558, baseEnd_664558] using wordTrace_append hprefix tailTrace_664558
  have hstable : (prefixWord ++ tailWord_664558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664558).length < 2 ^ (prefixWord ++ tailWord_664558).sum := by decide
  have hdescent : baseEnd_664558 < baseStart_664558 := by decide
  rcases family_descends (prefixWord ++ tailWord_664558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664600 : List Nat := [2, 1, 2, 3, 2, 10]
def baseStart_664600 : Nat := 118140960795 + 664600 * 2 ^ 59
def prefixEnd_664600 : Nat := 4983230072969 + 3 ^ 40 * 664600 * 2
def baseEnd_664600 : Nat := 11234872196813332778389

theorem tailTrace_664600 : CollatzResearch.WordTrace tailWord_664600 prefixEnd_664600 11234872196813332778389 := by
  unfold tailWord_664600
  simp only [CollatzResearch.WordTrace]
  refine ⟨12119976696137589744271627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16159968928183452992362169 12119976696137589744271627)
  ·
    refine ⟨18179965044206384616407441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12119976696137589744271627 18179965044206384616407441)
    ·
      refine ⟨13634973783154788462305581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18179965044206384616407441 13634973783154788462305581)
      ·
        refine ⟨5113115168683045673364593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13634973783154788462305581 5113115168683045673364593)
        ·
          refine ⟨3834836376512284255023445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5113115168683045673364593 3834836376512284255023445)
          ·
            refine ⟨11234872196813332778389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3834836376512284255023445 11234872196813332778389)
            ·
              rfl

theorem cell20_664600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 10].length) (baseStart_664600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664600 prefixEnd_664600 := by exact prefixLift 664600
  have htrace : WordTrace (prefixWord ++ tailWord_664600) baseStart_664600 baseEnd_664600 := by
    simpa [prefixWord, tailWord_664600, baseEnd_664600] using wordTrace_append hprefix tailTrace_664600
  have hstable : (prefixWord ++ tailWord_664600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664600).length < 2 ^ (prefixWord ++ tailWord_664600).sum := by decide
  have hdescent : baseEnd_664600 < baseStart_664600 := by decide
  rcases family_descends (prefixWord ++ tailWord_664600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664624 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_664624 : Nat := 118140960795 + 664624 * 2 ^ 59
def prefixEnd_664624 : Nat := 4983230072969 + 3 ^ 40 * 664624 * 2
def baseEnd_664624 : Nat := 303352503567922568216405

theorem tailTrace_664624 : CollatzResearch.WordTrace tailWord_664624 prefixEnd_664624 303352503567922568216405 := by
  unfold tailWord_664624
  simp only [CollatzResearch.WordTrace]
  refine ⟨12120414372094115793708463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16160552496125487724944617 12120414372094115793708463)
  ·
    refine ⟨18180621558141173690562695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12120414372094115793708463 18180621558141173690562695)
    ·
      refine ⟨27270932337211760535844043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18180621558141173690562695 27270932337211760535844043)
      ·
        refine ⟨40906398505817640803766065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27270932337211760535844043 40906398505817640803766065)
        ·
          refine ⟨30679798879363230602824549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40906398505817640803766065 30679798879363230602824549)
          ·
            refine ⟨5752462289880605738029603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30679798879363230602824549 5752462289880605738029603)
            ·
              refine ⟨8628693434820908607044405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752462289880605738029603 8628693434820908607044405)
              ·
                refine ⟨808940009514460181910413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8628693434820908607044405 808940009514460181910413)
                ·
                  refine ⟨303352503567922568216405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808940009514460181910413 303352503567922568216405)
                  ·
                    rfl

theorem cell20_664624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_664624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664624 prefixEnd_664624 := by exact prefixLift 664624
  have htrace : WordTrace (prefixWord ++ tailWord_664624) baseStart_664624 baseEnd_664624 := by
    simpa [prefixWord, tailWord_664624, baseEnd_664624] using wordTrace_append hprefix tailTrace_664624
  have hstable : (prefixWord ++ tailWord_664624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664624).length < 2 ^ (prefixWord ++ tailWord_664624).sum := by decide
  have hdescent : baseEnd_664624 < baseStart_664624 := by decide
  rcases family_descends (prefixWord ++ tailWord_664624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664658 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_664658 : Nat := 118140960795 + 664658 * 2 ^ 59
def prefixEnd_664658 : Nat := 4983230072969 + 3 ^ 40 * 664658 * 2
def baseEnd_664658 : Nat := 303368022094369561082933

theorem tailTrace_664658 : CollatzResearch.WordTrace tailWord_664658 prefixEnd_664658 303368022094369561082933 := by
  unfold tailWord_664658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6060517206516263848538657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16161379217376703596103085 6060517206516263848538657)
  ·
    refine ⟨4545387904887197886403993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6060517206516263848538657 4545387904887197886403993)
    ·
      refine ⟨3409040928665398414802995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4545387904887197886403993 3409040928665398414802995)
      ·
        refine ⟨5113561392998097622204493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409040928665398414802995 5113561392998097622204493)
        ·
          refine ⟨1917585522374286608326685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5113561392998097622204493 1917585522374286608326685)
          ·
            refine ⟨719094570890357478122507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1917585522374286608326685 719094570890357478122507)
            ·
              refine ⟨1078641856335536217183761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719094570890357478122507 1078641856335536217183761)
              ·
                refine ⟨808981392251652162887821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078641856335536217183761 808981392251652162887821)
                ·
                  refine ⟨303368022094369561082933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808981392251652162887821 303368022094369561082933)
                  ·
                    rfl

theorem cell20_664658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_664658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664658 prefixEnd_664658 := by exact prefixLift 664658
  have htrace : WordTrace (prefixWord ++ tailWord_664658) baseStart_664658 baseEnd_664658 := by
    simpa [prefixWord, tailWord_664658, baseEnd_664658] using wordTrace_append hprefix tailTrace_664658
  have hstable : (prefixWord ++ tailWord_664658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664658).length < 2 ^ (prefixWord ++ tailWord_664658).sum := by decide
  have hdescent : baseEnd_664658 < baseStart_664658 := by decide
  rcases family_descends (prefixWord ++ tailWord_664658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664676 : List Nat := [2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_664676 : Nat := 118140960795 + 664676 * 2 ^ 59
def prefixEnd_664676 : Nat := 4983230072969 + 3 ^ 40 * 664676 * 2
def baseEnd_664676 : Nat := 101125412594947166160953

theorem tailTrace_664676 : CollatzResearch.WordTrace tailWord_664676 prefixEnd_664676 101125412594947166160953 := by
  unfold tailWord_664676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121362669999922234154941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16161816893333229645539921 12121362669999922234154941)
  ·
    refine ⟨4545511001249970837808103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12121362669999922234154941 4545511001249970837808103)
    ·
      refine ⟨6818266501874956256712155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4545511001249970837808103 6818266501874956256712155)
      ·
        refine ⟨10227399752812434385068233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6818266501874956256712155 10227399752812434385068233)
        ·
          refine ⟨7670549814609325788801175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10227399752812434385068233 7670549814609325788801175)
          ·
            refine ⟨11505824721913988683201763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7670549814609325788801175 11505824721913988683201763)
            ·
              refine ⟨17258737082870983024802645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505824721913988683201763 17258737082870983024802645)
              ·
                refine ⟨101125412594947166160953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17258737082870983024802645 101125412594947166160953)
                ·
                  rfl

theorem cell20_664676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_664676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664676 prefixEnd_664676 := by exact prefixLift 664676
  have htrace : WordTrace (prefixWord ++ tailWord_664676) baseStart_664676 baseEnd_664676 := by
    simpa [prefixWord, tailWord_664676, baseEnd_664676] using wordTrace_append hprefix tailTrace_664676
  have hstable : (prefixWord ++ tailWord_664676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664676).length < 2 ^ (prefixWord ++ tailWord_664676).sum := by decide
  have hdescent : baseEnd_664676 < baseStart_664676 := by decide
  rcases family_descends (prefixWord ++ tailWord_664676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664686 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_664686 : Nat := 118140960795 + 664686 * 2 ^ 59
def prefixEnd_664686 : Nat := 4983230072969 + 3 ^ 40 * 664686 * 2
def baseEnd_664686 : Nat := 303380802057325908149485

theorem tailTrace_664686 : CollatzResearch.WordTrace tailWord_664686 prefixEnd_664686 303380802057325908149485 := by
  unfold tailWord_664686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030386258745452022021739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16162060046642410784115941 3030386258745452022021739)
  ·
    refine ⟨4545579388118178033032609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3030386258745452022021739 4545579388118178033032609)
    ·
      refine ⟨3409184541088633524774457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4545579388118178033032609 3409184541088633524774457)
      ·
        refine ⟨2556888405816475143580843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3409184541088633524774457 2556888405816475143580843)
        ·
          refine ⟨3835332608724712715371265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556888405816475143580843 3835332608724712715371265)
          ·
            refine ⟨2876499456543534536528449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3835332608724712715371265 2876499456543534536528449)
            ·
              refine ⟨2157374592407650902396337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2876499456543534536528449 2157374592407650902396337)
              ·
                refine ⟨1618030944305738176797253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2157374592407650902396337 1618030944305738176797253)
                ·
                  refine ⟨303380802057325908149485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618030944305738176797253 303380802057325908149485)
                  ·
                    rfl

theorem cell20_664686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_664686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664686 prefixEnd_664686 := by exact prefixLift 664686
  have htrace : WordTrace (prefixWord ++ tailWord_664686) baseStart_664686 baseEnd_664686 := by
    simpa [prefixWord, tailWord_664686, baseEnd_664686] using wordTrace_append hprefix tailTrace_664686
  have hstable : (prefixWord ++ tailWord_664686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664686).length < 2 ^ (prefixWord ++ tailWord_664686).sum := by decide
  have hdescent : baseEnd_664686 < baseStart_664686 := by decide
  rcases family_descends (prefixWord ++ tailWord_664686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664734 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_664734 : Nat := 118140960795 + 664734 * 2 ^ 59
def prefixEnd_664734 : Nat := 4983230072969 + 3 ^ 40 * 664734 * 2
def baseEnd_664734 : Nat := 303402710565251074549289

theorem tailTrace_664734 : CollatzResearch.WordTrace tailWord_664734 prefixEnd_664734 303402710565251074549289 := by
  unfold tailWord_664734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030605096723715046740157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16163227182526480249280837 3030605096723715046740157)
  ·
    refine ⟨1136476911271393142527559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3030605096723715046740157 1136476911271393142527559)
    ·
      refine ⟨1704715366907089713791339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136476911271393142527559 1704715366907089713791339)
      ·
        refine ⟨2557073050360634570687009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704715366907089713791339 2557073050360634570687009)
        ·
          refine ⟨1917804787770475928015257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2557073050360634570687009 1917804787770475928015257)
          ·
            refine ⟨1438353590827856946011443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917804787770475928015257 1438353590827856946011443)
            ·
              refine ⟨2157530386241785419017165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438353590827856946011443 2157530386241785419017165)
              ·
                refine ⟨809073894840669532131437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2157530386241785419017165 809073894840669532131437)
                ·
                  refine ⟨303402710565251074549289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809073894840669532131437 303402710565251074549289)
                  ·
                    rfl

theorem cell20_664734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_664734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664734 prefixEnd_664734 := by exact prefixLift 664734
  have htrace : WordTrace (prefixWord ++ tailWord_664734) baseStart_664734 baseEnd_664734 := by
    simpa [prefixWord, tailWord_664734, baseEnd_664734] using wordTrace_append hprefix tailTrace_664734
  have hstable : (prefixWord ++ tailWord_664734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664734).length < 2 ^ (prefixWord ++ tailWord_664734).sum := by decide
  have hdescent : baseEnd_664734 < baseStart_664734 := by decide
  rcases family_descends (prefixWord ++ tailWord_664734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664762 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_664762 : Nat := 118140960795 + 664762 * 2 ^ 59
def prefixEnd_664762 : Nat := 4983230072969 + 3 ^ 40 * 664762 * 2
def baseEnd_664762 : Nat := 303415490528207421615841

theorem tailTrace_664762 : CollatzResearch.WordTrace tailWord_664762 prefixEnd_664762 303415490528207421615841 := by
  unfold tailWord_664762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061465504422070288985135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16163908011792187437293693 6061465504422070288985135)
  ·
    refine ⟨9092198256633105433477703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6061465504422070288985135 9092198256633105433477703)
    ·
      refine ⟨13638297384949658150216555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9092198256633105433477703 13638297384949658150216555)
      ·
        refine ⟨20457446077424487225324833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13638297384949658150216555 20457446077424487225324833)
        ·
          refine ⟨15343084558068365418993625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20457446077424487225324833 15343084558068365418993625)
          ·
            refine ⟨11507313418551274064245219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15343084558068365418993625 11507313418551274064245219)
            ·
              refine ⟨17260970127826911096367829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11507313418551274064245219 17260970127826911096367829)
              ·
                refine ⟨404553987370943228821121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17260970127826911096367829 404553987370943228821121)
                ·
                  refine ⟨303415490528207421615841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404553987370943228821121 303415490528207421615841)
                  ·
                    rfl

theorem cell20_664762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_664762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664762 prefixEnd_664762 := by exact prefixLift 664762
  have htrace : WordTrace (prefixWord ++ tailWord_664762) baseStart_664762 baseEnd_664762 := by
    simpa [prefixWord, tailWord_664762, baseEnd_664762] using wordTrace_append hprefix tailTrace_664762
  have hstable : (prefixWord ++ tailWord_664762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664762).length < 2 ^ (prefixWord ++ tailWord_664762).sum := by decide
  have hdescent : baseEnd_664762 < baseStart_664762 := by decide
  rcases family_descends (prefixWord ++ tailWord_664762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664769 : List Nat := [1, 2, 6, 1, 1, 9]
def baseStart_664769 : Nat := 118140960795 + 664769 * 2 ^ 59
def prefixEnd_664769 : Nat := 4983230072969 + 3 ^ 40 * 664769 * 2
def baseEnd_664769 : Nat := 11237729093294315125277

theorem tailTrace_664769 : CollatzResearch.WordTrace tailWord_664769 prefixEnd_664769 11237729093294315125277 := by
  unfold tailWord_664769
  simp only [CollatzResearch.WordTrace]
  refine ⟨24246117328662921351445361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16164078219108614234296907 24246117328662921351445361)
  ·
    refine ⟨18184587996497191013584021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24246117328662921351445361 18184587996497191013584021)
    ·
      refine ⟨852402562335805828761751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18184587996497191013584021 852402562335805828761751)
      ·
        refine ⟨1278603843503708743142627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852402562335805828761751 1278603843503708743142627)
        ·
          refine ⟨1917905765255563114713941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278603843503708743142627 1917905765255563114713941)
          ·
            refine ⟨11237729093294315125277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1917905765255563114713941 11237729093294315125277)
            ·
              rfl

theorem cell20_664769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 9].length) (baseStart_664769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664769 prefixEnd_664769 := by exact prefixLift 664769
  have htrace : WordTrace (prefixWord ++ tailWord_664769) baseStart_664769 baseEnd_664769 := by
    simpa [prefixWord, tailWord_664769, baseEnd_664769] using wordTrace_append hprefix tailTrace_664769
  have hstable : (prefixWord ++ tailWord_664769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664769).length < 2 ^ (prefixWord ++ tailWord_664769).sum := by decide
  have hdescent : baseEnd_664769 < baseStart_664769 := by decide
  rcases family_descends (prefixWord ++ tailWord_664769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664772 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_664772 : Nat := 118140960795 + 664772 * 2 ^ 59
def prefixEnd_664772 : Nat := 4983230072969 + 3 ^ 40 * 664772 * 2
def baseEnd_664772 : Nat := 303420054800691831282467

theorem tailTrace_664772 : CollatzResearch.WordTrace tailWord_664772 prefixEnd_664772 303420054800691831282467 := by
  unfold tailWord_664772
  simp only [CollatzResearch.WordTrace]
  refine ⟨12123113373826026431902285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16164151165101368575869713 12123113373826026431902285)
  ·
    refine ⟨4546167515184759911963357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12123113373826026431902285 4546167515184759911963357)
    ·
      refine ⟨1704812818194284966986259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4546167515184759911963357 1704812818194284966986259)
      ·
        refine ⟨2557219227291427450479389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704812818194284966986259 2557219227291427450479389)
        ·
          refine ⟨958957210234285293929771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2557219227291427450479389 958957210234285293929771)
          ·
            refine ⟨1438435815351427940894657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958957210234285293929771 1438435815351427940894657)
            ·
              refine ⟨1078826861513570955670993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438435815351427940894657 1078826861513570955670993)
              ·
                refine ⟨809120146135178216753245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078826861513570955670993 809120146135178216753245)
                ·
                  refine ⟨303420054800691831282467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809120146135178216753245 303420054800691831282467)
                  ·
                    rfl

theorem cell20_664772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_664772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664772 prefixEnd_664772 := by exact prefixLift 664772
  have htrace : WordTrace (prefixWord ++ tailWord_664772) baseStart_664772 baseEnd_664772 := by
    simpa [prefixWord, tailWord_664772, baseEnd_664772] using wordTrace_append hprefix tailTrace_664772
  have hstable : (prefixWord ++ tailWord_664772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664772).length < 2 ^ (prefixWord ++ tailWord_664772).sum := by decide
  have hdescent : baseEnd_664772 < baseStart_664772 := by decide
  rcases family_descends (prefixWord ++ tailWord_664772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664776 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_664776 : Nat := 118140960795 + 664776 * 2 ^ 59
def prefixEnd_664776 : Nat := 4983230072969 + 3 ^ 40 * 664776 * 2
def baseEnd_664776 : Nat := 303421880509685595149117

theorem tailTrace_664776 : CollatzResearch.WordTrace tailWord_664776 prefixEnd_664776 303421880509685595149117 := by
  unfold tailWord_664776
  simp only [CollatzResearch.WordTrace]
  refine ⟨12123186319818780773475091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16164248426425041031300121 12123186319818780773475091)
  ·
    refine ⟨18184779479728171160212637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12123186319818780773475091 18184779479728171160212637)
    ·
      refine ⟨6819292304898064185079739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18184779479728171160212637 6819292304898064185079739)
      ·
        refine ⟨10228938457347096277619609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6819292304898064185079739 10228938457347096277619609)
        ·
          refine ⟨7671703843010322208214707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10228938457347096277619609 7671703843010322208214707)
          ·
            refine ⟨11507555764515483312322061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7671703843010322208214707 11507555764515483312322061)
            ·
              refine ⟨4315333411693306242120773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11507555764515483312322061 4315333411693306242120773)
              ·
                refine ⟨809125014692494920397645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4315333411693306242120773 809125014692494920397645)
                ·
                  refine ⟨303421880509685595149117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809125014692494920397645 303421880509685595149117)
                  ·
                    rfl

theorem cell20_664776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_664776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664776 prefixEnd_664776 := by exact prefixLift 664776
  have htrace : WordTrace (prefixWord ++ tailWord_664776) baseStart_664776 baseEnd_664776 := by
    simpa [prefixWord, tailWord_664776, baseEnd_664776] using wordTrace_append hprefix tailTrace_664776
  have hstable : (prefixWord ++ tailWord_664776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664776).length < 2 ^ (prefixWord ++ tailWord_664776).sum := by decide
  have hdescent : baseEnd_664776 < baseStart_664776 := by decide
  rcases family_descends (prefixWord ++ tailWord_664776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664831 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 3]
def baseStart_664831 : Nat := 118140960795 + 664831 * 2 ^ 59
def prefixEnd_664831 : Nat := 4983230072969 + 3 ^ 40 * 664831 * 2
def baseEnd_664831 : Nat := 303446984008349848315559

theorem tailTrace_664831 : CollatzResearch.WordTrace tailWord_664831 prefixEnd_664831 303446984008349848315559 := by
  unfold tailWord_664831
  simp only [CollatzResearch.WordTrace]
  refine ⟨24248378654438305940202347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16165585769625537293468231 24248378654438305940202347)
  ·
    refine ⟨36372567981657458910303521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24248378654438305940202347 36372567981657458910303521)
    ·
      refine ⟨27279425986243094182727641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36372567981657458910303521 27279425986243094182727641)
      ·
        refine ⟨20459569489682320637045731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27279425986243094182727641 20459569489682320637045731)
        ·
          refine ⟨30689354234523480955568597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20459569489682320637045731 30689354234523480955568597)
          ·
            refine ⟨719281739871644084896139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30689354234523480955568597 719281739871644084896139)
            ·
              refine ⟨1078922609807466127344209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719281739871644084896139 1078922609807466127344209)
              ·
                refine ⟨809191957355599595508157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078922609807466127344209 809191957355599595508157)
                ·
                  refine ⟨303446984008349848315559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809191957355599595508157 303446984008349848315559)
                  ·
                    rfl

theorem cell20_664831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_664831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664831 prefixEnd_664831 := by exact prefixLift 664831
  have htrace : WordTrace (prefixWord ++ tailWord_664831) baseStart_664831 baseEnd_664831 := by
    simpa [prefixWord, tailWord_664831, baseEnd_664831] using wordTrace_append hprefix tailTrace_664831
  have hstable : (prefixWord ++ tailWord_664831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664831).length < 2 ^ (prefixWord ++ tailWord_664831).sum := by decide
  have hdescent : baseEnd_664831 < baseStart_664831 := by decide
  rcases family_descends (prefixWord ++ tailWord_664831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664872 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 2]
def baseStart_664872 : Nat := 118140960795 + 664872 * 2 ^ 59
def prefixEnd_664872 : Nat := 4983230072969 + 3 ^ 40 * 664872 * 2
def baseEnd_664872 : Nat := 303465697525535927948725

theorem tailTrace_664872 : CollatzResearch.WordTrace tailWord_664872 prefixEnd_664872 303465697525535927948725 := by
  unfold tailWord_664872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12124937023644884971222435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16166582698193179961629913 12124937023644884971222435)
  ·
    refine ⟨18187405535467327456833653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12124937023644884971222435 18187405535467327456833653)
    ·
      refine ⟨1705069268950061949078155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18187405535467327456833653 1705069268950061949078155)
      ·
        refine ⟨2557603903425092923617233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705069268950061949078155 2557603903425092923617233)
        ·
          refine ⟨1918202927568819692712925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2557603903425092923617233 1918202927568819692712925)
          ·
            refine ⟨719326097838307384767347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1918202927568819692712925 719326097838307384767347)
            ·
              refine ⟨1078989146757461077151021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719326097838307384767347 1078989146757461077151021)
              ·
                refine ⟨404620930034047903931633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1078989146757461077151021 404620930034047903931633)
                ·
                  refine ⟨303465697525535927948725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404620930034047903931633 303465697525535927948725)
                  ·
                    rfl

theorem cell20_664872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_664872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664872 prefixEnd_664872 := by exact prefixLift 664872
  have htrace : WordTrace (prefixWord ++ tailWord_664872) baseStart_664872 baseEnd_664872 := by
    simpa [prefixWord, tailWord_664872, baseEnd_664872] using wordTrace_append hprefix tailTrace_664872
  have hstable : (prefixWord ++ tailWord_664872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664872).length < 2 ^ (prefixWord ++ tailWord_664872).sum := by decide
  have hdescent : baseEnd_664872 < baseStart_664872 := by decide
  rcases family_descends (prefixWord ++ tailWord_664872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664890 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_664890 : Nat := 118140960795 + 664890 * 2 ^ 59
def prefixEnd_664890 : Nat := 4983230072969 + 3 ^ 40 * 664890 * 2
def baseEnd_664890 : Nat := 303473913216007865348651

theorem tailTrace_664890 : CollatzResearch.WordTrace tailWord_664890 prefixEnd_664890 303473913216007865348651 := by
  unfold tailWord_664890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062632640306139754150031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16167020374149706011066749 6062632640306139754150031)
  ·
    refine ⟨9093948960459209631225047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062632640306139754150031 9093948960459209631225047)
    ·
      refine ⟨13640923440688814446837571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093948960459209631225047 13640923440688814446837571)
      ·
        refine ⟨20461385161033221670256357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13640923440688814446837571 20461385161033221670256357)
        ·
          refine ⟨3836509717693729063173067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20461385161033221670256357 3836509717693729063173067)
          ·
            refine ⟨5754764576540593594759601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836509717693729063173067 5754764576540593594759601)
            ·
              refine ⟨4316073432405445196069701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5754764576540593594759601 4316073432405445196069701)
              ·
                refine ⟨809263768576020974263069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4316073432405445196069701 809263768576020974263069)
                ·
                  refine ⟨303473913216007865348651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809263768576020974263069 303473913216007865348651)
                  ·
                    rfl

theorem cell20_664890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_664890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664890 prefixEnd_664890 := by exact prefixLift 664890
  have htrace : WordTrace (prefixWord ++ tailWord_664890) baseStart_664890 baseEnd_664890 := by
    simpa [prefixWord, tailWord_664890, baseEnd_664890] using wordTrace_append hprefix tailTrace_664890
  have hstable : (prefixWord ++ tailWord_664890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664890).length < 2 ^ (prefixWord ++ tailWord_664890).sum := by decide
  have hdescent : baseEnd_664890 < baseStart_664890 := by decide
  rcases family_descends (prefixWord ++ tailWord_664890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664900 : List Nat := [2, 3, 4, 1, 1, 2, 2, 5]
def baseStart_664900 : Nat := 118140960795 + 664900 * 2 ^ 59
def prefixEnd_664900 : Nat := 4983230072969 + 3 ^ 40 * 664900 * 2
def baseEnd_664900 : Nat := 101159492496164091671759

theorem tailTrace_664900 : CollatzResearch.WordTrace tailWord_664900 prefixEnd_664900 101159492496164091671759 := by
  unfold tailWord_664900
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125447645594165362232077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16167263527458887149642769 12125447645594165362232077)
  ·
    refine ⟨4547042867097812010837029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12125447645594165362232077 4547042867097812010837029)
    ·
      refine ⟨852570537580839752031943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4547042867097812010837029 852570537580839752031943)
      ·
        refine ⟨1278855806371259628047915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852570537580839752031943 1278855806371259628047915)
        ·
          refine ⟨1918283709556889442071873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278855806371259628047915 1918283709556889442071873)
          ·
            refine ⟨1438712782167667081553905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918283709556889442071873 1438712782167667081553905)
            ·
              refine ⟨1079034586625750311165429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438712782167667081553905 1079034586625750311165429)
              ·
                refine ⟨101159492496164091671759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1079034586625750311165429 101159492496164091671759)
                ·
                  rfl

theorem cell20_664900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_664900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664900 prefixEnd_664900 := by exact prefixLift 664900
  have htrace : WordTrace (prefixWord ++ tailWord_664900) baseStart_664900 baseEnd_664900 := by
    simpa [prefixWord, tailWord_664900, baseEnd_664900] using wordTrace_append hprefix tailTrace_664900
  have hstable : (prefixWord ++ tailWord_664900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664900).length < 2 ^ (prefixWord ++ tailWord_664900).sum := by decide
  have hdescent : baseEnd_664900 < baseStart_664900 := by decide
  rcases family_descends (prefixWord ++ tailWord_664900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664962 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_664962 : Nat := 118140960795 + 664962 * 2 ^ 59
def prefixEnd_664962 : Nat := 4983230072969 + 3 ^ 40 * 664962 * 2
def baseEnd_664962 : Nat := 303506775977895614948357

theorem tailTrace_664962 : CollatzResearch.WordTrace tailWord_664962 prefixEnd_664962 303506775977895614948357 := by
  unfold tailWord_664962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063289154240928828305285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16168771077975810208814093 6063289154240928828305285)
  ·
    refine ⟨1136866716420174155307241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6063289154240928828305285 1136866716420174155307241)
    ·
      refine ⟨852650037315130616480431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1136866716420174155307241 852650037315130616480431)
      ·
        refine ⟨1278975055972695924720647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852650037315130616480431 1278975055972695924720647)
        ·
          refine ⟨1918462583959043887080971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278975055972695924720647 1918462583959043887080971)
          ·
            refine ⟨2877693875938565830621457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918462583959043887080971 2877693875938565830621457)
            ·
              refine ⟨2158270406953924372966093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877693875938565830621457 2158270406953924372966093)
              ·
                refine ⟨809351402607721639862285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2158270406953924372966093 809351402607721639862285)
                ·
                  refine ⟨303506775977895614948357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809351402607721639862285 303506775977895614948357)
                  ·
                    rfl

theorem cell20_664962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_664962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_664962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_664962 prefixEnd_664962 := by exact prefixLift 664962
  have htrace : WordTrace (prefixWord ++ tailWord_664962) baseStart_664962 baseEnd_664962 := by
    simpa [prefixWord, tailWord_664962, baseEnd_664962] using wordTrace_append hprefix tailTrace_664962
  have hstable : (prefixWord ++ tailWord_664962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664962).length < 2 ^ (prefixWord ++ tailWord_664962).sum := by decide
  have hdescent : baseEnd_664962 < baseStart_664962 := by decide
  rcases family_descends (prefixWord ++ tailWord_664962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665004 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_665004 : Nat := 118140960795 + 665004 * 2 ^ 59
def prefixEnd_665004 : Nat := 4983230072969 + 3 ^ 40 * 665004 * 2
def baseEnd_665004 : Nat := 303525945922330135548185

theorem tailTrace_665004 : CollatzResearch.WordTrace tailWord_665004 prefixEnd_665004 303525945922330135548185 := by
  unfold tailWord_665004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127344241405778243125033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16169792321874370990833377 12127344241405778243125033)
  ·
    refine ⟨9095508181054333682343775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12127344241405778243125033 9095508181054333682343775)
    ·
      refine ⟨13643262271581500523515663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9095508181054333682343775 13643262271581500523515663)
      ·
        refine ⟨20464893407372250785273495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13643262271581500523515663 20464893407372250785273495)
        ·
          refine ⟨30697340111058376177910243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20464893407372250785273495 30697340111058376177910243)
          ·
            refine ⟨46046010166587564266865365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30697340111058376177910243 46046010166587564266865365)
            ·
              refine ⟨1079203363279396037504657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46046010166587564266865365 1079203363279396037504657)
              ·
                refine ⟨809402522459547028128493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079203363279396037504657 809402522459547028128493)
                ·
                  refine ⟨303525945922330135548185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809402522459547028128493 303525945922330135548185)
                  ·
                    rfl

theorem cell20_665004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_665004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665004 prefixEnd_665004 := by exact prefixLift 665004
  have htrace : WordTrace (prefixWord ++ tailWord_665004) baseStart_665004 baseEnd_665004 := by
    simpa [prefixWord, tailWord_665004, baseEnd_665004] using wordTrace_append hprefix tailTrace_665004
  have hstable : (prefixWord ++ tailWord_665004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665004).length < 2 ^ (prefixWord ++ tailWord_665004).sum := by decide
  have hdescent : baseEnd_665004 < baseStart_665004 := by decide
  rcases family_descends (prefixWord ++ tailWord_665004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665021 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 3]
def baseStart_665021 : Nat := 118140960795 + 665021 * 2 ^ 59
def prefixEnd_665021 : Nat := 4983230072969 + 3 ^ 40 * 665021 * 2
def baseEnd_665021 : Nat := 303533705185553631981449

theorem tailTrace_665021 : CollatzResearch.WordTrace tailWord_665021 prefixEnd_665021 303533705185553631981449 := by
  unfold tailWord_665021
  simp only [CollatzResearch.WordTrace]
  refine ⟨24255308523749968389618917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16170205682499978926412611 24255308523749968389618917)
  ·
    refine ⟨4547870348203119073053547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24255308523749968389618917 4547870348203119073053547)
    ·
      refine ⟨6821805522304678609580321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547870348203119073053547 6821805522304678609580321)
      ·
        refine ⟨5116354141728508957185241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6821805522304678609580321 5116354141728508957185241)
        ·
          refine ⟨3837265606296381717888931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5116354141728508957185241 3837265606296381717888931)
          ·
            refine ⟨5755898409444572576833397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837265606296381717888931 5755898409444572576833397)
            ·
              refine ⟨539615475885428679078131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5755898409444572576833397 539615475885428679078131)
              ·
                refine ⟨809423213828143018617197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539615475885428679078131 809423213828143018617197)
                ·
                  refine ⟨303533705185553631981449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809423213828143018617197 303533705185553631981449)
                  ·
                    rfl

theorem cell20_665021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_665021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665021 prefixEnd_665021 := by exact prefixLift 665021
  have htrace : WordTrace (prefixWord ++ tailWord_665021) baseStart_665021 baseEnd_665021 := by
    simpa [prefixWord, tailWord_665021, baseEnd_665021] using wordTrace_append hprefix tailTrace_665021
  have hstable : (prefixWord ++ tailWord_665021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665021).length < 2 ^ (prefixWord ++ tailWord_665021).sum := by decide
  have hdescent : baseEnd_665021 < baseStart_665021 := by decide
  rcases family_descends (prefixWord ++ tailWord_665021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665028 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_665028 : Nat := 118140960795 + 665028 * 2 ^ 59
def prefixEnd_665028 : Nat := 4983230072969 + 3 ^ 40 * 665028 * 2
def baseEnd_665028 : Nat := 303536900176292718748087

theorem tailTrace_665028 : CollatzResearch.WordTrace tailWord_665028 prefixEnd_665028 303536900176292718748087 := by
  unfold tailWord_665028
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127781917362304292561869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16170375889816405723415825 12127781917362304292561869)
  ·
    refine ⟨4547918219010864109710701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12127781917362304292561869 4547918219010864109710701)
    ·
      refine ⟨1705469332129074041141513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4547918219010864109710701 1705469332129074041141513)
      ·
        refine ⟨1279101999096805530856135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705469332129074041141513 1279101999096805530856135)
        ·
          refine ⟨1918652998645208296284203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279101999096805530856135 1918652998645208296284203)
          ·
            refine ⟨2877979497967812444426305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918652998645208296284203 2877979497967812444426305)
            ·
              refine ⟨2158484623475859333319729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877979497967812444426305 2158484623475859333319729)
              ·
                refine ⟨1618863467606894499989797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158484623475859333319729 1618863467606894499989797)
                ·
                  refine ⟨303536900176292718748087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618863467606894499989797 303536900176292718748087)
                  ·
                    rfl

theorem cell20_665028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_665028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665028 prefixEnd_665028 := by exact prefixLift 665028
  have htrace : WordTrace (prefixWord ++ tailWord_665028) baseStart_665028 baseEnd_665028 := by
    simpa [prefixWord, tailWord_665028, baseEnd_665028] using wordTrace_append hprefix tailTrace_665028
  have hstable : (prefixWord ++ tailWord_665028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665028).length < 2 ^ (prefixWord ++ tailWord_665028).sum := by decide
  have hdescent : baseEnd_665028 < baseStart_665028 := by decide
  rcases family_descends (prefixWord ++ tailWord_665028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665080 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_665080 : Nat := 118140960795 + 665080 * 2 ^ 59
def prefixEnd_665080 : Nat := 4983230072969 + 3 ^ 40 * 665080 * 2
def baseEnd_665080 : Nat := 303560634393211649014541

theorem tailTrace_665080 : CollatzResearch.WordTrace tailWord_665080 prefixEnd_665080 303560634393211649014541 := by
  unfold tailWord_665080
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128730215268110733008347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16171640287024147644011129 12128730215268110733008347)
  ·
    refine ⟨18193095322902166099512521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12128730215268110733008347 18193095322902166099512521)
    ·
      refine ⟨13644821492176624574634391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18193095322902166099512521 13644821492176624574634391)
      ·
        refine ⟨20467232238264936861951587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13644821492176624574634391 20467232238264936861951587)
        ·
          refine ⟨30700848357397405292927381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20467232238264936861951587 30700848357397405292927381)
          ·
            refine ⟨1439102266753003373105971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30700848357397405292927381 1439102266753003373105971)
            ·
              refine ⟨2158653400129505059658957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439102266753003373105971 2158653400129505059658957)
              ·
                refine ⟨809495025048564397372109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2158653400129505059658957 809495025048564397372109)
                ·
                  refine ⟨303560634393211649014541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809495025048564397372109 303560634393211649014541)
                  ·
                    rfl

theorem cell20_665080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_665080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665080 prefixEnd_665080 := by exact prefixLift 665080
  have htrace : WordTrace (prefixWord ++ tailWord_665080) baseStart_665080 baseEnd_665080 := by
    simpa [prefixWord, tailWord_665080, baseEnd_665080] using wordTrace_append hprefix tailTrace_665080
  have hstable : (prefixWord ++ tailWord_665080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665080).length < 2 ^ (prefixWord ++ tailWord_665080).sum := by decide
  have hdescent : baseEnd_665080 < baseStart_665080 := by decide
  rcases family_descends (prefixWord ++ tailWord_665080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665121 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 2]
def baseStart_665121 : Nat := 118140960795 + 665121 * 2 ^ 59
def prefixEnd_665121 : Nat := 4983230072969 + 3 ^ 40 * 665121 * 2
def baseEnd_665121 : Nat := 303579347910397728647707

theorem tailTrace_665121 : CollatzResearch.WordTrace tailWord_665121 prefixEnd_665121 303579347910397728647707 := by
  unfold tailWord_665121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24258955823387685468259217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16172637215591790312172811 24258955823387685468259217)
  ·
    refine ⟨18194216867540764101194413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24258955823387685468259217 18194216867540764101194413)
    ·
      refine ⟨6822831325327786537947905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18194216867540764101194413 6822831325327786537947905)
      ·
        refine ⟨5117123493995839903460929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6822831325327786537947905 5117123493995839903460929)
        ·
          refine ⟨3837842620496879927595697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5117123493995839903460929 3837842620496879927595697)
          ·
            refine ⟨2878381965372659945696773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837842620496879927595697 2878381965372659945696773)
            ·
              refine ⟨539696618507373739818145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2878381965372659945696773 539696618507373739818145)
              ·
                refine ⟨404772463880530304863609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539696618507373739818145 404772463880530304863609)
                ·
                  refine ⟨303579347910397728647707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404772463880530304863609 303579347910397728647707)
                  ·
                    rfl

theorem cell20_665121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_665121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665121 prefixEnd_665121 := by exact prefixLift 665121
  have htrace : WordTrace (prefixWord ++ tailWord_665121) baseStart_665121 baseEnd_665121 := by
    simpa [prefixWord, tailWord_665121, baseEnd_665121] using wordTrace_append hprefix tailTrace_665121
  have hstable : (prefixWord ++ tailWord_665121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665121).length < 2 ^ (prefixWord ++ tailWord_665121).sum := by decide
  have hdescent : baseEnd_665121 < baseStart_665121 := by decide
  rcases family_descends (prefixWord ++ tailWord_665121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665128 : List Nat := [2, 1, 5, 2, 2, 2, 1, 5]
def baseStart_665128 : Nat := 118140960795 + 665128 * 2 ^ 59
def prefixEnd_665128 : Nat := 4983230072969 + 3 ^ 40 * 665128 * 2
def baseEnd_665128 : Nat := 101194180967045605138115

theorem tailTrace_665128 : CollatzResearch.WordTrace tailWord_665128 prefixEnd_665128 101194180967045605138115 := by
  unfold tailWord_665128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129605567181162831882019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16172807422908217109176025 12129605567181162831882019)
  ·
    refine ⟨18194408350771744247823029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12129605567181162831882019 18194408350771744247823029)
    ·
      refine ⟨1705725782884851023233409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18194408350771744247823029 1705725782884851023233409)
      ·
        refine ⟨1279294337163638267425057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705725782884851023233409 1279294337163638267425057)
        ·
          refine ⟨959470752872728700568793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279294337163638267425057 959470752872728700568793)
          ·
            refine ⟨719603064654546525426595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959470752872728700568793 719603064654546525426595)
            ·
              refine ⟨1079404596981819788139893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719603064654546525426595 1079404596981819788139893)
              ·
                refine ⟨101194180967045605138115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1079404596981819788139893 101194180967045605138115)
                ·
                  rfl

theorem cell20_665128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_665128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665128 prefixEnd_665128 := by exact prefixLift 665128
  have htrace : WordTrace (prefixWord ++ tailWord_665128) baseStart_665128 baseEnd_665128 := by
    simpa [prefixWord, tailWord_665128, baseEnd_665128] using wordTrace_append hprefix tailTrace_665128
  have hstable : (prefixWord ++ tailWord_665128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665128).length < 2 ^ (prefixWord ++ tailWord_665128).sum := by decide
  have hdescent : baseEnd_665128 < baseStart_665128 := by decide
  rcases family_descends (prefixWord ++ tailWord_665128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665159 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 2]
def baseStart_665159 : Nat := 118140960795 + 665159 * 2 ^ 59
def prefixEnd_665159 : Nat := 4983230072969 + 3 ^ 40 * 665159 * 2
def baseEnd_665159 : Nat := 303596692145838485380885

theorem tailTrace_665159 : CollatzResearch.WordTrace tailWord_665159 prefixEnd_665159 303596692145838485380885 := by
  unfold tailWord_665159
  simp only [CollatzResearch.WordTrace]
  refine ⟨24260341797250017958142531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16173561198166678638761687 24260341797250017958142531)
  ·
    refine ⟨36390512695875026937213797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24260341797250017958142531 36390512695875026937213797)
    ·
      refine ⟨6823221130476567550727587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36390512695875026937213797 6823221130476567550727587)
      ·
        refine ⟨10234831695714851326091381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6823221130476567550727587 10234831695714851326091381)
        ·
          refine ⟨959515471473267311821067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10234831695714851326091381 959515471473267311821067)
          ·
            refine ⟨1439273207209900967731601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959515471473267311821067 1439273207209900967731601)
            ·
              refine ⟨1079454905407425725798701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439273207209900967731601 1079454905407425725798701)
              ·
                refine ⟨404795589527784647174513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1079454905407425725798701 404795589527784647174513)
                ·
                  refine ⟨303596692145838485380885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404795589527784647174513 303596692145838485380885)
                  ·
                    rfl

theorem cell20_665159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 2].length) (baseStart_665159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665159 prefixEnd_665159 := by exact prefixLift 665159
  have htrace : WordTrace (prefixWord ++ tailWord_665159) baseStart_665159 baseEnd_665159 := by
    simpa [prefixWord, tailWord_665159, baseEnd_665159] using wordTrace_append hprefix tailTrace_665159
  have hstable : (prefixWord ++ tailWord_665159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665159).length < 2 ^ (prefixWord ++ tailWord_665159).sum := by decide
  have hdescent : baseEnd_665159 < baseStart_665159 := by decide
  rcases family_descends (prefixWord ++ tailWord_665159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665170 : List Nat := [3, 2, 2, 1, 2, 3, 7]
def baseStart_665170 : Nat := 118140960795 + 665170 * 2 ^ 59
def prefixEnd_665170 : Nat := 4983230072969 + 3 ^ 40 * 665170 * 2
def baseEnd_665170 : Nat := 33733523649507926223797

theorem tailTrace_665170 : CollatzResearch.WordTrace tailWord_665170 prefixEnd_665170 33733523649507926223797 := by
  unfold tailWord_665170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065185750052541709198241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16173828666806777891195309 6065185750052541709198241)
  ·
    refine ⟨4548889312539406281898681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6065185750052541709198241 4548889312539406281898681)
    ·
      refine ⟨3411666984404554711424011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4548889312539406281898681 3411666984404554711424011)
      ·
        refine ⟨5117500476606832067136017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411666984404554711424011 5117500476606832067136017)
        ·
          refine ⟨3838125357455124050352013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5117500476606832067136017 3838125357455124050352013)
          ·
            refine ⟨1439297009045671518882005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3838125357455124050352013 1439297009045671518882005)
            ·
              refine ⟨33733523649507926223797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1439297009045671518882005 33733523649507926223797)
              ·
                rfl

theorem cell20_665170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_665170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665170 prefixEnd_665170 := by exact prefixLift 665170
  have htrace : WordTrace (prefixWord ++ tailWord_665170) baseStart_665170 baseEnd_665170 := by
    simpa [prefixWord, tailWord_665170, baseEnd_665170] using wordTrace_append hprefix tailTrace_665170
  have hstable : (prefixWord ++ tailWord_665170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665170).length < 2 ^ (prefixWord ++ tailWord_665170).sum := by decide
  have hdescent : baseEnd_665170 < baseStart_665170 := by decide
  rcases family_descends (prefixWord ++ tailWord_665170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665180 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_665180 : Nat := 118140960795 + 665180 * 2 ^ 59
def prefixEnd_665180 : Nat := 4983230072969 + 3 ^ 40 * 665180 * 2
def baseEnd_665180 : Nat := 303606277118055745680799

theorem tailTrace_665180 : CollatzResearch.WordTrace tailWord_665180 prefixEnd_665180 303606277118055745680799 := by
  unfold tailWord_665180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130553865086969272328497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16174071820115959029771329 12130553865086969272328497)
  ·
    refine ⟨9097915398815226954246373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12130553865086969272328497 9097915398815226954246373)
    ·
      refine ⟨1705859137277855053921195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9097915398815226954246373 1705859137277855053921195)
      ·
        refine ⟨2558788705916782580881793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705859137277855053921195 2558788705916782580881793)
        ·
          refine ⟨1919091529437586935661345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558788705916782580881793 1919091529437586935661345)
          ·
            refine ⟨1439318647078190201746009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919091529437586935661345 1439318647078190201746009)
            ·
              refine ⟨1079488985308642651309507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439318647078190201746009 1079488985308642651309507)
              ·
                refine ⟨1619233477962963976964261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079488985308642651309507 1619233477962963976964261)
                ·
                  refine ⟨303606277118055745680799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619233477962963976964261 303606277118055745680799)
                  ·
                    rfl

theorem cell20_665180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_665180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665180 prefixEnd_665180 := by exact prefixLift 665180
  have htrace : WordTrace (prefixWord ++ tailWord_665180) baseStart_665180 baseEnd_665180 := by
    simpa [prefixWord, tailWord_665180, baseEnd_665180] using wordTrace_append hprefix tailTrace_665180
  have hstable : (prefixWord ++ tailWord_665180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665180).length < 2 ^ (prefixWord ++ tailWord_665180).sum := by decide
  have hdescent : baseEnd_665180 < baseStart_665180 := by decide
  rcases family_descends (prefixWord ++ tailWord_665180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665239 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_665239 : Nat := 118140960795 + 665239 * 2 ^ 59
def prefixEnd_665239 : Nat := 4983230072969 + 3 ^ 40 * 665239 * 2
def baseEnd_665239 : Nat := 303633206325713762713891

theorem tailTrace_665239 : CollatzResearch.WordTrace tailWord_665239 prefixEnd_665239 303633206325713762713891 := by
  unfold tailWord_665239
  simp only [CollatzResearch.WordTrace]
  refine ⟨24263259636960191621054771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16175506424640127747369847 24263259636960191621054771)
  ·
    refine ⟨36394889455440287431582157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24263259636960191621054771 36394889455440287431582157)
    ·
      refine ⟨13648083545790107786843309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36394889455440287431582157 13648083545790107786843309)
      ·
        refine ⟨5118031329671290420066241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13648083545790107786843309 5118031329671290420066241)
        ·
          refine ⟨3838523497253467815049681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5118031329671290420066241 3838523497253467815049681)
          ·
            refine ⟨2878892622940100861287261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3838523497253467815049681 2878892622940100861287261)
            ·
              refine ⟨1079584733602537822982723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2878892622940100861287261 1079584733602537822982723)
              ·
                refine ⟨1619377100403806734474085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079584733602537822982723 1619377100403806734474085)
                ·
                  refine ⟨303633206325713762713891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619377100403806734474085 303633206325713762713891)
                  ·
                    rfl

theorem cell20_665239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_665239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665239 prefixEnd_665239 := by exact prefixLift 665239
  have htrace : WordTrace (prefixWord ++ tailWord_665239) baseStart_665239 baseEnd_665239 := by
    simpa [prefixWord, tailWord_665239, baseEnd_665239] using wordTrace_append hprefix tailTrace_665239
  have hstable : (prefixWord ++ tailWord_665239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665239).length < 2 ^ (prefixWord ++ tailWord_665239).sum := by decide
  have hdescent : baseEnd_665239 < baseStart_665239 := by decide
  rcases family_descends (prefixWord ++ tailWord_665239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665249 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 3]
def baseStart_665249 : Nat := 118140960795 + 665249 * 2 ^ 59
def prefixEnd_665249 : Nat := 4983230072969 + 3 ^ 40 * 665249 * 2
def baseEnd_665249 : Nat := 303637770598198172380517

theorem tailTrace_665249 : CollatzResearch.WordTrace tailWord_665249 prefixEnd_665249 303637770598198172380517 := by
  unfold tailWord_665249
  simp only [CollatzResearch.WordTrace]
  refine ⟨24263624366923963328918801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16175749577949308885945867 24263624366923963328918801)
  ·
    refine ⟨18197718275192972496689101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24263624366923963328918801 18197718275192972496689101)
    ·
      refine ⟨6824144353197364686258413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18197718275192972496689101 6824144353197364686258413)
      ·
        refine ⟨2559054132449011757346905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6824144353197364686258413 2559054132449011757346905)
        ·
          refine ⟨1919290599336758818010179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559054132449011757346905 1919290599336758818010179)
          ·
            refine ⟨2878935899005138227015269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919290599336758818010179 2878935899005138227015269)
            ·
              refine ⟨539800481063463417565363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2878935899005138227015269 539800481063463417565363)
              ·
                refine ⟨809700721595195126348045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539800481063463417565363 809700721595195126348045)
                ·
                  refine ⟨303637770598198172380517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809700721595195126348045 303637770598198172380517)
                  ·
                    rfl

theorem cell20_665249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_665249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665249 prefixEnd_665249 := by exact prefixLift 665249
  have htrace : WordTrace (prefixWord ++ tailWord_665249) baseStart_665249 baseEnd_665249 := by
    simpa [prefixWord, tailWord_665249, baseEnd_665249] using wordTrace_append hprefix tailTrace_665249
  have hstable : (prefixWord ++ tailWord_665249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665249).length < 2 ^ (prefixWord ++ tailWord_665249).sum := by decide
  have hdescent : baseEnd_665249 < baseStart_665249 := by decide
  rcases family_descends (prefixWord ++ tailWord_665249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665267 : List Nat := [1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_665267 : Nat := 118140960795 + 665267 * 2 ^ 59
def prefixEnd_665267 : Nat := 4983230072969 + 3 ^ 40 * 665267 * 2
def baseEnd_665267 : Nat := 101215328762890036593481

theorem tailTrace_665267 : CollatzResearch.WordTrace tailWord_665267 prefixEnd_665267 101215328762890036593481 := by
  unfold tailWord_665267
  simp only [CollatzResearch.WordTrace]
  refine ⟨24264280880858752403074055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16176187253905834935382703 24264280880858752403074055)
  ·
    refine ⟨36396421321288128604611083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24264280880858752403074055 36396421321288128604611083)
    ·
      refine ⟨54594631981932192906916625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36396421321288128604611083 54594631981932192906916625)
      ·
        refine ⟨40945973986449144680187469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54594631981932192906916625 40945973986449144680187469)
        ·
          refine ⟨15354740244918429255070301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40945973986449144680187469 15354740244918429255070301)
          ·
            refine ⟨5758027591844410970651363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15354740244918429255070301 5758027591844410970651363)
            ·
              refine ⟨8637041387766616455977045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758027591844410970651363 8637041387766616455977045)
              ·
                refine ⟨101215328762890036593481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8637041387766616455977045 101215328762890036593481)
                ·
                  rfl

theorem cell20_665267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_665267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665267 prefixEnd_665267 := by exact prefixLift 665267
  have htrace : WordTrace (prefixWord ++ tailWord_665267) baseStart_665267 baseEnd_665267 := by
    simpa [prefixWord, tailWord_665267, baseEnd_665267] using wordTrace_append hprefix tailTrace_665267
  have hstable : (prefixWord ++ tailWord_665267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665267).length < 2 ^ (prefixWord ++ tailWord_665267).sum := by decide
  have hdescent : baseEnd_665267 < baseStart_665267 := by decide
  rcases family_descends (prefixWord ++ tailWord_665267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665286 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_665286 : Nat := 118140960795 + 665286 * 2 ^ 59
def prefixEnd_665286 : Nat := 4983230072969 + 3 ^ 40 * 665286 * 2
def baseEnd_665286 : Nat := 303654658406390488147033

theorem tailTrace_665286 : CollatzResearch.WordTrace tailWord_665286 prefixEnd_665286 303654658406390488147033 := by
  unfold tailWord_665286
  simp only [CollatzResearch.WordTrace]
  refine ⟨758280433368434957750491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16176649245193279098677141 758280433368434957750491)
  ·
    refine ⟨1137420650052652436625737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758280433368434957750491 1137420650052652436625737)
    ·
      refine ⟨853065487539489327469303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1137420650052652436625737 853065487539489327469303)
      ·
        refine ⟨1279598231309233991203955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853065487539489327469303 1279598231309233991203955)
        ·
          refine ⟨1919397346963850986805933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279598231309233991203955 1919397346963850986805933)
          ·
            refine ⟨719774005111444120052225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1919397346963850986805933 719774005111444120052225)
            ·
              refine ⟨539830503833583090039169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719774005111444120052225 539830503833583090039169)
              ·
                refine ⟨404872877875187317529377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539830503833583090039169 404872877875187317529377)
                ·
                  refine ⟨303654658406390488147033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404872877875187317529377 303654658406390488147033)
                  ·
                    rfl

theorem cell20_665286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_665286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665286 prefixEnd_665286 := by exact prefixLift 665286
  have htrace : WordTrace (prefixWord ++ tailWord_665286) baseStart_665286 baseEnd_665286 := by
    simpa [prefixWord, tailWord_665286, baseEnd_665286] using wordTrace_append hprefix tailTrace_665286
  have hstable : (prefixWord ++ tailWord_665286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665286).length < 2 ^ (prefixWord ++ tailWord_665286).sum := by decide
  have hdescent : baseEnd_665286 < baseStart_665286 := by decide
  rcases family_descends (prefixWord ++ tailWord_665286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665290 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_665290 : Nat := 118140960795 + 665290 * 2 ^ 59
def prefixEnd_665290 : Nat := 4983230072969 + 3 ^ 40 * 665290 * 2
def baseEnd_665290 : Nat := 303656484115384252013683

theorem tailTrace_665290 : CollatzResearch.WordTrace tailWord_665290 prefixEnd_665290 303656484115384252013683 := by
  unfold tailWord_665290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066279939943856832790331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16176746506516951554107549 6066279939943856832790331)
  ·
    refine ⟨9099419909915785249185497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6066279939943856832790331 9099419909915785249185497)
    ·
      refine ⟨6824564932436838936889123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9099419909915785249185497 6824564932436838936889123)
      ·
        refine ⟨10236847398655258405333685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824564932436838936889123 10236847398655258405333685)
        ·
          refine ⟨959704443623930475500033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10236847398655258405333685 959704443623930475500033)
          ·
            refine ⟨719778332717947856625025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959704443623930475500033 719778332717947856625025)
            ·
              refine ⟨539833749538460892468769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719778332717947856625025 539833749538460892468769)
              ·
                refine ⟨404875312153845669351577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539833749538460892468769 404875312153845669351577)
                ·
                  refine ⟨303656484115384252013683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404875312153845669351577 303656484115384252013683)
                  ·
                    rfl

theorem cell20_665290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_665290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665290 prefixEnd_665290 := by exact prefixLift 665290
  have htrace : WordTrace (prefixWord ++ tailWord_665290) baseStart_665290 baseEnd_665290 := by
    simpa [prefixWord, tailWord_665290, baseEnd_665290] using wordTrace_append hprefix tailTrace_665290
  have hstable : (prefixWord ++ tailWord_665290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665290).length < 2 ^ (prefixWord ++ tailWord_665290).sum := by decide
  have hdescent : baseEnd_665290 < baseStart_665290 := by decide
  rcases family_descends (prefixWord ++ tailWord_665290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665294 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_665294 : Nat := 118140960795 + 665294 * 2 ^ 59
def prefixEnd_665294 : Nat := 4983230072969 + 3 ^ 40 * 665294 * 2
def baseEnd_665294 : Nat := 303658309824378015880333

theorem tailTrace_665294 : CollatzResearch.WordTrace tailWord_665294 prefixEnd_665294 303658309824378015880333 := by
  unfold tailWord_665294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033158206470117001788367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16176843767840624009537957 3033158206470117001788367)
  ·
    refine ⟨4549737309705175502682551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3033158206470117001788367 4549737309705175502682551)
    ·
      refine ⟨6824605964557763254023827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4549737309705175502682551 6824605964557763254023827)
      ·
        refine ⟨10236908946836644881035741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824605964557763254023827 10236908946836644881035741)
        ·
          refine ⟨3838840855063741830388403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10236908946836644881035741 3838840855063741830388403)
          ·
            refine ⟨5758261282595612745582605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838840855063741830388403 5758261282595612745582605)
            ·
              refine ⟨2159347980973354779593477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5758261282595612745582605 2159347980973354779593477)
              ·
                refine ⟨404877746432504021173777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2159347980973354779593477 404877746432504021173777)
                ·
                  refine ⟨303658309824378015880333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404877746432504021173777 303658309824378015880333)
                  ·
                    rfl

theorem cell20_665294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_665294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665294 prefixEnd_665294 := by exact prefixLift 665294
  have htrace : WordTrace (prefixWord ++ tailWord_665294) baseStart_665294 baseEnd_665294 := by
    simpa [prefixWord, tailWord_665294, baseEnd_665294] using wordTrace_append hprefix tailTrace_665294
  have hstable : (prefixWord ++ tailWord_665294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665294).length < 2 ^ (prefixWord ++ tailWord_665294).sum := by decide
  have hdescent : baseEnd_665294 < baseStart_665294 := by decide
  rcases family_descends (prefixWord ++ tailWord_665294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665342 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_665342 : Nat := 118140960795 + 665342 * 2 ^ 59
def prefixEnd_665342 : Nat := 4983230072969 + 3 ^ 40 * 665342 * 2
def baseEnd_665342 : Nat := 303680218332303182280137

theorem tailTrace_665342 : CollatzResearch.WordTrace tailWord_665342 prefixEnd_665342 303680218332303182280137 := by
  unfold tailWord_665342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033377044448380026506785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16178010903724693474702853 3033377044448380026506785)
  ·
    refine ⟨2275032783336285019880089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3033377044448380026506785 2275032783336285019880089)
    ·
      refine ⟨1706274587502213764910067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275032783336285019880089 1706274587502213764910067)
      ·
        refine ⟨2559411881253320647365101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706274587502213764910067 2559411881253320647365101)
        ·
          refine ⟨959779455469995242761913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2559411881253320647365101 959779455469995242761913)
          ·
            refine ⟨719834591602496432071435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959779455469995242761913 719834591602496432071435)
            ·
              refine ⟨1079751887403744648107153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719834591602496432071435 1079751887403744648107153)
              ·
                refine ⟨809813915552808486080365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079751887403744648107153 809813915552808486080365)
                ·
                  refine ⟨303680218332303182280137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809813915552808486080365 303680218332303182280137)
                  ·
                    rfl

theorem cell20_665342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_665342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665342 prefixEnd_665342 := by exact prefixLift 665342
  have htrace : WordTrace (prefixWord ++ tailWord_665342) baseStart_665342 baseEnd_665342 := by
    simpa [prefixWord, tailWord_665342, baseEnd_665342] using wordTrace_append hprefix tailTrace_665342
  have hstable : (prefixWord ++ tailWord_665342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665342).length < 2 ^ (prefixWord ++ tailWord_665342).sum := by decide
  have hdescent : baseEnd_665342 < baseStart_665342 := by decide
  rcases family_descends (prefixWord ++ tailWord_665342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665346 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_665346 : Nat := 118140960795 + 665346 * 2 ^ 59
def prefixEnd_665346 : Nat := 4983230072969 + 3 ^ 40 * 665346 * 2
def baseEnd_665346 : Nat := 303682044041296946146787

theorem tailTrace_665346 : CollatzResearch.WordTrace tailWord_665346 prefixEnd_665346 303682044041296946146787 := by
  unfold tailWord_665346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066790561893137223799973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16178108165048365930133261 6066790561893137223799973)
  ·
    refine ⟨1137523230354963229462495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6066790561893137223799973 1137523230354963229462495)
    ·
      refine ⟨1706284845532444844193743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137523230354963229462495 1706284845532444844193743)
      ·
        refine ⟨2559427268298667266290615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706284845532444844193743 2559427268298667266290615)
        ·
          refine ⟨3839140902448000899435923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559427268298667266290615 3839140902448000899435923)
          ·
            refine ⟨5758711353672001349153885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839140902448000899435923 5758711353672001349153885)
            ·
              refine ⟨2159516757627000505932707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5758711353672001349153885 2159516757627000505932707)
              ·
                refine ⟨3239275136440500758899061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159516757627000505932707 3239275136440500758899061)
                ·
                  refine ⟨303682044041296946146787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3239275136440500758899061 303682044041296946146787)
                  ·
                    rfl

theorem cell20_665346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_665346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665346 prefixEnd_665346 := by exact prefixLift 665346
  have htrace : WordTrace (prefixWord ++ tailWord_665346) baseStart_665346 baseEnd_665346 := by
    simpa [prefixWord, tailWord_665346, baseEnd_665346] using wordTrace_append hprefix tailTrace_665346
  have hstable : (prefixWord ++ tailWord_665346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665346).length < 2 ^ (prefixWord ++ tailWord_665346).sum := by decide
  have hdescent : baseEnd_665346 < baseStart_665346 := by decide
  rcases family_descends (prefixWord ++ tailWord_665346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665377 : List Nat := [1, 2, 3, 2, 1, 5, 2, 4]
def baseStart_665377 : Nat := 118140960795 + 665377 * 2 ^ 59
def prefixEnd_665377 : Nat := 4983230072969 + 3 ^ 40 * 665377 * 2
def baseEnd_665377 : Nat := 101232064428666205371109

theorem tailTrace_665377 : CollatzResearch.WordTrace tailWord_665377 prefixEnd_665377 101232064428666205371109 := by
  unfold tailWord_665377
  simp only [CollatzResearch.WordTrace]
  refine ⟨24268292910460241189578385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16178861940306827459718923 24268292910460241189578385)
  ·
    refine ⟨18201219682845180892183789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24268292910460241189578385 18201219682845180892183789)
    ·
      refine ⟨6825457381066942834568921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18201219682845180892183789 6825457381066942834568921)
      ·
        refine ⟨5119093035800207125926691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6825457381066942834568921 5119093035800207125926691)
        ·
          refine ⟨7678639553700310688890037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119093035800207125926691 7678639553700310688890037)
          ·
            refine ⟨719872458159404127083441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7678639553700310688890037 719872458159404127083441)
            ·
              refine ⟨539904343619553095312581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719872458159404127083441 539904343619553095312581)
              ·
                refine ⟨101232064428666205371109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 539904343619553095312581 101232064428666205371109)
                ·
                  rfl

theorem cell20_665377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_665377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665377 prefixEnd_665377 := by exact prefixLift 665377
  have htrace : WordTrace (prefixWord ++ tailWord_665377) baseStart_665377 baseEnd_665377 := by
    simpa [prefixWord, tailWord_665377, baseEnd_665377] using wordTrace_append hprefix tailTrace_665377
  have hstable : (prefixWord ++ tailWord_665377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665377).length < 2 ^ (prefixWord ++ tailWord_665377).sum := by decide
  have hdescent : baseEnd_665377 < baseStart_665377 := by decide
  rcases family_descends (prefixWord ++ tailWord_665377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665464 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_665464 : Nat := 118140960795 + 665464 * 2 ^ 59
def prefixEnd_665464 : Nat := 4983230072969 + 3 ^ 40 * 665464 * 2
def baseEnd_665464 : Nat := 303735902456612980212971

theorem tailTrace_665464 : CollatzResearch.WordTrace tailWord_665464 prefixEnd_665464 303735902456612980212971 := by
  unfold tailWord_665464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12135733030572527523997723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16180977374096703365330297 12135733030572527523997723)
  ·
    refine ⟨18203599545858791285996585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12135733030572527523997723 18203599545858791285996585)
    ·
      refine ⟨13652699659394093464497439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18203599545858791285996585 13652699659394093464497439)
      ·
        refine ⟨20479049489091140196746159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13652699659394093464497439 20479049489091140196746159)
        ·
          refine ⟨30718574233636710295119239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20479049489091140196746159 30718574233636710295119239)
          ·
            refine ⟨46077861350455065442678859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30718574233636710295119239 46077861350455065442678859)
            ·
              refine ⟨69116792025682598164018289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46077861350455065442678859 69116792025682598164018289)
              ·
                refine ⟨51837594019261948623013717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69116792025682598164018289 51837594019261948623013717)
                ·
                  refine ⟨303735902456612980212971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51837594019261948623013717 303735902456612980212971)
                  ·
                    rfl

theorem cell20_665464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_665464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665464 prefixEnd_665464 := by exact prefixLift 665464
  have htrace : WordTrace (prefixWord ++ tailWord_665464) baseStart_665464 baseEnd_665464 := by
    simpa [prefixWord, tailWord_665464, baseEnd_665464] using wordTrace_append hprefix tailTrace_665464
  have hstable : (prefixWord ++ tailWord_665464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665464).length < 2 ^ (prefixWord ++ tailWord_665464).sum := by decide
  have hdescent : baseEnd_665464 < baseStart_665464 := by decide
  rcases family_descends (prefixWord ++ tailWord_665464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665470 : List Nat := [4, 2, 3, 1, 1, 3, 1, 5]
def baseStart_665470 : Nat := 118140960795 + 665470 * 2 ^ 59
def prefixEnd_665470 : Nat := 4983230072969 + 3 ^ 40 * 665470 * 2
def baseEnd_665470 : Nat := 101246213673367875337649

theorem tailTrace_665470 : CollatzResearch.WordTrace tailWord_665470 prefixEnd_665470 101246213673367875337649 := by
  unfold tailWord_665470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033960612390414759089233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16181123266082212048475909 3033960612390414759089233)
  ·
    refine ⟨2275470459292811069316925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3033960612390414759089233 2275470459292811069316925)
    ·
      refine ⟨853301422234804150993847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2275470459292811069316925 853301422234804150993847)
      ·
        refine ⟨1279952133352206226490771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853301422234804150993847 1279952133352206226490771)
        ·
          refine ⟨1919928200028309339736157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279952133352206226490771 1919928200028309339736157)
          ·
            refine ⟨719973075010616002401059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1919928200028309339736157 719973075010616002401059)
            ·
              refine ⟨1079959612515924003601589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719973075010616002401059 1079959612515924003601589)
              ·
                refine ⟨101246213673367875337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1079959612515924003601589 101246213673367875337649)
                ·
                  rfl

theorem cell20_665470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_665470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665470 prefixEnd_665470 := by exact prefixLift 665470
  have htrace : WordTrace (prefixWord ++ tailWord_665470) baseStart_665470 baseEnd_665470 := by
    simpa [prefixWord, tailWord_665470, baseEnd_665470] using wordTrace_append hprefix tailTrace_665470
  have hstable : (prefixWord ++ tailWord_665470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665470).length < 2 ^ (prefixWord ++ tailWord_665470).sum := by decide
  have hdescent : baseEnd_665470 < baseStart_665470 := by decide
  rcases family_descends (prefixWord ++ tailWord_665470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665481 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_665481 : Nat := 118140960795 + 665481 * 2 ^ 59
def prefixEnd_665481 : Nat := 4983230072969 + 3 ^ 40 * 665481 * 2
def baseEnd_665481 : Nat := 303743661719836476646235

theorem tailTrace_665481 : CollatzResearch.WordTrace tailWord_665481 prefixEnd_665481 303743661719836476646235 := by
  unfold tailWord_665481
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272086102083466951364297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181390734722311300909531 24272086102083466951364297)
  ·
    refine ⟨18204064576562600213523223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24272086102083466951364297 18204064576562600213523223)
    ·
      refine ⟨27306096864843900320284835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18204064576562600213523223 27306096864843900320284835)
      ·
        refine ⟨40959145297265850480427253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27306096864843900320284835 40959145297265850480427253)
        ·
          refine ⟨3839919871618673482540055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40959145297265850480427253 3839919871618673482540055)
          ·
            refine ⟨5759879807428010223810083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839919871618673482540055 5759879807428010223810083)
            ·
              refine ⟨8639819711142015335715125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759879807428010223810083 8639819711142015335715125)
              ·
                refine ⟨809983097919563937723293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8639819711142015335715125 809983097919563937723293)
                ·
                  refine ⟨303743661719836476646235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809983097919563937723293 303743661719836476646235)
                  ·
                    rfl

theorem cell20_665481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_665481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665481 prefixEnd_665481 := by exact prefixLift 665481
  have htrace : WordTrace (prefixWord ++ tailWord_665481) baseStart_665481 baseEnd_665481 := by
    simpa [prefixWord, tailWord_665481, baseEnd_665481] using wordTrace_append hprefix tailTrace_665481
  have hstable : (prefixWord ++ tailWord_665481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665481).length < 2 ^ (prefixWord ++ tailWord_665481).sum := by decide
  have hdescent : baseEnd_665481 < baseStart_665481 := by decide
  rcases family_descends (prefixWord ++ tailWord_665481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665518 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_665518 : Nat := 118140960795 + 665518 * 2 ^ 59
def prefixEnd_665518 : Nat := 4983230072969 + 3 ^ 40 * 665518 * 2
def baseEnd_665518 : Nat := 303760549528028792412751

theorem tailTrace_665518 : CollatzResearch.WordTrace tailWord_665518 prefixEnd_665518 303760549528028792412751 := by
  unfold tailWord_665518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034179450368677783807651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16182290401966281513640805 3034179450368677783807651)
  ·
    refine ⟨4551269175553016675711477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3034179450368677783807651 4551269175553016675711477)
    ·
      refine ⟨426681485208095313347951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4551269175553016675711477 426681485208095313347951)
      ·
        refine ⟨640022227812142970021927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426681485208095313347951 640022227812142970021927)
        ·
          refine ⟨960033341718214455032891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640022227812142970021927 960033341718214455032891)
          ·
            refine ⟨1440050012577321682549337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960033341718214455032891 1440050012577321682549337)
            ·
              refine ⟨1080037509432991261912003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440050012577321682549337 1080037509432991261912003)
              ·
                refine ⟨1620056264149486892868005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080037509432991261912003 1620056264149486892868005)
                ·
                  refine ⟨303760549528028792412751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620056264149486892868005 303760549528028792412751)
                  ·
                    rfl

theorem cell20_665518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_665518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665518 prefixEnd_665518 := by exact prefixLift 665518
  have htrace : WordTrace (prefixWord ++ tailWord_665518) baseStart_665518 baseEnd_665518 := by
    simpa [prefixWord, tailWord_665518, baseEnd_665518] using wordTrace_append hprefix tailTrace_665518
  have hstable : (prefixWord ++ tailWord_665518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665518).length < 2 ^ (prefixWord ++ tailWord_665518).sum := by decide
  have hdescent : baseEnd_665518 < baseStart_665518 := by decide
  rcases family_descends (prefixWord ++ tailWord_665518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665532 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_665532 : Nat := 118140960795 + 665532 * 2 ^ 59
def prefixEnd_665532 : Nat := 4983230072969 + 3 ^ 40 * 665532 * 2
def baseEnd_665532 : Nat := 303766939509506965946027

theorem tailTrace_665532 : CollatzResearch.WordTrace tailWord_665532 prefixEnd_665532 303766939509506965946027 := by
  unfold tailWord_665532
  simp only [CollatzResearch.WordTrace]
  refine ⟨12136973112449351330735425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16182630816599135107647233 12136973112449351330735425)
  ·
    refine ⟨9102729834337013498051569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12136973112449351330735425 9102729834337013498051569)
    ·
      refine ⟨6827047375752760123538677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9102729834337013498051569 6827047375752760123538677)
      ·
        refine ⟨640035691476821261581751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6827047375752760123538677 640035691476821261581751)
        ·
          refine ⟨960053537215231892372627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640035691476821261581751 960053537215231892372627)
          ·
            refine ⟨1440080305822847838558941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960053537215231892372627 1440080305822847838558941)
            ·
              refine ⟨540030114683567939459603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1440080305822847838558941 540030114683567939459603)
              ·
                refine ⟨810045172025351909189405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540030114683567939459603 810045172025351909189405)
                ·
                  refine ⟨303766939509506965946027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810045172025351909189405 303766939509506965946027)
                  ·
                    rfl

theorem cell20_665532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_665532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665532 prefixEnd_665532 := by exact prefixLift 665532
  have htrace : WordTrace (prefixWord ++ tailWord_665532) baseStart_665532 baseEnd_665532 := by
    simpa [prefixWord, tailWord_665532, baseEnd_665532] using wordTrace_append hprefix tailTrace_665532
  have hstable : (prefixWord ++ tailWord_665532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665532).length < 2 ^ (prefixWord ++ tailWord_665532).sum := by decide
  have hdescent : baseEnd_665532 < baseStart_665532 := by decide
  rcases family_descends (prefixWord ++ tailWord_665532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665536 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_665536 : Nat := 118140960795 + 665536 * 2 ^ 59
def prefixEnd_665536 : Nat := 4983230072969 + 3 ^ 40 * 665536 * 2
def baseEnd_665536 : Nat := 303768765218500729812677

theorem tailTrace_665536 : CollatzResearch.WordTrace tailWord_665536 prefixEnd_665536 303768765218500729812677 := by
  unfold tailWord_665536
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137046058442105672308231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16182728077922807563077641 12137046058442105672308231)
  ·
    refine ⟨18205569087663158508462347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137046058442105672308231 18205569087663158508462347)
    ·
      refine ⟨27308353631494737762693521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18205569087663158508462347 27308353631494737762693521)
      ·
        refine ⟨20481265223621053322020141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27308353631494737762693521 20481265223621053322020141)
        ·
          refine ⟨7680474458857894995757553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20481265223621053322020141 7680474458857894995757553)
          ·
            refine ⟨5760355844143421246818165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7680474458857894995757553 5760355844143421246818165)
            ·
              refine ⟨540033360388445741889203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5760355844143421246818165 540033360388445741889203)
              ·
                refine ⟨810050040582668612833805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540033360388445741889203 810050040582668612833805)
                ·
                  refine ⟨303768765218500729812677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810050040582668612833805 303768765218500729812677)
                  ·
                    rfl

theorem cell20_665536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_665536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665536 prefixEnd_665536 := by exact prefixLift 665536
  have htrace : WordTrace (prefixWord ++ tailWord_665536) baseStart_665536 baseEnd_665536 := by
    simpa [prefixWord, tailWord_665536, baseEnd_665536] using wordTrace_append hprefix tailTrace_665536
  have hstable : (prefixWord ++ tailWord_665536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665536).length < 2 ^ (prefixWord ++ tailWord_665536).sum := by decide
  have hdescent : baseEnd_665536 < baseStart_665536 := by decide
  rcases family_descends (prefixWord ++ tailWord_665536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665557 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_665557 : Nat := 118140960795 + 665557 * 2 ^ 59
def prefixEnd_665557 : Nat := 4983230072969 + 3 ^ 40 * 665557 * 2
def baseEnd_665557 : Nat := 303778350190717990112591

theorem tailTrace_665557 : CollatzResearch.WordTrace tailWord_665557 prefixEnd_665557 303778350190717990112591 := by
  unfold tailWord_665557
  simp only [CollatzResearch.WordTrace]
  refine ⟨24274858049808131931130925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16183238699872087954087283 24274858049808131931130925)
  ·
    refine ⟨9103071768678049474174097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24274858049808131931130925 9103071768678049474174097)
    ·
      refine ⟨6827303826508537105630573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9103071768678049474174097 6827303826508537105630573)
      ·
        refine ⟨2560238934940701414611465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6827303826508537105630573 2560238934940701414611465)
        ·
          refine ⟨1920179201205526060958599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2560238934940701414611465 1920179201205526060958599)
          ·
            refine ⟨2880268801808289091437899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920179201205526060958599 2880268801808289091437899)
            ·
              refine ⟨4320403202712433637156849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880268801808289091437899 4320403202712433637156849)
              ·
                refine ⟨3240302402034325227867637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320403202712433637156849 3240302402034325227867637)
                ·
                  refine ⟨303778350190717990112591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240302402034325227867637 303778350190717990112591)
                  ·
                    rfl

theorem cell20_665557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_665557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665557 prefixEnd_665557 := by exact prefixLift 665557
  have htrace : WordTrace (prefixWord ++ tailWord_665557) baseStart_665557 baseEnd_665557 := by
    simpa [prefixWord, tailWord_665557, baseEnd_665557] using wordTrace_append hprefix tailTrace_665557
  have hstable : (prefixWord ++ tailWord_665557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665557).length < 2 ^ (prefixWord ++ tailWord_665557).sum := by decide
  have hdescent : baseEnd_665557 < baseStart_665557 := by decide
  rcases family_descends (prefixWord ++ tailWord_665557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665571 : List Nat := [1, 1, 1, 6, 1, 2, 8]
def baseStart_665571 : Nat := 118140960795 + 665571 * 2 ^ 59
def prefixEnd_665571 : Nat := 4983230072969 + 3 ^ 40 * 665571 * 2
def baseEnd_665571 : Nat := 33753860019132907071763

theorem tailTrace_665571 : CollatzResearch.WordTrace tailWord_665571 prefixEnd_665571 33753860019132907071763 := by
  unfold tailWord_665571
  simp only [CollatzResearch.WordTrace]
  refine ⟨24275368671757412322140567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16183579114504941548093711 24275368671757412322140567)
  ·
    refine ⟨36413053007636118483210851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24275368671757412322140567 36413053007636118483210851)
    ·
      refine ⟨54619579511454177724816277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36413053007636118483210851 54619579511454177724816277)
      ·
        refine ⟨2560292789599414580850763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54619579511454177724816277 2560292789599414580850763)
        ·
          refine ⟨3840439184399121871276145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560292789599414580850763 3840439184399121871276145)
          ·
            refine ⟨2880329388299341403457109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840439184399121871276145 2880329388299341403457109)
            ·
              refine ⟨33753860019132907071763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2880329388299341403457109 33753860019132907071763)
              ·
                rfl

theorem cell20_665571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_665571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665571 prefixEnd_665571 := by exact prefixLift 665571
  have htrace : WordTrace (prefixWord ++ tailWord_665571) baseStart_665571 baseEnd_665571 := by
    simpa [prefixWord, tailWord_665571, baseEnd_665571] using wordTrace_append hprefix tailTrace_665571
  have hstable : (prefixWord ++ tailWord_665571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665571).length < 2 ^ (prefixWord ++ tailWord_665571).sum := by decide
  have hdescent : baseEnd_665571 < baseStart_665571 := by decide
  rcases family_descends (prefixWord ++ tailWord_665571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665657 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_665657 : Nat := 118140960795 + 665657 * 2 ^ 59
def prefixEnd_665657 : Nat := 4983230072969 + 3 ^ 40 * 665657 * 2
def baseEnd_665657 : Nat := 303823992915562086778849

theorem tailTrace_665657 : CollatzResearch.WordTrace tailWord_665657 prefixEnd_665657 303823992915562086778849 := by
  unfold tailWord_665657
  simp only [CollatzResearch.WordTrace]
  refine ⟨24278505349445849009771225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16185670232963899339847483 24278505349445849009771225)
  ·
    refine ⟨18208879012084386757328419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24278505349445849009771225 18208879012084386757328419)
    ·
      refine ⟨27313318518126580135992629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18208879012084386757328419 27313318518126580135992629)
      ·
        refine ⟨2560623611074366887749309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27313318518126580135992629 2560623611074366887749309)
        ·
          refine ⟨960233854152887582905991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2560623611074366887749309 960233854152887582905991)
          ·
            refine ⟨1440350781229331374358987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960233854152887582905991 1440350781229331374358987)
            ·
              refine ⟨2160526171843997061538481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440350781229331374358987 2160526171843997061538481)
              ·
                refine ⟨1620394628882997796153861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160526171843997061538481 1620394628882997796153861)
                ·
                  refine ⟨303823992915562086778849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620394628882997796153861 303823992915562086778849)
                  ·
                    rfl

theorem cell20_665657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_665657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665657 prefixEnd_665657 := by exact prefixLift 665657
  have htrace : WordTrace (prefixWord ++ tailWord_665657) baseStart_665657 baseEnd_665657 := by
    simpa [prefixWord, tailWord_665657, baseEnd_665657] using wordTrace_append hprefix tailTrace_665657
  have hstable : (prefixWord ++ tailWord_665657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665657).length < 2 ^ (prefixWord ++ tailWord_665657).sum := by decide
  have hdescent : baseEnd_665657 < baseStart_665657 := by decide
  rcases family_descends (prefixWord ++ tailWord_665657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665664 : List Nat := [2, 1, 1, 2, 2, 5, 3, 4]
def baseStart_665664 : Nat := 118140960795 + 665664 * 2 ^ 59
def prefixEnd_665664 : Nat := 4983230072969 + 3 ^ 40 * 665664 * 2
def baseEnd_665664 : Nat := 101275729302100391181829

theorem tailTrace_665664 : CollatzResearch.WordTrace tailWord_665664 prefixEnd_665664 101275729302100391181829 := by
  unfold tailWord_665664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139380330210244602638023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16185840440280326136850697 12139380330210244602638023)
  ·
    refine ⟨18209070495315366903957035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12139380330210244602638023 18209070495315366903957035)
    ·
      refine ⟨27313605742973050355935553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18209070495315366903957035 27313605742973050355935553)
      ·
        refine ⟨20485204307229787766951665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27313605742973050355935553 20485204307229787766951665)
        ·
          refine ⟨15363903230422340825213749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20485204307229787766951665 15363903230422340825213749)
          ·
            refine ⟨1440365927852094452363789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15363903230422340825213749 1440365927852094452363789)
            ·
              refine ⟨540137222944535419636421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1440365927852094452363789 540137222944535419636421)
              ·
                refine ⟨101275729302100391181829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540137222944535419636421 101275729302100391181829)
                ·
                  rfl

theorem cell20_665664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_665664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665664 prefixEnd_665664 := by exact prefixLift 665664
  have htrace : WordTrace (prefixWord ++ tailWord_665664) baseStart_665664 baseEnd_665664 := by
    simpa [prefixWord, tailWord_665664, baseEnd_665664] using wordTrace_append hprefix tailTrace_665664
  have hstable : (prefixWord ++ tailWord_665664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665664).length < 2 ^ (prefixWord ++ tailWord_665664).sum := by decide
  have hdescent : baseEnd_665664 < baseStart_665664 := by decide
  rcases family_descends (prefixWord ++ tailWord_665664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665685 : List Nat := [1, 3, 2, 2, 1, 4, 7]
def baseStart_665685 : Nat := 118140960795 + 665685 * 2 ^ 59
def prefixEnd_665685 : Nat := 4983230072969 + 3 ^ 40 * 665685 * 2
def baseEnd_665685 : Nat := 33759641430946492649489

theorem tailTrace_665685 : CollatzResearch.WordTrace tailWord_665685 prefixEnd_665685 33759641430946492649489 := by
  unfold tailWord_665685
  simp only [CollatzResearch.WordTrace]
  refine ⟨24279526593344409791790509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16186351062229606527860339 24279526593344409791790509)
  ·
    refine ⟨9104822472504153671921441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24279526593344409791790509 9104822472504153671921441)
    ·
      refine ⟨6828616854378115253941081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9104822472504153671921441 6828616854378115253941081)
      ·
        refine ⟨5121462640783586440455811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6828616854378115253941081 5121462640783586440455811)
        ·
          refine ⟨7682193961175379660683717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121462640783586440455811 7682193961175379660683717)
          ·
            refine ⟨1440411367720383686378197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7682193961175379660683717 1440411367720383686378197)
            ·
              refine ⟨33759641430946492649489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1440411367720383686378197 33759641430946492649489)
              ·
                rfl

theorem cell20_665685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_665685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665685 prefixEnd_665685 := by exact prefixLift 665685
  have htrace : WordTrace (prefixWord ++ tailWord_665685) baseStart_665685 baseEnd_665685 := by
    simpa [prefixWord, tailWord_665685, baseEnd_665685] using wordTrace_append hprefix tailTrace_665685
  have hstable : (prefixWord ++ tailWord_665685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665685).length < 2 ^ (prefixWord ++ tailWord_665685).sum := by decide
  have hdescent : baseEnd_665685 < baseStart_665685 := by decide
  rcases family_descends (prefixWord ++ tailWord_665685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665688 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_665688 : Nat := 118140960795 + 665688 * 2 ^ 59
def prefixEnd_665688 : Nat := 4983230072969 + 3 ^ 40 * 665688 * 2
def baseEnd_665688 : Nat := 303838142160263756745389

theorem tailTrace_665688 : CollatzResearch.WordTrace tailWord_665688 prefixEnd_665688 303838142160263756745389 := by
  unfold tailWord_665688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139818006166770652074859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16186424008222360869433145 12139818006166770652074859)
  ·
    refine ⟨18209727009250155978112289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12139818006166770652074859 18209727009250155978112289)
    ·
      refine ⟨13657295256937616983584217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18209727009250155978112289 13657295256937616983584217)
      ·
        refine ⟨10242971442703212737688163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13657295256937616983584217 10242971442703212737688163)
        ·
          refine ⟨15364457164054819106532245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10242971442703212737688163 15364457164054819106532245)
          ·
            refine ⟨720208929565069645618699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15364457164054819106532245 720208929565069645618699)
            ·
              refine ⟨1080313394347604468428049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720208929565069645618699 1080313394347604468428049)
              ·
                refine ⟨810235045760703351321037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080313394347604468428049 810235045760703351321037)
                ·
                  refine ⟨303838142160263756745389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810235045760703351321037 303838142160263756745389)
                  ·
                    rfl

theorem cell20_665688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_665688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665688 prefixEnd_665688 := by exact prefixLift 665688
  have htrace : WordTrace (prefixWord ++ tailWord_665688) baseStart_665688 baseEnd_665688 := by
    simpa [prefixWord, tailWord_665688, baseEnd_665688] using wordTrace_append hprefix tailTrace_665688
  have hstable : (prefixWord ++ tailWord_665688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665688).length < 2 ^ (prefixWord ++ tailWord_665688).sum := by decide
  have hdescent : baseEnd_665688 < baseStart_665688 := by decide
  rcases family_descends (prefixWord ++ tailWord_665688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665729 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 2]
def baseStart_665729 : Nat := 118140960795 + 665729 * 2 ^ 59
def prefixEnd_665729 : Nat := 4983230072969 + 3 ^ 40 * 665729 * 2
def baseEnd_665729 : Nat := 303856855677449836378555

theorem tailTrace_665729 : CollatzResearch.WordTrace tailWord_665729 prefixEnd_665729 303856855677449836378555 := by
  unfold tailWord_665729
  simp only [CollatzResearch.WordTrace]
  refine ⟨24281131405185005306392241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16187420936790003537594827 24281131405185005306392241)
  ·
    refine ⟨18210848553888753979794181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24281131405185005306392241 18210848553888753979794181)
    ·
      refine ⟨3414534103854141371211409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18210848553888753979794181 3414534103854141371211409)
      ·
        refine ⟨2560900577890606028408557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3414534103854141371211409 2560900577890606028408557)
        ·
          refine ⟨960337716708977260653209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2560900577890606028408557 960337716708977260653209)
          ·
            refine ⟨720253287531732945489907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960337716708977260653209 720253287531732945489907)
            ·
              refine ⟨1080379931297599418234861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720253287531732945489907 1080379931297599418234861)
              ·
                refine ⟨405142474236599781838073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1080379931297599418234861 405142474236599781838073)
                ·
                  refine ⟨303856855677449836378555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405142474236599781838073 303856855677449836378555)
                  ·
                    rfl

theorem cell20_665729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_665729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665729 prefixEnd_665729 := by exact prefixLift 665729
  have htrace : WordTrace (prefixWord ++ tailWord_665729) baseStart_665729 baseEnd_665729 := by
    simpa [prefixWord, tailWord_665729, baseEnd_665729] using wordTrace_append hprefix tailTrace_665729
  have hstable : (prefixWord ++ tailWord_665729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665729).length < 2 ^ (prefixWord ++ tailWord_665729).sum := by decide
  have hdescent : baseEnd_665729 < baseStart_665729 := by decide
  rcases family_descends (prefixWord ++ tailWord_665729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665761 : List Nat := [1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_665761 : Nat := 118140960795 + 665761 * 2 ^ 59
def prefixEnd_665761 : Nat := 4983230072969 + 3 ^ 40 * 665761 * 2
def baseEnd_665761 : Nat := 101290487116466649103919

theorem tailTrace_665761 : CollatzResearch.WordTrace tailWord_665761 prefixEnd_665761 101290487116466649103919 := by
  unfold tailWord_665761
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282298541069074771557137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16188199027379383181038091 24282298541069074771557137)
  ·
    refine ⟨18211723905801806078667853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24282298541069074771557137 18211723905801806078667853)
    ·
      refine ⟨6829396464675677279500445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18211723905801806078667853 6829396464675677279500445)
      ·
        refine ⟨2561023674253378979812667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6829396464675677279500445 2561023674253378979812667)
        ·
          refine ⟨3841535511380068469719001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561023674253378979812667 3841535511380068469719001)
          ·
            refine ⟨2881151633535051352289251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3841535511380068469719001 2881151633535051352289251)
            ·
              refine ⟨4321727450302577028433877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881151633535051352289251 4321727450302577028433877)
              ·
                refine ⟨101290487116466649103919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4321727450302577028433877 101290487116466649103919)
                ·
                  rfl

theorem cell20_665761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_665761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665761 prefixEnd_665761 := by exact prefixLift 665761
  have htrace : WordTrace (prefixWord ++ tailWord_665761) baseStart_665761 baseEnd_665761 := by
    simpa [prefixWord, tailWord_665761, baseEnd_665761] using wordTrace_append hprefix tailTrace_665761
  have hstable : (prefixWord ++ tailWord_665761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665761).length < 2 ^ (prefixWord ++ tailWord_665761).sum := by decide
  have hdescent : baseEnd_665761 < baseStart_665761 := by decide
  rcases family_descends (prefixWord ++ tailWord_665761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665764 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_665764 : Nat := 118140960795 + 665764 * 2 ^ 59
def prefixEnd_665764 : Nat := 4983230072969 + 3 ^ 40 * 665764 * 2
def baseEnd_665764 : Nat := 303872830631145270211745

theorem tailTrace_665764 : CollatzResearch.WordTrace tailWord_665764 prefixEnd_665764 303872830631145270211745 := by
  unfold tailWord_665764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12141203980029103141958173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16188271973372137522610897 12141203980029103141958173)
  ·
    refine ⟨4552951492510913678234315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12141203980029103141958173 4552951492510913678234315)
    ·
      refine ⟨6829427238766370517351473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552951492510913678234315 6829427238766370517351473)
      ·
        refine ⟨5122070429074777888013605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6829427238766370517351473 5122070429074777888013605)
        ·
          refine ⟨960388205451520854002551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5122070429074777888013605 960388205451520854002551)
          ·
            refine ⟨1440582308177281281003827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960388205451520854002551 1440582308177281281003827)
            ·
              refine ⟨2160873462265921921505741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440582308177281281003827 2160873462265921921505741)
              ·
                refine ⟨810327548349720720564653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2160873462265921921505741 810327548349720720564653)
                ·
                  refine ⟨303872830631145270211745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810327548349720720564653 303872830631145270211745)
                  ·
                    rfl

theorem cell20_665764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_665764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665764 prefixEnd_665764 := by exact prefixLift 665764
  have htrace : WordTrace (prefixWord ++ tailWord_665764) baseStart_665764 baseEnd_665764 := by
    simpa [prefixWord, tailWord_665764, baseEnd_665764] using wordTrace_append hprefix tailTrace_665764
  have hstable : (prefixWord ++ tailWord_665764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665764).length < 2 ^ (prefixWord ++ tailWord_665764).sum := by decide
  have hdescent : baseEnd_665764 < baseStart_665764 := by decide
  rcases family_descends (prefixWord ++ tailWord_665764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665775 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_665775 : Nat := 118140960795 + 665775 * 2 ^ 59
def prefixEnd_665775 : Nat := 4983230072969 + 3 ^ 40 * 665775 * 2
def baseEnd_665775 : Nat := 303877851330878120845033

theorem tailTrace_665775 : CollatzResearch.WordTrace tailWord_665775 prefixEnd_665775 303877851330878120845033 := by
  unfold tailWord_665775
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282809163018355162566779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16188539442012236775044519 24282809163018355162566779)
  ·
    refine ⟨36424213744527532743850169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24282809163018355162566779 36424213744527532743850169)
    ·
      refine ⟨27318160308395649557887627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36424213744527532743850169 27318160308395649557887627)
      ·
        refine ⟨40977240462593474336831441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27318160308395649557887627 40977240462593474336831441)
        ·
          refine ⟨30732930346945105752623581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40977240462593474336831441 30732930346945105752623581)
          ·
            refine ⟨11524848880104414657233843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30732930346945105752623581 11524848880104414657233843)
            ·
              refine ⟨17287273320156621985850765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11524848880104414657233843 17287273320156621985850765)
              ·
                refine ⟨6482727495058733244694037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17287273320156621985850765 6482727495058733244694037)
                ·
                  refine ⟨303877851330878120845033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6482727495058733244694037 303877851330878120845033)
                  ·
                    rfl

theorem cell20_665775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_665775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665775 prefixEnd_665775 := by exact prefixLift 665775
  have htrace : WordTrace (prefixWord ++ tailWord_665775) baseStart_665775 baseEnd_665775 := by
    simpa [prefixWord, tailWord_665775, baseEnd_665775] using wordTrace_append hprefix tailTrace_665775
  have hstable : (prefixWord ++ tailWord_665775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665775).length < 2 ^ (prefixWord ++ tailWord_665775).sum := by decide
  have hdescent : baseEnd_665775 < baseStart_665775 := by decide
  rcases family_descends (prefixWord ++ tailWord_665775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665816 : List Nat := [2, 1, 2, 2, 4, 3, 1, 5]
def baseStart_665816 : Nat := 118140960795 + 665816 * 2 ^ 59
def prefixEnd_665816 : Nat := 4983230072969 + 3 ^ 40 * 665816 * 2
def baseEnd_665816 : Nat := 101298854949354733492733

theorem tailTrace_665816 : CollatzResearch.WordTrace tailWord_665816 prefixEnd_665816 101298854949354733492733 := by
  unfold tailWord_665816
  simp only [CollatzResearch.WordTrace]
  refine ⟨12142152277934909582404651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16189536370579879443206201 12142152277934909582404651)
  ·
    refine ⟨18213228416902364373606977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12142152277934909582404651 18213228416902364373606977)
    ·
      refine ⟨13659921312676773280205233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18213228416902364373606977 13659921312676773280205233)
      ·
        refine ⟨10244940984507579960153925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13659921312676773280205233 10244940984507579960153925)
        ·
          refine ⟨1920926434595171242528861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10244940984507579960153925 1920926434595171242528861)
          ·
            refine ⟨720347412973189215948323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1920926434595171242528861 720347412973189215948323)
            ·
              refine ⟨1080521119459783823922485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720347412973189215948323 1080521119459783823922485)
              ·
                refine ⟨101298854949354733492733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1080521119459783823922485 101298854949354733492733)
                ·
                  rfl

theorem cell20_665816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_665816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665816 prefixEnd_665816 := by exact prefixLift 665816
  have htrace : WordTrace (prefixWord ++ tailWord_665816) baseStart_665816 baseEnd_665816 := by
    simpa [prefixWord, tailWord_665816, baseEnd_665816] using wordTrace_append hprefix tailTrace_665816
  have hstable : (prefixWord ++ tailWord_665816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665816).length < 2 ^ (prefixWord ++ tailWord_665816).sum := by decide
  have hdescent : baseEnd_665816 < baseStart_665816 := by decide
  rcases family_descends (prefixWord ++ tailWord_665816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665868 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_665868 : Nat := 118140960795 + 665868 * 2 ^ 59
def prefixEnd_665868 : Nat := 4983230072969 + 3 ^ 40 * 665868 * 2
def baseEnd_665868 : Nat := 303920299064983130744653

theorem tailTrace_665868 : CollatzResearch.WordTrace tailWord_665868 prefixEnd_665868 303920299064983130744653 := by
  unfold tailWord_665868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143100575840716022851129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16190800767787621363801505 12143100575840716022851129)
  ·
    refine ⟨9107325431880537017138347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12143100575840716022851129 9107325431880537017138347)
    ·
      refine ⟨13660988147820805525707521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9107325431880537017138347 13660988147820805525707521)
      ·
        refine ⟨10245741110865604144280641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13660988147820805525707521 10245741110865604144280641)
        ·
          refine ⟨7684305833149203108210481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10245741110865604144280641 7684305833149203108210481)
          ·
            refine ⟨5763229374861902331157861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7684305833149203108210481 5763229374861902331157861)
            ·
              refine ⟨1080605507786606687092099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5763229374861902331157861 1080605507786606687092099)
              ·
                refine ⟨1620908261679910030638149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080605507786606687092099 1620908261679910030638149)
                ·
                  refine ⟨303920299064983130744653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620908261679910030638149 303920299064983130744653)
                  ·
                    rfl

theorem cell20_665868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_665868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665868 prefixEnd_665868 := by exact prefixLift 665868
  have htrace : WordTrace (prefixWord ++ tailWord_665868) baseStart_665868 baseEnd_665868 := by
    simpa [prefixWord, tailWord_665868, baseEnd_665868] using wordTrace_append hprefix tailTrace_665868
  have hstable : (prefixWord ++ tailWord_665868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665868).length < 2 ^ (prefixWord ++ tailWord_665868).sum := by decide
  have hdescent : baseEnd_665868 < baseStart_665868 := by decide
  rcases family_descends (prefixWord ++ tailWord_665868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665892 : List Nat := [2, 3, 1, 3, 1, 2, 4, 4]
def baseStart_665892 : Nat := 118140960795 + 665892 * 2 ^ 59
def prefixEnd_665892 : Nat := 4983230072969 + 3 ^ 40 * 665892 * 2
def baseEnd_665892 : Nat := 101310417772981904648185

theorem tailTrace_665892 : CollatzResearch.WordTrace tailWord_665892 prefixEnd_665892 101310417772981904648185 := by
  unfold tailWord_665892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143538251797242072287965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16191384335729656096383953 12143538251797242072287965)
  ·
    refine ⟨4553826844423965777107987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12143538251797242072287965 4553826844423965777107987)
    ·
      refine ⟨6830740266635948665661981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4553826844423965777107987 6830740266635948665661981)
      ·
        refine ⟨2561527599988480749623243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6830740266635948665661981 2561527599988480749623243)
        ·
          refine ⟨3842291399982721124434865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561527599988480749623243 3842291399982721124434865)
          ·
            refine ⟨2881718549987040843326149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3842291399982721124434865 2881718549987040843326149)
            ·
              refine ⟨540322228122570158123653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2881718549987040843326149 540322228122570158123653)
              ·
                refine ⟨101310417772981904648185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540322228122570158123653 101310417772981904648185)
                ·
                  rfl

theorem cell20_665892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_665892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665892 prefixEnd_665892 := by exact prefixLift 665892
  have htrace : WordTrace (prefixWord ++ tailWord_665892) baseStart_665892 baseEnd_665892 := by
    simpa [prefixWord, tailWord_665892, baseEnd_665892] using wordTrace_append hprefix tailTrace_665892
  have hstable : (prefixWord ++ tailWord_665892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665892).length < 2 ^ (prefixWord ++ tailWord_665892).sum := by decide
  have hdescent : baseEnd_665892 < baseStart_665892 := by decide
  rcases family_descends (prefixWord ++ tailWord_665892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665898 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_665898 : Nat := 118140960795 + 665898 * 2 ^ 59
def prefixEnd_665898 : Nat := 4983230072969 + 3 ^ 40 * 665898 * 2
def baseEnd_665898 : Nat := 303933991882436359744531

theorem tailTrace_665898 : CollatzResearch.WordTrace tailWord_665898 prefixEnd_665898 303933991882436359744531 := by
  unfold tailWord_665898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071823835393186792323587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16191530227715164779529565 6071823835393186792323587)
  ·
    refine ⟨9107735753089780188485381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6071823835393186792323587 9107735753089780188485381)
    ·
      refine ⟨1707700453704333785341009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9107735753089780188485381 1707700453704333785341009)
      ·
        refine ⟨1280775340278250339005757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707700453704333785341009 1280775340278250339005757)
        ·
          refine ⟨480290752604343877127159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1280775340278250339005757 480290752604343877127159)
          ·
            refine ⟨720436128906515815690739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480290752604343877127159 720436128906515815690739)
            ·
              refine ⟨1080654193359773723536109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720436128906515815690739 1080654193359773723536109)
              ·
                refine ⟨405245322509915146326041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1080654193359773723536109 405245322509915146326041)
                ·
                  refine ⟨303933991882436359744531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405245322509915146326041 303933991882436359744531)
                  ·
                    rfl

theorem cell20_665898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_665898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665898 prefixEnd_665898 := by exact prefixLift 665898
  have htrace : WordTrace (prefixWord ++ tailWord_665898) baseStart_665898 baseEnd_665898 := by
    simpa [prefixWord, tailWord_665898, baseEnd_665898] using wordTrace_append hprefix tailTrace_665898
  have hstable : (prefixWord ++ tailWord_665898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665898).length < 2 ^ (prefixWord ++ tailWord_665898).sum := by decide
  have hdescent : baseEnd_665898 < baseStart_665898 := by decide
  rcases family_descends (prefixWord ++ tailWord_665898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665913 : List Nat := [1, 2, 1, 6, 1, 1, 8]
def baseStart_665913 : Nat := 118140960795 + 665913 * 2 ^ 59
def prefixEnd_665913 : Nat := 4983230072969 + 3 ^ 40 * 665913 * 2
def baseEnd_665913 : Nat := 33771204254573663804941

theorem tailTrace_665913 : CollatzResearch.WordTrace tailWord_665913 prefixEnd_665913 33771204254573663804941 := by
  unfold tailWord_665913
  simp only [CollatzResearch.WordTrace]
  refine ⟨24287842436518404731090393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16191894957678936487393595 24287842436518404731090393)
  ·
    refine ⟨18215881827388803548317795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24287842436518404731090393 18215881827388803548317795)
    ·
      refine ⟨27323822741083205322476693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18215881827388803548317795 27323822741083205322476693)
      ·
        refine ⟨1280804190988275249491095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27323822741083205322476693 1280804190988275249491095)
        ·
          refine ⟨1921206286482412874236643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280804190988275249491095 1921206286482412874236643)
          ·
            refine ⟨2881809429723619311354965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921206286482412874236643 2881809429723619311354965)
            ·
              refine ⟨33771204254573663804941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2881809429723619311354965 33771204254573663804941)
              ·
                rfl

theorem cell20_665913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_665913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665913 prefixEnd_665913 := by exact prefixLift 665913
  have htrace : WordTrace (prefixWord ++ tailWord_665913) baseStart_665913 baseEnd_665913 := by
    simpa [prefixWord, tailWord_665913, baseEnd_665913] using wordTrace_append hprefix tailTrace_665913
  have hstable : (prefixWord ++ tailWord_665913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665913).length < 2 ^ (prefixWord ++ tailWord_665913).sum := by decide
  have hdescent : baseEnd_665913 < baseStart_665913 := by decide
  rcases family_descends (prefixWord ++ tailWord_665913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665937 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_665937 : Nat := 118140960795 + 665937 * 2 ^ 59
def prefixEnd_665937 : Nat := 4983230072969 + 3 ^ 40 * 665937 * 2
def baseEnd_665937 : Nat := 303951792545125557444371

theorem tailTrace_665937 : CollatzResearch.WordTrace tailWord_665937 prefixEnd_665937 303951792545125557444371 := by
  unfold tailWord_665937
  simp only [CollatzResearch.WordTrace]
  refine ⟨24288717788431456829964065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16192478525620971219976043 24288717788431456829964065)
  ·
    refine ⟨18216538341323592622473049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24288717788431456829964065 18216538341323592622473049)
    ·
      refine ⟨13662403755992694466854787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18216538341323592622473049 13662403755992694466854787)
      ·
        refine ⟨20493605633989041700282181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13662403755992694466854787 20493605633989041700282181)
        ·
          refine ⟨3842551056372945318802909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20493605633989041700282181 3842551056372945318802909)
          ·
            refine ⟨1440956646139854494551091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3842551056372945318802909 1440956646139854494551091)
            ·
              refine ⟨2161434969209781741826637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440956646139854494551091 2161434969209781741826637)
              ·
                refine ⟨810538113453668153184989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2161434969209781741826637 810538113453668153184989)
                ·
                  refine ⟨303951792545125557444371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810538113453668153184989 303951792545125557444371)
                  ·
                    rfl

theorem cell20_665937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_665937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_665937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_665937 prefixEnd_665937 := by exact prefixLift 665937
  have htrace : WordTrace (prefixWord ++ tailWord_665937) baseStart_665937 baseEnd_665937 := by
    simpa [prefixWord, tailWord_665937, baseEnd_665937] using wordTrace_append hprefix tailTrace_665937
  have hstable : (prefixWord ++ tailWord_665937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665937).length < 2 ^ (prefixWord ++ tailWord_665937).sum := by decide
  have hdescent : baseEnd_665937 < baseStart_665937 := by decide
  rcases family_descends (prefixWord ++ tailWord_665937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666034 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_666034 : Nat := 118140960795 + 666034 * 2 ^ 59
def prefixEnd_666034 : Nat := 4983230072969 + 3 ^ 40 * 666034 * 2
def baseEnd_666034 : Nat := 303996065988224331210641

theorem tailTrace_666034 : CollatzResearch.WordTrace tailWord_666034 prefixEnd_666034 303996065988224331210641 := by
  unfold tailWord_666034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073063917270010599061289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16194837112720028264163437 6073063917270010599061289)
  ·
    refine ⟨4554797937952507949295967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6073063917270010599061289 4554797937952507949295967)
    ·
      refine ⟨6832196906928761923943951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4554797937952507949295967 6832196906928761923943951)
      ·
        refine ⟨10248295360393142885915927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832196906928761923943951 10248295360393142885915927)
        ·
          refine ⟨15372443040589714328873891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248295360393142885915927 15372443040589714328873891)
          ·
            refine ⟨23058664560884571493310837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15372443040589714328873891 23058664560884571493310837)
            ·
              refine ⟨2161749802582928577497891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23058664560884571493310837 2161749802582928577497891)
              ·
                refine ⟨3242624703874392866246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161749802582928577497891 3242624703874392866246837)
                ·
                  refine ⟨303996065988224331210641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3242624703874392866246837 303996065988224331210641)
                  ·
                    rfl

theorem cell20_666034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_666034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666034 prefixEnd_666034 := by exact prefixLift 666034
  have htrace : WordTrace (prefixWord ++ tailWord_666034) baseStart_666034 baseEnd_666034 := by
    simpa [prefixWord, tailWord_666034, baseEnd_666034] using wordTrace_append hprefix tailTrace_666034
  have hstable : (prefixWord ++ tailWord_666034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666034).length < 2 ^ (prefixWord ++ tailWord_666034).sum := by decide
  have hdescent : baseEnd_666034 < baseStart_666034 := by decide
  rcases family_descends (prefixWord ++ tailWord_666034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666037 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_666037 : Nat := 118140960795 + 666037 * 2 ^ 59
def prefixEnd_666037 : Nat := 4983230072969 + 3 ^ 40 * 666037 * 2
def baseEnd_666037 : Nat := 303997435269969654110629

theorem tailTrace_666037 : CollatzResearch.WordTrace tailWord_666037 prefixEnd_666037 303997435269969654110629 := by
  unfold tailWord_666037
  simp only [CollatzResearch.WordTrace]
  refine ⟨24292365088069173908604365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16194910058712782605736243 24292365088069173908604365)
  ·
    refine ⟨9109636908025940215726637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24292365088069173908604365 9109636908025940215726637)
    ·
      refine ⟨3416113840509727580897489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9109636908025940215726637 3416113840509727580897489)
      ·
        refine ⟨2562085380382295685673117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3416113840509727580897489 2562085380382295685673117)
        ·
          refine ⟨960782017643360882127419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2562085380382295685673117 960782017643360882127419)
          ·
            refine ⟨1441173026465041323191129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960782017643360882127419 1441173026465041323191129)
            ·
              refine ⟨1080879769848780992393347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441173026465041323191129 1080879769848780992393347)
              ·
                refine ⟨1621319654773171488590021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080879769848780992393347 1621319654773171488590021)
                ·
                  refine ⟨303997435269969654110629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621319654773171488590021 303997435269969654110629)
                  ·
                    rfl

theorem cell20_666037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_666037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666037 prefixEnd_666037 := by exact prefixLift 666037
  have htrace : WordTrace (prefixWord ++ tailWord_666037) baseStart_666037 baseEnd_666037 := by
    simpa [prefixWord, tailWord_666037, baseEnd_666037] using wordTrace_append hprefix tailTrace_666037
  have hstable : (prefixWord ++ tailWord_666037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666037).length < 2 ^ (prefixWord ++ tailWord_666037).sum := by decide
  have hdescent : baseEnd_666037 < baseStart_666037 := by decide
  rcases family_descends (prefixWord ++ tailWord_666037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666048 : List Nat := [2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_666048 : Nat := 118140960795 + 666048 * 2 ^ 59
def prefixEnd_666048 : Nat := 4983230072969 + 3 ^ 40 * 666048 * 2
def baseEnd_666048 : Nat := 101334151989900834914639

theorem tailTrace_666048 : CollatzResearch.WordTrace tailWord_666048 prefixEnd_666048 101334151989900834914639 := by
  unfold tailWord_666048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12146383145514661393627399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16195177527352881858169865 12146383145514661393627399)
  ·
    refine ⟨18219574718271992090441099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12146383145514661393627399 18219574718271992090441099)
    ·
      refine ⟨27329362077407988135661649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18219574718271992090441099 27329362077407988135661649)
      ·
        refine ⟨20497021558055991101746237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27329362077407988135661649 20497021558055991101746237)
        ·
          refine ⟨7686383084270996663154839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20497021558055991101746237 7686383084270996663154839)
          ·
            refine ⟨11529574626406494994732259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7686383084270996663154839 11529574626406494994732259)
            ·
              refine ⟨17294361939609742492098389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11529574626406494994732259 17294361939609742492098389)
              ·
                refine ⟨101334151989900834914639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17294361939609742492098389 101334151989900834914639)
                ·
                  rfl

theorem cell20_666048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_666048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666048 prefixEnd_666048 := by exact prefixLift 666048
  have htrace : WordTrace (prefixWord ++ tailWord_666048) baseStart_666048 baseEnd_666048 := by
    simpa [prefixWord, tailWord_666048, baseEnd_666048] using wordTrace_append hprefix tailTrace_666048
  have hstable : (prefixWord ++ tailWord_666048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666048).length < 2 ^ (prefixWord ++ tailWord_666048).sum := by decide
  have hdescent : baseEnd_666048 < baseStart_666048 := by decide
  rcases family_descends (prefixWord ++ tailWord_666048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666117 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_666117 : Nat := 118140960795 + 666117 * 2 ^ 59
def prefixEnd_666117 : Nat := 4983230072969 + 3 ^ 40 * 666117 * 2
def baseEnd_666117 : Nat := 304033949449844931443635

theorem tailTrace_666117 : CollatzResearch.WordTrace tailWord_666117 prefixEnd_666117 304033949449844931443635 := by
  unfold tailWord_666117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24295282927779347571516605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16196855285186231714344403 24295282927779347571516605)
  ·
    refine ⟨9110731097917255339318727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24295282927779347571516605 9110731097917255339318727)
    ·
      refine ⟨13666096646875883008978091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110731097917255339318727 13666096646875883008978091)
      ·
        refine ⟨20499144970313824513467137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13666096646875883008978091 20499144970313824513467137)
        ·
          refine ⟨15374358727735368385100353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20499144970313824513467137 15374358727735368385100353)
          ·
            refine ⟨11530769045801526288825265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15374358727735368385100353 11530769045801526288825265)
            ·
              refine ⟨8648076784351144716618949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11530769045801526288825265 8648076784351144716618949)
              ·
                refine ⟨1621514397065839634366053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8648076784351144716618949 1621514397065839634366053)
                ·
                  refine ⟨304033949449844931443635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621514397065839634366053 304033949449844931443635)
                  ·
                    rfl

theorem cell20_666117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_666117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666117 prefixEnd_666117 := by exact prefixLift 666117
  have htrace : WordTrace (prefixWord ++ tailWord_666117) baseStart_666117 baseEnd_666117 := by
    simpa [prefixWord, tailWord_666117, baseEnd_666117] using wordTrace_append hprefix tailTrace_666117
  have hstable : (prefixWord ++ tailWord_666117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666117).length < 2 ^ (prefixWord ++ tailWord_666117).sum := by decide
  have hdescent : baseEnd_666117 < baseStart_666117 := by decide
  rcases family_descends (prefixWord ++ tailWord_666117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666144 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_666144 : Nat := 118140960795 + 666144 * 2 ^ 59
def prefixEnd_666144 : Nat := 4983230072969 + 3 ^ 40 * 666144 * 2
def baseEnd_666144 : Nat := 304046272985552837543525

theorem tailTrace_666144 : CollatzResearch.WordTrace tailWord_666144 prefixEnd_666144 304046272985552837543525 := by
  unfold tailWord_666144
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148133849340765591374743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16197511799121020788499657 12148133849340765591374743)
  ·
    refine ⟨18222200774011148387062115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12148133849340765591374743 18222200774011148387062115)
    ·
      refine ⟨27333301161016722580593173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18222200774011148387062115 27333301161016722580593173)
      ·
        refine ⟨1281248491922658870965305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27333301161016722580593173 1281248491922658870965305)
        ·
          refine ⟨960936368941994153223979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1281248491922658870965305 960936368941994153223979)
          ·
            refine ⟨1441404553412991229835969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960936368941994153223979 1441404553412991229835969)
            ·
              refine ⟨1081053415059743422376977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441404553412991229835969 1081053415059743422376977)
              ·
                refine ⟨810790061294807566782733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081053415059743422376977 810790061294807566782733)
                ·
                  refine ⟨304046272985552837543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810790061294807566782733 304046272985552837543525)
                  ·
                    rfl

theorem cell20_666144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_666144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666144 prefixEnd_666144 := by exact prefixLift 666144
  have htrace : WordTrace (prefixWord ++ tailWord_666144) baseStart_666144 baseEnd_666144 := by
    simpa [prefixWord, tailWord_666144, baseEnd_666144] using wordTrace_append hprefix tailTrace_666144
  have hstable : (prefixWord ++ tailWord_666144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666144).length < 2 ^ (prefixWord ++ tailWord_666144).sum := by decide
  have hdescent : baseEnd_666144 < baseStart_666144 := by decide
  rcases family_descends (prefixWord ++ tailWord_666144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666172 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_666172 : Nat := 118140960795 + 666172 * 2 ^ 59
def prefixEnd_666172 : Nat := 4983230072969 + 3 ^ 40 * 666172 * 2
def baseEnd_666172 : Nat := 304059052948509184610077

theorem tailTrace_666172 : CollatzResearch.WordTrace tailWord_666172 prefixEnd_666172 304059052948509184610077 := by
  unfold tailWord_666172
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148644471290045982384385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16198192628386727976512513 12148644471290045982384385)
  ·
    refine ⟨9111483353467534486788289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12148644471290045982384385 9111483353467534486788289)
    ·
      refine ⟨6833612515100650865091217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9111483353467534486788289 6833612515100650865091217)
      ·
        refine ⟨5125209386325488148818413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833612515100650865091217 5125209386325488148818413)
        ·
          refine ⟨1921953519872058055806905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5125209386325488148818413 1921953519872058055806905)
          ·
            refine ⟨1441465139904043541855179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1921953519872058055806905 1441465139904043541855179)
            ·
              refine ⟨2162197709856065312782769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441465139904043541855179 2162197709856065312782769)
              ·
                refine ⟨1621648282392048984587077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2162197709856065312782769 1621648282392048984587077)
                ·
                  refine ⟨304059052948509184610077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621648282392048984587077 304059052948509184610077)
                  ·
                    rfl

theorem cell20_666172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_666172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666172 prefixEnd_666172 := by exact prefixLift 666172
  have htrace : WordTrace (prefixWord ++ tailWord_666172) baseStart_666172 baseEnd_666172 := by
    simpa [prefixWord, tailWord_666172, baseEnd_666172] using wordTrace_append hprefix tailTrace_666172
  have hstable : (prefixWord ++ tailWord_666172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666172).length < 2 ^ (prefixWord ++ tailWord_666172).sum := by decide
  have hdescent : baseEnd_666172 < baseStart_666172 := by decide
  rcases family_descends (prefixWord ++ tailWord_666172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666230 : List Nat := [5, 1, 1, 2, 4, 1, 2, 4]
def baseStart_666230 : Nat := 118140960795 + 666230 * 2 ^ 59
def prefixEnd_666230 : Nat := 4983230072969 + 3 ^ 40 * 666230 * 2
def baseEnd_666230 : Nat := 101361841909639586892169

theorem tailTrace_666230 : CollatzResearch.WordTrace tailWord_666230 prefixEnd_666230 101361841909639586892169 := by
  unfold tailWord_666230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518712773523122991898759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16199602917579978580253429 1518712773523122991898759)
  ·
    refine ⟨2278069160284684487848139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1518712773523122991898759 2278069160284684487848139)
    ·
      refine ⟨3417103740427026731772209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278069160284684487848139 3417103740427026731772209)
      ·
        refine ⟨2562827805320270048829157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417103740427026731772209 2562827805320270048829157)
        ·
          refine ⟨480530213497550634155467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2562827805320270048829157 480530213497550634155467)
          ·
            refine ⟨720795320246325951233201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480530213497550634155467 720795320246325951233201)
            ·
              refine ⟨540596490184744463424901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720795320246325951233201 540596490184744463424901)
              ·
                refine ⟨101361841909639586892169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540596490184744463424901 101361841909639586892169)
                ·
                  rfl

theorem cell20_666230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_666230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666230 prefixEnd_666230 := by exact prefixLift 666230
  have htrace : WordTrace (prefixWord ++ tailWord_666230) baseStart_666230 baseEnd_666230 := by
    simpa [prefixWord, tailWord_666230, baseEnd_666230] using wordTrace_append hprefix tailTrace_666230
  have hstable : (prefixWord ++ tailWord_666230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666230).length < 2 ^ (prefixWord ++ tailWord_666230).sum := by decide
  have hdescent : baseEnd_666230 < baseStart_666230 := by decide
  rcases family_descends (prefixWord ++ tailWord_666230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666231 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_666231 : Nat := 118140960795 + 666231 * 2 ^ 59
def prefixEnd_666231 : Nat := 4983230072969 + 3 ^ 40 * 666231 * 2
def baseEnd_666231 : Nat := 304085982156167201643169

theorem tailTrace_666231 : CollatzResearch.WordTrace tailWord_666231 prefixEnd_666231 304085982156167201643169 := by
  unfold tailWord_666231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24299440849366345041166547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16199627232910896694111031 24299440849366345041166547)
  ·
    refine ⟨36449161274049517561749821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24299440849366345041166547 36449161274049517561749821)
    ·
      refine ⟨13668435477768569085656183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36449161274049517561749821 13668435477768569085656183)
      ·
        refine ⟨20502653216652853628484275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13668435477768569085656183 20502653216652853628484275)
        ·
          refine ⟨30753979824979280442726413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20502653216652853628484275 30753979824979280442726413)
          ·
            refine ⟨11532742434367230166022405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30753979824979280442726413 11532742434367230166022405)
            ·
              refine ⟨2162389206443855656129201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11532742434367230166022405 2162389206443855656129201)
              ·
                refine ⟨1621791904832891742096901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2162389206443855656129201 1621791904832891742096901)
                ·
                  refine ⟨304085982156167201643169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621791904832891742096901 304085982156167201643169)
                  ·
                    rfl

theorem cell20_666231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_666231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666231 prefixEnd_666231 := by exact prefixLift 666231
  have htrace : WordTrace (prefixWord ++ tailWord_666231) baseStart_666231 baseEnd_666231 := by
    simpa [prefixWord, tailWord_666231, baseEnd_666231] using wordTrace_append hprefix tailTrace_666231
  have hstable : (prefixWord ++ tailWord_666231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666231).length < 2 ^ (prefixWord ++ tailWord_666231).sum := by decide
  have hdescent : baseEnd_666231 < baseStart_666231 := by decide
  rcases family_descends (prefixWord ++ tailWord_666231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666244 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 2]
def baseStart_666244 : Nat := 118140960795 + 666244 * 2 ^ 59
def prefixEnd_666244 : Nat := 4983230072969 + 3 ^ 40 * 666244 * 2
def baseEnd_666244 : Nat := 304091915710396934209783

theorem tailTrace_666244 : CollatzResearch.WordTrace tailWord_666244 prefixEnd_666244 304091915710396934209783 := by
  unfold tailWord_666244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149957499159624130694893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16199943332212832174259857 12149957499159624130694893)
  ·
    refine ⟨4556234062184859049010585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12149957499159624130694893 4556234062184859049010585)
    ·
      refine ⟨3417175546638644286757939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4556234062184859049010585 3417175546638644286757939)
      ·
        refine ⟨5125763319957966430136909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417175546638644286757939 5125763319957966430136909)
        ·
          refine ⟨1922161244984237411301341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5125763319957966430136909 1922161244984237411301341)
          ·
            refine ⟨720810466869089029238003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1922161244984237411301341 720810466869089029238003)
            ·
              refine ⟨1081215700303633543857005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720810466869089029238003 1081215700303633543857005)
              ·
                refine ⟨405455887613862578946377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081215700303633543857005 405455887613862578946377)
                ·
                  refine ⟨304091915710396934209783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405455887613862578946377 304091915710396934209783)
                  ·
                    rfl

theorem cell20_666244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_666244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666244 prefixEnd_666244 := by exact prefixLift 666244
  have htrace : WordTrace (prefixWord ++ tailWord_666244) baseStart_666244 baseEnd_666244 := by
    simpa [prefixWord, tailWord_666244, baseEnd_666244] using wordTrace_append hprefix tailTrace_666244
  have hstable : (prefixWord ++ tailWord_666244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666244).length < 2 ^ (prefixWord ++ tailWord_666244).sum := by decide
  have hdescent : baseEnd_666244 < baseStart_666244 := by decide
  rcases family_descends (prefixWord ++ tailWord_666244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666265 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 2]
def baseStart_666265 : Nat := 118140960795 + 666265 * 2 ^ 59
def prefixEnd_666265 : Nat := 4983230072969 + 3 ^ 40 * 666265 * 2
def baseEnd_666265 : Nat := 304101500682614194509697

theorem tailTrace_666265 : CollatzResearch.WordTrace tailWord_666265 prefixEnd_666265 304101500682614194509697 := by
  unfold tailWord_666265
  simp only [CollatzResearch.WordTrace]
  refine ⟨24300680931243168847904249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16200453954162112565269499 24300680931243168847904249)
  ·
    refine ⟨18225510698432376635928187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24300680931243168847904249 18225510698432376635928187)
    ·
      refine ⟨27338266047648564953892281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18225510698432376635928187 27338266047648564953892281)
      ·
        refine ⟨20503699535736423715419211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27338266047648564953892281 20503699535736423715419211)
        ·
          refine ⟨30755549303604635573128817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20503699535736423715419211 30755549303604635573128817)
          ·
            refine ⟨23066661977703476679846613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30755549303604635573128817 23066661977703476679846613)
            ·
              refine ⟨540624890102425234683905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23066661977703476679846613 540624890102425234683905)
              ·
                refine ⟨405468667576818926012929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540624890102425234683905 405468667576818926012929)
                ·
                  refine ⟨304101500682614194509697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405468667576818926012929 304101500682614194509697)
                  ·
                    rfl

theorem cell20_666265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_666265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666265 prefixEnd_666265 := by exact prefixLift 666265
  have htrace : WordTrace (prefixWord ++ tailWord_666265) baseStart_666265 baseEnd_666265 := by
    simpa [prefixWord, tailWord_666265, baseEnd_666265] using wordTrace_append hprefix tailTrace_666265
  have hstable : (prefixWord ++ tailWord_666265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666265).length < 2 ^ (prefixWord ++ tailWord_666265).sum := by decide
  have hdescent : baseEnd_666265 < baseStart_666265 := by decide
  rcases family_descends (prefixWord ++ tailWord_666265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666293 : List Nat := [1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_666293 : Nat := 118140960795 + 666293 * 2 ^ 59
def prefixEnd_666293 : Nat := 4983230072969 + 3 ^ 40 * 666293 * 2
def baseEnd_666293 : Nat := 101371426881856847192083

theorem tailTrace_666293 : CollatzResearch.WordTrace tailWord_666293 prefixEnd_666293 101371426881856847192083 := by
  unfold tailWord_666293
  simp only [CollatzResearch.WordTrace]
  refine ⟨24301702175141729629923533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16201134783427819753282355 24301702175141729629923533)
  ·
    refine ⟨9113138315678148611221325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24301702175141729629923533 9113138315678148611221325)
    ·
      refine ⟨3417426868379305729207997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9113138315678148611221325 3417426868379305729207997)
      ·
        refine ⟨1281535075642239648452999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3417426868379305729207997 1281535075642239648452999)
        ·
          refine ⟨1922302613463359472679499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281535075642239648452999 1922302613463359472679499)
          ·
            refine ⟨2883453920195039209019249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922302613463359472679499 2883453920195039209019249)
            ·
              refine ⟨2162590440146279406764437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2883453920195039209019249 2162590440146279406764437)
              ·
                refine ⟨101371426881856847192083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2162590440146279406764437 101371426881856847192083)
                ·
                  rfl

theorem cell20_666293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_666293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666293 prefixEnd_666293 := by exact prefixLift 666293
  have htrace : WordTrace (prefixWord ++ tailWord_666293) baseStart_666293 baseEnd_666293 := by
    simpa [prefixWord, tailWord_666293, baseEnd_666293] using wordTrace_append hprefix tailTrace_666293
  have hstable : (prefixWord ++ tailWord_666293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666293).length < 2 ^ (prefixWord ++ tailWord_666293).sum := by decide
  have hdescent : baseEnd_666293 < baseStart_666293 := by decide
  rcases family_descends (prefixWord ++ tailWord_666293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666310 : List Nat := [6, 1, 2, 1, 10]
def baseStart_666310 : Nat := 118140960795 + 666310 * 2 ^ 59
def prefixEnd_666310 : Nat := 4983230072969 + 3 ^ 40 * 666310 * 2
def baseEnd_666310 : Nat := 3754593085293753555673

theorem tailTrace_666310 : CollatzResearch.WordTrace tailWord_666310 prefixEnd_666310 3754593085293753555673 := by
  unfold tailWord_666310
  simp only [CollatzResearch.WordTrace]
  refine ⟨759447569252504422915387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16201548144053427688861589 759447569252504422915387)
  ·
    refine ⟨1139171353878756634373081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 759447569252504422915387 1139171353878756634373081)
    ·
      refine ⟨854378515409067475779811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1139171353878756634373081 854378515409067475779811)
      ·
        refine ⟨1281567773113601213669717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854378515409067475779811 1281567773113601213669717)
        ·
          refine ⟨3754593085293753555673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1281567773113601213669717 3754593085293753555673)
          ·
            rfl

theorem cell20_666310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 10].length) (baseStart_666310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666310 prefixEnd_666310 := by exact prefixLift 666310
  have htrace : WordTrace (prefixWord ++ tailWord_666310) baseStart_666310 baseEnd_666310 := by
    simpa [prefixWord, tailWord_666310, baseEnd_666310] using wordTrace_append hprefix tailTrace_666310
  have hstable : (prefixWord ++ tailWord_666310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666310).length < 2 ^ (prefixWord ++ tailWord_666310).sum := by decide
  have hdescent : baseEnd_666310 < baseStart_666310 := by decide
  rcases family_descends (prefixWord ++ tailWord_666310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666314 : List Nat := [3, 1, 2, 1, 4, 9]
def baseStart_666314 : Nat := 118140960795 + 666314 * 2 ^ 59
def prefixEnd_666314 : Nat := 4983230072969 + 3 ^ 40 * 666314 * 2
def baseEnd_666314 : Nat := 11263846874732881550969

theorem tailTrace_666314 : CollatzResearch.WordTrace tailWord_666314 prefixEnd_666314 11263846874732881550969 := by
  unfold tailWord_666314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075617027016412554109499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16201645405377100144291997 6075617027016412554109499)
  ·
    refine ⟨9113425540524618831164249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6075617027016412554109499 9113425540524618831164249)
    ·
      refine ⟨6835069155393464123373187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9113425540524618831164249 6835069155393464123373187)
      ·
        refine ⟨10252603733090196185059781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835069155393464123373187 10252603733090196185059781)
        ·
          refine ⟨1922363199954411784698709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10252603733090196185059781 1922363199954411784698709)
          ·
            refine ⟨11263846874732881550969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1922363199954411784698709 11263846874732881550969)
            ·
              rfl

theorem cell20_666314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 9].length) (baseStart_666314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666314 prefixEnd_666314 := by exact prefixLift 666314
  have htrace : WordTrace (prefixWord ++ tailWord_666314) baseStart_666314 baseEnd_666314 := by
    simpa [prefixWord, tailWord_666314, baseEnd_666314] using wordTrace_append hprefix tailTrace_666314
  have hstable : (prefixWord ++ tailWord_666314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666314).length < 2 ^ (prefixWord ++ tailWord_666314).sum := by decide
  have hdescent : baseEnd_666314 < baseStart_666314 := by decide
  rcases family_descends (prefixWord ++ tailWord_666314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666359 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_666359 : Nat := 118140960795 + 666359 * 2 ^ 59
def prefixEnd_666359 : Nat := 4983230072969 + 3 ^ 40 * 666359 * 2
def baseEnd_666359 : Nat := 304144404843967645375979

theorem tailTrace_666359 : CollatzResearch.WordTrace tailWord_666359 prefixEnd_666359 304144404843967645375979 := by
  unfold tailWord_666359
  simp only [CollatzResearch.WordTrace]
  refine ⟨24304109392902622901826131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16202739595268415267884087 24304109392902622901826131)
  ·
    refine ⟨36456164089353934352739197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24304109392902622901826131 36456164089353934352739197)
    ·
      refine ⟨13671061533507725382277199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36456164089353934352739197 13671061533507725382277199)
      ·
        refine ⟨20506592300261588073415799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13671061533507725382277199 20506592300261588073415799)
        ·
          refine ⟨30759888450392382110123699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20506592300261588073415799 30759888450392382110123699)
          ·
            refine ⟨46139832675588573165185549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30759888450392382110123699 46139832675588573165185549)
            ·
              refine ⟨17302437253345714936944581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46139832675588573165185549 17302437253345714936944581)
              ·
                refine ⟨3244206985002321550677109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17302437253345714936944581 3244206985002321550677109)
                ·
                  refine ⟨304144404843967645375979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244206985002321550677109 304144404843967645375979)
                  ·
                    rfl

theorem cell20_666359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_666359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666359 prefixEnd_666359 := by exact prefixLift 666359
  have htrace : WordTrace (prefixWord ++ tailWord_666359) baseStart_666359 baseEnd_666359 := by
    simpa [prefixWord, tailWord_666359, baseEnd_666359] using wordTrace_append hprefix tailTrace_666359
  have hstable : (prefixWord ++ tailWord_666359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666359).length < 2 ^ (prefixWord ++ tailWord_666359).sum := by decide
  have hdescent : baseEnd_666359 < baseStart_666359 := by decide
  rcases family_descends (prefixWord ++ tailWord_666359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666362 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_666362 : Nat := 118140960795 + 666362 * 2 ^ 59
def prefixEnd_666362 : Nat := 4983230072969 + 3 ^ 40 * 666362 * 2
def baseEnd_666362 : Nat := 304145774125712968275967

theorem tailTrace_666362 : CollatzResearch.WordTrace tailWord_666362 prefixEnd_666362 304145774125712968275967 := by
  unfold tailWord_666362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6076054702972938603546335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16202812541261169609456893 6076054702972938603546335)
  ·
    refine ⟨9114082054459407905319503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6076054702972938603546335 9114082054459407905319503)
    ·
      refine ⟨13671123081689111857979255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114082054459407905319503 13671123081689111857979255)
      ·
        refine ⟨20506684622533667786968883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13671123081689111857979255 20506684622533667786968883)
        ·
          refine ⟨30760026933800501680453325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20506684622533667786968883 30760026933800501680453325)
          ·
            refine ⟨11535010100175188130169997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30760026933800501680453325 11535010100175188130169997)
            ·
              refine ⟨4325628787565695548813749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11535010100175188130169997 4325628787565695548813749)
              ·
                refine ⟨405527698834283957701289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4325628787565695548813749 405527698834283957701289)
                ·
                  refine ⟨304145774125712968275967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405527698834283957701289 304145774125712968275967)
                  ·
                    rfl

theorem cell20_666362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_666362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666362 prefixEnd_666362 := by exact prefixLift 666362
  have htrace : WordTrace (prefixWord ++ tailWord_666362) baseStart_666362 baseEnd_666362 := by
    simpa [prefixWord, tailWord_666362, baseEnd_666362] using wordTrace_append hprefix tailTrace_666362
  have hstable : (prefixWord ++ tailWord_666362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666362).length < 2 ^ (prefixWord ++ tailWord_666362).sum := by decide
  have hdescent : baseEnd_666362 < baseStart_666362 := by decide
  rcases family_descends (prefixWord ++ tailWord_666362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666376 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_666376 : Nat := 118140960795 + 666376 * 2 ^ 59
def prefixEnd_666376 : Nat := 4983230072969 + 3 ^ 40 * 666376 * 2
def baseEnd_666376 : Nat := 304152164107191141809243

theorem tailTrace_666376 : CollatzResearch.WordTrace tailWord_666376 prefixEnd_666376 304152164107191141809243 := by
  unfold tailWord_666376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152364716920517402597491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16203152955894023203463321 12152364716920517402597491)
  ·
    refine ⟨18228547075380776103896237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12152364716920517402597491 18228547075380776103896237)
    ·
      refine ⟨6835705153267791038961089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18228547075380776103896237 6835705153267791038961089)
      ·
        refine ⟨5126778864950843279220817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6835705153267791038961089 5126778864950843279220817)
        ·
          refine ⟨3845084148713132459415613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5126778864950843279220817 3845084148713132459415613)
          ·
            refine ⟨1441906555767424672280855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3845084148713132459415613 1441906555767424672280855)
            ·
              refine ⟨2162859833651137008421283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441906555767424672280855 2162859833651137008421283)
              ·
                refine ⟨3244289750476705512631925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162859833651137008421283 3244289750476705512631925)
                ·
                  refine ⟨304152164107191141809243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244289750476705512631925 304152164107191141809243)
                  ·
                    rfl

theorem cell20_666376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_666376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666376 prefixEnd_666376 := by exact prefixLift 666376
  have htrace : WordTrace (prefixWord ++ tailWord_666376) baseStart_666376 baseEnd_666376 := by
    simpa [prefixWord, tailWord_666376, baseEnd_666376] using wordTrace_append hprefix tailTrace_666376
  have hstable : (prefixWord ++ tailWord_666376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666376).length < 2 ^ (prefixWord ++ tailWord_666376).sum := by decide
  have hdescent : baseEnd_666376 < baseStart_666376 := by decide
  rcases family_descends (prefixWord ++ tailWord_666376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666383 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_666383 : Nat := 118140960795 + 666383 * 2 ^ 59
def prefixEnd_666383 : Nat := 4983230072969 + 3 ^ 40 * 666383 * 2
def baseEnd_666383 : Nat := 304155359097930228575881

theorem tailTrace_666383 : CollatzResearch.WordTrace tailWord_666383 prefixEnd_666383 304155359097930228575881 := by
  unfold tailWord_666383
  simp only [CollatzResearch.WordTrace]
  refine ⟨24304984744815675000699803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16203323163210450000466535 24304984744815675000699803)
  ·
    refine ⟨36457477117223512501049705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24304984744815675000699803 36457477117223512501049705)
    ·
      refine ⟨27343107837917634375787279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36457477117223512501049705 27343107837917634375787279)
      ·
        refine ⟨41014661756876451563680919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27343107837917634375787279 41014661756876451563680919)
        ·
          refine ⟨61521992635314677345521379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41014661756876451563680919 61521992635314677345521379)
          ·
            refine ⟨92282988952972016018282069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61521992635314677345521379 92282988952972016018282069)
            ·
              refine ⟨1081441276792640812714243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 92282988952972016018282069 1081441276792640812714243)
              ·
                refine ⟨1622161915188961219071365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081441276792640812714243 1622161915188961219071365)
                ·
                  refine ⟨304155359097930228575881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622161915188961219071365 304155359097930228575881)
                  ·
                    rfl

theorem cell20_666383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_666383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666383 prefixEnd_666383 := by exact prefixLift 666383
  have htrace : WordTrace (prefixWord ++ tailWord_666383) baseStart_666383 baseEnd_666383 := by
    simpa [prefixWord, tailWord_666383, baseEnd_666383] using wordTrace_append hprefix tailTrace_666383
  have hstable : (prefixWord ++ tailWord_666383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666383).length < 2 ^ (prefixWord ++ tailWord_666383).sum := by decide
  have hdescent : baseEnd_666383 < baseStart_666383 := by decide
  rcases family_descends (prefixWord ++ tailWord_666383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666435 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_666435 : Nat := 118140960795 + 666435 * 2 ^ 59
def prefixEnd_666435 : Nat := 4983230072969 + 3 ^ 40 * 666435 * 2
def baseEnd_666435 : Nat := 304179093314849158842335

theorem tailTrace_666435 : CollatzResearch.WordTrace tailWord_666435 prefixEnd_666435 304179093314849158842335 := by
  unfold tailWord_666435
  simp only [CollatzResearch.WordTrace]
  refine ⟨24306881340627287881592759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16204587560418191921061839 24306881340627287881592759)
  ·
    refine ⟨36460322010940931822389139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24306881340627287881592759 36460322010940931822389139)
    ·
      refine ⟨54690483016411397733583709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36460322010940931822389139 54690483016411397733583709)
      ·
        refine ⟨20508931131154274150093891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54690483016411397733583709 20508931131154274150093891)
        ·
          refine ⟨30763396696731411225140837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20508931131154274150093891 30763396696731411225140837)
          ·
            refine ⟨5768136880637139604713907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30763396696731411225140837 5768136880637139604713907)
            ·
              refine ⟨8652205320955709407070861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5768136880637139604713907 8652205320955709407070861)
              ·
                refine ⟨3244576995358391027651573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8652205320955709407070861 3244576995358391027651573)
                ·
                  refine ⟨304179093314849158842335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244576995358391027651573 304179093314849158842335)
                  ·
                    rfl

theorem cell20_666435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_666435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666435 prefixEnd_666435 := by exact prefixLift 666435
  have htrace : WordTrace (prefixWord ++ tailWord_666435) baseStart_666435 baseEnd_666435 := by
    simpa [prefixWord, tailWord_666435, baseEnd_666435] using wordTrace_append hprefix tailTrace_666435
  have hstable : (prefixWord ++ tailWord_666435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666435).length < 2 ^ (prefixWord ++ tailWord_666435).sum := by decide
  have hdescent : baseEnd_666435 < baseStart_666435 := by decide
  rcases family_descends (prefixWord ++ tailWord_666435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666476 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 2]
def baseStart_666476 : Nat := 118140960795 + 666476 * 2 ^ 59
def prefixEnd_666476 : Nat := 4983230072969 + 3 ^ 40 * 666476 * 2
def baseEnd_666476 : Nat := 304197806832035238475501

theorem tailTrace_666476 : CollatzResearch.WordTrace tailWord_666476 prefixEnd_666476 304197806832035238475501 := by
  unfold tailWord_666476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154188366739375941917641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16205584488985834589223521 12154188366739375941917641)
  ·
    refine ⟨9115641275054531956438231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12154188366739375941917641 9115641275054531956438231)
    ·
      refine ⟨13673461912581797934657347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9115641275054531956438231 13673461912581797934657347)
      ·
        refine ⟨20510192868872696901986021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13673461912581797934657347 20510192868872696901986021)
        ·
          refine ⟨3845661162913630669122379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20510192868872696901986021 3845661162913630669122379)
          ·
            refine ⟨5768491744370446003683569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845661162913630669122379 5768491744370446003683569)
            ·
              refine ⟨4326368808277834502762677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5768491744370446003683569 4326368808277834502762677)
              ·
                refine ⟨405597075776046984634001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4326368808277834502762677 405597075776046984634001)
                ·
                  refine ⟨304197806832035238475501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405597075776046984634001 304197806832035238475501)
                  ·
                    rfl

theorem cell20_666476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_666476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666476 prefixEnd_666476 := by exact prefixLift 666476
  have htrace : WordTrace (prefixWord ++ tailWord_666476) baseStart_666476 baseEnd_666476 := by
    simpa [prefixWord, tailWord_666476, baseEnd_666476] using wordTrace_append hprefix tailTrace_666476
  have hstable : (prefixWord ++ tailWord_666476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666476).length < 2 ^ (prefixWord ++ tailWord_666476).sum := by decide
  have hdescent : baseEnd_666476 < baseStart_666476 := by decide
  rcases family_descends (prefixWord ++ tailWord_666476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666486 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_666486 : Nat := 118140960795 + 666486 * 2 ^ 59
def prefixEnd_666486 : Nat := 4983230072969 + 3 ^ 40 * 666486 * 2
def baseEnd_666486 : Nat := 304202371104519648142127

theorem tailTrace_666486 : CollatzResearch.WordTrace tailWord_666486 prefixEnd_666486 304202371104519648142127 := by
  unfold tailWord_666486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519296341465157724481207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16205827642295015727799541 1519296341465157724481207)
  ·
    refine ⟨2278944512197736586721811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519296341465157724481207 2278944512197736586721811)
    ·
      refine ⟨3418416768296604880082717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278944512197736586721811 3418416768296604880082717)
      ·
        refine ⟨1281906288111226830031019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3418416768296604880082717 1281906288111226830031019)
        ·
          refine ⟨1922859432166840245046529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281906288111226830031019 1922859432166840245046529)
          ·
            refine ⟨1442144574125130183784897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922859432166840245046529 1442144574125130183784897)
            ·
              refine ⟨1081608430593847637838673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442144574125130183784897 1081608430593847637838673)
              ·
                refine ⟨811206322945385728379005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081608430593847637838673 811206322945385728379005)
                ·
                  refine ⟨304202371104519648142127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811206322945385728379005 304202371104519648142127)
                  ·
                    rfl

theorem cell20_666486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_666486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666486 prefixEnd_666486 := by exact prefixLift 666486
  have htrace : WordTrace (prefixWord ++ tailWord_666486) baseStart_666486 baseEnd_666486 := by
    simpa [prefixWord, tailWord_666486, baseEnd_666486] using wordTrace_append hprefix tailTrace_666486
  have hstable : (prefixWord ++ tailWord_666486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666486).length < 2 ^ (prefixWord ++ tailWord_666486).sum := by decide
  have hdescent : baseEnd_666486 < baseStart_666486 := by decide
  rcases family_descends (prefixWord ++ tailWord_666486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666493 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 2]
def baseStart_666493 : Nat := 118140960795 + 666493 * 2 ^ 59
def prefixEnd_666493 : Nat := 4983230072969 + 3 ^ 40 * 666493 * 2
def baseEnd_666493 : Nat := 304205566095258734908765

theorem tailTrace_666493 : CollatzResearch.WordTrace tailWord_666493 prefixEnd_666493 304205566095258734908765 := by
  unfold tailWord_666493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308996774417163787204133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16205997849611442524802755 24308996774417163787204133)
  ·
    refine ⟨4557936895203218210100775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24308996774417163787204133 4557936895203218210100775)
    ·
      refine ⟨6836905342804827315151163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4557936895203218210100775 6836905342804827315151163)
      ·
        refine ⟨10255358014207240972726745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836905342804827315151163 10255358014207240972726745)
        ·
          refine ⟨7691518510655430729545059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10255358014207240972726745 7691518510655430729545059)
          ·
            refine ⟨11537277765983146094317589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7691518510655430729545059 11537277765983146094317589)
            ·
              refine ⟨540809895280459973171137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11537277765983146094317589 540809895280459973171137)
              ·
                refine ⟨405607421460344979878353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540809895280459973171137 405607421460344979878353)
                ·
                  refine ⟨304205566095258734908765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405607421460344979878353 304205566095258734908765)
                  ·
                    rfl

theorem cell20_666493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_666493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666493 prefixEnd_666493 := by exact prefixLift 666493
  have htrace : WordTrace (prefixWord ++ tailWord_666493) baseStart_666493 baseEnd_666493 := by
    simpa [prefixWord, tailWord_666493, baseEnd_666493] using wordTrace_append hprefix tailTrace_666493
  have hstable : (prefixWord ++ tailWord_666493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666493).length < 2 ^ (prefixWord ++ tailWord_666493).sum := by decide
  have hdescent : baseEnd_666493 < baseStart_666493 := by decide
  rcases family_descends (prefixWord ++ tailWord_666493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666541 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 3]
def baseStart_666541 : Nat := 118140960795 + 666541 * 2 ^ 59
def prefixEnd_666541 : Nat := 4983230072969 + 3 ^ 40 * 666541 * 2
def baseEnd_666541 : Nat := 304227474603183901308569

theorem tailTrace_666541 : CollatzResearch.WordTrace tailWord_666541 prefixEnd_666541 304227474603183901308569 := by
  unfold tailWord_666541
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310747478243267984951477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16207164985495511989967651 24310747478243267984951477)
  ·
    refine ⟨2279132576085306373589201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24310747478243267984951477 2279132576085306373589201)
    ·
      refine ⟨1709349432063979780191901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2279132576085306373589201 1709349432063979780191901)
      ·
        refine ⟨641006037023992417571963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1709349432063979780191901 641006037023992417571963)
        ·
          refine ⟨961509055535988626357945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641006037023992417571963 961509055535988626357945)
          ·
            refine ⟨721131791651991469768459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 961509055535988626357945 721131791651991469768459)
            ·
              refine ⟨1081697687477987204652689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721131791651991469768459 1081697687477987204652689)
              ·
                refine ⟨811273265608490403489517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081697687477987204652689 811273265608490403489517)
                ·
                  refine ⟨304227474603183901308569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811273265608490403489517 304227474603183901308569)
                  ·
                    rfl

theorem cell20_666541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_666541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666541 prefixEnd_666541 := by exact prefixLift 666541
  have htrace : WordTrace (prefixWord ++ tailWord_666541) baseStart_666541 baseEnd_666541 := by
    simpa [prefixWord, tailWord_666541, baseEnd_666541] using wordTrace_append hprefix tailTrace_666541
  have hstable : (prefixWord ++ tailWord_666541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666541).length < 2 ^ (prefixWord ++ tailWord_666541).sum := by decide
  have hdescent : baseEnd_666541 < baseStart_666541 := by decide
  rcases family_descends (prefixWord ++ tailWord_666541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666548 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 2]
def baseStart_666548 : Nat := 118140960795 + 666548 * 2 ^ 59
def prefixEnd_666548 : Nat := 4983230072969 + 3 ^ 40 * 666548 * 2
def baseEnd_666548 : Nat := 304230669593922988075207

theorem tailTrace_666548 : CollatzResearch.WordTrace tailWord_666548 prefixEnd_666548 304230669593922988075207 := by
  unfold tailWord_666548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155501394608954090228149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16207335192811938786970865 12155501394608954090228149)
  ·
    refine ⟨1139578255744589445958889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12155501394608954090228149 1139578255744589445958889)
    ·
      refine ⟨854683691808442084469167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1139578255744589445958889 854683691808442084469167)
      ·
        refine ⟨1282025537712663126703751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854683691808442084469167 1282025537712663126703751)
        ·
          refine ⟨1923038306568994690055627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282025537712663126703751 1923038306568994690055627)
          ·
            refine ⟨2884557459853492035083441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923038306568994690055627 2884557459853492035083441)
            ·
              refine ⟨2163418094890119026312581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884557459853492035083441 2163418094890119026312581)
              ·
                refine ⟨405640892791897317433609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2163418094890119026312581 405640892791897317433609)
                ·
                  refine ⟨304230669593922988075207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405640892791897317433609 304230669593922988075207)
                  ·
                    rfl

theorem cell20_666548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_666548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666548 prefixEnd_666548 := by exact prefixLift 666548
  have htrace : WordTrace (prefixWord ++ tailWord_666548) baseStart_666548 baseEnd_666548 := by
    simpa [prefixWord, tailWord_666548, baseEnd_666548] using wordTrace_append hprefix tailTrace_666548
  have hstable : (prefixWord ++ tailWord_666548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666548).length < 2 ^ (prefixWord ++ tailWord_666548).sum := by decide
  have hdescent : baseEnd_666548 < baseStart_666548 := by decide
  rcases family_descends (prefixWord ++ tailWord_666548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666552 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 2]
def baseStart_666552 : Nat := 118140960795 + 666552 * 2 ^ 59
def prefixEnd_666552 : Nat := 4983230072969 + 3 ^ 40 * 666552 * 2
def baseEnd_666552 : Nat := 304232495302916751941857

theorem tailTrace_666552 : CollatzResearch.WordTrace tailWord_666552 prefixEnd_666552 304232495302916751941857 := by
  unfold tailWord_666552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155574340601708431800955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16207432454135611242401273 12155574340601708431800955)
  ·
    refine ⟨18233361510902562647701433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12155574340601708431800955 18233361510902562647701433)
    ·
      refine ⟨13675021133176921985776075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18233361510902562647701433 13675021133176921985776075)
      ·
        refine ⟨20512531699765382978664113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13675021133176921985776075 20512531699765382978664113)
        ·
          refine ⟨15384398774824037233998085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20512531699765382978664113 15384398774824037233998085)
          ·
            refine ⟨2884574770279506981374641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15384398774824037233998085 2884574770279506981374641)
            ·
              refine ⟨2163431077709630236030981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884574770279506981374641 2163431077709630236030981)
              ·
                refine ⟨405643327070555669255809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2163431077709630236030981 405643327070555669255809)
                ·
                  refine ⟨304232495302916751941857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405643327070555669255809 304232495302916751941857)
                  ·
                    rfl

theorem cell20_666552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_666552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666552 prefixEnd_666552 := by exact prefixLift 666552
  have htrace : WordTrace (prefixWord ++ tailWord_666552) baseStart_666552 baseEnd_666552 := by
    simpa [prefixWord, tailWord_666552, baseEnd_666552] using wordTrace_append hprefix tailTrace_666552
  have hstable : (prefixWord ++ tailWord_666552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666552).length < 2 ^ (prefixWord ++ tailWord_666552).sum := by decide
  have hdescent : baseEnd_666552 < baseStart_666552 := by decide
  rcases family_descends (prefixWord ++ tailWord_666552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666607 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 2]
def baseStart_666607 : Nat := 118140960795 + 666607 * 2 ^ 59
def prefixEnd_666607 : Nat := 4983230072969 + 3 ^ 40 * 666607 * 2
def baseEnd_666607 : Nat := 304257598801581005108299

theorem tailTrace_666607 : CollatzResearch.WordTrace tailWord_666607 prefixEnd_666607 304257598801581005108299 := by
  unfold tailWord_666607
  simp only [CollatzResearch.WordTrace]
  refine ⟨24313154696004161256854075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16208769797336107504569383 24313154696004161256854075)
  ·
    refine ⟨36469732044006241885281113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24313154696004161256854075 36469732044006241885281113)
    ·
      refine ⟨27352299033004681413960835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36469732044006241885281113 27352299033004681413960835)
      ·
        refine ⟨41028448549507022120941253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27352299033004681413960835 41028448549507022120941253)
        ·
          refine ⟨7692834103032566647676485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41028448549507022120941253 7692834103032566647676485)
          ·
            refine ⟨1442406394318606246439341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7692834103032566647676485 1442406394318606246439341)
            ·
              refine ⟨540902397869477342414753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1442406394318606246439341 540902397869477342414753)
              ·
                refine ⟨405676798402108006811065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540902397869477342414753 405676798402108006811065)
                ·
                  refine ⟨304257598801581005108299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405676798402108006811065 304257598801581005108299)
                  ·
                    rfl

theorem cell20_666607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 2].length) (baseStart_666607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666607 prefixEnd_666607 := by exact prefixLift 666607
  have htrace : WordTrace (prefixWord ++ tailWord_666607) baseStart_666607 baseEnd_666607 := by
    simpa [prefixWord, tailWord_666607, baseEnd_666607] using wordTrace_append hprefix tailTrace_666607
  have hstable : (prefixWord ++ tailWord_666607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666607).length < 2 ^ (prefixWord ++ tailWord_666607).sum := by decide
  have hdescent : baseEnd_666607 < baseStart_666607 := by decide
  rcases family_descends (prefixWord ++ tailWord_666607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666656 : List Nat := [2, 1, 1, 7, 9]
def baseStart_666656 : Nat := 118140960795 + 666656 * 2 ^ 59
def prefixEnd_666656 : Nat := 4983230072969 + 3 ^ 40 * 666656 * 2
def baseEnd_666656 : Nat := 3756542762182155709565

theorem tailTrace_666656 : CollatzResearch.WordTrace tailWord_666656 prefixEnd_666656 3756542762182155709565 := by
  unfold tailWord_666656
  simp only [CollatzResearch.WordTrace]
  refine ⟨12157470936413321312693911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16209961248551095083591881 12157470936413321312693911)
  ·
    refine ⟨18236206404619981969040867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12157470936413321312693911 18236206404619981969040867)
    ·
      refine ⟨27354309606929972953561301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18236206404619981969040867 27354309606929972953561301)
      ·
        refine ⟨641116631412421241099093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27354309606929972953561301 641116631412421241099093)
        ·
          refine ⟨3756542762182155709565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 641116631412421241099093 3756542762182155709565)
          ·
            rfl

theorem cell20_666656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 9].length) (baseStart_666656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666656 prefixEnd_666656 := by exact prefixLift 666656
  have htrace : WordTrace (prefixWord ++ tailWord_666656) baseStart_666656 baseEnd_666656 := by
    simpa [prefixWord, tailWord_666656, baseEnd_666656] using wordTrace_append hprefix tailTrace_666656
  have hstable : (prefixWord ++ tailWord_666656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666656).length < 2 ^ (prefixWord ++ tailWord_666656).sum := by decide
  have hdescent : baseEnd_666656 < baseStart_666656 := by decide
  rcases family_descends (prefixWord ++ tailWord_666656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666680 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_666680 : Nat := 118140960795 + 666680 * 2 ^ 59
def prefixEnd_666680 : Nat := 4983230072969 + 3 ^ 40 * 666680 * 2
def baseEnd_666680 : Nat := 304290917990717195674667

theorem tailTrace_666680 : CollatzResearch.WordTrace tailWord_666680 prefixEnd_666680 304290917990717195674667 := by
  unfold tailWord_666680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12157908612369847362130747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16210544816493129816174329 12157908612369847362130747)
  ·
    refine ⟨18236862918554771043196121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12157908612369847362130747 18236862918554771043196121)
    ·
      refine ⟨13677647188916078282397091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18236862918554771043196121 13677647188916078282397091)
      ·
        refine ⟨20516470783374117423595637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13677647188916078282397091 20516470783374117423595637)
        ·
          refine ⟨1923419135941323508462091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20516470783374117423595637 1923419135941323508462091)
          ·
            refine ⟨2885128703911985262693137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923419135941323508462091 2885128703911985262693137)
            ·
              refine ⟨2163846527933988947019853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885128703911985262693137 2163846527933988947019853)
              ·
                refine ⟨811442447975245855132445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2163846527933988947019853 811442447975245855132445)
                ·
                  refine ⟨304290917990717195674667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811442447975245855132445 304290917990717195674667)
                  ·
                    rfl

theorem cell20_666680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_666680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666680 prefixEnd_666680 := by exact prefixLift 666680
  have htrace : WordTrace (prefixWord ++ tailWord_666680) baseStart_666680 baseEnd_666680 := by
    simpa [prefixWord, tailWord_666680, baseEnd_666680] using wordTrace_append hprefix tailTrace_666680
  have hstable : (prefixWord ++ tailWord_666680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666680).length < 2 ^ (prefixWord ++ tailWord_666680).sum := by decide
  have hdescent : baseEnd_666680 < baseStart_666680 := by decide
  rcases family_descends (prefixWord ++ tailWord_666680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666710 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_666710 : Nat := 118140960795 + 666710 * 2 ^ 59
def prefixEnd_666710 : Nat := 4983230072969 + 3 ^ 40 * 666710 * 2
def baseEnd_666710 : Nat := 304304610808170424674545

theorem tailTrace_666710 : CollatzResearch.WordTrace tailWord_666710 prefixEnd_666710 304304610808170424674545 := by
  unfold tailWord_666710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519806963414438115490849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16211274276420673231902389 1519806963414438115490849)
  ·
    refine ⟨1139855222560828586618137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1519806963414438115490849 1139855222560828586618137)
    ·
      refine ⟨854891416920621439963603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1139855222560828586618137 854891416920621439963603)
      ·
        refine ⟨1282337125380932159945405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854891416920621439963603 1282337125380932159945405)
        ·
          refine ⟨480876422017849559979527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1282337125380932159945405 480876422017849559979527)
          ·
            refine ⟨721314633026774339969291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480876422017849559979527 721314633026774339969291)
            ·
              refine ⟨1081971949540161509953937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721314633026774339969291 1081971949540161509953937)
              ·
                refine ⟨811478962155121132465453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081971949540161509953937 811478962155121132465453)
                ·
                  refine ⟨304304610808170424674545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811478962155121132465453 304304610808170424674545)
                  ·
                    rfl

theorem cell20_666710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_666710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666710 prefixEnd_666710 := by exact prefixLift 666710
  have htrace : WordTrace (prefixWord ++ tailWord_666710) baseStart_666710 baseEnd_666710 := by
    simpa [prefixWord, tailWord_666710, baseEnd_666710] using wordTrace_append hprefix tailTrace_666710
  have hstable : (prefixWord ++ tailWord_666710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666710).length < 2 ^ (prefixWord ++ tailWord_666710).sum := by decide
  have hdescent : baseEnd_666710 < baseStart_666710 := by decide
  rcases family_descends (prefixWord ++ tailWord_666710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666725 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_666725 : Nat := 118140960795 + 666725 * 2 ^ 59
def prefixEnd_666725 : Nat := 4983230072969 + 3 ^ 40 * 666725 * 2
def baseEnd_666725 : Nat := 304311457216897039174483

theorem tailTrace_666725 : CollatzResearch.WordTrace tailWord_666725 prefixEnd_666725 304311457216897039174483 := by
  unfold tailWord_666725
  simp only [CollatzResearch.WordTrace]
  refine ⟨24317458509576667409649629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16211639006384444939766419 24317458509576667409649629)
  ·
    refine ⟨9119046941091250278618611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24317458509576667409649629 9119046941091250278618611)
    ·
      refine ⟨13678570411636875417927917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119046941091250278618611 13678570411636875417927917)
      ·
        refine ⟨5129463904363828281722969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13678570411636875417927917 5129463904363828281722969)
        ·
          refine ⟨3847097928272871211292227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5129463904363828281722969 3847097928272871211292227)
          ·
            refine ⟨5770646892409306816938341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847097928272871211292227 5770646892409306816938341)
            ·
              refine ⟨1081996292326745028175939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5770646892409306816938341 1081996292326745028175939)
              ·
                refine ⟨1622994438490117542263909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081996292326745028175939 1622994438490117542263909)
                ·
                  refine ⟨304311457216897039174483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622994438490117542263909 304311457216897039174483)
                  ·
                    rfl

theorem cell20_666725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_666725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666725 prefixEnd_666725 := by exact prefixLift 666725
  have htrace : WordTrace (prefixWord ++ tailWord_666725) baseStart_666725 baseEnd_666725 := by
    simpa [prefixWord, tailWord_666725, baseEnd_666725] using wordTrace_append hprefix tailTrace_666725
  have hstable : (prefixWord ++ tailWord_666725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666725).length < 2 ^ (prefixWord ++ tailWord_666725).sum := by decide
  have hdescent : baseEnd_666725 < baseStart_666725 := by decide
  rcases family_descends (prefixWord ++ tailWord_666725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666770 : List Nat := [3, 2, 3, 1, 1, 2, 8]
def baseStart_666770 : Nat := 118140960795 + 666770 * 2 ^ 59
def prefixEnd_666770 : Nat := 4983230072969 + 3 ^ 40 * 666770 * 2
def baseEnd_666770 : Nat := 33814666271452986963811

theorem tailTrace_666770 : CollatzResearch.WordTrace tailWord_666770 prefixEnd_666770 33814666271452986963811 := by
  unfold tailWord_666770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6079774948603410023759441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16212733196275760063358509 6079774948603410023759441)
  ·
    refine ⟨4559831211452557517819581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6079774948603410023759441 4559831211452557517819581)
    ·
      refine ⟨1709936704294709069182343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4559831211452557517819581 1709936704294709069182343)
      ·
        refine ⟨2564905056442063603773515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709936704294709069182343 2564905056442063603773515)
        ·
          refine ⟨3847357584663095405660273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564905056442063603773515 3847357584663095405660273)
          ·
            refine ⟨2885518188497321554245205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847357584663095405660273 2885518188497321554245205)
            ·
              refine ⟨33814666271452986963811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2885518188497321554245205 33814666271452986963811)
              ·
                rfl

theorem cell20_666770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_666770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666770 prefixEnd_666770 := by exact prefixLift 666770
  have htrace : WordTrace (prefixWord ++ tailWord_666770) baseStart_666770 baseEnd_666770 := by
    simpa [prefixWord, tailWord_666770, baseEnd_666770] using wordTrace_append hprefix tailTrace_666770
  have hstable : (prefixWord ++ tailWord_666770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666770).length < 2 ^ (prefixWord ++ tailWord_666770).sum := by decide
  have hdescent : baseEnd_666770 < baseStart_666770 := by decide
  rcases family_descends (prefixWord ++ tailWord_666770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666780 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_666780 : Nat := 118140960795 + 666780 * 2 ^ 59
def prefixEnd_666780 : Nat := 4983230072969 + 3 ^ 40 * 666780 * 2
def baseEnd_666780 : Nat := 304336560715561292340925

theorem tailTrace_666780 : CollatzResearch.WordTrace tailWord_666780 prefixEnd_666780 304336560715561292340925 := by
  unfold tailWord_666780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12159732262188705901450897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16212976349584941201934529 12159732262188705901450897)
  ·
    refine ⟨9119799196641529426088173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12159732262188705901450897 9119799196641529426088173)
    ·
      refine ⟨3419924698740573534783065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9119799196641529426088173 3419924698740573534783065)
      ·
        refine ⟨2564943524055430151087299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3419924698740573534783065 2564943524055430151087299)
        ·
          refine ⟨3847415286083145226630949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564943524055430151087299 3847415286083145226630949)
          ·
            refine ⟨721390366140589729993303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3847415286083145226630949 721390366140589729993303)
            ·
              refine ⟨1082085549210884594989955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721390366140589729993303 1082085549210884594989955)
              ·
                refine ⟨1623128323816326892484933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082085549210884594989955 1623128323816326892484933)
                ·
                  refine ⟨304336560715561292340925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623128323816326892484933 304336560715561292340925)
                  ·
                    rfl

theorem cell20_666780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_666780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666780 prefixEnd_666780 := by exact prefixLift 666780
  have htrace : WordTrace (prefixWord ++ tailWord_666780) baseStart_666780 baseEnd_666780 := by
    simpa [prefixWord, tailWord_666780, baseEnd_666780] using wordTrace_append hprefix tailTrace_666780
  have hstable : (prefixWord ++ tailWord_666780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666780).length < 2 ^ (prefixWord ++ tailWord_666780).sum := by decide
  have hdescent : baseEnd_666780 < baseStart_666780 := by decide
  rcases family_descends (prefixWord ++ tailWord_666780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666860 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_666860 : Nat := 118140960795 + 666860 * 2 ^ 59
def prefixEnd_666860 : Nat := 4983230072969 + 3 ^ 40 * 666860 * 2
def baseEnd_666860 : Nat := 304373074895436569673931

theorem tailTrace_666860 : CollatzResearch.WordTrace tailWord_666860 prefixEnd_666860 304373074895436569673931 := by
  unfold tailWord_666860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161191182043792732907017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16214921576058390310542689 12161191182043792732907017)
  ·
    refine ⟨9120893386532844549680263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12161191182043792732907017 9120893386532844549680263)
    ·
      refine ⟨13681340079799266824520395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9120893386532844549680263 13681340079799266824520395)
      ·
        refine ⟨20522010119698900236780593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13681340079799266824520395 20522010119698900236780593)
        ·
          refine ⟨15391507589774175177585445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20522010119698900236780593 15391507589774175177585445)
          ·
            refine ⟨2885907673082657845797271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15391507589774175177585445 2885907673082657845797271)
            ·
              refine ⟨4328861509623986768695907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885907673082657845797271 4328861509623986768695907)
              ·
                refine ⟨6493292264435980153043861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328861509623986768695907 6493292264435980153043861)
                ·
                  refine ⟨304373074895436569673931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6493292264435980153043861 304373074895436569673931)
                  ·
                    rfl

theorem cell20_666860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_666860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666860 prefixEnd_666860 := by exact prefixLift 666860
  have htrace : WordTrace (prefixWord ++ tailWord_666860) baseStart_666860 baseEnd_666860 := by
    simpa [prefixWord, tailWord_666860, baseEnd_666860] using wordTrace_append hprefix tailTrace_666860
  have hstable : (prefixWord ++ tailWord_666860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666860).length < 2 ^ (prefixWord ++ tailWord_666860).sum := by decide
  have hdescent : baseEnd_666860 < baseStart_666860 := by decide
  rcases family_descends (prefixWord ++ tailWord_666860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666863 : List Nat := [1, 1, 2, 1, 7, 1, 3, 4]
def baseStart_666863 : Nat := 118140960795 + 666863 * 2 ^ 59
def prefixEnd_666863 : Nat := 4983230072969 + 3 ^ 40 * 666863 * 2
def baseEnd_666863 : Nat := 101458148059060630857973

theorem tailTrace_666863 : CollatzResearch.WordTrace tailWord_666863 prefixEnd_666863 101458148059060630857973 := by
  unfold tailWord_666863
  simp only [CollatzResearch.WordTrace]
  refine ⟨24322491783076716978173243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16214994522051144652115495 24322491783076716978173243)
  ·
    refine ⟨36483737674615075467259865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24322491783076716978173243 36483737674615075467259865)
    ·
      refine ⟨27362803255961306600444899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36483737674615075467259865 27362803255961306600444899)
      ·
        refine ⟨41044204883941959900667349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27362803255961306600444899 41044204883941959900667349)
        ·
          refine ⟨961973551967389685171891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41044204883941959900667349 961973551967389685171891)
          ·
            refine ⟨1442960327951084527757837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961973551967389685171891 1442960327951084527757837)
            ·
              refine ⟨541110122981656697909189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1442960327951084527757837 541110122981656697909189)
              ·
                refine ⟨101458148059060630857973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541110122981656697909189 101458148059060630857973)
                ·
                  rfl

theorem cell20_666863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_666863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666863 prefixEnd_666863 := by exact prefixLift 666863
  have htrace : WordTrace (prefixWord ++ tailWord_666863) baseStart_666863 baseEnd_666863 := by
    simpa [prefixWord, tailWord_666863, baseEnd_666863] using wordTrace_append hprefix tailTrace_666863
  have hstable : (prefixWord ++ tailWord_666863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666863).length < 2 ^ (prefixWord ++ tailWord_666863).sum := by decide
  have hdescent : baseEnd_666863 < baseStart_666863 := by decide
  rcases family_descends (prefixWord ++ tailWord_666863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666884 : List Nat := [2, 3, 2, 2, 2, 2, 7]
def baseStart_666884 : Nat := 118140960795 + 666884 * 2 ^ 59
def prefixEnd_666884 : Nat := 4983230072969 + 3 ^ 40 * 666884 * 2
def baseEnd_666884 : Nat := 33820447683266572541537

theorem tailTrace_666884 : CollatzResearch.WordTrace tailWord_666884 prefixEnd_666884 33820447683266572541537 := by
  unfold tailWord_666884
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161628858000318782343853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16215505144000425043125137 12161628858000318782343853)
  ·
    refine ⟨4560610821750119543378945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12161628858000318782343853 4560610821750119543378945)
    ·
      refine ⟨3420458116312589657534209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4560610821750119543378945 3420458116312589657534209)
      ·
        refine ⟨2565343587234442243150657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3420458116312589657534209 2565343587234442243150657)
        ·
          refine ⟨1924007690425831682362993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2565343587234442243150657 1924007690425831682362993)
          ·
            refine ⟨1443005767819373761772245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1924007690425831682362993 1443005767819373761772245)
            ·
              refine ⟨33820447683266572541537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1443005767819373761772245 33820447683266572541537)
              ·
                rfl

theorem cell20_666884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_666884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666884 prefixEnd_666884 := by exact prefixLift 666884
  have htrace : WordTrace (prefixWord ++ tailWord_666884) baseStart_666884 baseEnd_666884 := by
    simpa [prefixWord, tailWord_666884, baseEnd_666884] using wordTrace_append hprefix tailTrace_666884
  have hstable : (prefixWord ++ tailWord_666884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666884).length < 2 ^ (prefixWord ++ tailWord_666884).sum := by decide
  have hdescent : baseEnd_666884 < baseStart_666884 := by decide
  rcases family_descends (prefixWord ++ tailWord_666884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666891 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_666891 : Nat := 118140960795 + 666891 * 2 ^ 59
def prefixEnd_666891 : Nat := 4983230072969 + 3 ^ 40 * 666891 * 2
def baseEnd_666891 : Nat := 304387224140138239640471

theorem tailTrace_666891 : CollatzResearch.WordTrace tailWord_666891 prefixEnd_666891 304387224140138239640471 := by
  unfold tailWord_666891
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323513026975277760192527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16215675351316851840128351 24323513026975277760192527)
  ·
    refine ⟨36485269540462916640288791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24323513026975277760192527 36485269540462916640288791)
    ·
      refine ⟨54727904310694374960433187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36485269540462916640288791 54727904310694374960433187)
      ·
        refine ⟨82091856466041562440649781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54727904310694374960433187 82091856466041562440649781)
        ·
          refine ⟨7696111543691396478810917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82091856466041562440649781 7696111543691396478810917)
          ·
            refine ⟨1443020914442136839777047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7696111543691396478810917 1443020914442136839777047)
            ·
              refine ⟨2164531371663205259665571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443020914442136839777047 2164531371663205259665571)
              ·
                refine ⟨3246797057494807889498357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164531371663205259665571 3246797057494807889498357)
                ·
                  refine ⟨304387224140138239640471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3246797057494807889498357 304387224140138239640471)
                  ·
                    rfl

theorem cell20_666891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_666891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666891 prefixEnd_666891 := by exact prefixLift 666891
  have htrace : WordTrace (prefixWord ++ tailWord_666891) baseStart_666891 baseEnd_666891 := by
    simpa [prefixWord, tailWord_666891, baseEnd_666891] using wordTrace_append hprefix tailTrace_666891
  have hstable : (prefixWord ++ tailWord_666891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666891).length < 2 ^ (prefixWord ++ tailWord_666891).sum := by decide
  have hdescent : baseEnd_666891 < baseStart_666891 := by decide
  rcases family_descends (prefixWord ++ tailWord_666891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666894 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_666894 : Nat := 118140960795 + 666894 * 2 ^ 59
def prefixEnd_666894 : Nat := 4983230072969 + 3 ^ 40 * 666894 * 2
def baseEnd_666894 : Nat := 304388593421883562540459

theorem tailTrace_666894 : CollatzResearch.WordTrace tailWord_666894 prefixEnd_666894 304388593421883562540459 := by
  unfold tailWord_666894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040452805745551159068967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16215748297309606181701157 3040452805745551159068967)
  ·
    refine ⟨4560679208618326738603451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3040452805745551159068967 4560679208618326738603451)
    ·
      refine ⟨6841018812927490107905177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560679208618326738603451 6841018812927490107905177)
      ·
        refine ⟨5130764109695617580928883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6841018812927490107905177 5130764109695617580928883)
        ·
          refine ⟨7696146164543426371393325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130764109695617580928883 7696146164543426371393325)
          ·
            refine ⟨2886054811703784889272497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7696146164543426371393325 2886054811703784889272497)
            ·
              refine ⟨2164541108777838666954373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2886054811703784889272497 2164541108777838666954373)
              ·
                refine ⟨405851457895844750053945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2164541108777838666954373 405851457895844750053945)
                ·
                  refine ⟨304388593421883562540459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405851457895844750053945 304388593421883562540459)
                  ·
                    rfl

theorem cell20_666894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_666894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666894 prefixEnd_666894 := by exact prefixLift 666894
  have htrace : WordTrace (prefixWord ++ tailWord_666894) baseStart_666894 baseEnd_666894 := by
    simpa [prefixWord, tailWord_666894, baseEnd_666894] using wordTrace_append hprefix tailTrace_666894
  have hstable : (prefixWord ++ tailWord_666894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666894).length < 2 ^ (prefixWord ++ tailWord_666894).sum := by decide
  have hdescent : baseEnd_666894 < baseStart_666894 := by decide
  rcases family_descends (prefixWord ++ tailWord_666894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666929 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_666929 : Nat := 118140960795 + 666929 * 2 ^ 59
def prefixEnd_666929 : Nat := 4983230072969 + 3 ^ 40 * 666929 * 2
def baseEnd_666929 : Nat := 304404568375578996373649

theorem tailTrace_666929 : CollatzResearch.WordTrace tailWord_666929 prefixEnd_666929 304404568375578996373649 := by
  unfold tailWord_666929
  simp only [CollatzResearch.WordTrace]
  refine ⟨24324899000837610250075841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16216599333891740166717227 24324899000837610250075841)
  ·
    refine ⟨18243674250628207687556881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24324899000837610250075841 18243674250628207687556881)
    ·
      refine ⟨13682755687971155765667661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18243674250628207687556881 13682755687971155765667661)
      ·
        refine ⟨5131033382989183412125373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13682755687971155765667661 5131033382989183412125373)
        ·
          refine ⟨1924137518620943779547015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5131033382989183412125373 1924137518620943779547015)
          ·
            refine ⟨2886206277931415669320523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924137518620943779547015 2886206277931415669320523)
            ·
              refine ⟨4329309416897123503980785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886206277931415669320523 4329309416897123503980785)
              ·
                refine ⟨3246982062672842627985589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4329309416897123503980785 3246982062672842627985589)
                ·
                  refine ⟨304404568375578996373649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3246982062672842627985589 304404568375578996373649)
                  ·
                    rfl

theorem cell20_666929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_666929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666929 prefixEnd_666929 := by exact prefixLift 666929
  have htrace : WordTrace (prefixWord ++ tailWord_666929) baseStart_666929 baseEnd_666929 := by
    simpa [prefixWord, tailWord_666929, baseEnd_666929] using wordTrace_append hprefix tailTrace_666929
  have hstable : (prefixWord ++ tailWord_666929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666929).length < 2 ^ (prefixWord ++ tailWord_666929).sum := by decide
  have hdescent : baseEnd_666929 < baseStart_666929 := by decide
  rcases family_descends (prefixWord ++ tailWord_666929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666943 : List Nat := [1, 1, 2, 2, 4, 2, 8]
def baseStart_666943 : Nat := 118140960795 + 666943 * 2 ^ 59
def prefixEnd_666943 : Nat := 4983230072969 + 3 ^ 40 * 666943 * 2
def baseEnd_666943 : Nat := 33823439817450796656325

theorem tailTrace_666943 : CollatzResearch.WordTrace tailWord_666943 prefixEnd_666943 33823439817450796656325 := by
  unfold tailWord_666943
  simp only [CollatzResearch.WordTrace]
  refine ⟨24325409622786890641085483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16216939748524593760723655 24325409622786890641085483)
  ·
    refine ⟨36488114434180335961628225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24325409622786890641085483 36488114434180335961628225)
    ·
      refine ⟨27366085825635251971221169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36488114434180335961628225 27366085825635251971221169)
      ·
        refine ⟨20524564369226438978415877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27366085825635251971221169 20524564369226438978415877)
        ·
          refine ⟨3848355819229957308452977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20524564369226438978415877 3848355819229957308452977)
          ·
            refine ⟨2886266864422467981339733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3848355819229957308452977 2886266864422467981339733)
            ·
              refine ⟨33823439817450796656325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2886266864422467981339733 33823439817450796656325)
              ·
                rfl

theorem cell20_666943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_666943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666943 prefixEnd_666943 := by exact prefixLift 666943
  have htrace : WordTrace (prefixWord ++ tailWord_666943) baseStart_666943 baseEnd_666943 := by
    simpa [prefixWord, tailWord_666943, baseEnd_666943] using wordTrace_append hprefix tailTrace_666943
  have hstable : (prefixWord ++ tailWord_666943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666943).length < 2 ^ (prefixWord ++ tailWord_666943).sum := by decide
  have hdescent : baseEnd_666943 < baseStart_666943 := by decide
  rcases family_descends (prefixWord ++ tailWord_666943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666953 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 2]
def baseStart_666953 : Nat := 118140960795 + 666953 * 2 ^ 59
def prefixEnd_666953 : Nat := 4983230072969 + 3 ^ 40 * 666953 * 2
def baseEnd_666953 : Nat := 304415522629541579573551

theorem tailTrace_666953 : CollatzResearch.WordTrace tailWord_666953 prefixEnd_666953 304415522629541579573551 := by
  unfold tailWord_666953
  simp only [CollatzResearch.WordTrace]
  refine ⟨24325774352750662348949513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16217182901833774899299675 24325774352750662348949513)
  ·
    refine ⟨18244330764562996761712135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24325774352750662348949513 18244330764562996761712135)
    ·
      refine ⟨27366496146844495142568203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18244330764562996761712135 27366496146844495142568203)
      ·
        refine ⟨41049744220266742713852305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27366496146844495142568203 41049744220266742713852305)
        ·
          refine ⟨30787308165200057035389229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41049744220266742713852305 30787308165200057035389229)
          ·
            refine ⟨11545240561950021388270961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30787308165200057035389229 11545240561950021388270961)
            ·
              refine ⟨8658930421462516041203221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11545240561950021388270961 8658930421462516041203221)
              ·
                refine ⟨405887363506055439431401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8658930421462516041203221 405887363506055439431401)
                ·
                  refine ⟨304415522629541579573551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405887363506055439431401 304415522629541579573551)
                  ·
                    rfl

theorem cell20_666953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_666953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666953 prefixEnd_666953 := by exact prefixLift 666953
  have htrace : WordTrace (prefixWord ++ tailWord_666953) baseStart_666953 baseEnd_666953 := by
    simpa [prefixWord, tailWord_666953, baseEnd_666953] using wordTrace_append hprefix tailTrace_666953
  have hstable : (prefixWord ++ tailWord_666953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666953).length < 2 ^ (prefixWord ++ tailWord_666953).sum := by decide
  have hdescent : baseEnd_666953 < baseStart_666953 := by decide
  rcases family_descends (prefixWord ++ tailWord_666953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666981 : List Nat := [1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_666981 : Nat := 118140960795 + 666981 * 2 ^ 59
def prefixEnd_666981 : Nat := 4983230072969 + 3 ^ 40 * 666981 * 2
def baseEnd_666981 : Nat := 101476100864165975546701

theorem tailTrace_666981 : CollatzResearch.WordTrace tailWord_666981 prefixEnd_666981 101476100864165975546701 := by
  unfold tailWord_666981
  simp only [CollatzResearch.WordTrace]
  refine ⟨24326795596649223130968797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16217863731099482087312531 24326795596649223130968797)
  ·
    refine ⟨9122548348743458674113299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24326795596649223130968797 9122548348743458674113299)
    ·
      refine ⟨13683822523115188011169949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9122548348743458674113299 13683822523115188011169949)
      ·
        refine ⟨5131433446168195504188731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13683822523115188011169949 5131433446168195504188731)
        ·
          refine ⟨7697150169252293256283097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5131433446168195504188731 7697150169252293256283097)
          ·
            refine ⟨5772862626939219942212323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7697150169252293256283097 5772862626939219942212323)
            ·
              refine ⟨8659293940408829913318485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5772862626939219942212323 8659293940408829913318485)
              ·
                refine ⟨101476100864165975546701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8659293940408829913318485 101476100864165975546701)
                ·
                  rfl

theorem cell20_666981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_666981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666981 prefixEnd_666981 := by exact prefixLift 666981
  have htrace : WordTrace (prefixWord ++ tailWord_666981) baseStart_666981 baseEnd_666981 := by
    simpa [prefixWord, tailWord_666981, baseEnd_666981] using wordTrace_append hprefix tailTrace_666981
  have hstable : (prefixWord ++ tailWord_666981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666981).length < 2 ^ (prefixWord ++ tailWord_666981).sum := by decide
  have hdescent : baseEnd_666981 < baseStart_666981 := by decide
  rcases family_descends (prefixWord ++ tailWord_666981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666991 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 2]
def baseStart_666991 : Nat := 118140960795 + 666991 * 2 ^ 59
def prefixEnd_666991 : Nat := 4983230072969 + 3 ^ 40 * 666991 * 2
def baseEnd_666991 : Nat := 304432866864982336306729

theorem tailTrace_666991 : CollatzResearch.WordTrace tailWord_666991 prefixEnd_666991 304432866864982336306729 := by
  unfold tailWord_666991
  simp only [CollatzResearch.WordTrace]
  refine ⟨24327160326612994838832827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16218106884408663225888551 24327160326612994838832827)
  ·
    refine ⟨36490740489919492258249241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24327160326612994838832827 36490740489919492258249241)
    ·
      refine ⟨27368055367439619193686931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36490740489919492258249241 27368055367439619193686931)
      ·
        refine ⟨41052083051159428790530397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27368055367439619193686931 41052083051159428790530397)
        ·
          refine ⟨15394531144184785796448899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41052083051159428790530397 15394531144184785796448899)
          ·
            refine ⟨23091796716277178694673349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15394531144184785796448899 23091796716277178694673349)
            ·
              refine ⟨4329711884301971005251253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23091796716277178694673349 4329711884301971005251253)
              ·
                refine ⟨405910489153309781742305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4329711884301971005251253 405910489153309781742305)
                ·
                  refine ⟨304432866864982336306729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405910489153309781742305 304432866864982336306729)
                  ·
                    rfl

theorem cell20_666991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 2].length) (baseStart_666991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_666991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_666991 prefixEnd_666991 := by exact prefixLift 666991
  have htrace : WordTrace (prefixWord ++ tailWord_666991) baseStart_666991 baseEnd_666991 := by
    simpa [prefixWord, tailWord_666991, baseEnd_666991] using wordTrace_append hprefix tailTrace_666991
  have hstable : (prefixWord ++ tailWord_666991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666991).length < 2 ^ (prefixWord ++ tailWord_666991).sum := by decide
  have hdescent : baseEnd_666991 < baseStart_666991 := by decide
  rcases family_descends (prefixWord ++ tailWord_666991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667057 : List Nat := [1, 2, 2, 4, 1, 1, 9]
def baseStart_667057 : Nat := 118140960795 + 667057 * 2 ^ 59
def prefixEnd_667057 : Nat := 4983230072969 + 3 ^ 40 * 667057 * 2
def baseEnd_667057 : Nat := 33829221229264382234051

theorem tailTrace_667057 : CollatzResearch.WordTrace tailWord_667057 prefixEnd_667057 33829221229264382234051 := by
  unfold tailWord_667057
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329567544373888110735425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16219711696249258740490283 24329567544373888110735425)
  ·
    refine ⟨18247175658280416083051569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24329567544373888110735425 18247175658280416083051569)
    ·
      refine ⟨13685381743710312062288677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18247175658280416083051569 13685381743710312062288677)
      ·
        refine ⟨2566009076945683511679127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13685381743710312062288677 2566009076945683511679127)
        ·
          refine ⟨3849013615418525267518691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566009076945683511679127 3849013615418525267518691)
          ·
            refine ⟨5773520423127787901278037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849013615418525267518691 5773520423127787901278037)
            ·
              refine ⟨33829221229264382234051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5773520423127787901278037 33829221229264382234051)
              ·
                rfl

theorem cell20_667057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_667057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667057 prefixEnd_667057 := by exact prefixLift 667057
  have htrace : WordTrace (prefixWord ++ tailWord_667057) baseStart_667057 baseEnd_667057 := by
    simpa [prefixWord, tailWord_667057, baseEnd_667057] using wordTrace_append hprefix tailTrace_667057
  have hstable : (prefixWord ++ tailWord_667057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667057).length < 2 ^ (prefixWord ++ tailWord_667057).sum := by decide
  have hdescent : baseEnd_667057 < baseStart_667057 := by decide
  rcases family_descends (prefixWord ++ tailWord_667057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667101 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 2]
def baseStart_667101 : Nat := 118140960795 + 667101 * 2 ^ 59
def prefixEnd_667101 : Nat := 4983230072969 + 3 ^ 40 * 667101 * 2
def baseEnd_667101 : Nat := 304483073862310842639613

theorem tailTrace_667101 : CollatzResearch.WordTrace tailWord_667101 prefixEnd_667101 304483073862310842639613 := by
  unfold tailWord_667101
  simp only [CollatzResearch.WordTrace]
  refine ⟨24331172356214483625337157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16220781570809655750224771 24331172356214483625337157)
  ·
    refine ⟨4562094816790215679750717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24331172356214483625337157 4562094816790215679750717)
    ·
      refine ⟨1710785556296330879906519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4562094816790215679750717 1710785556296330879906519)
      ·
        refine ⟨2566178334444496319859779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710785556296330879906519 2566178334444496319859779)
        ·
          refine ⟨3849267501666744479789669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566178334444496319859779 3849267501666744479789669)
          ·
            refine ⟨721737656562514589960563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3849267501666744479789669 721737656562514589960563)
            ·
              refine ⟨1082606484843771884940845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721737656562514589960563 1082606484843771884940845)
              ·
                refine ⟨405977431816414456852817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1082606484843771884940845 405977431816414456852817)
                ·
                  refine ⟨304483073862310842639613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405977431816414456852817 304483073862310842639613)
                  ·
                    rfl

theorem cell20_667101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_667101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667101 prefixEnd_667101 := by exact prefixLift 667101
  have htrace : WordTrace (prefixWord ++ tailWord_667101) baseStart_667101 baseEnd_667101 := by
    simpa [prefixWord, tailWord_667101, baseEnd_667101] using wordTrace_append hprefix tailTrace_667101
  have hstable : (prefixWord ++ tailWord_667101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667101).length < 2 ^ (prefixWord ++ tailWord_667101).sum := by decide
  have hdescent : baseEnd_667101 < baseStart_667101 := by decide
  rcases family_descends (prefixWord ++ tailWord_667101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667122 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_667122 : Nat := 118140960795 + 667122 * 2 ^ 59
def prefixEnd_667122 : Nat := 4983230072969 + 3 ^ 40 * 667122 * 2
def baseEnd_667122 : Nat := 304492658834528102939527

theorem tailTrace_667122 : CollatzResearch.WordTrace tailWord_667122 prefixEnd_667122 304492658834528102939527 := by
  unfold tailWord_667122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6082984572284601052962905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16221292192758936141234413 6082984572284601052962905)
  ·
    refine ⟨4562238429213450789722179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6082984572284601052962905 4562238429213450789722179)
    ·
      refine ⟨6843357643820176184583269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562238429213450789722179 6843357643820176184583269)
      ·
        refine ⟨1283129558216283034609363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6843357643820176184583269 1283129558216283034609363)
        ·
          refine ⟨1924694337324424551914045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283129558216283034609363 1924694337324424551914045)
          ·
            refine ⟨721760376496659206967767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1924694337324424551914045 721760376496659206967767)
            ·
              refine ⟨1082640564744988810451651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721760376496659206967767 1082640564744988810451651)
              ·
                refine ⟨1623960847117483215677477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082640564744988810451651 1623960847117483215677477)
                ·
                  refine ⟨304492658834528102939527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623960847117483215677477 304492658834528102939527)
                  ·
                    rfl

theorem cell20_667122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_667122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667122 prefixEnd_667122 := by exact prefixLift 667122
  have htrace : WordTrace (prefixWord ++ tailWord_667122) baseStart_667122 baseEnd_667122 := by
    simpa [prefixWord, tailWord_667122, baseEnd_667122] using wordTrace_append hprefix tailTrace_667122
  have hstable : (prefixWord ++ tailWord_667122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667122).length < 2 ^ (prefixWord ++ tailWord_667122).sum := by decide
  have hdescent : baseEnd_667122 < baseStart_667122 := by decide
  rcases family_descends (prefixWord ++ tailWord_667122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667133 : List Nat := [1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_667133 : Nat := 118140960795 + 667133 * 2 ^ 59
def prefixEnd_667133 : Nat := 4983230072969 + 3 ^ 40 * 667133 * 2
def baseEnd_667133 : Nat := 101499226511420317857605

theorem tailTrace_667133 : CollatzResearch.WordTrace tailWord_667133 prefixEnd_667133 101499226511420317857605 := by
  unfold tailWord_667133
  simp only [CollatzResearch.WordTrace]
  refine ⟨24332339492098553090502053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16221559661399035393668035 24332339492098553090502053)
  ·
    refine ⟨4562313654768478704469135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24332339492098553090502053 4562313654768478704469135)
    ·
      refine ⟨6843470482152718056703703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562313654768478704469135 6843470482152718056703703)
      ·
        refine ⟨10265205723229077085055555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843470482152718056703703 10265205723229077085055555)
        ·
          refine ⟨15397808584843615627583333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10265205723229077085055555 15397808584843615627583333)
          ·
            refine ⟨2887089109658177930171875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15397808584843615627583333 2887089109658177930171875)
            ·
              refine ⟨4330633664487266895257813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887089109658177930171875 4330633664487266895257813)
              ·
                refine ⟨101499226511420317857605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4330633664487266895257813 101499226511420317857605)
                ·
                  rfl

theorem cell20_667133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_667133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667133 prefixEnd_667133 := by exact prefixLift 667133
  have htrace : WordTrace (prefixWord ++ tailWord_667133) baseStart_667133 baseEnd_667133 := by
    simpa [prefixWord, tailWord_667133, baseEnd_667133] using wordTrace_append hprefix tailTrace_667133
  have hstable : (prefixWord ++ tailWord_667133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667133).length < 2 ^ (prefixWord ++ tailWord_667133).sum := by decide
  have hdescent : baseEnd_667133 < baseStart_667133 := by decide
  rcases family_descends (prefixWord ++ tailWord_667133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667171 : List Nat := [1, 1, 1, 4, 5, 8]
def baseStart_667171 : Nat := 118140960795 + 667171 * 2 ^ 59
def prefixEnd_667171 : Nat := 4983230072969 + 3 ^ 40 * 667171 * 2
def baseEnd_667171 : Nat := 11278334213692655937259

theorem tailTrace_667171 : CollatzResearch.WordTrace tailWord_667171 prefixEnd_667171 11278334213692655937259 := by
  unfold tailWord_667171
  simp only [CollatzResearch.WordTrace]
  refine ⟨24333725465960885580385367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16222483643973923720256911 24333725465960885580385367)
  ·
    refine ⟨36500588198941328370578051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24333725465960885580385367 36500588198941328370578051)
    ·
      refine ⟨54750882298411992555867077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36500588198941328370578051 54750882298411992555867077)
      ·
        refine ⟨10265790430952248604225077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54750882298411992555867077 10265790430952248604225077)
        ·
          refine ⟨962417852901773306646101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10265790430952248604225077 962417852901773306646101)
          ·
            refine ⟨11278334213692655937259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 962417852901773306646101 11278334213692655937259)
            ·
              rfl

theorem cell20_667171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 8].length) (baseStart_667171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667171 prefixEnd_667171 := by exact prefixLift 667171
  have htrace : WordTrace (prefixWord ++ tailWord_667171) baseStart_667171 baseEnd_667171 := by
    simpa [prefixWord, tailWord_667171, baseEnd_667171] using wordTrace_append hprefix tailTrace_667171
  have hstable : (prefixWord ++ tailWord_667171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667171).length < 2 ^ (prefixWord ++ tailWord_667171).sum := by decide
  have hdescent : baseEnd_667171 < baseStart_667171 := by decide
  rcases family_descends (prefixWord ++ tailWord_667171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667216 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_667216 : Nat := 118140960795 + 667216 * 2 ^ 59
def prefixEnd_667216 : Nat := 4983230072969 + 3 ^ 40 * 667216 * 2
def baseEnd_667216 : Nat := 304535562995881553805809

theorem tailTrace_667216 : CollatzResearch.WordTrace tailWord_667216 prefixEnd_667216 304535562995881553805809 := by
  unfold tailWord_667216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12167683375398929132886751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16223577833865238843849001 12167683375398929132886751)
  ·
    refine ⟨18251525063098393699330127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12167683375398929132886751 18251525063098393699330127)
    ·
      refine ⟨27377287594647590548995191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18251525063098393699330127 27377287594647590548995191)
      ·
        refine ⟨41065931391971385823492787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27377287594647590548995191 41065931391971385823492787)
        ·
          refine ⟨61598897087957078735239181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41065931391971385823492787 61598897087957078735239181)
          ·
            refine ⟨23099586407983904525714693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61598897087957078735239181 23099586407983904525714693)
            ·
              refine ⟨4331172451496982098571505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23099586407983904525714693 4331172451496982098571505)
              ·
                refine ⟨3248379338622736573928629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4331172451496982098571505 3248379338622736573928629)
                ·
                  refine ⟨304535562995881553805809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248379338622736573928629 304535562995881553805809)
                  ·
                    rfl

theorem cell20_667216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_667216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667216 prefixEnd_667216 := by exact prefixLift 667216
  have htrace : WordTrace (prefixWord ++ tailWord_667216) baseStart_667216 baseEnd_667216 := by
    simpa [prefixWord, tailWord_667216, baseEnd_667216] using wordTrace_append hprefix tailTrace_667216
  have hstable : (prefixWord ++ tailWord_667216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667216).length < 2 ^ (prefixWord ++ tailWord_667216).sum := by decide
  have hdescent : baseEnd_667216 < baseStart_667216 := by decide
  rcases family_descends (prefixWord ++ tailWord_667216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667222 : List Nat := [5, 2, 2, 2, 1, 1, 7]
def baseStart_667222 : Nat := 118140960795 + 667222 * 2 ^ 59
def prefixEnd_667222 : Nat := 4983230072969 + 3 ^ 40 * 667222 * 2
def baseEnd_667222 : Nat := 33837589062152466622865

theorem tailTrace_667222 : CollatzResearch.WordTrace tailWord_667222 prefixEnd_667222 33837589062152466622865 := by
  unfold tailWord_667222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520974099298507580655745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16223723725850747526994613 1520974099298507580655745)
  ·
    refine ⟨1140730574473880685491809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1520974099298507580655745 1140730574473880685491809)
    ·
      refine ⟨855547930855410514118857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1140730574473880685491809 855547930855410514118857)
      ·
        refine ⟨641660948141557885589143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855547930855410514118857 641660948141557885589143)
        ·
          refine ⟨962491422212336828383715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641660948141557885589143 962491422212336828383715)
          ·
            refine ⟨1443737133318505242575573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962491422212336828383715 1443737133318505242575573)
            ·
              refine ⟨33837589062152466622865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1443737133318505242575573 33837589062152466622865)
              ·
                rfl

theorem cell20_667222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 7].length) (baseStart_667222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667222 prefixEnd_667222 := by exact prefixLift 667222
  have htrace : WordTrace (prefixWord ++ tailWord_667222) baseStart_667222 baseEnd_667222 := by
    simpa [prefixWord, tailWord_667222, baseEnd_667222] using wordTrace_append hprefix tailTrace_667222
  have hstable : (prefixWord ++ tailWord_667222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667222).length < 2 ^ (prefixWord ++ tailWord_667222).sum := by decide
  have hdescent : baseEnd_667222 < baseStart_667222 := by decide
  rcases family_descends (prefixWord ++ tailWord_667222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667229 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 5]
def baseStart_667229 : Nat := 118140960795 + 667229 * 2 ^ 59
def prefixEnd_667229 : Nat := 4983230072969 + 3 ^ 40 * 667229 * 2
def baseEnd_667229 : Nat := 304541496550111286372423

theorem tailTrace_667229 : CollatzResearch.WordTrace tailWord_667229 prefixEnd_667229 304541496550111286372423 := by
  unfold tailWord_667229
  simp only [CollatzResearch.WordTrace]
  refine ⟨24335840899750761485996741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16223893933167174323997827 24335840899750761485996741)
  ·
    refine ⟨4562970168703267778624389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24335840899750761485996741 4562970168703267778624389)
    ·
      refine ⟨855556906631862708492073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4562970168703267778624389 855556906631862708492073)
      ·
        refine ⟨641667679973897031369055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855556906631862708492073 641667679973897031369055)
        ·
          refine ⟨962501519960845547053583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641667679973897031369055 962501519960845547053583)
          ·
            refine ⟨1443752279941268320580375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962501519960845547053583 1443752279941268320580375)
            ·
              refine ⟨2165628419911902480870563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443752279941268320580375 2165628419911902480870563)
              ·
                refine ⟨3248442629867853721305845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165628419911902480870563 3248442629867853721305845)
                ·
                  refine ⟨304541496550111286372423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3248442629867853721305845 304541496550111286372423)
                  ·
                    rfl

theorem cell20_667229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_667229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667229 prefixEnd_667229 := by exact prefixLift 667229
  have htrace : WordTrace (prefixWord ++ tailWord_667229) baseStart_667229 baseEnd_667229 := by
    simpa [prefixWord, tailWord_667229, baseEnd_667229] using wordTrace_append hprefix tailTrace_667229
  have hstable : (prefixWord ++ tailWord_667229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667229).length < 2 ^ (prefixWord ++ tailWord_667229).sum := by decide
  have hdescent : baseEnd_667229 < baseStart_667229 := by decide
  rcases family_descends (prefixWord ++ tailWord_667229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667274 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_667274 : Nat := 118140960795 + 667274 * 2 ^ 59
def prefixEnd_667274 : Nat := 4983230072969 + 3 ^ 40 * 667274 * 2
def baseEnd_667274 : Nat := 304562035776291129872239

theorem tailTrace_667274 : CollatzResearch.WordTrace tailWord_667274 prefixEnd_667274 304562035776291129872239 := by
  unfold tailWord_667274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6084370546146933542846219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16224988123058489447589917 6084370546146933542846219)
  ·
    refine ⟨9126555819220400314269329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6084370546146933542846219 9126555819220400314269329)
    ·
      refine ⟨6844916864415300235701997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9126555819220400314269329 6844916864415300235701997)
      ·
        refine ⟨2566843824155737588388249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6844916864415300235701997 2566843824155737588388249)
        ·
          refine ⟨1925132868116803191291187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2566843824155737588388249 1925132868116803191291187)
          ·
            refine ⟨2887699302175204786936781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925132868116803191291187 2887699302175204786936781)
            ·
              refine ⟨1082887238315701795101293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2887699302175204786936781 1082887238315701795101293)
              ·
                refine ⟨406082714368388173162985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1082887238315701795101293 406082714368388173162985)
                ·
                  refine ⟨304562035776291129872239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406082714368388173162985 304562035776291129872239)
                  ·
                    rfl

theorem cell20_667274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_667274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667274 prefixEnd_667274 := by exact prefixLift 667274
  have htrace : WordTrace (prefixWord ++ tailWord_667274) baseStart_667274 baseEnd_667274 := by
    simpa [prefixWord, tailWord_667274, baseEnd_667274] using wordTrace_append hprefix tailTrace_667274
  have hstable : (prefixWord ++ tailWord_667274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667274).length < 2 ^ (prefixWord ++ tailWord_667274).sum := by decide
  have hdescent : baseEnd_667274 < baseStart_667274 := by decide
  rcases family_descends (prefixWord ++ tailWord_667274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667340 : List Nat := [2, 2, 1, 5, 3, 7]
def baseStart_667340 : Nat := 118140960795 + 667340 * 2 ^ 59
def prefixEnd_667340 : Nat := 4983230072969 + 3 ^ 40 * 667340 * 2
def baseEnd_667340 : Nat := 11281191110173638284147

theorem tailTrace_667340 : CollatzResearch.WordTrace tailWord_667340 prefixEnd_667340 11281191110173638284147 := by
  unfold tailWord_667340
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169944701174313721643737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16226592934899084962191649 12169944701174313721643737)
  ·
    refine ⟨9127458525880735291232803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12169944701174313721643737 9127458525880735291232803)
    ·
      refine ⟨13691187788821102936849205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9127458525880735291232803 13691187788821102936849205)
      ·
        refine ⟨1283548855201978400329613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13691187788821102936849205 1283548855201978400329613)
        ·
          refine ⟨481330820700741900123605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1283548855201978400329613 481330820700741900123605)
          ·
            refine ⟨11281191110173638284147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 481330820700741900123605 11281191110173638284147)
            ·
              rfl

theorem cell20_667340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 7].length) (baseStart_667340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667340 prefixEnd_667340 := by exact prefixLift 667340
  have htrace : WordTrace (prefixWord ++ tailWord_667340) baseStart_667340 baseEnd_667340 := by
    simpa [prefixWord, tailWord_667340, baseEnd_667340] using wordTrace_append hprefix tailTrace_667340
  have hstable : (prefixWord ++ tailWord_667340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667340).length < 2 ^ (prefixWord ++ tailWord_667340).sum := by decide
  have hdescent : baseEnd_667340 < baseStart_667340 := by decide
  rcases family_descends (prefixWord ++ tailWord_667340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667378 : List Nat := [3, 2, 1, 3, 1, 1, 5, 4]
def baseStart_667378 : Nat := 118140960795 + 667378 * 2 ^ 59
def prefixEnd_667378 : Nat := 4983230072969 + 3 ^ 40 * 667378 * 2
def baseEnd_667378 : Nat := 101536501403376330135049

theorem tailTrace_667378 : CollatzResearch.WordTrace tailWord_667378 prefixEnd_667378 101536501403376330135049 := by
  unfold tailWord_667378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085318844052739983292697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16227516917473973288780525 6085318844052739983292697)
  ·
    refine ⟨4563989133039554987469523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6085318844052739983292697 4563989133039554987469523)
    ·
      refine ⟨6845983699559332481204285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563989133039554987469523 6845983699559332481204285)
      ·
        refine ⟨2567243887334749680451607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6845983699559332481204285 2567243887334749680451607)
        ·
          refine ⟨3850865831002124520677411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567243887334749680451607 3850865831002124520677411)
          ·
            refine ⟨5776298746503186781016117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3850865831002124520677411 5776298746503186781016117)
            ·
              refine ⟨541528007484673760720261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5776298746503186781016117 541528007484673760720261)
              ·
                refine ⟨101536501403376330135049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541528007484673760720261 101536501403376330135049)
                ·
                  rfl

theorem cell20_667378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_667378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667378 prefixEnd_667378 := by exact prefixLift 667378
  have htrace : WordTrace (prefixWord ++ tailWord_667378) baseStart_667378 baseEnd_667378 := by
    simpa [prefixWord, tailWord_667378, baseEnd_667378] using wordTrace_append hprefix tailTrace_667378
  have hstable : (prefixWord ++ tailWord_667378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667378).length < 2 ^ (prefixWord ++ tailWord_667378).sum := by decide
  have hdescent : baseEnd_667378 < baseStart_667378 := by decide
  rcases family_descends (prefixWord ++ tailWord_667378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667402 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_667402 : Nat := 118140960795 + 667402 * 2 ^ 59
def prefixEnd_667402 : Nat := 4983230072969 + 3 ^ 40 * 667402 * 2
def baseEnd_667402 : Nat := 304620458464091573605049

theorem tailTrace_667402 : CollatzResearch.WordTrace tailWord_667402 prefixEnd_667402 304620458464091573605049 := by
  unfold tailWord_667402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085537682031003008011115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16228100485416008021362973 6085537682031003008011115)
  ·
    refine ⟨9128306523046504512016673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6085537682031003008011115 9128306523046504512016673)
    ·
      refine ⟨6846229892284878384012505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9128306523046504512016673 6846229892284878384012505)
      ·
        refine ⟨5134672419213658788009379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6846229892284878384012505 5134672419213658788009379)
        ·
          refine ⟨7702008628820488182014069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5134672419213658788009379 7702008628820488182014069)
          ·
            refine ⟨722063308951920767063819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7702008628820488182014069 722063308951920767063819)
            ·
              refine ⟨1083094963427881150595729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722063308951920767063819 1083094963427881150595729)
              ·
                refine ⟨812321222570910862946797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083094963427881150595729 812321222570910862946797)
                ·
                  refine ⟨304620458464091573605049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812321222570910862946797 304620458464091573605049)
                  ·
                    rfl

theorem cell20_667402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_667402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667402 prefixEnd_667402 := by exact prefixLift 667402
  have htrace : WordTrace (prefixWord ++ tailWord_667402) baseStart_667402 baseEnd_667402 := by
    simpa [prefixWord, tailWord_667402, baseEnd_667402] using wordTrace_append hprefix tailTrace_667402
  have hstable : (prefixWord ++ tailWord_667402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667402).length < 2 ^ (prefixWord ++ tailWord_667402).sum := by decide
  have hdescent : baseEnd_667402 < baseStart_667402 := by decide
  rcases family_descends (prefixWord ++ tailWord_667402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667443 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 2]
def baseStart_667443 : Nat := 118140960795 + 667443 * 2 ^ 59
def prefixEnd_667443 : Nat := 4983230072969 + 3 ^ 40 * 667443 * 2
def baseEnd_667443 : Nat := 304639171981277653238215

theorem tailTrace_667443 : CollatzResearch.WordTrace tailWord_667443 prefixEnd_667443 304639171981277653238215 := by
  unfold tailWord_667443
  simp only [CollatzResearch.WordTrace]
  refine ⟨24343646120975476034286983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16229097413983650689524655 24343646120975476034286983)
  ·
    refine ⟨36515469181463214051430475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24343646120975476034286983 36515469181463214051430475)
    ·
      refine ⟨54773203772194821077145713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36515469181463214051430475 54773203772194821077145713)
      ·
        refine ⟨41079902829146115807859285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54773203772194821077145713 41079902829146115807859285)
        ·
          refine ⟨481405111279056044623351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 41079902829146115807859285 481405111279056044623351)
          ·
            refine ⟨722107666918584066935027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481405111279056044623351 722107666918584066935027)
            ·
              refine ⟨1083161500377876100402541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722107666918584066935027 1083161500377876100402541)
              ·
                refine ⟨406185562641703537650953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1083161500377876100402541 406185562641703537650953)
                ·
                  refine ⟨304639171981277653238215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406185562641703537650953 304639171981277653238215)
                  ·
                    rfl

theorem cell20_667443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 2].length) (baseStart_667443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667443 prefixEnd_667443 := by exact prefixLift 667443
  have htrace : WordTrace (prefixWord ++ tailWord_667443) baseStart_667443 baseEnd_667443 := by
    simpa [prefixWord, tailWord_667443, baseEnd_667443] using wordTrace_append hprefix tailTrace_667443
  have hstable : (prefixWord ++ tailWord_667443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667443).length < 2 ^ (prefixWord ++ tailWord_667443).sum := by decide
  have hdescent : baseEnd_667443 < baseStart_667443 := by decide
  rcases family_descends (prefixWord ++ tailWord_667443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667454 : List Nat := [4, 2, 1, 2, 2, 3, 6]
def baseStart_667454 : Nat := 118140960795 + 667454 * 2 ^ 59
def prefixEnd_667454 : Nat := 4983230072969 + 3 ^ 40 * 667454 * 2
def baseEnd_667454 : Nat := 33849354742334500430167

theorem tailTrace_667454 : CollatzResearch.WordTrace tailWord_667454 prefixEnd_667454 33849354742334500430167 := by
  unfold tailWord_667454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043005915491953114117177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16229364882623749941958277 3043005915491953114117177)
  ·
    refine ⟨2282254436618964835587883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3043005915491953114117177 2282254436618964835587883)
    ·
      refine ⟨3423381654928447253381825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282254436618964835587883 3423381654928447253381825)
      ·
        refine ⟨2567536241196335440036369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3423381654928447253381825 2567536241196335440036369)
        ·
          refine ⟨1925652180897251580027277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2567536241196335440036369 1925652180897251580027277)
          ·
            refine ⟨722119567836469342510229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1925652180897251580027277 722119567836469342510229)
            ·
              refine ⟨33849354742334500430167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 722119567836469342510229 33849354742334500430167)
              ·
                rfl

theorem cell20_667454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 6].length) (baseStart_667454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667454 prefixEnd_667454 := by exact prefixLift 667454
  have htrace : WordTrace (prefixWord ++ tailWord_667454) baseStart_667454 baseEnd_667454 := by
    simpa [prefixWord, tailWord_667454, baseEnd_667454] using wordTrace_append hprefix tailTrace_667454
  have hstable : (prefixWord ++ tailWord_667454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667454).length < 2 ^ (prefixWord ++ tailWord_667454).sum := by decide
  have hdescent : baseEnd_667454 < baseStart_667454 := by decide
  rcases family_descends (prefixWord ++ tailWord_667454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667464 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 2]
def baseStart_667464 : Nat := 118140960795 + 667464 * 2 ^ 59
def prefixEnd_667464 : Nat := 4983230072969 + 3 ^ 40 * 667464 * 2
def baseEnd_667464 : Nat := 304648756953494913538129

theorem tailTrace_667464 : CollatzResearch.WordTrace tailWord_667464 prefixEnd_667464 304648756953494913538129 := by
  unfold tailWord_667464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12172206026949698310400723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16229608035932931080534297 12172206026949698310400723)
  ·
    refine ⟨18258309040424547465601085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12172206026949698310400723 18258309040424547465601085)
    ·
      refine ⟨6846865890159205299600407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18258309040424547465601085 6846865890159205299600407)
      ·
        refine ⟨10270298835238807949400611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6846865890159205299600407 10270298835238807949400611)
        ·
          refine ⟨15405448252858211924100917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10270298835238807949400611 15405448252858211924100917)
          ·
            refine ⟨1444260773705457367884461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15405448252858211924100917 1444260773705457367884461)
            ·
              refine ⟨541597790139546512956673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1444260773705457367884461 541597790139546512956673)
              ·
                refine ⟨406198342604659884717505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541597790139546512956673 406198342604659884717505)
                ·
                  refine ⟨304648756953494913538129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406198342604659884717505 304648756953494913538129)
                  ·
                    rfl

theorem cell20_667464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_667464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667464 prefixEnd_667464 := by exact prefixLift 667464
  have htrace : WordTrace (prefixWord ++ tailWord_667464) baseStart_667464 baseEnd_667464 := by
    simpa [prefixWord, tailWord_667464, baseEnd_667464] using wordTrace_append hprefix tailTrace_667464
  have hstable : (prefixWord ++ tailWord_667464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667464).length < 2 ^ (prefixWord ++ tailWord_667464).sum := by decide
  have hdescent : baseEnd_667464 < baseStart_667464 := by decide
  rcases family_descends (prefixWord ++ tailWord_667464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667489 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_667489 : Nat := 118140960795 + 667489 * 2 ^ 59
def prefixEnd_667489 : Nat := 4983230072969 + 3 ^ 40 * 667489 * 2
def baseEnd_667489 : Nat := 304660167634705937704693

theorem tailTrace_667489 : CollatzResearch.WordTrace tailWord_667489 prefixEnd_667489 304660167634705937704693 := by
  unfold tailWord_667489
  simp only [CollatzResearch.WordTrace]
  refine ⟨24345323878808825890461521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16230215919205883926974347 24345323878808825890461521)
  ·
    refine ⟨18258992909106619417846141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24345323878808825890461521 18258992909106619417846141)
    ·
      refine ⟨6847122340914982281692303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18258992909106619417846141 6847122340914982281692303)
      ·
        refine ⟨10270683511372473422538455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847122340914982281692303 10270683511372473422538455)
        ·
          refine ⟨15406025267058710133807683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10270683511372473422538455 15406025267058710133807683)
          ·
            refine ⟨23109037900588065200711525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15406025267058710133807683 23109037900588065200711525)
            ·
              refine ⟨4332944606360262225133411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23109037900588065200711525 4332944606360262225133411)
              ·
                refine ⟨6499416909540393337700117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4332944606360262225133411 6499416909540393337700117)
                ·
                  refine ⟨304660167634705937704693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6499416909540393337700117 304660167634705937704693)
                  ·
                    rfl

theorem cell20_667489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_667489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667489 prefixEnd_667489 := by exact prefixLift 667489
  have htrace : WordTrace (prefixWord ++ tailWord_667489) baseStart_667489 baseEnd_667489 := by
    simpa [prefixWord, tailWord_667489, baseEnd_667489] using wordTrace_append hprefix tailTrace_667489
  have hstable : (prefixWord ++ tailWord_667489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667489).length < 2 ^ (prefixWord ++ tailWord_667489).sum := by decide
  have hdescent : baseEnd_667489 < baseStart_667489 := by decide
  rcases family_descends (prefixWord ++ tailWord_667489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667523 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 2]
def baseStart_667523 : Nat := 118140960795 + 667523 * 2 ^ 59
def prefixEnd_667523 : Nat := 4983230072969 + 3 ^ 40 * 667523 * 2
def baseEnd_667523 : Nat := 304675686161152930571221

theorem tailTrace_667523 : CollatzResearch.WordTrace tailWord_667523 prefixEnd_667523 304675686161152930571221 := by
  unfold tailWord_667523
  simp only [CollatzResearch.WordTrace]
  refine ⟨24346563960685649697199223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16231042640457099798132815 24346563960685649697199223)
  ·
    refine ⟨36519845941028474545798835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24346563960685649697199223 36519845941028474545798835)
    ·
      refine ⟨54779768911542711818698253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36519845941028474545798835 54779768911542711818698253)
      ·
        refine ⟨20542413341828516932011845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54779768911542711818698253 20542413341828516932011845)
        ·
          refine ⟨3851702501592846924752221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20542413341828516932011845 3851702501592846924752221)
          ·
            refine ⟨1444388438097317596782083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3851702501592846924752221 1444388438097317596782083)
            ·
              refine ⟨2166582657145976395173125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444388438097317596782083 2166582657145976395173125)
              ·
                refine ⟨406234248214870574094961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2166582657145976395173125 406234248214870574094961)
                ·
                  refine ⟨304675686161152930571221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406234248214870574094961 304675686161152930571221)
                  ·
                    rfl

theorem cell20_667523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 2].length) (baseStart_667523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667523 prefixEnd_667523 := by exact prefixLift 667523
  have htrace : WordTrace (prefixWord ++ tailWord_667523) baseStart_667523 baseEnd_667523 := by
    simpa [prefixWord, tailWord_667523, baseEnd_667523] using wordTrace_append hprefix tailTrace_667523
  have hstable : (prefixWord ++ tailWord_667523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667523).length < 2 ^ (prefixWord ++ tailWord_667523).sum := by decide
  have hdescent : baseEnd_667523 < baseStart_667523 := by decide
  rcases family_descends (prefixWord ++ tailWord_667523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667582 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_667582 : Nat := 118140960795 + 667582 * 2 ^ 59
def prefixEnd_667582 : Nat := 4983230072969 + 3 ^ 40 * 667582 * 2
def baseEnd_667582 : Nat := 304702615368810947604313

theorem tailTrace_667582 : CollatzResearch.WordTrace tailWord_667582 prefixEnd_667582 304702615368810947604313 := by
  unfold tailWord_667582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043589483433987846699625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16232477244981268515731333 3043589483433987846699625)
  ·
    refine ⟨2282692112575490885024719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3043589483433987846699625 2282692112575490885024719)
    ·
      refine ⟨3424038168863236327537079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282692112575490885024719 3424038168863236327537079)
      ·
        refine ⟨5136057253294854491305619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3424038168863236327537079 5136057253294854491305619)
        ·
          refine ⟨7704085879942281736958429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136057253294854491305619 7704085879942281736958429)
          ·
            refine ⟨2889032204978355651359411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7704085879942281736958429 2889032204978355651359411)
            ·
              refine ⟨4333548307467533477039117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889032204978355651359411 4333548307467533477039117)
              ·
                refine ⟨1625080615300325053889669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4333548307467533477039117 1625080615300325053889669)
                ·
                  refine ⟨304702615368810947604313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625080615300325053889669 304702615368810947604313)
                  ·
                    rfl

theorem cell20_667582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_667582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667582 prefixEnd_667582 := by exact prefixLift 667582
  have htrace : WordTrace (prefixWord ++ tailWord_667582) baseStart_667582 baseEnd_667582 := by
    simpa [prefixWord, tailWord_667582, baseEnd_667582] using wordTrace_append hprefix tailTrace_667582
  have hstable : (prefixWord ++ tailWord_667582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667582).length < 2 ^ (prefixWord ++ tailWord_667582).sum := by decide
  have hdescent : baseEnd_667582 < baseStart_667582 := by decide
  rcases family_descends (prefixWord ++ tailWord_667582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667592 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_667592 : Nat := 118140960795 + 667592 * 2 ^ 59
def prefixEnd_667592 : Nat := 4983230072969 + 3 ^ 40 * 667592 * 2
def baseEnd_667592 : Nat := 304707179641295357270939

theorem tailTrace_667592 : CollatzResearch.WordTrace tailWord_667592 prefixEnd_667592 304707179641295357270939 := by
  unfold tailWord_667592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12174540298717837240730515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16232720398290449654307353 12174540298717837240730515)
  ·
    refine ⟨18261810448076755861095773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12174540298717837240730515 18261810448076755861095773)
    ·
      refine ⟨6848178918028783447910915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18261810448076755861095773 6848178918028783447910915)
      ·
        refine ⟨10272268377043175171866373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848178918028783447910915 10272268377043175171866373)
        ·
          refine ⟨1926050320695595344724945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10272268377043175171866373 1926050320695595344724945)
          ·
            refine ⟨1444537740521696508543709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1926050320695595344724945 1444537740521696508543709)
            ·
              refine ⟨541701652695636190703891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1444537740521696508543709 541701652695636190703891)
              ·
                refine ⟨812552479043454286055837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541701652695636190703891 812552479043454286055837)
                ·
                  refine ⟨304707179641295357270939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812552479043454286055837 304707179641295357270939)
                  ·
                    rfl

theorem cell20_667592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_667592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667592 prefixEnd_667592 := by exact prefixLift 667592
  have htrace : WordTrace (prefixWord ++ tailWord_667592) baseStart_667592 baseEnd_667592 := by
    simpa [prefixWord, tailWord_667592, baseEnd_667592] using wordTrace_append hprefix tailTrace_667592
  have hstable : (prefixWord ++ tailWord_667592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667592).length < 2 ^ (prefixWord ++ tailWord_667592).sum := by decide
  have hdescent : baseEnd_667592 < baseStart_667592 := by decide
  rcases family_descends (prefixWord ++ tailWord_667592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667602 : List Nat := [3, 2, 2, 3, 3, 1, 2, 4]
def baseStart_667602 : Nat := 118140960795 + 667602 * 2 ^ 59
def prefixEnd_667602 : Nat := 4983230072969 + 3 ^ 40 * 667602 * 2
def baseEnd_667602 : Nat := 101570581304593255645855

theorem tailTrace_667602 : CollatzResearch.WordTrace tailWord_667602 prefixEnd_667602 101570581304593255645855 := by
  unfold tailWord_667602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087361331849861547331265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16232963551599630792883373 6087361331849861547331265)
  ·
    refine ⟨4565520998887396160498449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6087361331849861547331265 4565520998887396160498449)
    ·
      refine ⟨3424140749165547120373837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4565520998887396160498449 3424140749165547120373837)
      ·
        refine ⟨1284052780937080170140189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3424140749165547120373837 1284052780937080170140189)
        ·
          refine ⟨481519792851405063802571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1284052780937080170140189 481519792851405063802571)
          ·
            refine ⟨722279689277107595703857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481519792851405063802571 722279689277107595703857)
            ·
              refine ⟨541709766957830696777893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722279689277107595703857 541709766957830696777893)
              ·
                refine ⟨101570581304593255645855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541709766957830696777893 101570581304593255645855)
                ·
                  rfl

theorem cell20_667602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_667602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667602 prefixEnd_667602 := by exact prefixLift 667602
  have htrace : WordTrace (prefixWord ++ tailWord_667602) baseStart_667602 baseEnd_667602 := by
    simpa [prefixWord, tailWord_667602, baseEnd_667602] using wordTrace_append hprefix tailTrace_667602
  have hstable : (prefixWord ++ tailWord_667602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667602).length < 2 ^ (prefixWord ++ tailWord_667602).sum := by decide
  have hdescent : baseEnd_667602 < baseStart_667602 := by decide
  rcases family_descends (prefixWord ++ tailWord_667602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667688 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 2]
def baseStart_667688 : Nat := 118140960795 + 667688 * 2 ^ 59
def prefixEnd_667688 : Nat := 4983230072969 + 3 ^ 40 * 667688 * 2
def baseEnd_667688 : Nat := 304750996657145690070547

theorem tailTrace_667688 : CollatzResearch.WordTrace tailWord_667688 prefixEnd_667688 304750996657145690070547 := by
  unfold tailWord_667688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12176291002543941438477859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16235054670058588584637145 12176291002543941438477859)
  ·
    refine ⟨18264436503815912157716789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12176291002543941438477859 18264436503815912157716789)
    ·
      refine ⟨1712290922232741764785949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18264436503815912157716789 1712290922232741764785949)
      ·
        refine ⟨642109095837278161794731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1712290922232741764785949 642109095837278161794731)
        ·
          refine ⟨963163643755917242692097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642109095837278161794731 963163643755917242692097)
          ·
            refine ⟨722372732816937932019073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963163643755917242692097 722372732816937932019073)
            ·
              refine ⟨541779549612703449014305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722372732816937932019073 541779549612703449014305)
              ·
                refine ⟨406334662209527586760729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541779549612703449014305 406334662209527586760729)
                ·
                  refine ⟨304750996657145690070547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406334662209527586760729 304750996657145690070547)
                  ·
                    rfl

theorem cell20_667688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_667688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667688 prefixEnd_667688 := by exact prefixLift 667688
  have htrace : WordTrace (prefixWord ++ tailWord_667688) baseStart_667688 baseEnd_667688 := by
    simpa [prefixWord, tailWord_667688, baseEnd_667688] using wordTrace_append hprefix tailTrace_667688
  have hstable : (prefixWord ++ tailWord_667688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667688).length < 2 ^ (prefixWord ++ tailWord_667688).sum := by decide
  have hdescent : baseEnd_667688 < baseStart_667688 := by decide
  rcases family_descends (prefixWord ++ tailWord_667688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667724 : List Nat := [2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_667724 : Nat := 118140960795 + 667724 * 2 ^ 59
def prefixEnd_667724 : Nat := 4983230072969 + 3 ^ 40 * 667724 * 2
def baseEnd_667724 : Nat := 101589142679363188290133

theorem tailTrace_667724 : CollatzResearch.WordTrace tailWord_667724 prefixEnd_667724 101589142679363188290133 := by
  unfold tailWord_667724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12176947516478730512633113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16235930021971640683510817 12176947516478730512633113)
  ·
    refine ⟨9132710637359047884474835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12176947516478730512633113 9132710637359047884474835)
    ·
      refine ⟨13699065956038571826712253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9132710637359047884474835 13699065956038571826712253)
      ·
        refine ⟨5137149733514464435017095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13699065956038571826712253 5137149733514464435017095)
        ·
          refine ⟨7705724600271696652525643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137149733514464435017095 7705724600271696652525643)
          ·
            refine ⟨11558586900407544978788465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705724600271696652525643 11558586900407544978788465)
            ·
              refine ⟨8668940175305658734091349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11558586900407544978788465 8668940175305658734091349)
              ·
                refine ⟨101589142679363188290133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8668940175305658734091349 101589142679363188290133)
                ·
                  rfl

theorem cell20_667724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_667724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667724 prefixEnd_667724 := by exact prefixLift 667724
  have htrace : WordTrace (prefixWord ++ tailWord_667724) baseStart_667724 baseEnd_667724 := by
    simpa [prefixWord, tailWord_667724, baseEnd_667724] using wordTrace_append hprefix tailTrace_667724
  have hstable : (prefixWord ++ tailWord_667724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667724).length < 2 ^ (prefixWord ++ tailWord_667724).sum := by decide
  have hdescent : baseEnd_667724 < baseStart_667724 := by decide
  rcases family_descends (prefixWord ++ tailWord_667724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667730 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_667730 : Nat := 118140960795 + 667730 * 2 ^ 59
def prefixEnd_667730 : Nat := 4983230072969 + 3 ^ 40 * 667730 * 2
def baseEnd_667730 : Nat := 304770166601580210670375

theorem tailTrace_667730 : CollatzResearch.WordTrace tailWord_667730 prefixEnd_667730 304770166601580210670375 := by
  unfold tailWord_667730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088528467733931012496161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16236075913957149366656429 6088528467733931012496161)
  ·
    refine ⟨4566396350800448259372121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6088528467733931012496161 4566396350800448259372121)
    ·
      refine ⟨3424797263100336194529091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4566396350800448259372121 3424797263100336194529091)
      ·
        refine ⟨5137195894650504291793637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3424797263100336194529091 5137195894650504291793637)
        ·
          refine ⟨963224230246969554711307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5137195894650504291793637 963224230246969554711307)
          ·
            refine ⟨1444836345370454332066961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963224230246969554711307 1444836345370454332066961)
            ·
              refine ⟨1083627259027840749050221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444836345370454332066961 1083627259027840749050221)
              ·
                refine ⟨406360222135440280893833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1083627259027840749050221 406360222135440280893833)
                ·
                  refine ⟨304770166601580210670375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406360222135440280893833 304770166601580210670375)
                  ·
                    rfl

theorem cell20_667730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_667730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667730 prefixEnd_667730 := by exact prefixLift 667730
  have htrace : WordTrace (prefixWord ++ tailWord_667730) baseStart_667730 baseEnd_667730 := by
    simpa [prefixWord, tailWord_667730, baseEnd_667730] using wordTrace_append hprefix tailTrace_667730
  have hstable : (prefixWord ++ tailWord_667730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667730).length < 2 ^ (prefixWord ++ tailWord_667730).sum := by decide
  have hdescent : baseEnd_667730 < baseStart_667730 := by decide
  rcases family_descends (prefixWord ++ tailWord_667730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667779 : List Nat := [1, 1, 1, 3, 3, 3, 4, 4]
def baseStart_667779 : Nat := 118140960795 + 667779 * 2 ^ 59
def prefixEnd_667779 : Nat := 4983230072969 + 3 ^ 40 * 667779 * 2
def baseEnd_667779 : Nat := 101597510512251272678947

theorem tailTrace_667779 : CollatzResearch.WordTrace tailWord_667779 prefixEnd_667779 101597510512251272678947 := by
  unfold tailWord_667779
  simp only [CollatzResearch.WordTrace]
  refine ⟨24355901047758205418518391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16237267365172136945678927 24355901047758205418518391)
  ·
    refine ⟨36533851571637308127777587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24355901047758205418518391 36533851571637308127777587)
    ·
      refine ⟨54800777357455962191666381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36533851571637308127777587 54800777357455962191666381)
      ·
        refine ⟨20550291509045985821874893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54800777357455962191666381 20550291509045985821874893)
        ·
          refine ⟨7706359315892244683203085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20550291509045985821874893 7706359315892244683203085)
          ·
            refine ⟨2889884743459591756201157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7706359315892244683203085 2889884743459591756201157)
            ·
              refine ⟨541853389398673454287717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2889884743459591756201157 541853389398673454287717)
              ·
                refine ⟨101597510512251272678947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541853389398673454287717 101597510512251272678947)
                ·
                  rfl

theorem cell20_667779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_667779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667779 prefixEnd_667779 := by exact prefixLift 667779
  have htrace : WordTrace (prefixWord ++ tailWord_667779) baseStart_667779 baseEnd_667779 := by
    simpa [prefixWord, tailWord_667779, baseEnd_667779] using wordTrace_append hprefix tailTrace_667779
  have hstable : (prefixWord ++ tailWord_667779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667779).length < 2 ^ (prefixWord ++ tailWord_667779).sum := by decide
  have hdescent : baseEnd_667779 < baseStart_667779 := by decide
  rcases family_descends (prefixWord ++ tailWord_667779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667786 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_667786 : Nat := 118140960795 + 667786 * 2 ^ 59
def prefixEnd_667786 : Nat := 4983230072969 + 3 ^ 40 * 667786 * 2
def baseEnd_667786 : Nat := 304795726527492904803479

theorem tailTrace_667786 : CollatzResearch.WordTrace tailWord_667786 prefixEnd_667786 304795726527492904803479 := by
  unfold tailWord_667786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089039089683211403505803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16237437572488563742682141 6089039089683211403505803)
  ·
    refine ⟨9133558634524817105258705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089039089683211403505803 9133558634524817105258705)
    ·
      refine ⟨6850168975893612828944029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9133558634524817105258705 6850168975893612828944029)
      ·
        refine ⟨2568813365960104810854011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6850168975893612828944029 2568813365960104810854011)
        ·
          refine ⟨3853220048940157216281017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568813365960104810854011 3853220048940157216281017)
          ·
            refine ⟨2889915036705117912210763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3853220048940157216281017 2889915036705117912210763)
            ·
              refine ⟨4334872555057676868316145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889915036705117912210763 4334872555057676868316145)
              ·
                refine ⟨3251154416293257651237109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4334872555057676868316145 3251154416293257651237109)
                ·
                  refine ⟨304795726527492904803479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251154416293257651237109 304795726527492904803479)
                  ·
                    rfl

theorem cell20_667786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_667786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667786 prefixEnd_667786 := by exact prefixLift 667786
  have htrace : WordTrace (prefixWord ++ tailWord_667786) baseStart_667786 baseEnd_667786 := by
    simpa [prefixWord, tailWord_667786, baseEnd_667786] using wordTrace_append hprefix tailTrace_667786
  have hstable : (prefixWord ++ tailWord_667786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667786).length < 2 ^ (prefixWord ++ tailWord_667786).sum := by decide
  have hdescent : baseEnd_667786 < baseStart_667786 := by decide
  rcases family_descends (prefixWord ++ tailWord_667786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667798 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_667798 : Nat := 118140960795 + 667798 * 2 ^ 59
def prefixEnd_667798 : Nat := 4983230072969 + 3 ^ 40 * 667798 * 2
def baseEnd_667798 : Nat := 304801203654474196403431

theorem tailTrace_667798 : CollatzResearch.WordTrace tailWord_667798 prefixEnd_667798 304801203654474196403431 := by
  unfold tailWord_667798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522287127168085728966253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16237729356459581108973365 1522287127168085728966253)
  ·
    refine ⟨570857672688032148362345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1522287127168085728966253 570857672688032148362345)
    ·
      refine ⟨428143254516024111271759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 570857672688032148362345 428143254516024111271759)
      ·
        refine ⟨642214881774036166907639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428143254516024111271759 642214881774036166907639)
        ·
          refine ⟨963322322661054250361459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642214881774036166907639 963322322661054250361459)
          ·
            refine ⟨1444983483991581375542189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963322322661054250361459 1444983483991581375542189)
            ·
              refine ⟨541868806496843015828321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1444983483991581375542189 541868806496843015828321)
              ·
                refine ⟨406401604872632261871241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541868806496843015828321 406401604872632261871241)
                ·
                  refine ⟨304801203654474196403431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406401604872632261871241 304801203654474196403431)
                  ·
                    rfl

theorem cell20_667798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_667798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667798 prefixEnd_667798 := by exact prefixLift 667798
  have htrace : WordTrace (prefixWord ++ tailWord_667798) baseStart_667798 baseEnd_667798 := by
    simpa [prefixWord, tailWord_667798, baseEnd_667798] using wordTrace_append hprefix tailTrace_667798
  have hstable : (prefixWord ++ tailWord_667798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667798).length < 2 ^ (prefixWord ++ tailWord_667798).sum := by decide
  have hdescent : baseEnd_667798 < baseStart_667798 := by decide
  rcases family_descends (prefixWord ++ tailWord_667798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667806 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_667806 : Nat := 118140960795 + 667806 * 2 ^ 59
def prefixEnd_667806 : Nat := 4983230072969 + 3 ^ 40 * 667806 * 2
def baseEnd_667806 : Nat := 304804855072461724136731

theorem tailTrace_667806 : CollatzResearch.WordTrace tailWord_667806 prefixEnd_667806 304804855072461724136731 := by
  unfold tailWord_667806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3044610727332548628718909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16237923879106926019834181 3044610727332548628718909)
  ·
    refine ⟨1141729022749705735769591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3044610727332548628718909 1141729022749705735769591)
    ·
      refine ⟨1712593534124558603654387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141729022749705735769591 1712593534124558603654387)
      ·
        refine ⟨2568890301186837905481581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712593534124558603654387 2568890301186837905481581)
        ·
          refine ⟨963333862945064214555593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2568890301186837905481581 963333862945064214555593)
          ·
            refine ⟨722500397208798160916695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963333862945064214555593 722500397208798160916695)
            ·
              refine ⟨1083750595813197241375043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722500397208798160916695 1083750595813197241375043)
              ·
                refine ⟨1625625893719795862062565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083750595813197241375043 1625625893719795862062565)
                ·
                  refine ⟨304804855072461724136731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625625893719795862062565 304804855072461724136731)
                  ·
                    rfl

theorem cell20_667806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_667806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_667806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_667806 prefixEnd_667806 := by exact prefixLift 667806
  have htrace : WordTrace (prefixWord ++ tailWord_667806) baseStart_667806 baseEnd_667806 := by
    simpa [prefixWord, tailWord_667806, baseEnd_667806] using wordTrace_append hprefix tailTrace_667806
  have hstable : (prefixWord ++ tailWord_667806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667806).length < 2 ^ (prefixWord ++ tailWord_667806).sum := by decide
  have hdescent : baseEnd_667806 < baseStart_667806 := by decide
  rcases family_descends (prefixWord ++ tailWord_667806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
